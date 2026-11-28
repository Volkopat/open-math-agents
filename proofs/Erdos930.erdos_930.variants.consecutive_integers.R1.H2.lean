import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1
import Mathlib

/-!
Hypothesis H2 of the reduction imported above: the product of k consecutive integers
n+1, ..., n+k with 3 <= k < n is not an l-th power when l = 2, or when l is an odd prime
and k < 30000. For odd l the route follows P. Erdos and J. L. Selfridge, The product of
consecutive integers is never a power, Illinois J. Math. 19 (1975), 292-301, with the case
analysis replaced by a finite table checked by decide. The case l = 2 reuses the merged
project proof proofs/Erdos137.erdos_137.variants.perfect_power.R1.H3.R1.H1.lean, which
builds on proofs/Erdos683.erdos_683.variant.sylvester_schur.lean by @senamakel.
-/
-- Credit: @LordMike

namespace OMA.E930

open Finset

-- Fixed data and definitions. Do not change them.

/-- Consecutive primes from `p`, given their gaps in base 128. -/
def dg : ℕ → ℕ → ℕ → List ℕ
  | n + 1, p, x => p :: dg n (p + x % 128) (x / 128)
  | _, _, _ => []

set_option maxRecDepth 100000 in
/-- All primes below 30000. -/
def PL : List ℕ := dg 3245 2 0xc606140c112020c1820c1c107101c7010618483221808316101090c1818404047830434485141418406182810a0410a1010183101018512242060a180830a181830e0c283020c58c0e0868304041041e24308060c3041610104100c502061c1090c0c08b06182030a241810410186040c086040c1860604305020c10a041c1880e2020304240830a0c9011e14085080c101301420512044861c1808502141860c0c5020824107100c203040458110102900428103080c103021818304180830404110040c088140c407063808f0a04281122c181161030304240851e0c6041e20082061818602383830c484090208307040c1811018383120c18b060410a06242810a044010c141860818483122c181060c1010a04183040430b061018f0624302123430208145050c0c2030a10183101c284120820604341010a04305120c383060c2840c2c181041040f0c182020e080880c2420206043030a1c403120418b120418b080830308203850e0c1850e081860c0c0860608088140839a020c182061040602244830a1018212180820250203040c2051e0c301061418a06081870a1c40a040448c0a041820e145020214486121010314182830c1c1071030303080c1861c1030916281070614205121010d0424083062030302185840c48782081418a0620085121c1060808082060c20306143030e0c1060610302061c706060428306101820c30082080c306100c184060808b1e04283020c7820208383040c30704041040a0418b0c30386101c48e0218483060c28704043051230483020820806104060e243030a101010418085020c103081450502241880e0c6030a0419206085020610485021818208140830c1448404044010650082120c08514144810c2018308303030a1808906481060808082021830924084860208187040c30110043030608306020c1070a0c187102418412243050808205022410704183830a0c3010a1c3090a183011e080850214085080c1011c0c0820e08181040c3910e1818206101011e0c4820208783082c5030a240820814183080c1090e0c30b060470404041010a24089041820508241010a101880850089100430304041060c042870c245810c203031e180830a1830118080910214502080c10a0a0410306101821a144840c2008612241820c180820e0c182060c3090818109060428704043030a043060a1018b022c1840a045830c10407040c0860c14205021418a340c187060c3030a0428c061818306041830a0c20202080820e18103020ca070a103080610286061818104300890620089220c0830424383120820b061c30e02080861e14512060818710101860c0c3050c1028c14301821e1808802083850c2810308081830e1810908083860c2008206180890c08089040c1830c10286140c281040c08b08184010a041011c30083040c30112141810a041860a243060214508020c586021420806300860a047820e14088020c1090c28286060418306084830c1808808080820624205080c182120c0911210581041808310105870614203103018308080830a241830220503060818902181820838301061860c04181861a08181121810302200860c0878306101890a3418304300820e0c182063c30302182830e247030e08481060c6020208a810c20203060838202080821834185120430b0e0818306180830424903080c183041c1830c140820208b02080818602080860a1818902182840a1c40704281830a101060e1828406083010a24085060c205021418106084840614483061c3060a041850e0c2840608304161c10f0e18182081418d06082050220206040c2080e08202080c183040c203041c4070c08383040418e02380820604183041c4070a243010a0c202080818602245830e080890a18781062c3851408383040c90a04042870624109021408f043c085080c10112080820e2428116102841208083160c0850218101040c085142018406201870a1c4070a1c305080c1830a281030c044071c041820e0830318102840c1408f040c184041010a0618182063c38306086010404482060c2030c2410106082030448306060430508144830e084840a0c2090c0c18304241810a1818308201830218283080c182080c4030e08304041028602086820e0c58608082030a042810c2020322041040630182020c10c022c181043410a0614085061808306083830614502180c08206101830c0c1012218301100428404286060428103083808b0820183020c30214081870c181850e2008b08081860c10186040c2021a2050202140851218082140c10602140851430283080c4040a047030c0418806041830a0c80508144870608186022410a040c1860808383060820b08380880c043050e08082140808e082c307060808508140861004104060c10a0c24302080c1040a0418b08081810c140831604701220c4840a04188061c1060c04186060830308181030c04483040c30116102811018186020c1030c1c902080c3050e0c303060808b0208085020c283061c18b0604107041048502085080218186060830308181030e0818906186040a0c086100410302380830c14202063c18a0404305020c2810c085021210183040c30306101820808203100c301041c281101028a040428308188830e0830106087810a1018518181870404107040c50304042810a24304040c38c060c28404041860a0c38b060440f0c0430206103031208082061c306060c6021e041060e081870410103080850304243820c041830418085020c104060c2840a041821204189100c48c12044010a180850e3c182061028302083830a2420b020c303181430704182030c08184060c103021408f06082080c04183101010104282810a04401180838506042810a0c30106204860824103020c281042420f0a10109022c18c08141830604185061018306140860a0c0830614484040c2020230286081408508182810a0c187060818412085031c1c302140c4010a0418206041820c0c20306142021e0c082140c284040c385020808206044100a10103063410302181011208083160c08206180820610183063c1070a1c18310041861808082121820508083831c0c183021818212103080214083040c1870404283080c1010c141870c0c28f0e083010608082181048206044860c0c2830604182022048306104030c0460202081870a044830608189021830312141840a0428f080c2810a041850214085020c28c120410706080880c0c0860620181160c08306080861628106020c1010608484041c281041c281120c1070a0418b060c20508081870404308060c203040c38502143010a0c08304042830c105810404104102818802200850218106020c103060c08e0c04101161010406181030c0410d100428a06083030c1010704102811c04183041c305080c1850824103080c1071004103021828704102810a0c082080c101040c18404042870c082080218583020c1040a246820610303041c1830c0c10302081870608181062c086040c184040440404044040608609081408206044010c1408202181850e140850610101040c2031604401120c1860a04101040c38808182860208189060c1840a043050208601040c5050604182020c10704101040608186081830304041010a18181041018202083851210183220c0860404103020c1011214303020c1820c101830a10281160c184060c10104241810a0428302140830418184060c107060c1040a1010a040410704041070a041010a043050e08202061010306102840a101820c0418304042860208183020c18506041830a0c4810c0c10404103020208203040c0850214202080c1030610182021418704041070a04103020c1830a0418202083060208085020c182060c085020c107040410104101820604103020c18202081810608082020808101

/-- All primes below 256. -/
def PH : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
  101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
  197, 199, 211, 223, 227, 229, 233, 239, 241, 251]

/-- All primes up to 173. Trial division by these decides primality below 30000. -/
def PD : List ℕ := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
  101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173]

/-- `hasDiv n` holds when some member of `PD` below `n` divides `n`. -/
def hasDiv (n : ℕ) : Bool := PD.any (fun d => decide (d < n) && decide (n % d = 0))

/-- The numbers below 30000 that survive trial division. -/
def sieveL : List ℕ := (List.range 30000).filter (fun n => decide (2 ≤ n) && !hasDiv n)

/-- Weight of a prime `p` with `y1 < p < K`: a bound for its multiples in a block of length `K`. -/
def wBig (K y1 p : ℕ) : ℕ := if y1 < p then (if p < K then (K - 1) / p + 1 else 0) else 0

/-- Weight of a pair `q ≤ q'` of primes in `(y0, y1]`: a bound for the multiples of `q * q'`. -/
def wPair (K y0 y1 : ℕ) (i : ℕ × ℕ) : ℕ :=
  if y0 < i.1 then (if i.1 ≤ i.2 then (if i.2 ≤ y1 then (K - 1) / (i.1 * i.2) + 1 else 0) else 0)
  else 0

/-- Upper bound for the number of bad members of a block of length `K`. -/
def badL (K y0 y1 : ℕ) : ℕ :=
  (PL.map (wBig K y1)).sum + ((PH.product PH).map (wPair K y0 y1)).sum

/-- Upper bound for the number of primes up to `y0` (for `y0 < 256`). -/
def mOf (y0 : ℕ) : ℕ := (PH.filter (fun p => decide (p ≤ y0))).length

/-- Upper bound for the number of primes in `(y0, y1]` (for `y1 < 256`). -/
def rOf (y0 y1 : ℕ) : ℕ := (PH.filter (fun p => decide (y0 < p) && decide (p ≤ y1))).length

/-- The three numerical conditions on `F` good numbers, `m` small primes, `r` medium primes. -/
def condP (F m r : ℕ) : Prop :=
  3 ^ m * (r + 1) * (r + 2) < F * (F + 1) ∧ (r + m) * 4 ^ m ≤ F * 3 ^ m ∧
    (m + 1) * (m + r) + r + 2 ≤ 2 * F

/-- Boolean form of `condP`. -/
def condB (F m r : ℕ) : Bool :=
  decide (3 ^ m * (r + 1) * (r + 2) < F * (F + 1)) && decide ((r + m) * 4 ^ m ≤ F * 3 ^ m) &&
    decide ((m + 1) * (m + r) + r + 2 ≤ 2 * F)

/-- The check for one row `(K1, K2, y0, y1)` of the table. -/
def okB (b : ℕ × ℕ × ℕ × ℕ) : Bool :=
  decide (b.2.2.1 < 256) && decide (b.2.2.2 < 256) && decide (b.2.1 ≤ 30000) &&
    condB (b.1 - badL b.2.1 b.2.2.1 b.2.2.2) (mOf b.2.2.1) (rOf b.2.2.1 b.2.2.2)

/-- The table. A row `(K1, K2, y0, y1)` handles all `k` with `K1 ≤ k ≤ K2`. -/
def blocks : List (ℕ × ℕ × ℕ × ℕ) := [
  (3, 3, 2, 2), (4, 5, 3, 3), (6, 7, 3, 3), (8, 10, 3, 3), (11, 13, 3, 3), (14, 15, 3, 3),
  (16, 17, 3, 3), (18, 19, 3, 3), (20, 22, 3, 5), (23, 26, 5, 5), (27, 31, 5, 5), (32, 37, 5, 5),
  (38, 43, 5, 7), (44, 52, 7, 7), (53, 61, 7, 7), (62, 71, 7, 7), (72, 83, 7, 7), (84, 95, 7, 7),
  (96, 109, 11, 11), (110, 127, 11, 11), (128, 146, 11, 11), (147, 167, 11, 11), (168, 188, 7, 13),
  (189, 212, 7, 13), (213, 239, 7, 17), (240, 269, 7, 17), (270, 305, 7, 19), (306, 347, 7, 19),
  (348, 394, 7, 23), (395, 444, 7, 23), (445, 501, 7, 23), (502, 566, 7, 29), (567, 639, 7, 31),
  (640, 719, 7, 31), (720, 809, 7, 37), (810, 906, 7, 37), (907, 1012, 7, 41), (1013, 1128, 7, 43),
  (1129, 1255, 7, 43), (1256, 1398, 11, 43), (1399, 1553, 11, 43), (1554, 1723, 11, 47),
  (1724, 1912, 11, 53), (1913, 2119, 11, 59), (2120, 2345, 11, 59), (2346, 2594, 11, 61),
  (2595, 2859, 11, 67), (2860, 3154, 11, 71), (3155, 3470, 11, 73), (3471, 3810, 11, 79),
  (3811, 4177, 11, 83), (4178, 4568, 11, 89), (4569, 4991, 13, 79), (4992, 5453, 13, 83),
  (5454, 5955, 13, 89), (5956, 6499, 13, 97), (6500, 7083, 13, 101), (7084, 7716, 13, 107),
  (7717, 8405, 13, 109), (8406, 9144, 13, 113), (9145, 9929, 13, 127), (9930, 10774, 13, 131),
  (10775, 11678, 13, 139), (11679, 12623, 13, 139), (12624, 13627, 13, 149),
  (13628, 14694, 13, 157), (14695, 15803, 13, 157), (15804, 16974, 13, 167),
  (16975, 18193, 13, 179), (18194, 19490, 17, 157), (19491, 20869, 17, 163),
  (20870, 22325, 17, 173), (22326, 23859, 17, 179), (23860, 25481, 17, 181),
  (25482, 27193, 17, 193), (27194, 28996, 17, 199), (28997, 29999, 13, 131)]

/-- `cov s L` is one more than the last number covered when the rows of `L` are read from `s`. -/
def cov : ℕ → List (ℕ × ℕ × ℕ × ℕ) → ℕ
  | s, [] => s
  | s, b :: bs => if b.1 ≤ s then cov (max s (b.2.1 + 1)) bs else s

/-- The primes up to `y0`. -/
def smallP (y0 : ℕ) : Finset ℕ := (range (y0 + 1)).filter Nat.Prime

/-- The primes in `(y0, y1]`. -/
def medP (y0 y1 : ℕ) : Finset ℕ := (Ioc y0 y1).filter Nat.Prime

/-- The tag of `N`: the medium prime whose exponent is not divisible by `l`, or `0`. -/
def tag (l y0 y1 N : ℕ) : ℕ := ∑ q ∈ medP y0 y1, q * (N.factorization q % l)

/-- `N` is good: large primes have exponent divisible by `l`, medium primes have exponent
residue at most `1`, and at most one medium prime has a nonzero residue. -/
def IsGood (l y0 y1 N : ℕ) : Prop :=
  (∀ p, p.Prime → y1 < p → l ∣ N.factorization p) ∧
  (∀ q ∈ medP y0 y1, N.factorization q % l ≤ 1) ∧
  (∀ q ∈ medP y0 y1, ∀ q' ∈ medP y0 y1,
    N.factorization q % l ≠ 0 → N.factorization q' % l ≠ 0 → q = q')

open scoped Classical in
/-- The good members of the block `(n, n + k]`. -/
noncomputable def good (l y0 y1 n k : ℕ) : Finset ℕ := (Ioc n (n + k)).filter (IsGood l y0 y1)

theorem mem_good {l y0 y1 n k N : ℕ} :
    N ∈ good l y0 y1 n k ↔ N ∈ Ioc n (n + k) ∧ IsGood l y0 y1 N := by
  classical
  simp only [good, Finset.mem_filter]

theorem okB_spec (b : ℕ × ℕ × ℕ × ℕ) (h : okB b = true) :
    b.2.2.1 < 256 ∧ b.2.2.2 < 256 ∧ b.2.1 ≤ 30000 ∧
      condP (b.1 - badL b.2.1 b.2.2.1 b.2.2.2) (mOf b.2.2.1) (rOf b.2.2.1 b.2.2.2) := by
  unfold okB condB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

-- A. Merged sibling results (worked proofs: proved/sylvester_block.lean, proved/square_of_sylvester.lean)

-- Worked proof. The block below is copied unchanged from the merged sibling proof
-- proofs/Erdos137.erdos_137.variants.perfect_power.R1.H3.R1.H1.lean (lines 1116 to 1897, and 1905 to 1913),
-- in the repository open-math-agents. See ROUTE.md, section Credits.
section SylvesterPart

/- Sylvester–Schur for the interval used in Erdős 137.

The binomial theorem below is the existing Lean proof credited to @senamakel
in proofs/Erdos683.erdos_683.variant.sylvester_schur.lean. The last lemma
adapts its conclusion to the interval product used here.
-/

open Nat Finset


namespace SylvesterSchurOMA

/-- The number of primes `≤ k`. -/
def pc (k : ℕ) : ℕ := ((Finset.range (k + 1)).filter Nat.Prime).card

/- ## Step 2: valuations of `N.choose k` -/

/-- A prime `p` with `p ≤ k`, `N < 3p`, `N < p²` and `2k ≤ N` does not divide `N.choose k`. -/
lemma factorization_choose_eq_zero_of_third {p N k : ℕ} (hp : p.Prime) (hpk : p ≤ k)
    (h3 : N < 3 * p) (hsq : N < p ^ 2) (h2k : 2 * k ≤ N) :
    (N.choose k).factorization p = 0 := by
  have hkN : k ≤ N := by omega
  have hlog : Nat.log p N < 2 := Nat.log_lt_of_lt_pow (by omega) hsq
  rw [Nat.factorization_choose hp hkN hlog]
  have hk1 : k % p = k - p := by
    rw [Nat.mod_eq_sub_mod hpk, Nat.mod_eq_of_lt (by omega)]
  have hk2 : (N - k) % p = N - k - p := by
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi
  rw [Finset.mem_Ico] at hi
  have : i = 1 := by omega
  subst this
  simp only [pow_one, hk1, hk2]
  omega

/- ## Step 3: the counting bound -/

/-- Under the hypothesis that every prime factor of `N.choose k` is at most `k`,
`N.choose k ≤ N ^ π(k)`. -/
lemma choose_le_pow_primeCounting {N k : ℕ} (hN : 0 < N) (hkN : k ≤ N)
    (H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k) :
    N.choose k ≤ N ^ pc k := by
  have hC : N.choose k ≠ 0 := (Nat.choose_pos hkN).ne'
  calc N.choose k = ∏ p ∈ (N.choose k).primeFactors, p ^ (N.choose k).factorization p :=
        (Nat.prod_factorization_pow_eq_self hC).symm
    _ ≤ ∏ _p ∈ (N.choose k).primeFactors, N :=
        Finset.prod_le_prod' fun p _ => Nat.pow_factorization_choose_le hN
    _ = N ^ (N.choose k).primeFactors.card := Finset.prod_const _
    _ ≤ N ^ pc k := by
        apply Nat.pow_le_pow_right hN
        apply Finset.card_le_card
        intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpk := H p hpp (Nat.dvd_of_mem_primeFactors hp)
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hpp⟩

/-- Counting bound: `N ^ k ≤ 2 ^ k * k! * N ^ π(k)` when no prime above `k` divides `N.choose k`. -/
lemma counting_bound {N k : ℕ} (h2k : 2 * k ≤ N) (hN : 0 < N)
    (H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k) :
    N ^ k ≤ 2 ^ k * k ! * N ^ pc k := by
  have h1 : (N + 1 - k) ^ k ≤ N.descFactorial k := Nat.pow_sub_le_descFactorial N k
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  have h2 : N ≤ 2 * (N + 1 - k) := by omega
  calc N ^ k ≤ (2 * (N + 1 - k)) ^ k := Nat.pow_le_pow_left h2 k
    _ = 2 ^ k * (N + 1 - k) ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (k ! * N.choose k) := Nat.mul_le_mul_left _ h1
    _ ≤ 2 ^ k * (k ! * N ^ pc k) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (choose_le_pow_primeCounting hN (by omega) H))
    _ = 2 ^ k * k ! * N ^ pc k := by ring


/- ## Step 4a: upper and lower bounds for `N.choose k` -/

lemma pc_mono {a b : ℕ} (h : a ≤ b) : pc a ≤ pc b := by
  unfold pc
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- Upper bound when no prime above `k` divides `N.choose k`. -/
lemma choose_le_upper {N k : ℕ} (h2k : 2 * k ≤ N)
    (H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k) :
    N.choose k ≤ N ^ pc (Nat.sqrt N) * 4 ^ (min k (N / 3)) := by
  have hN : 0 < N ∨ N = 0 := by omega
  rcases hN with hN | hN
  swap
  · subst hN
    have : k = 0 := by omega
    subst this
    show 1 ≤ 0 ^ pc 0 * 4 ^ (min 0 (0 / 3))
    decide
  set f := (N.choose k).factorization with hf
  set m := min k (N / 3) with hm
  rw [← Nat.prod_pow_factorization_choose N k (by omega),
    ← Finset.prod_filter_mul_prod_filter_not (Finset.range (N + 1)) (· ≤ Nat.sqrt N)]
  apply Nat.mul_le_mul
  · -- small primes
    calc ∏ p ∈ (Finset.range (N + 1)).filter (· ≤ Nat.sqrt N), p ^ f p
        ≤ ∏ p ∈ (Finset.range (N + 1)).filter (· ≤ Nat.sqrt N), (if p.Prime then N else 1) := by
          apply Finset.prod_le_prod'
          intro p _
          split_ifs with hp
          · exact Nat.pow_factorization_choose_le hN
          · simp [hf, Nat.factorization_eq_zero_of_not_prime _ hp]
      _ = ∏ p ∈ ((Finset.range (N + 1)).filter (· ≤ Nat.sqrt N)).filter Nat.Prime, N :=
          (Finset.prod_filter _ _).symm
      _ = N ^ (((Finset.range (N + 1)).filter (· ≤ Nat.sqrt N)).filter Nat.Prime).card :=
          Finset.prod_const _
      _ ≤ N ^ pc (Nat.sqrt N) := by
          apply Nat.pow_le_pow_right hN
          unfold pc
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
          exact ⟨by omega, hp.2⟩
  · -- large primes
    calc ∏ p ∈ (Finset.range (N + 1)).filter (fun p => ¬ p ≤ Nat.sqrt N), p ^ f p
        ≤ ∏ p ∈ (Finset.range (N + 1)).filter (fun p => ¬ p ≤ Nat.sqrt N),
            (if p.Prime ∧ p ≤ m then p else 1) := by
          apply Finset.prod_le_prod'
          intro p hpS
          simp only [Finset.mem_filter, Finset.mem_range] at hpS
          have hp1 : 1 ≤ p := by have := hpS.2; omega
          have hsq : N < p ^ 2 := by
            have := Nat.sqrt_lt'.1 (show Nat.sqrt N < p by omega)
            exact this
          have hle1 : f p ≤ 1 := Nat.factorization_choose_le_one hsq
          rcases Nat.eq_zero_or_pos (f p) with h0 | hpos
          · rw [h0, pow_zero]; split_ifs
            · exact hp1
            · exact le_refl 1
          · have hne : (N.choose k).factorization p ≠ 0 := by rw [← hf]; omega
            have hp : p.Prime := by
              by_contra hnp
              exact hne (Nat.factorization_eq_zero_of_not_prime _ hnp)
            have hdvd : p ∣ N.choose k := Nat.dvd_of_factorization_pos hne
            have hpk := H p hp hdvd
            have h3 : 3 * p ≤ N := by
              by_contra hlt
              have := factorization_choose_eq_zero_of_third hp hpk (by omega) hsq h2k
              rw [← hf] at this
              omega
            have hpm : p ≤ m := by
              rw [hm]; apply le_min hpk; omega
            have : f p = 1 := by omega
            rw [this, pow_one, if_pos ⟨hp, hpm⟩]
      _ = ∏ p ∈ ((Finset.range (N + 1)).filter (fun p => ¬ p ≤ Nat.sqrt N)).filter
            (fun p => p.Prime ∧ p ≤ m), p := (Finset.prod_filter _ _).symm
      _ ≤ ∏ p ∈ (Finset.range (m + 1)).filter Nat.Prime, p := by
          apply Finset.prod_le_prod_of_subset_of_one_le'
          · intro p hp
            simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
            exact ⟨by omega, hp.2.1⟩
          · intro p hp _
            simp only [Finset.mem_filter] at hp
            exact hp.2.one_lt.le
      _ = primorial m := rfl
      _ ≤ 4 ^ m := primorial_le_four_pow m

/-- Lower bound: `4^k N^k ≤ 2k (2k)^k * N.choose k` for `2k ≤ N`. -/
lemma lower_bound {N k : ℕ} (hk : 0 < k) (h2k : 2 * k ≤ N) :
    4 ^ k * N ^ k ≤ 2 * k * (2 * k) ^ k * N.choose k := by
  have key : (2 * k).descFactorial k * N ^ k ≤ N.descFactorial k * (2 * k) ^ k := by
    have e1 : N ^ k = ∏ _i ∈ Finset.range k, N := by simp
    have e2 : (2 * k) ^ k = ∏ _i ∈ Finset.range k, (2 * k) := by simp
    rw [Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_prod_range, e1, e2,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod'
    intro i hi
    rw [Finset.mem_range] at hi
    obtain ⟨a, ha⟩ : ∃ a, 2 * k = a + i := ⟨2 * k - i, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, N = b + i := ⟨N - i, by omega⟩
    have hab : a ≤ b := by omega
    rw [ha, hb, Nat.add_sub_cancel, Nat.add_sub_cancel]
    nlinarith
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose,
    mul_assoc, mul_assoc] at key
  have key' := Nat.le_of_mul_le_mul_left key (Nat.factorial_pos k)
  have h4 := Nat.four_pow_le_two_mul_self_mul_centralBinom k hk
  rw [Nat.centralBinom_eq_two_mul_choose] at h4
  calc 4 ^ k * N ^ k ≤ 2 * k * (2 * k).choose k * N ^ k := Nat.mul_le_mul_right _ h4
    _ = 2 * k * ((2 * k).choose k * N ^ k) := by ring
    _ ≤ 2 * k * (N.choose k * (2 * k) ^ k) := Nat.mul_le_mul_left _ key'
    _ = 2 * k * (2 * k) ^ k * N.choose k := by ring


/- ## Step 4b: prime counting by the mod-30 wheel -/

lemma pc_eq_count (x : ℕ) : pc x = Nat.count Nat.Prime (x + 1) := by
  rw [pc, Nat.count_eq_card_filter_range]

lemma pc_wheel {x : ℕ} (hx : 30 ≤ x) : pc x ≤ 10 + 8 * ((x - 30) / 30 + 1) := by
  rw [pc_eq_count]
  have h := Nat.primeCounting'_add_le (a := 30) (k := 31) (by norm_num) (by norm_num) (x - 30)
  have h31 : Nat.primeCounting' 31 = 10 := by decide
  have ht : Nat.totient 30 = 8 := by decide
  rw [h31, ht] at h
  have : 31 + (x - 30) = x + 1 := by omega
  rw [this] at h
  exact h

set_option maxRecDepth 100000 in
lemma three_pc_lt {k : ℕ} (hk : 34 ≤ k) : 3 * pc k < k := by
  rcases lt_or_ge k 160 with h | h
  · have key : ∀ k < 160, 34 ≤ k → 3 * pc k < k := by decide
    exact key k h hk
  · have := pc_wheel (x := k) (by omega)
    omega

/- ## Step 4c: the large-`N` region via counting -/

lemma not_large_region {N k : ℕ} (hk : 34 ≤ k) (h2k : 2 * k ≤ N)
    (H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k) : N ^ 2 < (2 * k) ^ 3 := by
  by_contra hge'
  have hge := not_lt.1 hge'
  have hN : 0 < N := by omega
  have hc := counting_bound h2k hN H
  have h3 := three_pc_lt hk
  have hpk : pc k ≤ k := by omega
  have hfac : k ! ≤ k ^ k := Nat.factorial_le_pow k
  have h1 : N ^ (k - pc k) * N ^ pc k ≤ (2 * k) ^ k * N ^ pc k := by
    rw [← pow_add, Nat.sub_add_cancel hpk, mul_pow]
    calc N ^ k ≤ 2 ^ k * k ! * N ^ pc k := hc
      _ ≤ 2 ^ k * k ^ k * N ^ pc k := by gcongr
  have h2 : N ^ (k - pc k) ≤ (2 * k) ^ k :=
    Nat.le_of_mul_le_mul_right h1 (by positivity)
  have h4 : ((2 * k) ^ 3) ^ (k - pc k) ≤ (N ^ 2) ^ (k - pc k) := Nat.pow_le_pow_left hge _
  have h5 : (N ^ 2) ^ (k - pc k) ≤ ((2 * k) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_le_pow_left h2 2
  rw [← pow_mul, ← pow_mul] at h4
  rw [← pow_mul, ← pow_mul] at h5
  have h6 : (2 * k) ^ (3 * (k - pc k)) ≤ (2 * k) ^ (k * 2) := le_trans h4 h5
  have h7 := (Nat.pow_le_pow_iff_right (show 1 < 2 * k by omega)).1 h6
  omega


/- ## Step 4d: elementary growth lemmas -/

lemma poly1 : ∀ j ≥ 14, 48 * (j + 3) ^ 2 ≤ 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have e : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have h : (j + 1 + 3) ^ 2 ≤ 2 * (j + 3) ^ 2 := by nlinarith
    rw [e]; linarith

lemma poly2 : ∀ j ≥ 14, 32 * (j + 4) ^ 2 ≤ 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have e : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have h : (j + 1 + 4) ^ 2 ≤ 2 * (j + 4) ^ 2 := by nlinarith
    rw [e]; linarith

lemma poly3 : ∀ j ≥ 14, 128 * (j + 8) ^ 2 ≤ 4 * 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have e : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have h : (j + 1 + 8) ^ 2 ≤ 2 * (j + 8) ^ 2 := by nlinarith
    rw [e]; linarith

lemma poly4 : ∀ j ≥ 14, 8 * (3 * j + 6) ^ 4 ≤ 50625 * 2 ^ j := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    have e : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have h16 : 16 * (3 * (j + 1) + 6) ≤ 17 * (3 * j + 6) := by omega
    have h4 := Nat.pow_le_pow_left h16 4
    rw [mul_pow, mul_pow] at h4
    norm_num at h4
    rw [e]
    generalize (3 * (j + 1) + 6) ^ 4 = y at h4 ⊢
    generalize (3 * j + 6) ^ 4 = x at h4 ih
    generalize 2 ^ j = P at ih ⊢
    omega

/-- `2^(k/4) * 4^k ≤ 5^k`. -/
lemma five_pow (k : ℕ) : 2 ^ (k / 4) * 4 ^ k ≤ 5 ^ k := by
  obtain ⟨q, t, ht, rfl⟩ : ∃ q t, t < 4 ∧ k = 4 * q + t := ⟨k / 4, k % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 4).symm⟩
  have hq : (4 * q + t) / 4 = q := by omega
  rw [hq, pow_add, pow_add, pow_mul, pow_mul]
  have h1 : 2 ^ q * (4 ^ 4) ^ q ≤ (5 ^ 4) ^ q := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) q
  have h2 : 4 ^ t ≤ 5 ^ t := Nat.pow_le_pow_left (by norm_num) t
  calc 2 ^ q * ((4 ^ 4) ^ q * 4 ^ t) = (2 ^ q * (4 ^ 4) ^ q) * 4 ^ t := by ring
    _ ≤ (5 ^ 4) ^ q * 5 ^ t := Nat.mul_le_mul h1 h2

/-- `2^(k/2) * 2^k ≤ 3^k`. -/
lemma three_pow (k : ℕ) : 2 ^ (k / 2) * 2 ^ k ≤ 3 ^ k := by
  obtain ⟨q, t, ht, rfl⟩ : ∃ q t, t < 2 ∧ k = 2 * q + t := ⟨k / 2, k % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod k 2).symm⟩
  have hq : (2 * q + t) / 2 = q := by omega
  rw [hq, pow_add, pow_add, pow_mul, pow_mul]
  have h1 : 2 ^ q * (2 ^ 2) ^ q ≤ (3 ^ 2) ^ q := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) q
  have h2 : 2 ^ t ≤ 3 ^ t := Nat.pow_le_pow_left (by norm_num) t
  calc 2 ^ q * ((2 ^ 2) ^ q * 2 ^ t) = (2 ^ q * (2 ^ 2) ^ q) * 2 ^ t := by ring
    _ ≤ (3 ^ 2) ^ q * 3 ^ t := Nat.mul_le_mul h1 h2


lemma aux_lin (j : ℕ) : 114 * j + 228 ≤ 48 * (j + 3) ^ 2 := by nlinarith

lemma four_pow_eq (k : ℕ) : 4 ^ k = 2 ^ k * 2 ^ k := by
  rw [← mul_pow]; norm_num

/- ## Step 4e: the middle region for `k ≥ 2^14` -/

lemma middle_region {N k : ℕ} (hk : 2 ^ 14 ≤ k) (h2k : 2 * k ≤ N) (hsm : N ^ 2 < (2 * k) ^ 3)
    (H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k) : False := by
  have hk' : 16384 ≤ k := by norm_num at hk; exact hk
  have hk0 : 0 < k := by omega
  have hN0 : 0 < N := by omega
  set j := Nat.log 2 k with hjdef
  have hj14 : 14 ≤ j := Nat.le_log_of_pow_le (by norm_num) hk
  have hjk : 2 ^ j ≤ k := Nat.pow_log_le_self 2 (by omega)
  have hkj : k < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  set r := Nat.sqrt N with hrdef
  have hr2 : r ^ 2 ≤ N := Nat.sqrt_le' N
  have hr30 : 30 ≤ r := Nat.le_sqrt'.2 (by omega)
  set s := pc r with hsdef
  have hs : s ≤ 18 + r / 3 := by have := pc_wheel hr30; omega
  set L := Nat.log 2 N + 1 with hLdef
  have hNL : N < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) N
  have hLb : ∀ e, N < 2 ^ e → L ≤ e := fun e he => by
    have := Nat.log_lt_of_lt_pow (by omega : N ≠ 0) he
    omega
  have hup : 2 * k * N ^ s < 2 ^ (L * (s + 1)) := by
    have h1 : 2 * k < 2 ^ L := by omega
    have h2 : N ^ s ≤ (2 ^ L) ^ s := Nat.pow_le_pow_left hNL.le s
    calc 2 * k * N ^ s < 2 ^ L * (2 ^ L) ^ s :=
          Nat.mul_lt_mul_of_lt_of_le h1 h2 (by positivity)
      _ = 2 ^ (L * (s + 1)) := by rw [← pow_mul, ← pow_add]; ring_nf
  have hLs : L * (s + 1) ≤ 19 * L + L * r / 3 := by
    calc L * (s + 1) ≤ L * (19 + r / 3) := Nat.mul_le_mul_left _ (by omega)
      _ = 19 * L + L * (r / 3) := by ring
      _ ≤ 19 * L + L * r / 3 := by
          have := Nat.mul_div_le_mul_div_assoc L r 3
          omega
  have fin : ∀ E, 2 ^ E ≤ 2 * k * N ^ s → L * (s + 1) ≤ E → False := fun E h1 h2 => by
    have h3 := lt_of_le_of_lt h1 hup
    have h4 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h3
    omega
  have hstar : 4 ^ k * N ^ k ≤ 2 * k * (2 * k) ^ k * (N ^ s * 4 ^ (min k (N / 3))) :=
    le_trans (lower_bound hk0 h2k) (Nat.mul_le_mul_left _ (choose_le_upper h2k H))
  have hb : N ^ k ≤ 2 * k * (2 * k) ^ k * N ^ s := by
    have hm4 : 4 ^ (min k (N / 3)) ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (min_le_left _ _)
    have h1 : N ^ k * 4 ^ k ≤ (2 * k * (2 * k) ^ k * N ^ s) * 4 ^ k := by
      calc N ^ k * 4 ^ k = 4 ^ k * N ^ k := by ring
        _ ≤ 2 * k * (2 * k) ^ k * (N ^ s * 4 ^ (min k (N / 3))) := hstar
        _ ≤ 2 * k * (2 * k) ^ k * (N ^ s * 4 ^ k) := by gcongr
        _ = (2 * k * (2 * k) ^ k * N ^ s) * 4 ^ k := by ring
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  have hkk : 0 < k ^ k := by positivity
  rcases lt_or_ge N (3 * k) with hN3 | hN3
  · -- `N < 3k`
    have hL3 : L ≤ j + 3 := hLb _ (by
      have : 2 ^ (j + 3) = 8 * 2 ^ j := by ring
      have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      omega)
    have hLr : 4 * (L * r) ≤ k := by
      have : (4 * (L * r)) ^ 2 ≤ k ^ 2 := by
        calc (4 * (L * r)) ^ 2 = 16 * L ^ 2 * r ^ 2 := by ring
          _ ≤ 16 * (j + 3) ^ 2 * (3 * k) := by gcongr; omega
          _ = 48 * (j + 3) ^ 2 * k := by ring
          _ ≤ 2 ^ j * k := Nat.mul_le_mul_right _ (poly1 j hj14)
          _ ≤ k * k := Nat.mul_le_mul_right _ hjk
          _ = k ^ 2 := by ring
      exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
    have hL456 : 456 * L ≤ k := by have := poly1 j hj14; nlinarith
    rcases le_or_gt (2 * N) (5 * k) with h5 | h5
    · -- `2N ≤ 5k`
      have hm : min k (N / 3) = N / 3 := min_eq_right (by omega)
      rw [hm] at hstar
      have h1 : 4 ^ k * N ^ k ≤ (2 * k * N ^ s * 4 ^ (N / 3)) * N ^ k := by
        calc 4 ^ k * N ^ k ≤ 2 * k * (2 * k) ^ k * (N ^ s * 4 ^ (N / 3)) := hstar
          _ ≤ 2 * k * N ^ k * (N ^ s * 4 ^ (N / 3)) := by gcongr
          _ = (2 * k * N ^ s * 4 ^ (N / 3)) * N ^ k := by ring
      have h2 : 4 ^ k ≤ 2 * k * N ^ s * 4 ^ (N / 3) :=
        Nat.le_of_mul_le_mul_right h1 (by positivity)
      have h3 : 4 ^ (k - N / 3) * 4 ^ (N / 3) ≤ (2 * k * N ^ s) * 4 ^ (N / 3) := by
        rw [← pow_add, Nat.sub_add_cancel (by omega)]; exact h2
      have h4 := Nat.le_of_mul_le_mul_right h3 (by positivity)
      have h5' : 2 ^ (2 * (k - N / 3)) ≤ 2 * k * N ^ s := by
        rw [pow_mul]; norm_num; exact h4
      apply fin _ h5'
      generalize L * (s + 1) = A at hLs ⊢
      generalize L * r = B at hLs hLr
      omega
    · -- `5k < 2N < 6k`
      have h1 : 5 ^ k * k ^ k ≤ (2 * k * 4 ^ k * N ^ s) * k ^ k := by
        calc 5 ^ k * k ^ k = (5 * k) ^ k := (mul_pow _ _ _).symm
          _ ≤ (2 * N) ^ k := Nat.pow_le_pow_left (by omega) k
          _ = 2 ^ k * N ^ k := mul_pow _ _ _
          _ ≤ 2 ^ k * (2 * k * (2 * k) ^ k * N ^ s) := Nat.mul_le_mul_left _ hb
          _ = (2 * k * 4 ^ k * N ^ s) * k ^ k := by rw [mul_pow, four_pow_eq]; ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hkk
      have h3 : 2 ^ (k / 4) * 4 ^ k ≤ (2 * k * N ^ s) * 4 ^ k := by
        calc 2 ^ (k / 4) * 4 ^ k ≤ 5 ^ k := five_pow k
          _ ≤ 2 * k * 4 ^ k * N ^ s := h2
          _ = (2 * k * N ^ s) * 4 ^ k := by ring
      apply fin _ (Nat.le_of_mul_le_mul_right h3 (by positivity))
      generalize L * (s + 1) = A at hLs ⊢
      generalize L * r = B at hLs hLr
      omega
  · -- `N ≥ 3k`
    rcases lt_or_ge N (8 * k) with h8 | h8
    · have hL4 : L ≤ j + 4 := hLb _ (by
        have : 2 ^ (j + 4) = 16 * 2 ^ j := by ring
        have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        omega)
      have hLr : 2 * (L * r) ≤ k := by
        have : (2 * (L * r)) ^ 2 ≤ k ^ 2 := by
          calc (2 * (L * r)) ^ 2 = 4 * L ^ 2 * r ^ 2 := by ring
            _ ≤ 4 * (j + 4) ^ 2 * (8 * k) := by gcongr; omega
            _ = 32 * (j + 4) ^ 2 * k := by ring
            _ ≤ 2 ^ j * k := Nat.mul_le_mul_right _ (poly2 j hj14)
            _ ≤ k * k := Nat.mul_le_mul_right _ hjk
            _ = k ^ 2 := by ring
        exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
      have hL114 : 114 * L ≤ k := by have := poly2 j hj14; nlinarith
      have h1 : 2 ^ (k / 2) * 2 ^ k * 2 ^ k * k ^ k ≤ ((2 * k * N ^ s) * 2 ^ k * 2 ^ k) * k ^ k := by
        calc 2 ^ (k / 2) * 2 ^ k * 2 ^ k * k ^ k ≤ 3 ^ k * 2 ^ k * k ^ k := by
              gcongr; exact three_pow k
          _ = (6 * k) ^ k := by rw [mul_pow, show (6 : ℕ) = 3 * 2 by norm_num, mul_pow]
          _ ≤ (2 * N) ^ k := Nat.pow_le_pow_left (by omega) k
          _ = 2 ^ k * N ^ k := mul_pow _ _ _
          _ ≤ 2 ^ k * (2 * k * (2 * k) ^ k * N ^ s) := Nat.mul_le_mul_left _ hb
          _ = ((2 * k * N ^ s) * 2 ^ k * 2 ^ k) * k ^ k := by rw [mul_pow]; ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hkk
      have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
      have h4 := Nat.le_of_mul_le_mul_right h3 (by positivity)
      apply fin _ h4
      generalize L * (s + 1) = A at hLs ⊢
      generalize L * r = B at hLs hLr
      omega
    rcases lt_or_ge N (128 * k) with h128 | h128
    · have hL8 : L ≤ j + 8 := hLb _ (by
        have : 2 ^ (j + 8) = 256 * 2 ^ j := by ring
        have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        omega)
      have hLr : L * r ≤ 2 * k := by
        have : (L * r) ^ 2 ≤ (2 * k) ^ 2 := by
          calc (L * r) ^ 2 = L ^ 2 * r ^ 2 := by ring
            _ ≤ (j + 8) ^ 2 * (128 * k) := by gcongr; omega
            _ = 128 * (j + 8) ^ 2 * k := by ring
            _ ≤ 4 * 2 ^ j * k := Nat.mul_le_mul_right _ (poly3 j hj14)
            _ ≤ 4 * k * k := by gcongr
            _ = (2 * k) ^ 2 := by ring
        exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
      have hL19 : 19 * L ≤ k := by have := poly3 j hj14; nlinarith
      have h1 : 4 ^ k * 2 ^ k * k ^ k ≤ ((2 * k * N ^ s) * 2 ^ k) * k ^ k := by
        calc 4 ^ k * 2 ^ k * k ^ k = (8 * k) ^ k := by
              rw [mul_pow, show (8 : ℕ) = 4 * 2 by norm_num, mul_pow]
          _ ≤ N ^ k := Nat.pow_le_pow_left (by omega) k
          _ ≤ 2 * k * (2 * k) ^ k * N ^ s := hb
          _ = ((2 * k * N ^ s) * 2 ^ k) * k ^ k := by rw [mul_pow]; ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hkk
      have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
      have h4 : 2 ^ (2 * k) ≤ 2 * k * N ^ s := by rw [pow_mul]; norm_num; exact h3
      apply fin _ h4
      generalize L * (s + 1) = A at hLs ⊢
      generalize L * r = B at hLs hLr
      omega
    · have hL6 : L ≤ 3 * j + 6 := hLb _ (by
        have e1 : (2 * k) ^ 3 < (2 ^ (j + 2)) ^ 3 := by
          apply Nat.pow_lt_pow_left _ (by norm_num)
          have : 2 ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
          omega
        have e2 : (2 ^ (j + 2)) ^ 3 = 2 ^ (3 * j + 6) := by rw [← pow_mul]; ring_nf
        have e3 : N ≤ N ^ 2 := by nlinarith
        omega)
      have hLr : L * r ≤ 15 * k := by
        have : (L * r) ^ 4 ≤ (15 * k) ^ 4 := by
          calc (L * r) ^ 4 = L ^ 4 * (r ^ 2) ^ 2 := by ring
            _ ≤ (3 * j + 6) ^ 4 * N ^ 2 := by gcongr
            _ ≤ (3 * j + 6) ^ 4 * (2 * k) ^ 3 := by gcongr
            _ = 8 * (3 * j + 6) ^ 4 * k ^ 3 := by ring
            _ ≤ 50625 * 2 ^ j * k ^ 3 := Nat.mul_le_mul_right _ (poly4 j hj14)
            _ ≤ 50625 * k * k ^ 3 := by gcongr
            _ = (15 * k) ^ 4 := by ring
        exact (Nat.pow_le_pow_iff_left (by norm_num)).1 this
      have hL38 : 38 * L ≤ k := by
        have h1 := poly1 j hj14
        have h2 : 114 * j + 228 ≤ 48 * (j + 3) ^ 2 := aux_lin j
        omega
      have h1 : 64 ^ k * 2 ^ k * k ^ k ≤ ((2 * k * N ^ s) * 2 ^ k) * k ^ k := by
        calc 64 ^ k * 2 ^ k * k ^ k = (128 * k) ^ k := by
              rw [mul_pow, show (128 : ℕ) = 64 * 2 by norm_num, mul_pow]
          _ ≤ N ^ k := Nat.pow_le_pow_left h128 k
          _ ≤ 2 * k * (2 * k) ^ k * N ^ s := hb
          _ = ((2 * k * N ^ s) * 2 ^ k) * k ^ k := by rw [mul_pow]; ring
      have h2 := Nat.le_of_mul_le_mul_right h1 hkk
      have h3 := Nat.le_of_mul_le_mul_right h2 (by positivity)
      have h4 : 2 ^ (6 * k) ≤ 2 * k * N ^ s := by
        have e : (64 : ℕ) = 2 ^ 6 := by norm_num
        rw [e, ← pow_mul] at h3; exact h3
      apply fin _ h4
      generalize L * (s + 1) = A at hLs ⊢
      generalize L * r = B at hLs hLr
      omega

/-- Primes with gaps at most 34, from at most 68 up to `(128)^(3/2)`. -/
def band0 : List ℕ := [67, 101, 131, 163, 197, 229, 263, 293, 317, 349, 383, 409, 443, 467, 499, 523, 557, 587, 619, 653, 683, 709, 743, 773, 797, 829, 863, 887, 919, 953, 983, 1013, 1039, 1069, 1103, 1129, 1163, 1193, 1223, 1249, 1283, 1307, 1327, 1361, 1381, 1409, 1439, 1471]

/-- Primes with gaps at most 64, from at most 128 up to `(256)^(3/2)`. -/
def band1 : List ℕ := [127, 191, 251, 313, 373, 433, 491, 547, 607, 661, 719, 773, 829, 887, 947, 1009, 1069, 1129, 1193, 1249, 1307, 1367, 1429, 1493, 1553, 1613, 1669, 1733, 1789, 1847, 1907, 1951, 2011, 2069, 2131, 2179, 2243, 2297, 2357, 2417, 2477, 2539, 2593, 2657, 2719, 2777, 2837, 2897, 2957, 3019, 3083, 3137, 3191, 3253, 3313, 3373, 3433, 3491, 3547, 3607, 3671, 3733, 3797, 3853, 3917, 3967, 4027, 4091, 4153]

/-- Primes with gaps at most 128, from at most 256 up to `(512)^(3/2)`. -/
def band2 : List ℕ := [251, 379, 503, 631, 757, 883, 1009, 1129, 1249, 1373, 1499, 1627, 1753, 1879, 2003, 2131, 2251, 2377, 2503, 2621, 2749, 2861, 2971, 3089, 3217, 3343, 3469, 3593, 3719, 3847, 3967, 4093, 4219, 4339, 4463, 4591, 4703, 4831, 4957, 5081, 5209, 5333, 5449, 5573, 5701, 5827, 5953, 6079, 6203, 6329, 6451, 6577, 6703, 6829, 6949, 7069, 7193, 7321, 7433, 7561, 7687, 7793, 7919, 8039, 8167, 8293, 8419, 8543, 8669, 8783, 8893, 9013, 9137, 9257, 9377, 9497, 9623, 9749, 9871, 9973, 10099, 10223, 10343, 10463, 10589, 10711, 10837, 10957, 11083, 11197, 11321, 11447, 11551, 11677]

/-- Primes with gaps at most 256, from at most 512 up to `(1024)^(3/2)`. -/
def band3 : List ℕ := [509, 761, 1013, 1259, 1511, 1759, 2011, 2267, 2521, 2777, 3023, 3271, 3527, 3779, 4027, 4283, 4523, 4759, 5011, 5261, 5507, 5749, 5987, 6229, 6481, 6737, 6991, 7247, 7499, 7753, 8009, 8263, 8513, 8761, 9013, 9257, 9511, 9767, 10009, 10259, 10513, 10753, 11003, 11257, 11503, 11743, 11987, 12241, 12497, 12743, 12983, 13229, 13477, 13729, 13967, 14221, 14461, 14717, 14969, 15217, 15473, 15727, 15973, 16229, 16481, 16729, 16981, 17231, 17483, 17737, 17989, 18233, 18481, 18731, 18979, 19231, 19483, 19739, 19993, 20249, 20483, 20731, 20983, 21227, 21481, 21737, 21991, 22247, 22501, 22751, 23003, 23251, 23497, 23753, 24007, 24251, 24499, 24749, 24989, 25243, 25471, 25717, 25969, 26209, 26459, 26713, 26959, 27211, 27457, 27701, 27953, 28201, 28447, 28703, 28949, 29201, 29453, 29683, 29927, 30181, 30431, 30677, 30931, 31183, 31397, 31649, 31891, 32143, 32381, 32633, 32887]

/-- Primes with gaps at most 512, from at most 1024 up to `(2048)^(3/2)`. -/
def band4 : List ℕ := [1021, 1531, 2039, 2551, 3061, 3571, 4079, 4591, 5101, 5591, 6101, 6607, 7109, 7621, 8123, 8629, 9137, 9649, 10159, 10667, 11177, 11689, 12197, 12703, 13187, 13697, 14207, 14717, 15227, 15739, 16249, 16759, 17257, 17761, 18269, 18773, 19273, 19777, 20287, 20789, 21283, 21787, 22291, 22787, 23297, 23801, 24281, 24793, 25303, 25801, 26309, 26821, 27329, 27827, 28319, 28817, 29327, 29837, 30347, 30859, 31357, 31859, 32371, 32869, 33377, 33889, 34381, 34883, 35393, 35899, 36389, 36901, 37409, 37907, 38393, 38903, 39409, 39901, 40387, 40897, 41399, 41911, 42409, 42901, 43411, 43913, 44417, 44927, 45439, 45949, 46457, 46957, 47459, 47969, 48481, 48991, 49499, 49999, 50503, 51001, 51511, 52021, 52529, 53017, 53527, 54037, 54547, 55057, 55547, 56053, 56543, 57047, 57559, 58067, 58579, 59083, 59581, 60091, 60601, 61099, 61609, 62119, 62627, 63131, 63629, 64123, 64633, 65141, 65651, 66161, 66653, 67157, 67651, 68161, 68669, 69163, 69661, 70163, 70667, 71171, 71671, 72173, 72679, 73189, 73699, 74209, 74719, 75227, 75731, 76243, 76753, 77263, 77773, 78283, 78791, 79301, 79813, 80317, 80819, 81331, 81839, 82351, 82847, 83357, 83869, 84377, 84871, 85381, 85889, 86399, 86869, 87359, 87869, 88379, 88883, 89393, 89899, 90407, 90917, 91423, 91921, 92431, 92941]

/-- Primes with gaps at most 1024, from at most 2048 up to `(4096)^(3/2)`. -/
def band5 : List ℕ := [2039, 3061, 4079, 5101, 6121, 7129, 8147, 9161, 10181, 11197, 12211, 13229, 14251, 15271, 16273, 17293, 18313, 19333, 20357, 21379, 22397, 23417, 24439, 25463, 26479, 27487, 28499, 29501, 30517, 31541, 32563, 33587, 34607, 35617, 36637, 37657, 38677, 39679, 40699, 41719, 42743, 43759, 44777, 45779, 46771, 47791, 48809, 49831, 50849, 51871, 52889, 53899, 54919, 55933, 56957, 57977, 58997, 60017, 61031, 62053, 63073, 64091, 65111, 66109, 67129, 68147, 69163, 70183, 71191, 72211, 73189, 74209, 75227, 76249, 77269, 78283, 79301, 80317, 81331, 82351, 83357, 84377, 85381, 86399, 87421, 88427, 89449, 90473, 91493, 92507, 93529, 94547, 95569, 96589, 97613, 98627, 99643, 100649, 101663, 102679, 103703, 104723, 105733, 106753, 107777, 108799, 109819, 110821, 111833, 112843, 113843, 114859, 115883, 116903, 117917, 118931, 119953, 120977, 121997, 123017, 124021, 125029, 126047, 127051, 128053, 129061, 130079, 131101, 132113, 133121, 134129, 135151, 136163, 137183, 138197, 139201, 140221, 141241, 142237, 143261, 144271, 145289, 146309, 147331, 148339, 149351, 150373, 151397, 152419, 153443, 154459, 155473, 156493, 157513, 158537, 159553, 160553, 161573, 162593, 163613, 164627, 165617, 166631, 167641, 168643, 169667, 170689, 171713, 172721, 173743, 174767, 175783, 176807, 177823, 178831, 179849, 180871, 181891, 182899, 183919, 184913, 185923, 186947, 187963, 188983, 189997, 191021, 192043, 193057, 194071, 195089, 196111, 197123, 198139, 199153, 200177, 201193, 202201, 203221, 204233, 205253, 206273, 207293, 208309, 209333, 210347, 211369, 212383, 213407, 214399, 215417, 216431, 217439, 218461, 219467, 220471, 221489, 222511, 223529, 224527, 225529, 226553, 227569, 228593, 229613, 230611, 231631, 232643, 233663, 234683, 235699, 236723, 237737, 238759, 239783, 240797, 241817, 242819, 243839, 244861, 245881, 246899, 247913, 248909, 249923, 250919, 251941, 252949, 253969, 254993, 255989, 257003, 258023, 259033, 260047, 261071, 262079, 263101]

/-- Primes with gaps at most 2048, from at most 4096 up to `(8192)^(3/2)`. -/
def band6 : List ℕ := [4093, 6133, 8179, 10223, 12269, 14303, 16349, 18397, 20443, 22483, 24527, 26573, 28621, 30661, 32707, 34747, 36793, 38839, 40883, 42929, 44971, 47017, 49057, 51071, 53117, 55163, 57203, 59243, 61291, 63337, 65381, 67429, 69473, 71503, 73547, 75583, 77621, 79669, 81707, 83737, 85781, 87811, 89849, 91873, 93913, 95959, 97987, 100019, 102061, 104107, 106129, 108161, 110183, 112223, 114269, 116293, 118297, 120331, 122363, 124367, 126397, 128437, 130483, 132529, 134513, 136559, 138599, 140639, 142673, 144719, 146767, 148793, 150833, 152879, 154927, 156971, 159017, 161059, 163063, 165103, 167149, 169181, 171203, 173249, 175291, 177337, 179383, 181421, 183461, 185491, 187531, 189559, 191599, 193619, 195659, 197699, 199741, 201787, 203821, 205847, 207877, 209917, 211949, 213989, 216037, 218083, 220123, 222163, 224209, 226241, 228281, 230327, 232367, 234383, 236429, 238477, 240517, 242551, 244597, 246643, 248683, 250727, 252767, 254803, 256831, 258871, 260893, 262937, 264977, 267017, 269063, 271109, 273157, 275201, 277247, 279269, 281317, 283303, 285343, 287387, 289423, 291457, 293483, 295517, 297533, 299569, 301601, 303649, 305663, 307711, 309737, 311749, 313783, 315829, 317857, 319901, 321949, 323987, 326023, 328067, 330103, 332147, 334189, 336227, 338269, 340297, 342343, 344371, 346417, 348463, 350503, 352549, 354587, 356621, 358669, 360653, 362693, 364739, 366787, 368833, 370879, 372917, 374953, 376969, 379013, 381061, 383107, 385153, 387199, 389231, 391273, 393311, 395323, 397361, 399409, 401417, 403439, 405487, 407527, 409573, 411617, 413653, 415697, 417737, 419777, 421807, 423853, 425899, 427939, 429973, 432007, 434039, 436087, 438133, 440179, 442217, 444253, 446293, 448321, 450367, 452401, 454417, 456461, 458501, 460543, 462589, 464621, 466651, 468697, 470731, 472763, 474811, 476851, 478897, 480941, 482971, 484999, 487021, 489061, 491083, 493127, 495161, 497197, 499229, 501271, 503317, 505357, 507401, 509449, 511487, 513533, 515579, 517619, 519667, 521707, 523741, 525781, 527819, 529847, 531877, 533921, 535967, 538001, 540041, 542083, 544129, 546173, 548221, 550267, 552301, 554347, 556373, 558421, 560459, 562501, 564533, 566567, 568609, 570649, 572687, 574733, 576769, 578803, 580843, 582887, 584923, 586961, 588977, 591023, 593071, 595117, 597137, 599153, 601201, 603227, 605261, 607309, 609337, 611333, 613381, 615427, 617473, 619511, 621541, 623563, 625609, 627643, 629689, 631733, 633781, 635821, 637841, 639857, 641897, 643927, 645973, 648019, 650059, 652087, 654127, 656171, 658219, 660251, 662287, 664331, 666353, 668347, 670379, 672379, 674419, 676463, 678499, 680539, 682547, 684587, 686611, 688657, 690689, 692729, 694763, 696811, 698849, 700897, 702937, 704983, 707029, 709057, 711097, 713129, 715171, 717191, 719239, 721283, 723319, 725359, 727399, 729413, 731447, 733489, 735533, 737573, 739621, 741667]

/-- Primes with gaps at most 4096, from at most 8192 up to `(16384)^(3/2)`. -/
def band7 : List ℕ := [8191, 12281, 16369, 20443, 24533, 28627, 32719, 36809, 40903, 44987, 49081, 53173, 57269, 61363, 65449, 69539, 73613, 77699, 81773, 85853, 89939, 94033, 98129, 102217, 106307, 110359, 114451, 118543, 122611, 126703, 130787, 134873, 138967, 143063, 147151, 151247, 155333, 159421, 163517, 167611, 171707, 175783, 179849, 183943, 188029, 192121, 196201, 200297, 204377, 208469, 212561, 216653, 220747, 224831, 228923, 232987, 237073, 241169, 245261, 249341, 253433, 257519, 261601, 265621, 269713, 273803, 277897, 281993, 286073, 290161, 294251, 298343, 302429, 306517, 310591, 314651, 318743, 322807, 326903, 330997, 335089, 339173, 343267, 347359, 351437, 355529, 359621, 363691, 367781, 371873, 375967, 380059, 384151, 388237, 392333, 396427, 400523, 404597, 408691, 412771, 416851, 420941, 425027, 429119, 433207, 437293, 441361, 445453, 449549, 453643, 457739, 461819, 465901, 469993, 474077, 478171, 482263, 486349, 490421, 494497, 498583, 502669, 506743, 510827, 514903, 518989, 523049, 527143, 531239, 535333, 539401, 543497, 547583, 551671, 555767, 559859, 563947, 568033, 572107, 576203, 580291, 584387, 588481, 592577, 596671, 600751, 604837, 608903, 612977, 617059, 621143, 625237, 629311, 633407, 637499, 641581, 645661, 649751, 653831, 657911, 662003, 666091, 670177, 674273, 678367, 682463, 686551, 690629, 694721, 698779, 702869, 706961, 711049, 715123, 719203, 723293, 727369, 731447, 735533, 739621, 743711, 747781, 751871, 755959, 760043, 764131, 768221, 772313, 776401, 780469, 784561, 788651, 792731, 796819, 800909, 804997, 809093, 813167, 817237, 821333, 825421, 829511, 833597, 837679, 841751, 845833, 849923, 854017, 858113, 862207, 866293, 870367, 874459, 878551, 882631, 886667, 890761, 894811, 898897, 902987, 907073, 911167, 915259, 919351, 923441, 927533, 931621, 935717, 939793, 943871, 947963, 952057, 956147, 960229, 964309, 968389, 972481, 976571, 980641, 984733, 988829, 992923, 997019, 1001107, 1005203, 1009291, 1013377, 1017473, 1021561, 1025653, 1029731, 1033807, 1037903, 1041991, 1046081, 1050169, 1054259, 1058353, 1062443, 1066531, 1070621, 1074713, 1078807, 1082891, 1086937, 1091033, 1095119, 1099199, 1103293, 1107389, 1111457, 1115551, 1119623, 1123709, 1127803, 1131883, 1135969, 1139993, 1144081, 1148177, 1152233, 1156327, 1160413, 1164503, 1168553, 1172579, 1176673, 1180757, 1184839, 1188931, 1193021, 1197113, 1201201, 1205293, 1209379, 1213469, 1217561, 1221653, 1225729, 1229807, 1233899, 1237993, 1242089, 1246181, 1250273, 1254367, 1258457, 1262543, 1266631, 1270679, 1274773, 1278857, 1282951, 1287047, 1291139, 1295221, 1299317, 1303411, 1307507, 1311599, 1315673, 1319743, 1323799, 1327889, 1331969, 1336057, 1340153, 1344227, 1348313, 1352389, 1356473, 1360537, 1364633, 1368727, 1372799, 1376839, 1380931, 1385023, 1389107, 1393193, 1397287, 1401377, 1405451, 1409543, 1413623, 1417699, 1421779, 1425863, 1429951, 1434031, 1438123, 1442209, 1446301, 1450391, 1454477, 1458547, 1462631, 1466719, 1470797, 1474877, 1478963, 1483049, 1487131, 1491227, 1495321, 1499413, 1503503, 1507591, 1511687, 1515757, 1519831, 1523917, 1528013, 1532107, 1536191, 1540249, 1544341, 1548433, 1552517, 1556609, 1560683, 1564777, 1568873, 1572929, 1577021, 1581113, 1585201, 1589297, 1593379, 1597469, 1601563, 1605631, 1609717, 1613813, 1617893, 1621979, 1626073, 1630169, 1634257, 1638353, 1642447, 1646543, 1650637, 1654733, 1658827, 1662901, 1666991, 1671077, 1675139, 1679233, 1683317, 1687393, 1691479, 1695559, 1699651, 1703731, 1707791, 1711859, 1715927, 1720003, 1724083, 1728179, 1732273, 1736369, 1740461, 1744549, 1748639, 1752721, 1756817, 1760897, 1764979, 1769069, 1773157, 1777247, 1781341, 1785431, 1789519, 1793611, 1797673, 1801769, 1805863, 1809953, 1814047, 1818109, 1822189, 1826281, 1830349, 1834439, 1838531, 1842619, 1846711, 1850803, 1854899, 1858973, 1863067, 1867157, 1871249, 1875337, 1879429, 1883513, 1887607, 1891679, 1895767, 1899847, 1903931, 1908013, 1912093, 1916183, 1920271, 1924343, 1928419, 1932503, 1936579, 1940663, 1944737, 1948801, 1952893, 1956979, 1961059, 1965133, 1969223, 1973317, 1977407, 1981493, 1985587, 1989683, 1993763, 1997851, 2001919, 2006009, 2010103, 2014193, 2018287, 2022359, 2026447, 2030533, 2034619, 2038703, 2042797, 2046893, 2050987, 2055071, 2059157, 2063251, 2067337, 2071429, 2075483, 2079577, 2083643, 2087717, 2091809, 2095867, 2099963]

/-- Primes with gaps at most 8192, from at most 16384 up to `(32768)^(3/2)`. -/
def band8 : List ℕ := [16381, 24571, 32749, 40939, 49123, 57301, 65479, 73651, 81839, 90031, 98221, 106411, 114601, 122789, 130981, 139169, 147353, 155539, 163729, 171917, 180097, 188281, 196459, 204641, 212827, 220973, 229157, 237343, 245533, 253717, 261887, 270073, 278261, 286453, 294641, 302833, 311021, 319211, 327401, 335591, 343771, 351959, 360091, 368279, 376471, 384641, 392831, 401017, 409187, 417379, 425563, 433747, 441937, 450127, 458317, 466483, 474671, 482863, 491041, 499229, 507421, 515611, 523801, 531989, 540181, 548371, 556559, 564713, 572903, 581089, 589273, 597451, 605641, 613829, 622019, 630197, 638371, 646549, 654739, 662917, 671093, 679279, 687461, 695641, 703819, 712007, 720197, 728383, 736511, 744701, 752891, 761069, 769261, 777451, 785641, 793813, 801989, 810151, 818341, 826499, 834671, 842857, 851041, 859223, 867413, 875593, 883783, 891967, 900157, 908321, 916511, 924697, 932887, 941041, 949213, 957403, 965567, 973759, 981949, 990137, 998329, 1006513, 1014697, 1022881, 1031057, 1039249, 1047419, 1055611, 1063781, 1071943, 1080119, 1088309, 1096499, 1104683, 1112857, 1121047, 1129229, 1137407, 1145593, 1153777, 1161949, 1170139, 1178297, 1186489, 1194679, 1202867, 1211059, 1219241, 1227431, 1235593, 1243783, 1251961, 1260143, 1268327, 1276511, 1284691, 1292857, 1301033, 1309219, 1317409, 1325581, 1333751, 1341931, 1350119, 1358309, 1366493, 1374683, 1382861, 1391051, 1399231, 1407409, 1415591, 1423781, 1431967, 1440119, 1448309, 1456501, 1464689, 1472869, 1481047, 1489231, 1497421, 1505611, 1513777, 1521937, 1530107, 1538293, 1546477, 1554659, 1562833, 1571023, 1579187, 1587361, 1595527, 1603711, 1611901, 1620071, 1628261, 1636423, 1644611, 1652801, 1660963, 1669147, 1677337, 1685527, 1693711, 1701901, 1710091, 1718281, 1726471, 1734647, 1742809, 1750999, 1759181, 1767373, 1775563, 1783751, 1791943, 1800121, 1808309, 1816489, 1824679, 1832863, 1841039, 1849231, 1857407, 1865587, 1873771, 1881961, 1890149, 1898317, 1906481, 1914673, 1922863, 1931053, 1939243, 1947431, 1955609, 1963799, 1971967, 1980113, 1988299, 1996487, 2004679, 2012849, 2021029, 2029207, 2037391, 2045569, 2053757, 2061923, 2070091, 2078243, 2086433, 2094623, 2102809, 2110981, 2119171, 2127347, 2135537, 2143711, 2151899, 2160061, 2168239, 2176423, 2184583, 2192761, 2200949, 2209117, 2217301, 2225491, 2233657, 2241809, 2249987, 2258177, 2266343, 2274523, 2282711, 2290901, 2299093, 2307281, 2315471, 2323631, 2331781, 2339969, 2348161, 2356351, 2364521, 2372687, 2380877, 2389067, 2397259, 2405443, 2413613, 2421791, 2429983, 2438173, 2446363, 2454539, 2462731, 2470903, 2479069, 2487259, 2495443, 2503597, 2511779, 2519969, 2528161, 2536343, 2544523, 2552713, 2560891, 2569079, 2577241, 2585417, 2593609, 2601787, 2609963, 2618117, 2626307, 2634493, 2642639, 2650829, 2659001, 2667193, 2675369, 2683561, 2691743, 2699911, 2708099, 2716289, 2724481, 2732671, 2740853, 2749031, 2757221, 2765387, 2773579, 2781749, 2789939, 2798129, 2806291, 2814481, 2822669, 2830859, 2839049, 2847227, 2855399, 2863591, 2871767, 2879927, 2888117, 2896297, 2904487, 2912659, 2920837, 2929009, 2937173, 2945359, 2953537, 2961727, 2969903, 2978089, 2986259, 2994449, 3002641, 3010831, 3019019, 3027187, 3035371, 3043559, 3051751, 3059921, 3068111, 3076289, 3084481, 3092669, 3100861, 3109031, 3117223, 3125387, 3133547, 3141713, 3149903, 3158087, 3166279, 3174467, 3182659, 3190829, 3199013, 3207199, 3215383, 3223567, 3231757, 3239947, 3248137, 3256327, 3264491, 3272681, 3280867, 3289043, 3297209, 3305389, 3313577, 3321763, 3329939, 3338131, 3346309, 3354493, 3362683, 3370849, 3379037, 3387203, 3395369, 3403559, 3411743, 3419921, 3428099, 3436291, 3444481, 3452671, 3460819, 3468991, 3477161, 3485353, 3493541, 3501733, 3509917, 3518101, 3526283, 3534473, 3542657, 3550843, 3559019, 3567211, 3575371, 3583543, 3591733, 3599899, 3608071, 3616259, 3624443, 3632633, 3640823, 3649003, 3657187, 3665377, 3673529, 3681719, 3689911, 3698099, 3706259, 3714439, 3722629, 3730817, 3739009, 3747197, 3755387, 3763567, 3771751, 3779929, 3788117, 3796307, 3804491, 3812663, 3820853, 3828973, 3837151, 3845341, 3853529, 3861721, 3869881, 3878051, 3886237, 3894419, 3902609, 3910787, 3918949, 3927139, 3935311, 3943481, 3951611, 3959803, 3967993, 3976183, 3984347, 3992533, 4000723, 4008887, 4017067, 4025249, 4033423, 4041601, 4049789, 4057969, 4066151, 4074319, 4082489, 4090679, 4098869, 4107029, 4115213, 4123387, 4131577, 4139767, 4147943, 4156093, 4164271, 4172431, 4180621, 4188803, 4196993, 4205183, 4213369, 4221551, 4229741, 4237927, 4246111, 4254277, 4262459, 4270639, 4278829, 4286987, 4295177, 4303361, 4311551, 4319743, 4327913, 4336103, 4344283, 4352473, 4360663, 4368823, 4377001, 4385159, 4393321, 4401497, 4409687, 4417813, 4425997, 4434181, 4442363, 4450553, 4458739, 4466923, 4475083, 4483273, 4491439, 4499623, 4507799, 4515943, 4524097, 4532267, 4540439, 4548631, 4556813, 4565003, 4573183, 4581331, 4589521, 4597709, 4605901, 4614067, 4622257, 4630447, 4638631, 4646821, 4655009, 4663201, 4671389, 4679581, 4687769, 4695953, 4704127, 4712317, 4720501, 4728677, 4736861, 4745051, 4753219, 4761403, 4769593, 4777781, 4785961, 4794151, 4802339, 4810517, 4818691, 4826867, 4835057, 4843247, 4851397, 4859581, 4867771, 4875943, 4884127, 4892309, 4900501, 4908691, 4916869, 4925029, 4933207, 4941383, 4949551, 4957739, 4965923, 4974097, 4982273, 4990463, 4998647, 5006839, 5014979, 5023169, 5031361, 5039549, 5047739, 5055923, 5064091, 5072269, 5080451, 5088631, 5096813, 5104993, 5113169, 5121359, 5129489, 5137681, 5145871, 5154049, 5162233, 5170411, 5178599, 5186777, 5194967, 5203157, 5211347, 5219537, 5227727, 5235917, 5244103, 5252281, 5260469, 5268647, 5276833, 5284999, 5293181, 5301367, 5309539, 5317703, 5325869, 5334047, 5342237, 5350417, 5358607, 5366791, 5374973, 5383159, 5391349, 5399531, 5407693, 5415881, 5424053, 5432239, 5440427, 5448617, 5456807, 5464981, 5473147, 5481323, 5489513, 5497697, 5505889, 5514079, 5522261, 5530439, 5538581, 5546771, 5554951, 5563127, 5571283, 5579461, 5587627, 5595817, 5604007, 5612179, 5620369, 5628533, 5636693, 5644861, 5653049, 5661217, 5669387, 5677571, 5685763, 5693921, 5702063, 5710223, 5718413, 5726587, 5734747, 5742937, 5751113, 5759267, 5767453, 5775617, 5783807, 5791993, 5800159, 5808349, 5816521, 5824703, 5832847, 5841029, 5849203, 5857381, 5865571, 5873761, 5881919, 5890111, 5898293, 5906449, 5914627, 5922811, 5930963, 5939149]

def bnd : List ℕ := [0, 3, 9, 49, 20, 62, 36, 87, 57, 46, 40, 66, 58, 91, 79, 71, 66, 93, 86, 119, 109, 101, 95, 125, 117, 111, 107, 103, 99, 123, 119, 146, 140, 136]
def lpf : List ℕ := [2, 2, 2, 3, 2, 5, 3, 7, 2, 3, 5, 11, 3, 13, 7, 5, 2, 17, 3, 19, 5, 7, 11, 23, 3, 5, 13, 3, 7, 29, 5, 31, 2, 11, 17, 7, 3, 37, 19, 13, 5, 41, 7, 43, 11, 5, 23, 47, 3, 7, 5, 17, 13, 53, 3, 11, 7, 19, 29, 59, 5, 61, 31, 7, 2, 13, 11, 67, 17, 23, 7, 71, 3, 73, 37, 5, 19, 11, 13, 79, 5, 3, 41, 83, 7, 17, 43, 29, 11, 89, 5, 13, 23, 31, 47, 19, 3, 97, 7, 11, 5, 101, 17, 103, 13, 7, 53, 107, 3, 109, 11, 37, 7, 113, 19, 23, 29, 13, 59, 17, 5, 11, 61, 41, 31, 5, 7, 127, 2, 43, 13, 131, 11, 19, 67, 5, 17, 137, 23, 139, 7, 47, 71, 13, 3, 29, 73]
def smallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139]

/- ## Step 5: the finite residue -/

lemma prime_dvd_choose_of_dvd_term {p N k i : ℕ} (hp : p.Prime) (hkp : k < p) (hi : i < k)
    (hd : p ∣ N - i) : p ∣ N.choose k := by
  have h1 : p ∣ N.descFactorial k := by
    rw [Nat.descFactorial_eq_prod_range]
    exact dvd_trans hd (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hi))
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h1
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
  · exact absurd ((Nat.Prime.dvd_factorial hp).1 h) (by omega)
  · exact h

/-- Boolean check that consecutive entries of a list differ by at most `g`. -/
def chainOK (g : ℕ) : List ℕ → Bool
  | a :: b :: rest => decide (b ≤ a + g) && chainOK g (b :: rest)
  | _ => true

/-- The last entry of a list (`0` for the empty list). -/
def lastD : List ℕ → ℕ
  | [] => 0
  | [a] => a
  | _ :: b :: rest => lastD (b :: rest)

lemma window_ok (g N : ℕ) (hg : 0 < g) :
    ∀ (rest : List ℕ) (a : ℕ), chainOK g (a :: rest) = true → a ≤ N →
      N ≤ lastD (a :: rest) → ∃ p ∈ a :: rest, p ≤ N ∧ N < p + g
  | [], a, _, h1, h2 => ⟨a, List.mem_cons_self, h1, by simp only [lastD] at h2; omega⟩
  | b :: rest, a, hc, h1, h2 => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at hc
    by_cases hN : N < b
    · exact ⟨a, List.mem_cons_self, h1, by omega⟩
    · obtain ⟨p, hp, h⟩ := window_ok g N hg rest b hc.2 (by omega)
        (by simp only [lastD] at h2; exact h2)
      exact ⟨p, List.mem_cons_of_mem _ hp, h⟩

lemma band_ok (L : List ℕ) (lo hi : ℕ) (hlo : 0 < lo) (hpr : ∀ p ∈ L, p.Prime)
    (hch : chainOK lo L = true) (ha2 : L.headD 0 ≤ 2 * lo) (hb2 : (2 * hi) ^ 3 ≤ lastD L ^ 2)
    {N k : ℕ} (hk1 : lo ≤ k) (hk2 : k < hi)
    (h2k : 2 * k ≤ N) (hsm : N ^ 2 < (2 * k) ^ 3) : ∃ p, p.Prime ∧ k < p ∧ p ∣ N.choose k := by
  have hNb : N ≤ lastD L := by
    have h3 : (2 * k) ^ 3 ≤ (2 * hi) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have : N ^ 2 < lastD L ^ 2 := by omega
    exact ((Nat.pow_lt_pow_iff_left (by norm_num)).1 this).le
  cases L with
  | nil =>
    simp only [lastD] at hb2
    have : 0 < (2 * hi) ^ 3 := pow_pos (by omega) 3
    omega
  | cons a rest =>
    simp only [List.headD_cons] at ha2
    obtain ⟨p, hpL, hpN, hNp⟩ := window_ok lo N hlo rest a hch (by omega) hNb
    refine ⟨p, hpr p hpL, by omega, ?_⟩
    exact prime_dvd_choose_of_dvd_term (i := N - p) (hpr p hpL) (by omega) (by omega)
      (by rw [show N - (N - p) = p by omega])

set_option maxRecDepth 100000 in
lemma band0_prime : ∀ p ∈ band0, p.Prime := by
  simp only [band0, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band0_chain : chainOK 34 band0 = true := by decide

set_option maxRecDepth 100000 in
lemma band0_ends : band0.headD 0 ≤ 2 * 34 ∧ (2 * 64) ^ 3 ≤ lastD band0 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band1_prime : ∀ p ∈ band1, p.Prime := by
  simp only [band1, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band1_chain : chainOK 64 band1 = true := by decide

set_option maxRecDepth 100000 in
lemma band1_ends : band1.headD 0 ≤ 2 * 64 ∧ (2 * 128) ^ 3 ≤ lastD band1 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band2_prime : ∀ p ∈ band2, p.Prime := by
  simp only [band2, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band2_chain : chainOK 128 band2 = true := by decide

set_option maxRecDepth 100000 in
lemma band2_ends : band2.headD 0 ≤ 2 * 128 ∧ (2 * 256) ^ 3 ≤ lastD band2 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band3_prime : ∀ p ∈ band3, p.Prime := by
  simp only [band3, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band3_chain : chainOK 256 band3 = true := by decide

set_option maxRecDepth 100000 in
lemma band3_ends : band3.headD 0 ≤ 2 * 256 ∧ (2 * 512) ^ 3 ≤ lastD band3 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band4_prime : ∀ p ∈ band4, p.Prime := by
  simp only [band4, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band4_chain : chainOK 512 band4 = true := by decide

set_option maxRecDepth 100000 in
lemma band4_ends : band4.headD 0 ≤ 2 * 512 ∧ (2 * 1024) ^ 3 ≤ lastD band4 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band5_prime : ∀ p ∈ band5, p.Prime := by
  simp only [band5, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band5_chain : chainOK 1024 band5 = true := by decide

set_option maxRecDepth 100000 in
lemma band5_ends : band5.headD 0 ≤ 2 * 1024 ∧ (2 * 2048) ^ 3 ≤ lastD band5 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band6_prime : ∀ p ∈ band6, p.Prime := by
  simp only [band6, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band6_chain : chainOK 2048 band6 = true := by decide

set_option maxRecDepth 100000 in
lemma band6_ends : band6.headD 0 ≤ 2 * 2048 ∧ (2 * 4096) ^ 3 ≤ lastD band6 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band7_prime : ∀ p ∈ band7, p.Prime := by
  simp only [band7, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band7_chain : chainOK 4096 band7 = true := by decide

set_option maxRecDepth 100000 in
lemma band7_ends : band7.headD 0 ≤ 2 * 4096 ∧ (2 * 8192) ^ 3 ≤ lastD band7 ^ 2 := by decide

set_option maxRecDepth 100000 in
lemma band8_prime : ∀ p ∈ band8, p.Prime := by
  simp only [band8, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true]
  norm_num

set_option maxRecDepth 100000 in
lemma band8_chain : chainOK 8192 band8 = true := by decide

set_option maxRecDepth 100000 in
lemma band8_ends : band8.headD 0 ≤ 2 * 8192 ∧ (2 * 16384) ^ 3 ≤ lastD band8 ^ 2 := by decide

lemma small_bound {N k B : ℕ} (hB : 2 ^ k * k ! < B ^ (k - pc k)) (hpk : pc k ≤ k)
    (hBN : B ≤ N) (hc : N ^ k ≤ 2 ^ k * k ! * N ^ pc k) (hN : 0 < N) : False := by
  have h1 : N ^ k = N ^ (k - pc k) * N ^ pc k := by rw [← pow_add, Nat.sub_add_cancel hpk]
  have h2 : B ^ (k - pc k) ≤ N ^ (k - pc k) := Nat.pow_le_pow_left hBN _
  have h3 : 2 ^ k * k ! * N ^ pc k < B ^ (k - pc k) * N ^ pc k :=
    Nat.mul_lt_mul_of_pos_right hB (by positivity)
  have h4 : B ^ (k - pc k) * N ^ pc k ≤ N ^ k := by rw [h1]; exact Nat.mul_le_mul_right _ h2
  omega

set_option maxRecDepth 100000 in
lemma small_table : ∀ k < 34, 1 ≤ k → pc k ≤ k ∧ 2 ^ k * k ! < (bnd.getD k 0) ^ (k - pc k) := by
  decide

set_option maxRecDepth 100000 in
lemma small_witness : ∀ k < 34, ∀ N < 147, 1 ≤ k → 2 * k ≤ N → N < bnd.getD k 0 →
    ∃ i < k, k < lpf.getD (N - i) 0 := by
  decide

set_option maxRecDepth 100000 in
lemma lpf_mem : ∀ j < 147, 2 ≤ j → lpf.getD j 0 ∈ smallPrimes ∧ lpf.getD j 0 ∣ j := by
  decide

lemma smallPrimes_prime : ∀ p ∈ smallPrimes, p.Prime := by
  simp only [smallPrimes, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  norm_num

lemma bnd_le (k : ℕ) (hk : k < 34) (hk1 : 1 ≤ k) : bnd.getD k 0 ≤ 147 := by
  interval_cases k <;> decide

/-- **Sylvester–Schur** in binomial form. -/
theorem sylvester (k N : ℕ) (hk : 0 < k) (h2k : 2 * k ≤ N) :
    ∃ p, p.Prime ∧ k < p ∧ p ∣ N.choose k := by
  by_contra hcon
  have H : ∀ p, p.Prime → p ∣ N.choose k → p ≤ k := fun p hp hd => by
    by_contra h
    exact hcon ⟨p, hp, by omega, hd⟩
  rcases lt_or_ge k 34 with hk34 | hk34
  · obtain ⟨hpk, hB⟩ := small_table k hk34 hk
    rcases lt_or_ge N (bnd.getD k 0) with hNB | hNB
    · have h147 := bnd_le k hk34 hk
      obtain ⟨i, hi, hki⟩ := small_witness k hk34 N (by omega) hk h2k hNB
      obtain ⟨hmem, hdvd⟩ := lpf_mem (N - i) (by omega) (by omega)
      have hq := smallPrimes_prime _ hmem
      exact hcon ⟨_, hq, hki, prime_dvd_choose_of_dvd_term hq hki hi hdvd⟩
    · exact small_bound hB hpk hNB (counting_bound h2k (by omega) H) (by omega)
  · have hsm := not_large_region hk34 h2k H
    rcases lt_or_ge k 16384 with hkb | hkb
    · apply hcon

      rcases lt_or_ge k 64 with h0 | h0
      · exact band_ok band0 34 64 (by norm_num) band0_prime band0_chain band0_ends.1
          band0_ends.2 (by omega) h0 h2k hsm
      rcases lt_or_ge k 128 with h1 | h1
      · exact band_ok band1 64 128 (by norm_num) band1_prime band1_chain band1_ends.1
          band1_ends.2 (by omega) h1 h2k hsm
      rcases lt_or_ge k 256 with h2 | h2
      · exact band_ok band2 128 256 (by norm_num) band2_prime band2_chain band2_ends.1
          band2_ends.2 (by omega) h2 h2k hsm
      rcases lt_or_ge k 512 with h3 | h3
      · exact band_ok band3 256 512 (by norm_num) band3_prime band3_chain band3_ends.1
          band3_ends.2 (by omega) h3 h2k hsm
      rcases lt_or_ge k 1024 with h4 | h4
      · exact band_ok band4 512 1024 (by norm_num) band4_prime band4_chain band4_ends.1
          band4_ends.2 (by omega) h4 h2k hsm
      rcases lt_or_ge k 2048 with h5 | h5
      · exact band_ok band5 1024 2048 (by norm_num) band5_prime band5_chain band5_ends.1
          band5_ends.2 (by omega) h5 h2k hsm
      rcases lt_or_ge k 4096 with h6 | h6
      · exact band_ok band6 2048 4096 (by norm_num) band6_prime band6_chain band6_ends.1
          band6_ends.2 (by omega) h6 h2k hsm
      rcases lt_or_ge k 8192 with h7 | h7
      · exact band_ok band7 4096 8192 (by norm_num) band7_prime band7_chain band7_ends.1
          band7_ends.2 (by omega) h7 h2k hsm
      exact band_ok band8 8192 16384 (by norm_num) band8_prime band8_chain band8_ends.1
        band8_ends.2 (by omega) hkb h2k hsm
    · exact middle_region (by norm_num; omega) h2k hsm H

end SylvesterSchurOMA

end SylvesterPart

theorem sylvester_block (n k : ℕ) (hk : 0 < k) (hn : k < n) :
    ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n + k), t := by
  obtain ⟨p, hp, hpBig, hpChoose⟩ := SylvesterSchurOMA.sylvester k (n+k) hk (by omega)
  have hd : p ∣ (n+k).descFactorial k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    exact Dvd.dvd.mul_left hpChoose _
  rw [Nat.descFactorial_eq_prod_range] at hd
  obtain ⟨i, hi, hpTerm⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
  have hi' := mem_range.mp hi
  have ht : n+k-i ∈ Ioc n (n+k) := mem_Ioc.mpr ⟨by omega, by omega⟩
  exact ⟨p, hp, hpBig, hpTerm.trans (Finset.dvd_prod_of_mem (fun t : ℕ => t) ht)⟩

-- Worked proof. The block below is copied unchanged from the merged sibling proof
-- proofs/Erdos137.erdos_137.variants.perfect_power.R1.H3.R1.H1.lean (lines 14 to 1113),
-- in the repository open-math-agents. See ROUTE.md, section Credits.
namespace Erdos137H3Square

open Finset

def cutoff (k : ℕ) : ℕ :=
  if k < 20 then 3 else if k < 56 then 5 else if k < 176 then 7
  else if k < 416 then 11 else 13

def smallPrimes (k s : ℕ) : Finset ℕ :=
  ((range k).filter Nat.Prime).filter (· ≤ s)

def largePrimes (k s : ℕ) : Finset ℕ :=
  ((range k).filter Nat.Prime).filter (s < ·)

def multiples (n k p : ℕ) : Finset ℕ :=
  (Ioc n (n + k)).filter (p ∣ ·)

lemma card_multiples_le (n k p : ℕ) (hp : 0 < p) :
    (multiples n k p).card ≤ (k + p - 1) / p := by
  let left := (Ioc 0 n).filter (p ∣ ·)
  have hUnion : (Ioc 0 (n + k)).filter (p ∣ ·) = left ∪ multiples n k p := by
    ext m
    simp only [left, multiples, mem_union, mem_filter, mem_Ioc]
    omega
  have hDisj : Disjoint left (multiples n k p) := by
    rw [Finset.disjoint_left]
    intro m hl hr
    have hl' := mem_Ioc.mp (mem_filter.mp hl).1
    have hr' := mem_Ioc.mp (mem_filter.mp hr).1
    omega
  have hCard : (n + k) / p = n / p + (multiples n k p).card := by
    have h := congrArg Finset.card hUnion
    rw [Finset.card_union_of_disjoint hDisj, Nat.Ioc_filter_dvd_card_eq_div] at h
    dsimp only [left] at h
    rw [Nat.Ioc_filter_dvd_card_eq_div] at h
    exact h
  have hEq : (n + k) / p = (n % p + k) / p + n / p := by
    have hSplit := Nat.mod_add_div n p
    calc
      (n + k) / p = (n % p + k + p * (n / p)) / p := by
        have hv : n + k = n % p + k + p * (n / p) := by omega
        rw [hv]
      _ = (n % p + k) / p + n / p := Nat.add_mul_div_left _ _ hp
  have hMod := Nat.mod_lt n hp
  have hLe : (n % p + k) / p ≤ (k + p - 1) / p :=
    Nat.div_le_div_right (by omega)
  omega

lemma primeFactors_injective_on_squarefree {S : Finset ℕ} {a : ℕ → ℕ}
    (hSquare : ∀ t ∈ S, Squarefree (a t)) (hInj : Set.InjOn a ↑S) :
    Set.InjOn (fun t => (a t).primeFactors) ↑S := by
  intro i hi j hj h
  change (a i).primeFactors = (a j).primeFactors at h
  apply hInj hi hj
  calc
    a i = ∏ p ∈ (a i).primeFactors, p := (Nat.prod_primeFactors_of_squarefree (hSquare i hi)).symm
    _ = ∏ p ∈ (a j).primeFactors, p := by rw [h]
    _ = a j := Nat.prod_primeFactors_of_squarefree (hSquare j hj)

lemma squarefree_capacity_with_bad (n k s : ℕ) (a : ℕ → ℕ)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hDvd : ∀ t ∈ Ioc n (n + k), a t ∣ t)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) :
    k ≤ 2 ^ (smallPrimes k s).card + ((largePrimes k s).biUnion (multiples n k)).card := by
  let S := Ioc n (n + k)
  let bad := (largePrimes k s).biUnion (multiples n k)
  let good := S \ bad
  have hBadSub : bad ⊆ S := by
    intro t ht
    obtain ⟨p, _, ht⟩ := mem_biUnion.mp ht
    exact (mem_filter.mp ht).1
  have hGoodSub : good ⊆ S := Finset.sdiff_subset
  have hGoodCard : good.card ≤ 2 ^ (smallPrimes k s).card := by
    rw [← Finset.card_powerset]
    apply Finset.card_le_card_of_injOn (fun t => (a t).primeFactors)
    · intro t ht
      apply mem_powerset.mpr
      intro p hp
      obtain ⟨hpPrime, hpDvd, _⟩ := Nat.mem_primeFactors.mp hp
      have htS := hGoodSub ht
      have hpLt := hSupport t htS p hp
      have hpSmall : p ≤ s := by
        by_contra! hpLarge
        have hLarge : p ∈ largePrimes k s := by
          simp [largePrimes, hpLt, hpPrime, hpLarge]
        have hHit : t ∈ multiples n k p := mem_filter.mpr ⟨htS, hpDvd.trans (hDvd t htS)⟩
        exact (mem_sdiff.mp ht).2 (mem_biUnion.mpr ⟨p, hLarge, hHit⟩)
      simp [smallPrimes, hpLt, hpPrime, hpSmall]
    · exact (primeFactors_injective_on_squarefree hSquare hInj).mono (fun _ ht => hGoodSub ht)
  have hTotal := Finset.card_sdiff_add_card_eq_card hBadSub
  have hSC : S.card = k := by simp [S]
  calc
    k = S.card := hSC.symm
    _ = good.card + bad.card := hTotal.symm
    _ ≤ 2 ^ (smallPrimes k s).card + bad.card := Nat.add_le_add_right hGoodCard _

lemma squarefree_capacity (n k s : ℕ) (a : ℕ → ℕ)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hDvd : ∀ t ∈ Ioc n (n + k), a t ∣ t)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) :
    k ≤ 2 ^ (smallPrimes k s).card + ∑ p ∈ largePrimes k s, (k + p - 1) / p := by
  let bad := (largePrimes k s).biUnion (multiples n k)
  have hBadCard : bad.card ≤ ∑ p ∈ largePrimes k s, (k + p - 1) / p := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro p hp
    have hpPrime : p.Prime := (mem_filter.mp (mem_filter.mp hp).1).2
    exact card_multiples_le n k p hpPrime.pos
  exact (squarefree_capacity_with_bad n k s a hSquare hInj hDvd hSupport).trans
    (Nat.add_le_add_left hBadCard _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma square_capacity_certificate :
    ∀ k : Fin 676, 3 ≤ k.val → k.val ≠ 4 → k.val ≠ 6 → k.val ≠ 8 →
      2 ^ (smallPrimes k.val (cutoff k.val)).card +
        (∑ p ∈ largePrimes k.val (cutoff k.val), (k.val + p - 1) / p) < k.val := by
  decide

theorem squarefree_coefficients_impossible_below_676 {n k : ℕ} {a : ℕ → ℕ}
    (hk : 3 ≤ k) (hUpper : k < 676) (h4 : k ≠ 4) (h6 : k ≠ 6) (h8 : k ≠ 8)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hDvd : ∀ t ∈ Ioc n (n + k), a t ∣ t)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) : False := by
  have hUpperCount := square_capacity_certificate ⟨k, hUpper⟩ hk h4 h6 h8
  have hLowerCount := squarefree_capacity n k (cutoff k) a hSquare hInj hDvd hSupport
  exact (not_lt_of_ge hLowerCount) hUpperCount

lemma four_consecutive_not_square (a x : ℕ) (ha : 0 < a) :
    a * (a + 1) * (a + 2) * (a + 3) ≠ x ^ 2 := by
  intro h
  let m := a ^ 2 + 3 * a + 1
  have heq : x ^ 2 + 1 = m ^ 2 := by
    rw [← h]
    dsimp [m]
    ring
  have hm : 1 < m := by dsimp [m]; nlinarith
  have hx : 0 < x := by
    by_contra! hx
    have hx' : x = 0 := by omega
    rw [hx'] at heq
    nlinarith
  have hxm : x < m :=
    (Nat.pow_lt_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp (by omega)
  have hgap : (x + 1) ^ 2 ≤ m ^ 2 :=
    (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).2 (by omega)
  nlinarith

theorem four_coefficients_cannot_permute_divisors_six (n : ℕ) (a x : ℕ → ℕ)
    (hRepr : ∀ t ∈ Ioc n (n + 4), t = a t * x t ^ 2)
    (hInj : Set.InjOn a ↑(Ioc n (n + 4)))
    (hSupport : ∀ t ∈ Ioc n (n + 4), a t ∈ ({1, 2, 3, 6} : Finset ℕ)) : False := by
  let S := Ioc n (n + 4)
  let values : Finset ℕ := {1, 2, 3, 6}
  have hImage : S.image a = values := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hz
      exact hSupport t ht
    · rw [Finset.card_image_of_injOn hInj]
      have hSC : S.card = 4 := by simp [S]
      rw [hSC]
      decide
  have hCoeff : (∏ t ∈ S, a t) = 36 := by
    calc
      (∏ t ∈ S, a t) = ∏ z ∈ S.image a, z := by
        rw [Finset.prod_image]
        exact hInj
      _ = 36 := by rw [hImage]; decide
  have hProduct : (∏ t ∈ S, t) = (6 * ∏ t ∈ S, x t) ^ 2 := by
    calc
      (∏ t ∈ S, t) = ∏ t ∈ S, a t * x t ^ 2 :=
        Finset.prod_congr rfl hRepr
      _ = (6 * ∏ t ∈ S, x t) ^ 2 := by
        rw [Finset.prod_mul_distrib, hCoeff, Finset.prod_pow, mul_pow]
        norm_num
  have hS : S = {n + 1, n + 2, n + 3, n + 4} := by
    ext z
    simp only [S, mem_Ioc, mem_insert, mem_singleton]
    omega
  have hList : (∏ t ∈ S, t) = (n + 1) * (n + 2) * (n + 3) * (n + 4) := by
    rw [hS]
    simp [Finset.prod_insert, Nat.mul_assoc]
  rw [hList] at hProduct
  have hFour := four_consecutive_not_square (n + 1) (6 * ∏ t ∈ S, x t) (by omega)
  exact hFour (by simpa [Nat.add_assoc] using hProduct)

lemma small_coefficients_mem {a : ℕ} (ha : Squarefree a)
    (hSupport : ∀ p ∈ a.primeFactors, p ≤ 3) :
    a ∈ ({1, 2, 3, 6} : Finset ℕ) := by
  have hSub : a.primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    have hPrime := (Nat.mem_primeFactors.mp hp).1
    have h2 := hPrime.two_le
    have h3 := hSupport p hp
    simp only [mem_insert, mem_singleton]
    omega
  have hDvd := Finset.prod_dvd_prod_of_subset a.primeFactors ({2, 3} : Finset ℕ) id hSub
  rw [show (∏ p ∈ a.primeFactors, id p) = a from Nat.prod_primeFactors_of_squarefree ha] at hDvd
  have hDvd6 : a ∣ 6 := by simpa using hDvd
  have hPos : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hBound := Nat.le_of_dvd (by decide : 0 < (6 : ℕ)) hDvd6
  have hVals : ∀ j : Fin 7, 0 < j.val → j.val ∣ 6 →
      j.val ∈ ({1, 2, 3, 6} : Finset ℕ) := by decide
  exact hVals ⟨a, by omega⟩ hPos hDvd6

def exceptionalBad (k r : ℕ) : Finset ℕ :=
  (range k).filter (fun i => 5 ∣ r + i + 1 ∨ (k = 8 ∧ 7 ∣ r + i + 1))

lemma exceptional_six_positions :
    ∀ r : Fin 35, 2 ≤ (exceptionalBad 6 r.val).card →
      ∀ i : Fin 4, 1 + i.val ∉ exceptionalBad 6 r.val := by decide

lemma exceptional_eight_positions :
    ∀ r : Fin 35, 4 ≤ (exceptionalBad 8 r.val).card →
      ∀ i : Fin 4, 2 + i.val ∉ exceptionalBad 8 r.val := by decide

lemma exceptional_divisibility (n p i : ℕ) (hp : p ∣ 35) :
    (p ∣ n + i + 1) ↔ p ∣ n % 35 + i + 1 := by
  have hDiv : p ∣ 35 * (n / 35) := dvd_mul_of_dvd_left hp _
  have hDecomp := Nat.mod_add_div n 35
  have hEq : n + i + 1 = (n % 35 + i + 1) + 35 * (n / 35) := by omega
  rw [hEq]
  exact (Nat.dvd_add_iff_left hDiv).symm

lemma exceptional_bad_image (n k : ℕ) (hk : k = 6 ∨ k = 8) :
    (exceptionalBad k (n % 35)).image (fun i => n + i + 1) =
      (largePrimes k 3).biUnion (multiples n k) := by
  have hLarge : largePrimes k 3 = if k = 8 then ({5, 7} : Finset ℕ) else {5} := by
    rcases hk with rfl | rfl <;> decide
  have hMembership (t : ℕ) : t ∈ (largePrimes k 3).biUnion (multiples n k) ↔
      t ∈ Ioc n (n + k) ∧ (5 ∣ t ∨ (k = 8 ∧ 7 ∣ t)) := by
    rw [mem_biUnion, hLarge]
    rcases hk with rfl | rfl <;> simp [multiples, and_or_left]
  ext t
  rw [hMembership, mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hiRange, hiPrime⟩ := mem_filter.mp hi
    have hiLt := mem_range.mp hiRange
    refine ⟨mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
    simpa only [exceptional_divisibility n 5 i (by decide : 5 ∣ 35),
      exceptional_divisibility n 7 i (by decide : 7 ∣ 35)] using hiPrime
  · rintro ⟨ht, htPrime⟩
    have h := mem_Ioc.mp ht
    let i := t - n - 1
    have hIt : n + i + 1 = t := by dsimp [i]; omega
    refine ⟨i, mem_filter.mpr ⟨mem_range.mpr (by dsimp [i]; omega), ?_⟩, hIt⟩
    rw [← exceptional_divisibility n 5 i (by decide : 5 ∣ 35),
      ← exceptional_divisibility n 7 i (by decide : 7 ∣ 35), hIt]
    exact htPrime

lemma exceptional_middle_avoids_large (n k : ℕ) (hk : k = 6 ∨ k = 8)
    (hCount : k - 4 ≤ ((largePrimes k 3).biUnion (multiples n k)).card) :
    ∀ t ∈ Ioc (n + (k - 4) / 2) (n + (k - 4) / 2 + 4),
      t ∉ (largePrimes k 3).biUnion (multiples n k) := by
  have hImage := exceptional_bad_image n k hk
  have hAddInj : Function.Injective (fun i : ℕ => n + i + 1) := by
    intro i j e
    change n + i + 1 = n + j + 1 at e
    omega
  rw [← hImage, Finset.card_image_of_injective _ hAddInj] at hCount
  let r : Fin 35 := ⟨n % 35, Nat.mod_lt _ (by decide)⟩
  intro t ht htBad
  have hBounds := mem_Ioc.mp ht
  rw [← hImage] at htBad
  obtain ⟨j, hj, hJt⟩ := mem_image.mp htBad
  rcases hk with rfl | rfl
  · change 2 ≤ (exceptionalBad 6 r.val).card at hCount
    change j ∈ exceptionalBad 6 r.val at hj
    let i : Fin 4 := ⟨j - 1, by omega⟩
    have hIdx : 1 + i.val = j := by dsimp [i]; omega
    exact exceptional_six_positions r hCount i (by simpa only [hIdx] using hj)
  · change 4 ≤ (exceptionalBad 8 r.val).card at hCount
    change j ∈ exceptionalBad 8 r.val at hj
    let i : Fin 4 := ⟨j - 2, by omega⟩
    have hIdx : 2 + i.val = j := by dsimp [i]; omega
    exact exceptional_eight_positions r hCount i (by simpa only [hIdx] using hj)

theorem exceptional_coefficients_impossible {n k : ℕ} {a x : ℕ → ℕ}
    (hk : k = 4 ∨ k = 6 ∨ k = 8)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hRepr : ∀ t ∈ Ioc n (n + k), t = a t * x t ^ 2)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) : False := by
  rcases hk with rfl | hk
  · apply four_coefficients_cannot_permute_divisors_six n a x hRepr hInj
    intro t ht
    apply small_coefficients_mem (hSquare t ht)
    intro p hp
    have hh := hSupport t ht p hp
    omega
  · have hDvd (t : ℕ) (ht : t ∈ Ioc n (n + k)) : a t ∣ t := ⟨x t ^ 2, hRepr t ht⟩
    have hCap := squarefree_capacity_with_bad n k 3 a hSquare hInj hDvd hSupport
    have hSmall : (smallPrimes k 3).card = 2 := by
      rcases hk with rfl | rfl <;> decide
    rw [hSmall, show (2 : ℕ) ^ 2 = 4 by decide] at hCap
    have hCount : k - 4 ≤ ((largePrimes k 3).biUnion (multiples n k)).card := by omega
    let m := n + (k - 4) / 2
    have hSub : Ioc m (m + 4) ⊆ Ioc n (n + k) := by
      intro t ht
      have hBounds := mem_Ioc.mp ht
      apply mem_Ioc.mpr
      dsimp [m] at hBounds
      rcases hk with rfl | rfl <;> omega
    apply four_coefficients_cannot_permute_divisors_six m a x
    · exact fun t ht => hRepr t (hSub ht)
    · exact hInj.mono (fun _ ht => hSub ht)
    · intro t ht
      have ht' := hSub ht
      apply small_coefficients_mem (hSquare t ht')
      intro p hp
      by_contra! hLarge
      obtain ⟨hpPrime, hpDvd, _⟩ := Nat.mem_primeFactors.mp hp
      have hpLt := hSupport t ht' p hp
      have hpIn : p ∈ largePrimes k 3 := by simp [largePrimes, hpPrime, hpLt, hLarge]
      have hHit : t ∈ multiples n k p := mem_filter.mpr ⟨ht', hpDvd.trans (hDvd t ht')⟩
      exact exceptional_middle_avoids_large n k hk hCount t ht
        (mem_biUnion.mpr ⟨p, hpIn, hHit⟩)

theorem normalized_square_impossible_below_676 {n k : ℕ} {a x : ℕ → ℕ}
    (hk : 3 ≤ k) (hUpper : k < 676)
    (hSquare : ∀ t ∈ Ioc n (n + k), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + k)))
    (hRepr : ∀ t ∈ Ioc n (n + k), t = a t * x t ^ 2)
    (hSupport : ∀ t ∈ Ioc n (n + k), ∀ p ∈ (a t).primeFactors, p < k) : False := by
  by_cases h : k = 4 ∨ k = 6 ∨ k = 8
  · exact exceptional_coefficients_impossible h hSquare hInj hRepr hSupport
  · exact squarefree_coefficients_impossible_below_676 hk hUpper
      (fun e => h (Or.inl e)) (fun e => h (Or.inr (Or.inl e)))
      (fun e => h (Or.inr (Or.inr e))) hSquare hInj
      (fun t ht => ⟨x t ^ 2, hRepr t ht⟩) hSupport

lemma square_remainders (t : ℕ) :
    ∃ a x : ℕ, a ≠ 0 ∧ t = a * x ^ 2 ∧
      ∀ p : ℕ, a.factorization p = t.factorization p % 2 := by
  by_cases ht : t = 0
  · subst t
    exact ⟨1, 0, by decide, by decide, by simp⟩
  let remainders := Finsupp.mapRange (fun e : ℕ => e % 2) (by decide) t.factorization
  let quotients := Finsupp.mapRange (fun e : ℕ => e / 2) (by decide) t.factorization
  have hRem : remainders ≤ t.factorization := by
    intro p
    exact Nat.mod_le _ _
  have hQuot : quotients ≤ t.factorization := by
    intro p
    exact Nat.div_le_self _ _
  let a := remainders.prod fun p e => p ^ e
  let x := quotients.prod fun p e => p ^ e
  have ha : a ≠ 0 := by
    have hd : a ∣ t := Nat.prod_pow_dvd_of_le_factorization hRem
    intro hz
    rw [hz] at hd
    exact ht (Nat.eq_zero_of_zero_dvd hd)
  have hx : x ≠ 0 := by
    have hd : x ∣ t := Nat.prod_pow_dvd_of_le_factorization hQuot
    intro hz
    rw [hz] at hd
    exact ht (Nat.eq_zero_of_zero_dvd hd)
  have hFactorA : a.factorization = remainders :=
    Nat.factorization_prod_pow_eq_self_of_le_factorization hRem
  have hFactorX : x.factorization = quotients :=
    Nat.factorization_prod_pow_eq_self_of_le_factorization hQuot
  refine ⟨a, x, ha, ?_, ?_⟩
  · apply Nat.eq_of_factorization_eq ht (mul_ne_zero ha (pow_ne_zero 2 hx))
    intro p
    rw [Nat.factorization_mul ha (pow_ne_zero 2 hx), Nat.factorization_pow, hFactorA, hFactorX]
    change t.factorization p = t.factorization p % 2 + 2 * (t.factorization p / 2)
    exact (Nat.mod_add_div _ _).symm
  · intro p
    rw [hFactorA]
    exact Finsupp.mapRange_apply

lemma large_prime_single {n k p t : ℕ} (hkp : k ≤ p)
    (ht : t ∈ Ioc n (n + k)) (hpt : p ∣ t) :
    (∏ m ∈ Ioc n (n + k), m).factorization p = t.factorization p := by
  have hNonzero : ∀ m ∈ Ioc n (n + k), m ≠ 0 := by
    intro m hm
    have hm' := (mem_Ioc.mp hm).1
    omega
  have htBounds := mem_Ioc.mp ht
  rw [Nat.factorization_prod hNonzero, Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · intro m hm hne
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpm
    have hmBounds := mem_Ioc.mp hm
    rcases lt_or_gt_of_ne hne with h | h
    · have hdiv := Nat.le_of_dvd (show 0 < t - m by omega) (Nat.dvd_sub hpt hpm)
      omega
    · have hdiv := Nat.le_of_dvd (show 0 < m - t by omega) (Nat.dvd_sub hpm hpt)
      omega
  · intro hMissing
    exact (hMissing ht).elim

lemma equal_square_coefficients_gap {k a x y : ℕ} (ha : a ≠ 0)
    (hSize : k ^ 2 ≤ a * x ^ 2) (hxy : x < y) : a * x ^ 2 + k ≤ a * y ^ 2 := by
  have hxA : x ≤ a * x := by
    have h := Nat.mul_le_mul_right x (show 1 ≤ a by omega)
    simpa only [Nat.one_mul] using h
  have hSquare : k ^ 2 ≤ (a * x) ^ 2 := calc
    k ^ 2 ≤ a * x ^ 2 := hSize
    _ = (a * x) * x := by ring
    _ ≤ (a * x) * (a * x) := Nat.mul_le_mul_left _ hxA
    _ = (a * x) ^ 2 := (pow_two _).symm
  have hkA := (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).1 hSquare
  have hMono : a * x ≤ a * y := Nat.mul_le_mul_left _ hxy.le
  calc
    a * x ^ 2 + k ≤ a * x ^ 2 + a * x := Nat.add_le_add_left hkA _
    _ = (a * x) * (x + 1) := by ring
    _ ≤ (a * y) * y := Nat.mul_le_mul hMono (by omega)
    _ = a * y ^ 2 := by ring

theorem normalize_square_coefficients {n k : ℕ}
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n + k), t)
    (hAll : ∀ p : ℕ, k ≤ p → p.Prime →
      2 ∣ (∏ t ∈ Ioc n (n + k), t).factorization p) :
    ∃ a x : ℕ → ℕ, (∀ t ∈ Ioc n (n+k), Squarefree (a t)) ∧
      Set.InjOn a ↑(Ioc n (n+k)) ∧
      (∀ t ∈ Ioc n (n+k), t = a t * x t ^ 2) ∧
      (∀ t ∈ Ioc n (n+k), ∀ p ∈ (a t).primeFactors, p < k) ∧
      (∀ t ∈ Ioc n (n+k), ∀ p, (a t).factorization p = t.factorization p % 2) := by
  classical
  have hSize : k ^ 2 < n := by
    obtain ⟨p, hp, hkp, hProd⟩ := hSylvester
    obtain ⟨t, ht, hpt⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hProd
    have hBounds := mem_Ioc.mp ht
    have ht0 : t ≠ 0 := by omega
    have hDiv := hAll p hkp.le hp
    rw [large_prime_single hkp.le ht hpt] at hDiv
    have he := Nat.le_of_dvd (hp.factorization_pos_of_dvd ht0 hpt) hDiv
    have hpSq := Nat.le_of_dvd (show 0 < t by omega)
      ((hp.pow_dvd_iff_le_factorization ht0).2 he)
    have hMon : (k + 1) ^ 2 ≤ p ^ 2 := pow_le_pow_left' (by omega) _
    nlinarith
  choose a x ha hRepr hFac using square_remainders
  have hSquare (t : ℕ) (_ : t ∈ Ioc n (n + k)) : Squarefree (a t) := by
    apply (Nat.squarefree_iff_factorization_le_one (ha t)).2
    intro p
    rw [hFac]
    omega
  have hSupport (t : ℕ) (ht : t ∈ Ioc n (n + k)) (p : ℕ)
      (hp : p ∈ (a t).primeFactors) : p < k := by
    by_contra! hkp
    obtain ⟨hpPrime, hpDvd, _⟩ := Nat.mem_primeFactors.mp hp
    have htDvd : a t ∣ t := ⟨x t ^ 2, hRepr t⟩
    have hDiv := hAll p hkp hpPrime
    rw [large_prime_single hkp ht (hpDvd.trans htDvd)] at hDiv
    have hZero : (a t).factorization p = 0 := by
      rw [hFac, Nat.mod_eq_zero_of_dvd hDiv]
    have := hpPrime.factorization_pos_of_dvd (ha t) hpDvd
    omega
  have hDistinct : Set.InjOn a ↑(Ioc n (n + k)) := by
    intro i hi j hj heq
    have hI := mem_Ioc.mp hi
    have hJ := mem_Ioc.mp hj
    have hApart (u v : ℕ) (hu : u ∈ Ioc n (n + k)) (hv : v ∈ Ioc n (n + k))
        (huv : u < v) (haEq : a u = a v) : False := by
      have huBounds := mem_Ioc.mp hu
      have hvBounds := mem_Ioc.mp hv
      have hRoot : x u < x v := by
        by_contra! h
        have hMon : x v ^ 2 ≤ x u ^ 2 := pow_le_pow_left' h _
        apply (not_le_of_gt huv)
        calc
          v = a v * x v ^ 2 := hRepr v
          _ = a u * x v ^ 2 := by rw [haEq]
          _ ≤ a u * x u ^ 2 := Nat.mul_le_mul_left _ hMon
          _ = u := (hRepr u).symm
      have hU : k ^ 2 ≤ a u * x u ^ 2 := by rw [← hRepr u]; omega
      have hGap := equal_square_coefficients_gap (ha u) hU hRoot
      rw [← hRepr u, haEq, ← hRepr v] at hGap
      omega
    rcases lt_trichotomy i j with h | h | h
    · exact (hApart i j hi hj h heq).elim
    · exact h
    · exact (hApart j i hj hi h heq.symm).elim
  exact ⟨a, x, hSquare, hDistinct, fun t _ => hRepr t, hSupport, fun t _ => hFac t⟩

def oddBoundAux (p : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k =>
    if k ≤ 1 then k else
      let a := (k + p - 1) / p
      let b := a / p
      a - b + oddBoundAux p fuel b

def oddBound (k p : ℕ) : ℕ := oddBoundAux p k k

def factorialValuationAux (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, k =>
    if k = 0 then 0 else
      let q := k / p
      q + factorialValuationAux p fuel q

def factorialValuation (k p : ℕ) : ℕ := factorialValuationAux p k k

lemma ceiling_le_length (k : ℕ) {p : ℕ} (hp : p.Prime) : (k + p - 1) / p ≤ k := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hp.pos).2
  rw [Nat.succ_mul]
  have h := Nat.mul_le_mul_left k hp.one_lt.le
  rw [Nat.mul_one] at h
  have hPos := hp.pos
  omega

lemma odd_bound_aux_le_length {p : ℕ} (hp : p.Prime) (fuel k : ℕ) :
    oddBoundAux p fuel k ≤ k := by
  induction fuel generalizing k with
  | zero => exact le_rfl
  | succ fuel ih =>
    by_cases hSmall : k ≤ 1
    · rw [oddBoundAux, if_pos hSmall]
    · rw [oddBoundAux, if_neg hSmall]
      let a := (k + p - 1) / p
      let b := a / p
      change a - b + oddBoundAux p fuel b ≤ k
      have hb : b ≤ a := Nat.div_le_self _ _
      have hi := ih b
      have ha : a ≤ k := ceiling_le_length k hp
      omega

lemma div_le_factorial_valuation (k p : ℕ) : k / p ≤ factorialValuation k p := by
  cases k with
  | zero => simp [factorialValuation, factorialValuationAux]
  | succ k =>
    rw [factorialValuation, factorialValuationAux, if_neg (Nat.succ_ne_zero k)]
    exact Nat.le_add_right (k.succ / p) (factorialValuationAux p k (k.succ / p))

lemma ceiling_eq_div_add_one {k p : ℕ} (hk : 0 < k) (hp : 0 < p) :
    (k+p-1)/p = (k-1)/p + 1 := by
  rw [show k+p-1 = (k-1)+p by omega, Nat.add_div_right _ hp]

lemma odd_bound_le_factorial_valuation {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime) :
    oddBound k p ≤ 1 + factorialValuation (k-1) p := by
  have hCeil : oddBound k p ≤ (k + p - 1) / p := by
    cases k with
    | zero => omega
    | succ k =>
      rw [oddBound, oddBoundAux, if_neg (by omega)]
      let a := (k.succ + p - 1) / p
      let b := a / p
      change a - b + oddBoundAux p k b ≤ a
      have hb : b ≤ a := Nat.div_le_self _ _
      have hi := odd_bound_aux_le_length hp k b
      omega
  rw [ceiling_eq_div_add_one (by omega) hp.pos] at hCeil
  have hVal := div_le_factorial_valuation (k-1) p
  omega

def savingPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19}

def baseDivisor (k : ℕ) : ℕ :=
  ∏ p ∈ savingPrimes, p ^ (1 + factorialValuation (k - 1) p - oddBound k p)

def blockDivisor : ℕ :=
  ∏ p ∈ savingPrimes, p ^ (factorialValuation 650 p - oddBound 650 p)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma base_block_certificate :
    ∀ r : Fin 650, 2 ^ (674 + r.val) * (675 + r.val) * 4 ^ (676 + r.val) <
      3 ^ (674 + r.val) * baseDivisor (676 + r.val) := by
  decide

set_option maxRecDepth 100000 in
lemma gain_certificate :
    8 ^ 650 * (675 + 650) < (3 ^ 650 * blockDivisor) * 675 := by
  decide

lemma extend_gain {a c start interval length : ℕ} (hStart : start ≤ length)
    (hGain : a * (start + interval) < c * start) :
    a * (length + interval) < c * length := by
  have hAC : a ≤ c := by
    by_contra! h
    have h1 := Nat.mul_le_mul_right start h.le
    have h2 := Nat.mul_le_mul_left a (show start ≤ start + interval by omega)
    exact (not_lt_of_ge (h1.trans h2)) hGain
  have hTail := Nat.mul_le_mul_right (length - start) hAC
  have hLeft : length + interval = (start + interval) + (length - start) := by omega
  have hRight : length = start + (length - start) := by omega
  calc
    a * (length + interval) = a * (start + interval) + a * (length - start) := by
      rw [hLeft, Nat.mul_add]
    _ < c * start + c * (length - start) := Nat.add_lt_add_of_lt_of_le hGain hTail
    _ = c * length := by rw [← Nat.mul_add, ← hRight]

set_option maxRecDepth 100000 in
theorem quadratic_block_inequality (r : Fin 650) (q : ℕ) :
    let k := 676 + r.val + q * 650
    2 ^ (k - 2) * (k - 1) * 4 ^ k <
      3 ^ (k - 2) * (baseDivisor (676 + r.val) * blockDivisor ^ q) := by
  induction q with
  | zero =>
    have hBase := base_block_certificate r
    dsimp
    simp only [Nat.mul_one]
    rw [show 676 + r.val - 2 = 674 + r.val by omega,
      show 676 + r.val - 1 = 675 + r.val by omega]
    exact hBase
  | succ q ih =>
    let k := 676 + r.val + q * 650
    let left := 2 ^ (k - 2) * 4 ^ k
    let right := 3 ^ (k - 2) * (baseDivisor (676 + r.val) * blockDivisor ^ q)
    have hLeft : 0 < left :=
      Nat.mul_pos (pow_pos (by decide) _) (pow_pos (by decide) _)
    have hBlock : 0 < 3 ^ 650 * blockDivisor :=
      Nat.mul_pos (pow_pos (by decide) _) (by decide)
    have hStart : 675 ≤ k - 1 := by dsimp [k]; omega
    have hGain := extend_gain hStart gain_certificate
    have hIh : left * (k - 1) < right := by
      dsimp [left, right, k]
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using ih
    have hBoth : left * (8 ^ 650 * (k - 1 + 650)) <
        (3 ^ 650 * blockDivisor) * right := by
      calc
        left * (8 ^ 650 * (k - 1 + 650)) <
            left * ((3 ^ 650 * blockDivisor) * (k - 1)) :=
          Nat.mul_lt_mul_of_pos_left hGain hLeft
        _ = (3 ^ 650 * blockDivisor) * (left * (k - 1)) := Nat.mul_left_comm _ _ _
        _ < (3 ^ 650 * blockDivisor) * right := Nat.mul_lt_mul_of_pos_left hIh hBlock
    have hk : 676 + r.val + q.succ * 650 = k + 650 := by dsimp [k]; omega
    dsimp
    rw [hk]
    have hMinusTwo : k + 650 - 2 = k - 2 + 650 := by omega
    have hMinusOne : k + 650 - 1 = k - 1 + 650 := by omega
    have hEight : (8 : ℕ) ^ 650 = 2 ^ 650 * 4 ^ 650 := by
      exact mul_pow (2 : ℕ) 4 650
    dsimp only [left, right] at hBoth
    rw [hMinusTwo, hMinusOne, pow_add 2, pow_add 4, pow_add 3, pow_succ blockDivisor]
    simpa only [hEight, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hBoth

lemma mod36_count_le (n : ℕ) :
    3 * (n - n / 4 - n / 9 + n / 36) ≤ 2 * n + 6 := by
  have hResidues : ∀ r : Fin 36,
      3 * (r.val - r.val / 4 - r.val / 9) ≤ 2 * r.val + 6 := by decide
  have h := hResidues ⟨n % 36, Nat.mod_lt _ (by decide)⟩
  change 3 * (n % 36 - (n % 36) / 4 - (n % 36) / 9) ≤ 2 * (n % 36) + 6 at h
  have h4 : n / 4 = 9 * (n / 36) + (n % 36) / 4 := by omega
  have h9 : n / 9 = 4 * (n / 36) + (n % 36) / 9 := by omega
  omega

lemma avoiding_four_nine_card (n : ℕ) :
    3 * ((Ioc 0 n).filter fun t => ¬ 4 ∣ t ∧ ¬ 9 ∣ t).card ≤ 2 * n + 6 := by
  let S := Ioc 0 n
  let A := S.filter (4 ∣ ·)
  let B := S.filter (9 ∣ ·)
  let C := S.filter (fun t => ¬ 4 ∣ t ∧ ¬ 9 ∣ t)
  have hComp : S \ (A ∪ B) = C := by
    ext t
    simp only [S, A, B, C, mem_sdiff, mem_union, mem_filter]
    tauto
  have hSub : A ∪ B ⊆ S := by
    intro t ht
    rcases mem_union.mp ht with ht | ht <;> exact (mem_filter.mp ht).1
  have hInter : A ∩ B = S.filter (36 ∣ ·) := by
    ext t
    simp only [A, B, mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨hS, h4⟩, _, h9⟩
      exact ⟨hS, (by decide : Nat.Coprime 4 9).mul_dvd_of_dvd_of_dvd h4 h9⟩
    · rintro ⟨hS, h36⟩
      exact ⟨⟨hS, (by decide : 4 ∣ 36).trans h36⟩,
        hS, (by decide : 9 ∣ 36).trans h36⟩
  have hAB := card_union_add_card_inter A B
  have hCS := card_sdiff_add_card_eq_card hSub
  rw [hComp] at hCS
  have ha : A.card = n / 4 := Nat.Ioc_filter_dvd_card_eq_div n 4
  have hb : B.card = n / 9 := Nat.Ioc_filter_dvd_card_eq_div n 9
  have hi : (A ∩ B).card = n / 36 := by
    rw [hInter]
    exact Nat.Ioc_filter_dvd_card_eq_div n 36
  have hs : S.card = n := by simp [S]
  have hBound := mod36_count_le n
  change 3 * C.card ≤ 2 * n + 6
  omega

theorem separated_squarefree_product_lower (S : Finset ℕ)
    (hS : ∀ t ∈ S, 0 < t ∧ ¬ 4 ∣ t ∧ ¬ 9 ∣ t) :
    3 ^ (S.card - 2) * (S.card - 2).factorial ≤
      2 ^ (S.card - 2) * ∏ t ∈ S, t := by
  generalize hCard : S.card = m
  induction m using Nat.strong_induction_on generalizing S with
  | h m ih =>
    by_cases hSmall : m ≤ 2
    · have hZero : m - 2 = 0 := by omega
      have hProd : 0 < ∏ t ∈ S, t := Finset.prod_pos (fun t ht => (hS t ht).1)
      simpa only [hZero, pow_zero, Nat.factorial_zero, Nat.one_mul] using
        (Nat.succ_le_of_lt hProd)
    · have hNonempty : S.Nonempty := Finset.card_pos.mp (by omega)
      let z := S.max' hNonempty
      have hz : z ∈ S := Finset.max'_mem _ _
      let T := S.erase z
      have hT : T.card = m - 1 := by simp [T, Finset.card_erase_of_mem hz, hCard]
      have hTdata : ∀ t ∈ T, 0 < t ∧ ¬ 4 ∣ t ∧ ¬ 9 ∣ t :=
        fun t ht => hS t (Finset.mem_of_mem_erase ht)
      have hPrev := ih (m - 1) (by omega) T hTdata hT
      have hIn : S ⊆ (Ioc 0 z).filter (fun t => ¬ 4 ∣ t ∧ ¬ 9 ∣ t) := by
        intro t ht
        exact mem_filter.mpr
          ⟨mem_Ioc.mpr ⟨(hS t ht).1, Finset.le_max' _ _ ht⟩, (hS t ht).2⟩
      have hSize := Finset.card_le_card hIn
      have hWheel := avoiding_four_nine_card z
      have hZ : 3 * (m - 2) ≤ 2 * z := by omega
      have hExp : m - 2 = (m - 1 - 2) + 1 := by omega
      have hProd : (∏ t ∈ S, t) = z * ∏ t ∈ T, t :=
        (Finset.mul_prod_erase S id hz).symm
      rw [hExp, pow_succ, pow_succ, Nat.factorial_succ, hProd]
      calc
        3 ^ (m - 1 - 2) * 3 * ((m - 1 - 2 + 1) * (m - 1 - 2).factorial) =
            (3 ^ (m - 1 - 2) * (m - 1 - 2).factorial) * (3 * (m - 2)) := by
          rw [hExp]
          ac_rfl
        _ ≤ (2 ^ (m - 1 - 2) * ∏ t ∈ T, t) * (2 * z) := Nat.mul_le_mul hPrev hZ
        _ = 2 ^ (m - 1 - 2) * 2 * (z * ∏ t ∈ T, t) := by ac_rfl

def oddMultiplicities (n k p : ℕ) : Finset ℕ :=
  (Ioc n (n + k)).filter fun t => t.factorization p % 2 = 1

def evenMultiplicities (n k p : ℕ) : Finset ℕ :=
  (Ioc n (n + k)).filter fun t => t.factorization p % 2 = 0

lemma odd_even_multiplicities_card (n k p : ℕ) :
    (oddMultiplicities n k p).card + (evenMultiplicities n k p).card = k := by
  have hC := Finset.card_filter_add_card_filter_not
    (s := Ioc n (n + k)) (fun t => t.factorization p % 2 = 1)
  have hEven : ((Ioc n (n + k)).filter fun t => ¬ t.factorization p % 2 = 1) =
      evenMultiplicities n k p := by
    ext t
    simp only [evenMultiplicities, mem_filter]
    constructor
    · rintro ⟨ht, hEven⟩
      exact ⟨ht, by omega⟩
    · rintro ⟨ht, hEven⟩
      exact ⟨ht, by omega⟩
  rw [hEven] at hC
  simpa [oddMultiplicities] using hC

lemma interval_div_length_bounds (n k p : ℕ) (hp : 0 < p) :
    k / p ≤ (n + k) / p - n / p ∧
      (n + k) / p - n / p ≤ (k + p - 1) / p := by
  have hEq : (n + k) / p = (n % p + k) / p + n / p := by
    have hSplit := Nat.mod_add_div n p
    calc
      (n + k) / p = (n % p + k + p * (n / p)) / p := by
        rw [show n + k = n % p + k + p * (n / p) by omega]
      _ = (n % p + k) / p + n / p := Nat.add_mul_div_left _ _ hp
  have hMod := Nat.mod_lt n hp
  have hLo : k / p ≤ (n % p + k) / p := Nat.div_le_div_right (by omega)
  have hHi : (n % p + k) / p ≤ (k + p - 1) / p := Nat.div_le_div_right (by omega)
  rw [hEq, Nat.add_sub_cancel]
  exact ⟨hLo, hHi⟩

lemma oddMultiplicity_dvd {t p : ℕ} (h : t.factorization p % 2 = 1) : p ∣ t := by
  by_contra! hNot
  rw [Nat.factorization_eq_zero_of_not_dvd hNot] at h
  omega

lemma odd_multiplicities_scale (n k : ℕ) {p : ℕ} (hp : p.Prime) :
    (oddMultiplicities n k p).card =
      (evenMultiplicities (n / p) ((n+k)/p - n/p) p).card := by
  have hMon : n / p ≤ (n + k) / p := Nat.div_le_div_right (by omega)
  have hEnd : n / p + ((n+k)/p - n/p) = (n+k)/p := by omega
  have hFac (q : ℕ) (hq : q ≠ 0) :
      (p*q).factorization p = 1 + q.factorization p := by
    rw [Nat.factorization_mul hp.ne_zero hq, Finsupp.add_apply, hp.factorization_self]
  have hImage : (oddMultiplicities n k p).image (· / p) =
      evenMultiplicities (n / p) ((n+k)/p - n/p) p := by
    ext q
    simp only [mem_image, oddMultiplicities, evenMultiplicities, mem_filter, mem_Ioc, hEnd]
    constructor
    · rintro ⟨t, ⟨ht, hOdd⟩, rfl⟩
      have hEq := Nat.mul_div_cancel' (oddMultiplicity_dvd hOdd)
      have hLow : n/p < t/p := (Nat.div_lt_iff_lt_mul hp.pos).2 (by
        simpa only [Nat.mul_comm] using (show n < p*(t/p) by omega))
      refine ⟨⟨hLow, Nat.div_le_div_right ht.2⟩, ?_⟩
      have hQ : t / p ≠ 0 := (lt_of_le_of_lt (Nat.zero_le _) hLow).ne'
      have hh := hFac (t/p) hQ
      rw [hEq] at hh
      rw [hh] at hOdd
      omega
    · rintro ⟨⟨hLow, hHigh⟩, hEven⟩
      have hLeft : n < q*p := (Nat.div_lt_iff_lt_mul hp.pos).1 hLow
      have hRight : q*p ≤ n+k := (Nat.le_div_iff_mul_le hp.pos).1 hHigh
      refine ⟨p*q, ⟨⟨by simpa only [Nat.mul_comm] using hLeft,
        by simpa only [Nat.mul_comm] using hRight⟩, ?_⟩, Nat.mul_div_cancel_left q hp.pos⟩
      rw [hFac q (lt_of_le_of_lt (Nat.zero_le _) hLow).ne']
      omega
  rw [← hImage, Finset.card_image_of_injOn]
  intro s hs t ht heq
  have hdS := oddMultiplicity_dvd (mem_filter.mp hs).2
  have hdT := oddMultiplicity_dvd (mem_filter.mp ht).2
  have hS := Nat.mul_div_cancel' hdS
  have hT := Nat.mul_div_cancel' hdT
  change s / p = t / p at heq
  rw [heq] at hS
  exact hS.symm.trans hT

lemma even_multiplicities_card_mono (n p : ℕ) {k j : ℕ} (h : k ≤ j) :
    (evenMultiplicities n k p).card ≤ (evenMultiplicities n j p).card := by
  apply card_le_card
  intro t ht
  obtain ⟨htI, htE⟩ := mem_filter.mp ht
  have hBounds := mem_Ioc.mp htI
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hBounds.1, by omega⟩, htE⟩

lemma odd_bound_aux_valid {p : ℕ} (hp : p.Prime) (fuel : ℕ) :
    ∀ n k : ℕ, k ≤ fuel → (oddMultiplicities n k p).card ≤ oddBoundAux p fuel k := by
  induction fuel with
  | zero =>
    intro n k hk
    have hz : k = 0 := by omega
    simp [hz, oddMultiplicities, oddBoundAux]
  | succ fuel ih =>
    intro n k hk
    by_cases hSmall : k ≤ 1
    · rw [oddBoundAux, if_pos hSmall]
      have h := odd_even_multiplicities_card n k p
      omega
    · rw [oddBoundAux, if_neg hSmall]
      let a := (k + p - 1) / p
      let b := a / p
      change (oddMultiplicities n k p).card ≤ a - b + oddBoundAux p fuel b
      have ha : a ≤ k := ceiling_le_length k hp
      have hBlt : b < k := by
        by_cases hza : a = 0
        · simp [b, hza]; omega
        · exact (Nat.div_lt_self (Nat.pos_of_ne_zero hza) hp.one_lt).trans_le ha
      have hFirst : (n+k)/p - n/p ≤ a := (interval_div_length_bounds n k p hp.pos).2
      have hSecond : b ≤ (n/p+a)/p - (n/p)/p :=
        (interval_div_length_bounds (n/p) a p hp.pos).1
      have h1 := odd_multiplicities_scale n k hp
      have h2 := even_multiplicities_card_mono (n/p) p hFirst
      have h3 := odd_multiplicities_scale (n/p) a hp
      have h4 := even_multiplicities_card_mono ((n/p)/p) p hSecond
      have hBalanceA := odd_even_multiplicities_card (n/p) a p
      have hBalanceB := odd_even_multiplicities_card ((n/p)/p) b p
      have hRec := ih ((n/p)/p) b (by omega)
      have hbA : b ≤ a := Nat.div_le_self _ _
      omega

theorem odd_multiplicities_card_le (n k : ℕ) {p : ℕ} (hp : p.Prime) :
    (oddMultiplicities n k p).card ≤ oddBound k p :=
  odd_bound_aux_valid hp k n k (Nat.le_refl _)

lemma factorial_valuation_sum (p fuel k : ℕ) :
    factorialValuationAux p fuel k = ∑ j ∈ range fuel, k / p ^ (j + 1) := by
  induction fuel generalizing k with
  | zero => simp [factorialValuationAux]
  | succ fuel ih =>
    by_cases hk : k = 0
    · simp [factorialValuationAux, hk]
    · rw [factorialValuationAux, if_neg hk]
      change k / p + factorialValuationAux p fuel (k / p) = _
      rw [ih, Finset.sum_range_succ']
      simp only [Nat.zero_add, pow_one]
      rw [Nat.add_comm (k / p)]
      refine congrArg (fun value : ℕ => value + k / p) ?_
      apply Finset.sum_congr rfl
      intro j _
      change k / p / p ^ (j + 1) = k / p ^ (j + 1 + 1)
      rw [Nat.div_div_eq_div_mul, pow_succ' p (j + 1)]

lemma factorial_valuation_eq {p : ℕ} (hp : p.Prime) (k : ℕ) :
    factorialValuation k p = k.factorial.factorization p := by
  rw [factorialValuation, factorial_valuation_sum,
    Nat.factorization_factorial hp (b := k + 1) ((Nat.log_le_self p k).trans_lt (by omega)),
    Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

lemma odd_multiplicities_add (n k l p : ℕ) :
    (oddMultiplicities n (k+l) p).card =
      (oddMultiplicities n k p).card + (oddMultiplicities (n+k) l p).card := by
  have hu : oddMultiplicities n (k+l) p =
      oddMultiplicities n k p ∪ oddMultiplicities (n+k) l p := by
    ext t
    simp only [oddMultiplicities, mem_union, mem_filter, mem_Ioc]
    omega
  have hd : Disjoint (oddMultiplicities n k p) (oddMultiplicities (n+k) l p) := by
    rw [Finset.disjoint_left]
    intro t ht hu
    have h1 := mem_Ioc.mp (mem_filter.mp ht).1
    have h2 := mem_Ioc.mp (mem_filter.mp hu).1
    omega
  rw [hu, card_union_of_disjoint hd]

lemma odd_multiplicities_blocks (n r q : ℕ) {p : ℕ} (hp : p.Prime) :
    (oddMultiplicities n (r+q*650) p).card ≤ oddBound r p + q * oddBound 650 p := by
  induction q with
  | zero => simpa using odd_multiplicities_card_le n r hp
  | succ q ih =>
    rw [show r + q.succ*650 = (r+q*650)+650 by omega, odd_multiplicities_add]
    have hLast := odd_multiplicities_card_le (n+(r+q*650)) 650 hp
    rw [Nat.succ_mul]
    omega

lemma factorial_valuation_superadditive (u v p : ℕ) :
    u.factorial.factorization p + v.factorial.factorization p ≤
      (u+v).factorial.factorization p := by
  have hd := Nat.factorial_mul_factorial_dvd_factorial_add u v
  have h := (Nat.factorization_le_iff_dvd
    (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
    (Nat.factorial_ne_zero _)).2 hd p
  rw [Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] at h
  exact h

lemma factorial_valuations_blocks (r q p : ℕ) :
    r.factorial.factorization p + q * (650 : ℕ).factorial.factorization p ≤
      (r+q*650).factorial.factorization p := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show r + q.succ*650 = (r+q*650)+650 by omega, Nat.succ_mul]
    have h := factorial_valuation_superadditive (r+q*650) 650 p
    omega

lemma saving_prime_bounds {p : ℕ} (hp : p ∈ savingPrimes) : p.Prime ∧ p ≤ 19 := by
  simp [savingPrimes] at hp
  rcases hp with h | h | h | h | h | h | h | h <;> subst p <;> decide

lemma prime_power_product_factorization {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (e : ℕ → ℕ) (p : ℕ) :
    (∏ t ∈ s, t ^ e t).factorization p = if p ∈ s then e p else 0 := by
  rw [Nat.factorization_prod (fun t ht => pow_ne_zero _ (hs t ht).ne_zero),
    Finsupp.finsetSum_apply]
  have hZero (t : ℕ) (ht : t ∈ s) (hne : t ≠ p) : (t ^ e t).factorization p = 0 := by
    rw [(hs t ht).factorization_pow, Finsupp.single_apply, if_neg hne]
  by_cases hm : p ∈ s
  · rw [if_pos hm, sum_eq_single p]
    · rw [(hs p hm).factorization_pow, Finsupp.single_apply, if_pos rfl]
    · exact hZero
    · intro h
      exact (h hm).elim
  · rw [if_neg hm]
    apply sum_eq_zero
    intro t ht
    exact hZero t ht (fun h => hm (h ▸ ht))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma block_savings_nat :
    ∀ p : Fin 20, p.val ∈ savingPrimes → oddBound 650 p.val ≤ factorialValuation 650 p.val := by
  decide

lemma normalized_product_factorization (n k : ℕ) (a : ℕ → ℕ)
    (hPos : ∀ t ∈ Ioc n (n+k), a t ≠ 0)
    (hParity : ∀ t ∈ Ioc n (n+k), ∀ p, (a t).factorization p = t.factorization p % 2)
    (p : ℕ) : (∏ t ∈ Ioc n (n+k), a t).factorization p = (oddMultiplicities n k p).card := by
  rw [Nat.factorization_prod hPos, Finsupp.finsetSum_apply]
  rw [oddMultiplicities, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  rw [hParity t ht]
  split <;> omega

lemma odd_multiplicities_le_ceiling (n k : ℕ) {p : ℕ} (hp : p.Prime) :
    (oddMultiplicities n k p).card ≤ (k + p - 1) / p := by
  refine (card_le_card ?_).trans (card_multiples_le n k p hp.pos)
  intro t ht
  obtain ⟨hI, hOdd⟩ := mem_filter.mp ht
  exact mem_filter.mpr ⟨hI, oddMultiplicity_dvd hOdd⟩

lemma primorial_valuation_one {p k : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    (primorial k).factorization p = 1 := by
  have hPos := hp.factorization_pos_of_dvd (primorial_ne_zero k)
    (hp.dvd_primorial_iff.2 hpk)
  have hUpper := (Nat.squarefree_iff_factorization_le_one (primorial_ne_zero k)).1
    (squarefree_primorial k) p
  omega

theorem normalized_large_square_impossible (n : ℕ) (r : Fin 650) (q : ℕ)
    (a : ℕ → ℕ)
    (hSquare : ∀ t ∈ Ioc n (n + (676+r.val+q*650)), Squarefree (a t))
    (hInj : Set.InjOn a ↑(Ioc n (n + (676+r.val+q*650))))
    (hSupport : ∀ t ∈ Ioc n (n + (676+r.val+q*650)), ∀ p ∈ (a t).primeFactors,
      p < 676+r.val+q*650)
    (hParity : ∀ t ∈ Ioc n (n + (676+r.val+q*650)), ∀ p,
      (a t).factorization p = t.factorization p % 2) : False := by
  let b := 676+r.val
  let k := b+q*650
  let R := Ioc n (n+k)
  let A := ∏ t ∈ R, a t
  let D := baseDivisor b * blockDivisor ^ q
  have hk : 676 ≤ k := by dsimp [k, b]; omega
  have hA0 : A ≠ 0 := (Finset.prod_pos (fun t ht => Nat.pos_of_ne_zero (hSquare t ht).ne_zero)).ne'
  have hBase0 : baseDivisor b ≠ 0 := (Finset.prod_pos fun p hp =>
    pow_pos (saving_prime_bounds hp).1.pos _).ne'
  have hBlock0 : blockDivisor ≠ 0 := (by decide)
  have hD0 : D ≠ 0 := mul_ne_zero hBase0 (pow_ne_zero _ hBlock0)
  have hPrecise (p : ℕ) : A.factorization p = (oddMultiplicities n k p).card :=
    normalized_product_factorization n k a (fun t ht => (hSquare t ht).ne_zero) hParity p
  have hDiv : A * D ∣ (k-1).factorial * primorial (k-1) := by
    apply (Nat.factorization_prime_le_iff_dvd (mul_ne_zero hA0 hD0)
      (mul_ne_zero (Nat.factorial_ne_zero _) (primorial_ne_zero _))).1
    intro p hp
    rw [Nat.factorization_mul hA0 hD0,
      Nat.factorization_mul (Nat.factorial_ne_zero _) (primorial_ne_zero _), Finsupp.add_apply,
      Finsupp.add_apply]
    have hD : D.factorization p =
        (if p ∈ savingPrimes then
           1 + factorialValuation (b-1) p - oddBound b p else 0) +
        q * (if p ∈ savingPrimes then factorialValuation 650 p - oddBound 650 p else 0) := by
      dsimp [D]
      rw [Nat.factorization_mul hBase0 (pow_ne_zero _ hBlock0), Nat.factorization_pow]
      change (baseDivisor b).factorization p + q * blockDivisor.factorization p = _
      rw [baseDivisor, blockDivisor, prime_power_product_factorization
        (fun t ht => (saving_prime_bounds ht).1), prime_power_product_factorization
        (fun t ht => (saving_prime_bounds ht).1)]
    rw [hD]
    by_cases hSel : p ∈ savingPrimes
    · have hp19 := (saving_prime_bounds hSel).2
      let j : Fin 20 := ⟨p, by omega⟩
      have hBg := block_savings_nat j hSel
      have hB0 := odd_bound_le_factorial_valuation (k := b) (by dsimp [b]; omega) hp
      change oddBound 650 p ≤ factorialValuation 650 p at hBg
      have hOdd := odd_multiplicities_blocks n b q hp
      have hFact := factorial_valuations_blocks (b-1) q p
      have hIndex : (b-1)+q*650 = k-1 := by dsimp [k, b]; omega
      rw [hIndex, ← factorial_valuation_eq hp (b-1), ← factorial_valuation_eq hp 650] at hFact
      have hBMult : q * (factorialValuation 650 p - oddBound 650 p) +
          q * oddBound 650 p = q * factorialValuation 650 p := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hBg]
      have hPrim := primorial_valuation_one hp (show p ≤ k-1 by omega)
      rw [if_pos hSel, if_pos hSel, hPrecise, hPrim]
      change (oddMultiplicities n k p).card ≤ _ at hOdd
      omega
    · rw [if_neg hSel, if_neg hSel]
      simp only [Nat.mul_zero, Nat.add_zero]
      by_cases hpK : p < k
      · rw [hPrecise, primorial_valuation_one hp (by omega)]
        have hOdd := odd_multiplicities_le_ceiling n k hp
        have hQ := ceiling_eq_div_add_one (show 0 < k by omega) hp.pos
        have hVal : (k-1)/p ≤ (k-1).factorial.factorization p := by
          rw [← factorial_valuation_eq hp]
          exact div_le_factorial_valuation (k-1) p
        omega
      · have hZero (t : ℕ) (ht : t ∈ R) : (a t).factorization p = 0 := by
          apply Nat.factorization_eq_zero_of_not_dvd
          intro hpDvd
          have hpMem := Nat.mem_primeFactors.mpr ⟨hp, hpDvd, (hSquare t ht).ne_zero⟩
          exact hpK (hSupport t ht p hpMem)
        dsimp only [A]
        rw [Nat.factorization_prod (fun t ht => (hSquare t ht).ne_zero), Finsupp.finsetSum_apply]
        rw [Finset.sum_eq_zero hZero]
        exact Nat.zero_le _
  have hUpper : A * D ≤ (k-1).factorial * 4^k := by
    have h := Nat.le_of_dvd (Nat.mul_pos (Nat.factorial_pos _) (primorial_pos _)) hDiv
    exact h.trans (Nat.mul_le_mul_left _ ((primorial_le_four_pow (k-1)).trans
      (pow_le_pow_right' (by decide : 1 ≤ (4 : ℕ)) (by omega))))
  have hCard : (R.image a).card = k := by
    rw [Finset.card_image_of_injOn hInj]
    change (Ioc n (n+k)).card = k
    simp
  have hNoDiv (t : ℕ) (ht : t ∈ R.image a) : 0 < t ∧ ¬ 4 ∣ t ∧ ¬ 9 ∣ t := by
    obtain ⟨j, hj, rfl⟩ := mem_image.mp ht
    have hs := hSquare j hj
    refine ⟨Nat.pos_of_ne_zero hs.ne_zero, ?_, ?_⟩
    · intro hd
      have hU : IsUnit (2 : ℕ) := hs 2 (by simpa using hd)
      norm_num at hU
    · intro hd
      have hU : IsUnit (3 : ℕ) := hs 3 (by simpa using hd)
      norm_num at hU
  have hLow := separated_squarefree_product_lower (R.image a) hNoDiv
  rw [hCard, Finset.prod_image hInj] at hLow
  change 3^(k-2)*(k-2).factorial ≤ 2^(k-2)*A at hLow
  have hStrict := quadratic_block_inequality r q
  change 2^(k-2)*(k-1)*4^k < 3^(k-2)*D at hStrict
  have hLowD := Nat.mul_le_mul_right D hLow
  have hUp2 := Nat.mul_le_mul_left (2^(k-2)) hUpper
  have hFactorial : (k-1).factorial = (k-1)*(k-2).factorial := by
    rw [show k-1 = k-2+1 by omega, Nat.factorial_succ]
  rw [hFactorial] at hUp2
  have hStrict2 := Nat.mul_lt_mul_of_pos_right hStrict (Nat.factorial_pos (k-2))
  nlinarith only [hLowD, hUp2, hStrict2]

theorem h3_square_of_sylvester {n k : ℕ} (hk : 3 ≤ k)
    (hSylvester : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n+k), t) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ 2 ∣ (∏ t ∈ Ioc n (n+k), t).factorization p := by
  by_contra! hAll
  obtain ⟨a, x, hSquare, hInj, hRepr, hSupport, hParity⟩ :=
    normalize_square_coefficients hSylvester hAll
  by_cases hSmall : k < 676
  · exact normalized_square_impossible_below_676 hk hSmall hSquare hInj hRepr hSupport
  · let r : Fin 650 := ⟨(k-676)%650, Nat.mod_lt _ (by decide)⟩
    let q := (k-676)/650
    have hDecompose : 676+r.val+q*650 = k := by
      have h := Nat.mod_add_div (k-676) 650
      dsimp [r, q]
      omega
    apply normalized_large_square_impossible n r q a
    · rwa [hDecompose]
    · rwa [hDecompose]
    · rwa [hDecompose]
    · rwa [hDecompose]

end Erdos137H3Square

theorem square_of_sylvester (n k : ℕ) (hk : 3 ≤ k)
    (hS : ∃ p : ℕ, p.Prime ∧ k < p ∧ p ∣ ∏ t ∈ Ioc n (n + k), t) :
    ∃ p : ℕ, k ≤ p ∧ p.Prime ∧ ¬ 2 ∣ (∏ t ∈ Ioc n (n + k), t).factorization p :=
  Erdos137H3Square.h3_square_of_sylvester hk hS

-- B. Setup: the block, big primes, n is large

theorem prod_fin_eq_prod_Ioc (n k : ℕ) :
    (∏ i : Fin k, (n + 1 + (i : ℕ))) = ∏ t ∈ Ioc n (n + k), t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_castSucc, ← Nat.add_assoc, Finset.prod_Ioc_succ_top (by omega)]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

theorem prime_dvd_unique (n k p N t : ℕ) (hkp : k ≤ p) (hN : N ∈ Ioc n (n + k))
    (ht : t ∈ Ioc n (n + k)) (hpN : p ∣ N) (hpt : p ∣ t) : t = N := by
  have h1 := Finset.mem_Ioc.mp hN
  have h2 := Finset.mem_Ioc.mp ht
  by_contra hne
  rcases Nat.lt_or_ge t N with h | h
  · have hd : p ∣ N - t := Nat.dvd_sub hpN hpt
    have h3 := Nat.le_of_dvd (by omega) hd
    omega
  · have hd : p ∣ t - N := Nat.dvd_sub hpt hpN
    have h3 := Nat.le_of_dvd (by omega) hd
    omega

theorem big_prime_val (n k l z p N : ℕ) (hz : ∏ t ∈ Ioc n (n + k), t = z ^ l)
    (hN : N ∈ Ioc n (n + k)) (hp : p.Prime) (hkp : k ≤ p) : l ∣ N.factorization p := by
  by_cases hpN : p ∣ N
  · have hfac : (∏ t ∈ Ioc n (n + k), t).factorization p = N.factorization p := by
      rw [Nat.factorization_prod (fun t ht => by have := Finset.mem_Ioc.mp ht; omega),
        Finsupp.finsetSum_apply]
      apply Finset.sum_eq_single_of_mem N hN
      intro t ht htN
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpt
      exact htN (prime_dvd_unique n k p N t hkp hN ht hpN hpt)
    rw [hz, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul] at hfac
    exact Dvd.intro _ hfac
  · rw [Nat.factorization_eq_zero_of_not_dvd hpN]
    exact dvd_zero l

theorem pow_le_of_big_prime (n k l z p : ℕ) (hz : ∏ t ∈ Ioc n (n + k), t = z ^ l)
    (hp : p.Prime) (hkp : k ≤ p) (hd : p ∣ ∏ t ∈ Ioc n (n + k), t) : p ^ l ≤ n + k := by
  obtain ⟨N, hN, hpN⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hd
  have h1 := Finset.mem_Ioc.mp hN
  have hN0 : N ≠ 0 := by omega
  have hl := big_prime_val n k l z p N hz hN hp hkp
  have hpos : 0 < N.factorization p := hp.factorization_pos_of_dvd hN0 hpN
  have hle : l ≤ N.factorization p := Nat.le_of_dvd hpos hl
  have h2 : p ^ l ∣ N := (hp.pow_dvd_iff_le_factorization hN0).mpr hle
  have h3 := Nat.le_of_dvd (by omega) h2
  omega

theorem succ_pow_ge (k l : ℕ) (hl : 2 ≤ l) : k ^ l + k ≤ (k + 1) ^ l := by
  induction l, hl using Nat.le_induction with
  | base => nlinarith
  | succ l hl ih =>
    have e1 : (k + 1) ^ (l + 1) = (k + 1) ^ l * (k + 1) := pow_succ _ _
    have e2 : k ^ (l + 1) = k ^ l * k := pow_succ _ _
    have h := Nat.mul_le_mul_right (k + 1) ih
    rw [e1, e2]
    nlinarith [Nat.zero_le (k ^ l), Nat.zero_le (k * k)]

-- C. Two numbers A * u ^ l < A * v ^ l cannot both lie in (n ^ (l - 1), (n + k) ^ (l - 1)]

theorem pow_add_le (n k m : ℕ) : (n + k) ^ m * (n - m * k) ≤ n ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rcases Nat.lt_or_ge ((m + 1) * k) n with h | h
    · obtain ⟨c, hc⟩ : ∃ c, n = (m + 1) * k + c := ⟨n - (m + 1) * k, by omega⟩
      have e1 : n - (m + 1) * k = c := by omega
      have e2 : n - m * k = k + c := by
        have e3 : (m + 1) * k = m * k + k := by ring
        omega
      rw [e1]
      rw [e2] at ih
      have h1 : (n + k) * c ≤ n * (k + c) := by
        rw [hc]
        nlinarith [Nat.zero_le (m * (k * k)), Nat.zero_le (k * k)]
      calc (n + k) ^ (m + 1) * c = (n + k) ^ m * ((n + k) * c) := by ring
        _ ≤ (n + k) ^ m * (n * (k + c)) := Nat.mul_le_mul_left _ h1
        _ = n * ((n + k) ^ m * (k + c)) := by ring
        _ ≤ n * n ^ (m + 1) := Nat.mul_le_mul_left _ ih
        _ = n ^ (m + 1 + 1) := by ring
    · rw [Nat.sub_eq_zero_of_le h]
      simp

theorem lsq_le (e : ℕ) : (e + 1) * (e + 2) ≤ 3 ^ (e + 1) := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    have e1 : 3 ^ (e + 1 + 1) = 3 ^ (e + 1) * 3 := pow_succ _ _
    rw [e1]
    nlinarith

theorem gap_upper (n k e : ℕ) (hk : 3 ≤ k) (hn : k ^ (e + 2) ≤ n) :
    (n + k) ^ (e + 1) ≤ n ^ (e + 1) + (e + 2) * k * n ^ e := by
  have h1 : (e + 1) * (e + 2) * k ≤ n := by
    have h3 : 3 ^ (e + 1) ≤ k ^ (e + 1) := Nat.pow_le_pow_left hk _
    have h4 := lsq_le e
    calc (e + 1) * (e + 2) * k ≤ k ^ (e + 1) * k := Nat.mul_le_mul_right k (le_trans h4 h3)
      _ = k ^ (e + 2) := (pow_succ k (e + 1)).symm
      _ ≤ n := hn
  have h0 : (e + 1) * k ≤ n := by nlinarith
  have h2 := pow_add_le n k (e + 1)
  obtain ⟨d, hd⟩ : ∃ d, n = (e + 1) * k + d := ⟨n - (e + 1) * k, by omega⟩
  have hd' : n - (e + 1) * k = d := by omega
  rw [hd'] at h2
  have h7 : (e + 1) * (e + 1) * k ≤ d := by
    rw [hd] at h1
    nlinarith
  have h8 : (e + 1) * (e + 1) * k * k ≤ d * k := Nat.mul_le_mul_right k h7
  have hdpos : 0 < d := by nlinarith
  have h5 : n * n ≤ (n + (e + 2) * k) * d := by
    rw [hd]
    nlinarith
  have h6 : (n + k) ^ (e + 1) * d ≤ (n ^ (e + 1) + (e + 2) * k * n ^ e) * d := by
    calc (n + k) ^ (e + 1) * d ≤ n ^ (e + 1 + 1) := h2
      _ = n ^ e * (n * n) := by ring
      _ ≤ n ^ e * ((n + (e + 2) * k) * d) := Nat.mul_le_mul_left _ h5
      _ = (n ^ (e + 1) + (e + 2) * k * n ^ e) * d := by ring
  exact Nat.le_of_mul_le_mul_right h6 hdpos

theorem coef_lower (n k e A u : ℕ) (hn : k ^ (e + 2) ≤ n)
    (h : n ^ (e + 1) < A * u ^ (e + 2)) : k * n ^ e < A * u ^ (e + 1) := by
  by_contra hc
  have hc' : A * u ^ (e + 1) ≤ k * n ^ e := Nat.le_of_not_lt hc
  have hA : 0 < A := by
    rcases Nat.eq_zero_or_pos A with rfl | hA
    · simp at h
    · exact hA
  have h1 : (A * u ^ (e + 1)) ^ (e + 2) ≤ (k * n ^ e) ^ (e + 2) := Nat.pow_le_pow_left hc' _
  have h2 : (k * n ^ e) ^ (e + 2) ≤ (n ^ (e + 1)) ^ (e + 1) := by
    calc (k * n ^ e) ^ (e + 2) = k ^ (e + 2) * (n ^ e) ^ (e + 2) := mul_pow _ _ _
      _ ≤ n * (n ^ e) ^ (e + 2) := Nat.mul_le_mul_right _ hn
      _ = (n ^ (e + 1)) ^ (e + 1) := by ring
  have h3 : (n ^ (e + 1)) ^ (e + 1) < (A * u ^ (e + 2)) ^ (e + 1) :=
    Nat.pow_lt_pow_left h (by omega)
  have h4 : (A * u ^ (e + 1)) ^ (e + 2) = A * (A * u ^ (e + 2)) ^ (e + 1) := by ring
  have h5 : (A * u ^ (e + 2)) ^ (e + 1) ≤ A * (A * u ^ (e + 2)) ^ (e + 1) :=
    Nat.le_mul_of_pos_left _ hA
  rw [h4] at h1
  omega

theorem gap_lower (e A u v : ℕ) (huv : u < v) :
    A * u ^ (e + 2) + (e + 2) * (A * u ^ (e + 1)) ≤ A * v ^ (e + 2) := by
  have key : ∀ m : ℕ, u ^ (m + 1) + (m + 1) * u ^ m ≤ (u + 1) ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have e1 : (u + 1) ^ (m + 1 + 1) = (u + 1) ^ (m + 1) * (u + 1) := pow_succ _ _
      have e2 : u ^ (m + 1 + 1) = u ^ (m + 1) * u := pow_succ _ _
      have e3 : u ^ (m + 1) = u ^ m * u := pow_succ _ _
      have h := Nat.mul_le_mul_right (u + 1) ih
      rw [e1, e2]
      rw [e3] at h ⊢
      nlinarith [Nat.zero_le (u ^ m), Nat.zero_le (m * u ^ m)]
  have h1 := key (e + 1)
  have h2 : (u + 1) ^ (e + 2) ≤ v ^ (e + 2) := Nat.pow_le_pow_left huv _
  calc A * u ^ (e + 2) + (e + 2) * (A * u ^ (e + 1))
      = A * (u ^ (e + 2) + (e + 2) * u ^ (e + 1)) := by ring
    _ ≤ A * v ^ (e + 2) := Nat.mul_le_mul_left A (le_trans h1 h2)

-- D. Equal exponents modulo l give a common factor A and two l-th powers

theorem eq_pow_of_factorization (a l : ℕ) (ha : a ≠ 0)
    (h : ∀ p, p.Prime → l ∣ a.factorization p) : ∃ u, a = u ^ l := by
  refine ⟨a.factorization.prod (fun p e => p ^ (e / l)), ?_⟩
  have h1 := Nat.prod_factorization_pow_eq_self ha
  rw [Finsupp.prod] at h1
  rw [Finsupp.prod, ← Finset.prod_pow]
  rw [← h1]
  apply Finset.prod_congr
  · rw [h1]
  · intro p hp
    rw [h1, ← pow_mul]
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
    rw [Nat.div_mul_cancel (h p hp')]

theorem val_div_gcd (X Y l p : ℕ) (hX : 0 < X) (hY : 0 < Y)
    (h : X.factorization p ≡ Y.factorization p [MOD l]) :
    l ∣ (X / Nat.gcd X Y).factorization p := by
  have hd : (X / Nat.gcd X Y).factorization p =
      X.factorization p - (Nat.gcd X Y).factorization p := by
    rw [Nat.factorization_div (Nat.gcd_dvd_left X Y)]
    rfl
  have hg : (Nat.gcd X Y).factorization p = X.factorization p ⊓ Y.factorization p := by
    rw [Nat.factorization_gcd (by omega) (by omega)]
    rfl
  rw [hd, hg]
  rcases Nat.le_total (X.factorization p) (Y.factorization p) with hle | hle
  · rw [inf_eq_left.mpr hle, Nat.sub_self]
    exact dvd_zero l
  · rw [inf_eq_right.mpr hle]
    exact (Nat.modEq_iff_dvd' hle).mp h.symm

theorem exists_scaled (X Y l : ℕ) (hX : 0 < X) (hY : 0 < Y)
    (h : ∀ p, p.Prime → X.factorization p ≡ Y.factorization p [MOD l]) :
    ∃ A u v : ℕ, X = A * u ^ l ∧ Y = A * v ^ l := by
  have hg : 0 < Nat.gcd X Y := Nat.gcd_pos_of_pos_left Y hX
  have hXd : 0 < X / Nat.gcd X Y :=
    Nat.div_pos (Nat.le_of_dvd hX (Nat.gcd_dvd_left X Y)) hg
  have hYd : 0 < Y / Nat.gcd X Y :=
    Nat.div_pos (Nat.le_of_dvd hY (Nat.gcd_dvd_right X Y)) hg
  obtain ⟨u, hu⟩ := eq_pow_of_factorization (X / Nat.gcd X Y) l (by omega)
    (fun p hp => val_div_gcd X Y l p hX hY (h p hp))
  obtain ⟨v, hv⟩ := eq_pow_of_factorization (Y / Nat.gcd X Y) l (by omega)
    (fun p hp => by
      have h1 := val_div_gcd Y X l p hY hX (h p hp).symm
      rw [Nat.gcd_comm Y X] at h1
      exact h1)
  refine ⟨Nat.gcd X Y, u, v, ?_, ?_⟩
  · rw [← hu]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left X Y)).symm
  · rw [← hv]
    exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right X Y)).symm

-- E. Multisets of block members with equal products are equal

theorem prod_sub_modEq (N0 : ℕ) (T : Multiset ℕ) (h : ∀ t ∈ T, N0 ≤ t) :
    T.prod ≡ (T.map (fun t => t - N0)).prod [MOD N0] := by
  induction T using Multiset.induction_on with
  | empty => exact Nat.ModEq.refl _
  | cons a T ih =>
    have ha := h a (Multiset.mem_cons_self a T)
    have ih' := ih (fun t ht => h t (Multiset.mem_cons_of_mem ht))
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons]
    have h1 : a - N0 ≡ a [MOD N0] :=
      (Nat.modEq_iff_dvd' (Nat.sub_le a N0)).mpr (Dvd.intro 1 (by omega))
    exact Nat.ModEq.mul h1.symm ih'

theorem prod_sub_bounds (N0 k : ℕ) (T : Multiset ℕ) (h : ∀ t ∈ T, N0 < t ∧ t < N0 + k) :
    0 < (T.map (fun t => t - N0)).prod ∧ (T.map (fun t => t - N0)).prod ≤ k ^ T.card := by
  constructor
  · apply Nat.pos_of_ne_zero
    intro h0
    obtain ⟨t, ht, h1⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h0)
    have h2 := h t ht
    omega
  · have h1 := Multiset.prod_le_pow_card (T.map (fun t => t - N0)) k (by
      intro x hx
      obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hx
      have h2 := h t ht
      omega)
    rw [Multiset.card_map] at h1
    exact h1

theorem asym (n k N0 : ℕ) (S T : Multiset ℕ) (hN0 : N0 ∈ S)
    (hT : ∀ t ∈ T, N0 < t ∧ t < N0 + k) (hk : k ^ T.card ≤ n) (hn : n < N0) :
    S.prod ≠ T.prod := by
  intro heq
  have h1 : N0 ∣ T.prod := by
    rw [← heq]
    exact Multiset.dvd_prod hN0
  have h2 := prod_sub_modEq N0 T (fun t ht => (hT t ht).1.le)
  obtain ⟨h3, h4⟩ := prod_sub_bounds N0 k T hT
  have h5 : N0 ∣ (T.map (fun t => t - N0)).prod :=
    (Nat.modEq_zero_iff_dvd).mp (h2.symm.trans ((Nat.modEq_zero_iff_dvd).mpr h1))
  have h6 := Nat.le_of_dvd h3 h5
  omega

theorem cancel (S T : Multiset ℕ) (hS : ∀ x ∈ S, 0 < x) (h : S.prod = T.prod) :
    (S - T).prod = (T - S).prod := by
  have h1 : (S - T).prod * (S ∩ T).prod = S.prod := by
    rw [← Multiset.prod_add, Multiset.sub_add_inter]
  have h2 : (T - S).prod * (S ∩ T).prod = T.prod := by
    rw [Multiset.inter_comm, ← Multiset.prod_add, Multiset.sub_add_inter]
  have h3 : 0 < (S ∩ T).prod := by
    apply Nat.pos_of_ne_zero
    intro h0
    have h4 := Multiset.prod_eq_zero_iff.mp h0
    have h5 := hS 0 (Multiset.mem_of_le (Multiset.inter_le_left) h4)
    omega
  have h6 : (S - T).prod * (S ∩ T).prod = (T - S).prod * (S ∩ T).prod := by
    rw [h1, h2, h]
  exact Nat.eq_of_mul_eq_mul_right h3 h6

theorem card_sub_eq (S T : Multiset ℕ) (h : S.card = T.card) :
    (S - T).card = (T - S).card := by
  have h1 : (S - T + S ∩ T).card = S.card := by rw [Multiset.sub_add_inter]
  have h2 : (T - S + T ∩ S).card = T.card := by rw [Multiset.sub_add_inter]
  rw [Multiset.card_add] at h1 h2
  rw [Multiset.inter_comm T S] at h2
  omega

theorem sub_disjoint (S T : Multiset ℕ) (x : ℕ) (hx : x ∈ S - T) : x ∉ T - S := by
  intro hx'
  have h1 := Multiset.count_pos.mpr hx
  have h2 := Multiset.count_pos.mpr hx'
  rw [Multiset.count_sub] at h1 h2
  omega

theorem eq_of_sub_eq_zero (S T : Multiset ℕ) (h1 : S - T = 0) (h2 : T - S = 0) : S = T := by
  exact le_antisymm (tsub_eq_zero_iff_le.mp h1) (tsub_eq_zero_iff_le.mp h2)

theorem prod_inj_disjoint (n k : ℕ) (S T : Multiset ℕ)
    (hS : ∀ x ∈ S, n < x ∧ x ≤ n + k) (hT : ∀ x ∈ T, n < x ∧ x ≤ n + k)
    (hd : ∀ x ∈ S, x ∉ T) (hc : S.card = T.card) (hk : k ^ S.card ≤ n)
    (h : S.prod = T.prod) : S = 0 := by
  by_contra hS0
  have hT0 : T ≠ 0 := by
    intro hT0
    rw [hT0, Multiset.card_zero] at hc
    exact hS0 (Multiset.card_eq_zero.mp hc)
  obtain ⟨s0, hs0⟩ := Multiset.exists_mem_of_ne_zero hS0
  obtain ⟨t0, ht0⟩ := Multiset.exists_mem_of_ne_zero hT0
  obtain ⟨a, ha, hamin⟩ := Finset.exists_min_image S.toFinset (fun x => x)
    ⟨s0, Multiset.mem_toFinset.mpr hs0⟩
  obtain ⟨b, hb, hbmin⟩ := Finset.exists_min_image T.toFinset (fun x => x)
    ⟨t0, Multiset.mem_toFinset.mpr ht0⟩
  rw [Multiset.mem_toFinset] at ha hb
  have hab : a ≠ b := by
    intro hab
    subst hab
    exact hd a ha hb
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · refine asym n k a S T ha (fun t ht => ?_) (by rw [← hc]; exact hk) (hS a ha).1 h
    have h1 : b ≤ t := hbmin t (Multiset.mem_toFinset.mpr ht)
    have h2 := hT t ht
    have h3 := hS a ha
    omega
  · refine asym n k b T S hb (fun t ht => ?_) hk (hT b hb).1 h.symm
    have h1 : a ≤ t := hamin t (Multiset.mem_toFinset.mpr ht)
    have h2 := hS t ht
    have h3 := hT b hb
    omega

theorem prod_bounds (n k : ℕ) (S : Multiset ℕ) (hS : ∀ x ∈ S, n < x ∧ x ≤ n + k)
    (hc : 1 ≤ S.card) : n ^ S.card < S.prod ∧ S.prod ≤ (n + k) ^ S.card := by
  constructor
  · have h1 : (n + 1) ^ S.card ≤ S.prod :=
      Multiset.pow_card_le_prod (fun x hx => (hS x hx).1)
    have h2 : n ^ S.card < (n + 1) ^ S.card := Nat.pow_lt_pow_left (by omega) (by omega)
    omega
  · exact Multiset.prod_le_pow_card S (n + k) (fun x hx => (hS x hx).2)

-- F. Good numbers, tags and the class of a multiset

theorem tag_spec (l y0 y1 N : ℕ) (hN : IsGood l y0 y1 N) :
    (tag l y0 y1 N = 0 ∧ ∀ q ∈ medP y0 y1, N.factorization q % l = 0) ∨
    (∃ q0 ∈ medP y0 y1, tag l y0 y1 N = q0 ∧ N.factorization q0 % l = 1 ∧
      ∀ q ∈ medP y0 y1, q ≠ q0 → N.factorization q % l = 0) := by
  obtain ⟨_, h1, h2⟩ := hN
  by_cases hall : ∀ q ∈ medP y0 y1, N.factorization q % l = 0
  · left
    refine ⟨?_, hall⟩
    unfold tag
    apply Finset.sum_eq_zero
    intro q hq
    rw [hall q hq, Nat.mul_zero]
  · right
    push Not at hall
    obtain ⟨q0, hq0, hne⟩ := hall
    have h10 : N.factorization q0 % l = 1 := by
      have h3 := h1 q0 hq0
      omega
    have hrest : ∀ q ∈ medP y0 y1, q ≠ q0 → N.factorization q % l = 0 := by
      intro q hq hqne
      by_contra hc
      exact hqne (h2 q hq q0 hq0 hc hne)
    refine ⟨q0, hq0, ?_, h10, hrest⟩
    unfold tag
    rw [Finset.sum_eq_single_of_mem q0 hq0]
    · rw [h10, Nat.mul_one]
    · intro q hq hqne
      rw [hrest q hq hqne, Nat.mul_zero]

theorem val_mod_tag (l y0 y1 N q : ℕ) (hN : IsGood l y0 y1 N) (hq : q ∈ medP y0 y1) :
    N.factorization q % l = if q = tag l y0 y1 N then 1 else 0 := by
  have hq2 : 2 ≤ q := by
    unfold medP at hq
    exact (Finset.mem_filter.mp hq).2.two_le
  rcases tag_spec l y0 y1 N hN with ⟨h0, hall⟩ | ⟨q0, hq0, ht, h1, hrest⟩
  · rw [h0, if_neg (by omega), hall q hq]
  · rw [ht]
    by_cases hqq : q = q0
    · rw [if_pos hqq, hqq, h1]
    · rw [if_neg hqq, hrest q hq hqq]

theorem tag_mem (l y0 y1 N : ℕ) (hN : IsGood l y0 y1 N) :
    tag l y0 y1 N ∈ insert 0 (medP y0 y1) := by
  rcases tag_spec l y0 y1 N hN with ⟨h0, _⟩ | ⟨q0, hq0, ht, _, _⟩
  · rw [h0]
    exact Finset.mem_insert_self 0 _
  · rw [ht]
    exact Finset.mem_insert_of_mem hq0

theorem factorization_multiset_prod (S : Multiset ℕ) (h : ∀ x ∈ S, x ≠ 0) (p : ℕ) :
    S.prod.factorization p = (S.map (fun x => x.factorization p)).sum := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have ha : a ≠ 0 := h a (Multiset.mem_cons_self a S)
    have hS : ∀ x ∈ S, x ≠ 0 := fun x hx => h x (Multiset.mem_cons_of_mem hx)
    have hp : S.prod ≠ 0 := by
      intro h0
      exact hS 0 (Multiset.prod_eq_zero_iff.mp h0) rfl
    rw [Multiset.prod_cons, Nat.factorization_mul ha hp, Multiset.map_cons, Multiset.sum_cons,
      Finsupp.add_apply, ih hS]

theorem sum_val_large (l y0 y1 p : ℕ) (S : Multiset ℕ) (hS : ∀ x ∈ S, IsGood l y0 y1 x)
    (hp : p.Prime) (hy : y1 < p) : l ∣ (S.map (fun x => x.factorization p)).sum := by
  apply Multiset.dvd_sum
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp ha
  exact (hS x hx).1 p hp hy

theorem sum_val_medium (l y0 y1 q : ℕ) (S : Multiset ℕ) (hS : ∀ x ∈ S, IsGood l y0 y1 x)
    (hq : q ∈ medP y0 y1) :
    (S.map (fun x => x.factorization q)).sum ≡ (S.map (tag l y0 y1)).count q [MOD l] := by
  induction S using Multiset.induction_on with
  | empty => exact Nat.ModEq.refl _
  | cons a S ih =>
    have ha := hS a (Multiset.mem_cons_self a S)
    have ih' := ih (fun x hx => hS x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.count_cons, Nat.add_comm]
    apply Nat.ModEq.add ih'
    unfold Nat.ModEq
    rw [← val_mod_tag l y0 y1 a q ha hq, Nat.mod_mod]

theorem class_congr (l y0 y1 : ℕ) (S T : Multiset ℕ)
    (hS : ∀ x ∈ S, x ≠ 0 ∧ IsGood l y0 y1 x) (hT : ∀ x ∈ T, x ≠ 0 ∧ IsGood l y0 y1 x)
    (hsmall : ∀ p ∈ smallP y0, (S.map (fun x => x.factorization p)).sum % l =
      (T.map (fun x => x.factorization p)).sum % l)
    (htag : S.map (tag l y0 y1) = T.map (tag l y0 y1)) :
    ∀ p, p.Prime → S.prod.factorization p ≡ T.prod.factorization p [MOD l] := by
  intro p hp
  rw [factorization_multiset_prod S (fun x hx => (hS x hx).1) p,
    factorization_multiset_prod T (fun x hx => (hT x hx).1) p]
  by_cases h0 : p ≤ y0
  · have hmem : p ∈ smallP y0 := by
      unfold smallP
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp⟩
    exact hsmall p hmem
  · by_cases h1 : p ≤ y1
    · have hq : p ∈ medP y0 y1 := by
        unfold medP
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, h1⟩, hp⟩
      have hs := sum_val_medium l y0 y1 p S (fun x hx => (hS x hx).2) hq
      have ht := sum_val_medium l y0 y1 p T (fun x hx => (hT x hx).2) hq
      rw [htag] at hs
      exact hs.trans ht.symm
    · have hs := sum_val_large l y0 y1 p S (fun x hx => (hS x hx).2) hp (by omega)
      have ht := sum_val_large l y0 y1 p T (fun x hx => (hT x hx).2) hp (by omega)
      exact ((Nat.modEq_zero_iff_dvd).mpr hs).trans ((Nat.modEq_zero_iff_dvd).mpr ht).symm

theorem multiset_pigeon {A : Type} [Fintype A] (G Tg : Finset ℕ) (c : ℕ)
    (f : Multiset ℕ → A) (g : ℕ → ℕ) (hg : ∀ x ∈ G, g x ∈ Tg)
    (h : Fintype.card A * (Tg.card + c).choose (c + 1) < (G.card + c).choose (c + 1)) :
    ∃ S T : Multiset ℕ, S ≠ T ∧ (∀ x ∈ S, x ∈ G) ∧ (∀ x ∈ T, x ∈ G) ∧
      S.card = c + 1 ∧ T.card = c + 1 ∧ f S = f T ∧ S.map g = T.map g := by
  classical
  have hcard : Fintype.card (A × Sym {t // t ∈ Tg} (c + 1)) <
      Fintype.card (Sym {x // x ∈ G} (c + 1)) := by
    rw [Fintype.card_prod, Sym.card_sym_eq_choose, Sym.card_sym_eq_choose, Fintype.card_coe,
      Fintype.card_coe]
    exact h
  obtain ⟨s, t, hne, hst⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun s : Sym {x // x ∈ G} (c + 1) =>
      (f ((s : Multiset {x // x ∈ G}).map Subtype.val),
        Sym.map (fun x : {x // x ∈ G} => (⟨g x.1, hg x.1 x.2⟩ : {t // t ∈ Tg})) s)) hcard
  have h1 := congrArg Prod.fst hst
  have h2 := congrArg Prod.snd hst
  simp only at h1 h2
  refine ⟨(s : Multiset {x // x ∈ G}).map Subtype.val,
    (t : Multiset {x // x ∈ G}).map Subtype.val, ?_, ?_, ?_, ?_, ?_, h1, ?_⟩
  · intro heq
    exact hne (Sym.coe_injective (Multiset.map_injective Subtype.val_injective heq))
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx
    exact y.2
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Multiset.mem_map.mp hx
    exact y.2
  · rw [Multiset.card_map]
    exact s.2
  · rw [Multiset.card_map]
    exact t.2
  · have h3 := congrArg
      (fun u : Sym {t // t ∈ Tg} (c + 1) => (u : Multiset {t // t ∈ Tg}).map Subtype.val) h2
    simp only [Sym.coe_map, Multiset.map_map] at h3
    rw [Multiset.map_map, Multiset.map_map]
    exact h3

-- G. Counting the bad members of a block

-- The case 0 < d is adapted from the merged sibling proof
-- proofs/Erdos137.erdos_137.variants.perfect_power.R1.H3.R1.H1.lean (open-math-agents).
theorem card_multiples_le (n k d : ℕ) (hk : 1 ≤ k) :
    ((Ioc n (n + k)).filter (fun N => d ∣ N)).card ≤ (k - 1) / d + 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : (Ioc n (n + k)).filter (fun N => 0 ∣ N) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro N hN h0
      have h1 := Finset.mem_Ioc.mp hN
      have h2 := Nat.eq_zero_of_zero_dvd h0
      omega
    rw [h0]
    simp
  · have hUnion : (Ioc 0 (n + k)).filter (fun N => d ∣ N) =
        (Ioc 0 n).filter (fun N => d ∣ N) ∪ (Ioc n (n + k)).filter (fun N => d ∣ N) := by
      ext m
      simp only [mem_union, mem_filter, mem_Ioc]
      omega
    have hDisj : Disjoint ((Ioc 0 n).filter (fun N => d ∣ N))
        ((Ioc n (n + k)).filter (fun N => d ∣ N)) := by
      rw [Finset.disjoint_left]
      intro m hl hr
      have hl' := mem_Ioc.mp (mem_filter.mp hl).1
      have hr' := mem_Ioc.mp (mem_filter.mp hr).1
      omega
    have hCard : (n + k) / d = n / d + ((Ioc n (n + k)).filter (fun N => d ∣ N)).card := by
      have h := congrArg Finset.card hUnion
      rw [Finset.card_union_of_disjoint hDisj, Nat.Ioc_filter_dvd_card_eq_div,
        Nat.Ioc_filter_dvd_card_eq_div] at h
      exact h
    have hEq : (n + k) / d = (n % d + k) / d + n / d := by
      have hv : n + k = n % d + k + d * (n / d) := by
        have hSplit := Nat.mod_add_div n d
        omega
      rw [hv]
      exact Nat.add_mul_div_left _ _ hd
    have hMod := Nat.mod_lt n hd
    have hLe : (n % d + k) / d ≤ (k - 1 + d) / d := Nat.div_le_div_right (by omega)
    have hR : (k - 1 + d) / d = (k - 1) / d + 1 := Nat.add_div_right _ hd
    omega

theorem cover_card {ι : Type} (n k : ℕ) (hk : 1 ≤ k) (dv w : ι → ℕ) (D : List ι)
    (X : Finset ℕ) (hX : X ⊆ Ioc n (n + k))
    (h : ∀ N ∈ X, ∃ i ∈ D, dv i ∣ N ∧ (k - 1) / dv i + 1 ≤ w i) :
    X.card ≤ (D.map w).sum := by
  induction D generalizing X with
  | nil =>
    have hE : X = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro N hN
      obtain ⟨i, hi, _⟩ := h N hN
      simp at hi
    rw [hE]
    simp
  | cons a D ih =>
    rw [List.map_cons, List.sum_cons]
    by_cases hw : (k - 1) / dv a + 1 ≤ w a
    · have h1 : (X.filter (fun N => dv a ∣ N)).card ≤ w a := by
        refine le_trans (Finset.card_le_card ?_) (le_trans (card_multiples_le n k (dv a) hk) hw)
        intro N hN
        rw [Finset.mem_filter] at hN ⊢
        exact ⟨hX hN.1, hN.2⟩
      have h2 : (X.filter (fun N => ¬ dv a ∣ N)).card ≤ (D.map w).sum := by
        apply ih
        · exact (Finset.filter_subset _ _).trans hX
        · intro N hN
          rw [Finset.mem_filter] at hN
          obtain ⟨i, hi, hd, hwi⟩ := h N hN.1
          rcases List.mem_cons.mp hi with rfl | hi'
          · exact absurd hd hN.2
          · exact ⟨i, hi', hd, hwi⟩
      have h3 := Finset.card_filter_add_card_filter_not (s := X) (fun N => dv a ∣ N)
      omega
    · have h2 : X.card ≤ (D.map w).sum := by
        apply ih X hX
        intro N hN
        obtain ⟨i, hi, hd, hwi⟩ := h N hN
        rcases List.mem_cons.mp hi with rfl | hi'
        · exact absurd hwi hw
        · exact ⟨i, hi', hd, hwi⟩
      omega

theorem not_good_cases (l y0 y1 N : ℕ) (h : ¬ IsGood l y0 y1 N) :
    (∃ p, p.Prime ∧ y1 < p ∧ ¬ l ∣ N.factorization p) ∨
    (∃ q ∈ medP y0 y1, 2 ≤ N.factorization q % l) ∨
    (∃ q ∈ medP y0 y1, ∃ q' ∈ medP y0 y1, q < q' ∧
      N.factorization q % l ≠ 0 ∧ N.factorization q' % l ≠ 0) := by
  by_cases c1 : ∃ p, p.Prime ∧ y1 < p ∧ ¬ l ∣ N.factorization p
  · exact Or.inl c1
  by_cases c2 : ∃ q ∈ medP y0 y1, 2 ≤ N.factorization q % l
  · exact Or.inr (Or.inl c2)
  by_cases c3 : ∃ q ∈ medP y0 y1, ∃ q' ∈ medP y0 y1, q < q' ∧
      N.factorization q % l ≠ 0 ∧ N.factorization q' % l ≠ 0
  · exact Or.inr (Or.inr c3)
  exfalso
  apply h
  unfold IsGood
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hy
    by_contra hnd
    exact c1 ⟨p, hp, hy, hnd⟩
  · intro q hq
    by_contra hgt
    exact c2 ⟨q, hq, by omega⟩
  · intro q hq q' hq' h1 h2
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact c3 ⟨q, hq, q', hq', hlt, h1, h2⟩
    · exact c3 ⟨q', hq', q, hq, hlt, h2, h1⟩

set_option maxRecDepth 100000 in
theorem sieve_cert : sieveL = PL := by
  decide +kernel

theorem hasDiv_not_prime (p : ℕ) (hp : p.Prime) : hasDiv p = false := by
  have hPD : ∀ d ∈ PD, 2 ≤ d := by decide
  unfold hasDiv
  rw [List.any_eq_false]
  intro d hd
  have h2 := hPD d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
  intro hlt hmod
  rcases (Nat.dvd_prime hp).mp (Nat.dvd_of_mod_eq_zero hmod) with h1 | h1
  · omega
  · omega

theorem prime_mem_PL (p : ℕ) (hp : p.Prime) (h : p < 30000) : p ∈ PL := by
  rw [← sieve_cert]
  unfold sieveL
  rw [List.mem_filter, List.mem_range]
  refine ⟨h, ?_⟩
  rw [hasDiv_not_prime p hp]
  simp [hp.two_le]

set_option maxRecDepth 100000 in
theorem PH_cert : PL.filter (fun p => decide (p < 256)) = PH := by
  decide +kernel

theorem prime_mem_PH (p : ℕ) (hp : p.Prime) (h : p < 256) : p ∈ PH := by
  rw [← PH_cert, List.mem_filter]
  exact ⟨prime_mem_PL p hp (by omega), decide_eq_true h⟩

theorem big_witness (l y1 n k z N p : ℕ) (hk : k ≤ 30000)
    (hz : ∏ t ∈ Ioc n (n + k), t = z ^ l) (hN : N ∈ Ioc n (n + k)) (hp : p.Prime)
    (hy : y1 < p) (hnd : ¬ l ∣ N.factorization p) :
    ∃ i ∈ PL, i ∣ N ∧ (k - 1) / i + 1 ≤ wBig k y1 i := by
  have hpk : p < k := by
    by_contra hc
    exact hnd (big_prime_val n k l z p N hz hN hp (by omega))
  have hpN : p ∣ N := by
    by_contra hc
    apply hnd
    rw [Nat.factorization_eq_zero_of_not_dvd hc]
    exact dvd_zero l
  have e : wBig k y1 p = (k - 1) / p + 1 := by
    unfold wBig
    rw [if_pos hy, if_pos hpk]
  exact ⟨p, prime_mem_PL p hp (by omega), hpN, le_of_eq e.symm⟩

theorem sq_witness (l y0 y1 k N q : ℕ) (hy1 : y1 < 256) (hq : q ∈ medP y0 y1)
    (h : 2 ≤ N.factorization q % l) :
    ∃ i ∈ PH.product PH, i.1 * i.2 ∣ N ∧ (k - 1) / (i.1 * i.2) + 1 ≤ wPair k y0 y1 i := by
  unfold medP at hq
  obtain ⟨hq1, hqp⟩ := Finset.mem_filter.mp hq
  have hq2 := Finset.mem_Ioc.mp hq1
  have hmem : q ∈ PH := prime_mem_PH q hqp (by omega)
  have hle : N.factorization q % l ≤ N.factorization q := Nat.mod_le _ _
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  have hdvd : q * q ∣ N := by
    rw [← pow_two]
    exact (hqp.pow_dvd_iff_le_factorization hN0).mpr (by omega)
  have e : wPair k y0 y1 (q, q) = (k - 1) / (q * q) + 1 := by
    simp [wPair, hq2.1, hq2.2]
  exact ⟨(q, q), List.pair_mem_product.mpr ⟨hmem, hmem⟩, hdvd, le_of_eq e.symm⟩

theorem pair_witness (l y0 y1 k N q q' : ℕ) (hy1 : y1 < 256) (hq : q ∈ medP y0 y1)
    (hq' : q' ∈ medP y0 y1) (hlt : q < q') (h1 : N.factorization q % l ≠ 0)
    (h2 : N.factorization q' % l ≠ 0) :
    ∃ i ∈ PH.product PH, i.1 * i.2 ∣ N ∧ (k - 1) / (i.1 * i.2) + 1 ≤ wPair k y0 y1 i := by
  unfold medP at hq hq'
  obtain ⟨hq1, hqp⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq1', hqp'⟩ := Finset.mem_filter.mp hq'
  have hq2 := Finset.mem_Ioc.mp hq1
  have hq2' := Finset.mem_Ioc.mp hq1'
  have hf : N.factorization q ≠ 0 := by
    intro h0
    apply h1
    rw [h0]
    exact Nat.zero_mod l
  have hf' : N.factorization q' ≠ 0 := by
    intro h0
    apply h2
    rw [h0]
    exact Nat.zero_mod l
  have hdvd : q * q' ∣ N := Nat.Coprime.mul_dvd_of_dvd_of_dvd
    ((Nat.coprime_primes hqp hqp').mpr (Nat.ne_of_lt hlt))
    (Nat.dvd_of_factorization_pos hf) (Nat.dvd_of_factorization_pos hf')
  have e : wPair k y0 y1 (q, q') = (k - 1) / (q * q') + 1 := by
    simp [wPair, hq2.1, hq2'.2, hlt.le]
  exact ⟨(q, q'), List.pair_mem_product.mpr
    ⟨prime_mem_PH q hqp (by omega), prime_mem_PH q' hqp' (by omega)⟩, hdvd, le_of_eq e.symm⟩

theorem wBig_mono (K K' y1 p : ℕ) (h : K ≤ K') : wBig K y1 p ≤ wBig K' y1 p := by
  have h4 : (K - 1) / p ≤ (K' - 1) / p := Nat.div_le_div_right (by omega)
  unfold wBig
  split_ifs <;> first | omega | exact Nat.zero_le _

theorem wPair_mono (K K' y0 y1 : ℕ) (i : ℕ × ℕ) (h : K ≤ K') :
    wPair K y0 y1 i ≤ wPair K' y0 y1 i := by
  have h4 : (K - 1) / (i.1 * i.2) ≤ (K' - 1) / (i.1 * i.2) := Nat.div_le_div_right (by omega)
  unfold wPair
  split_ifs <;> omega

theorem map_sum_le {ι : Type} (f g : ι → ℕ) (L : List ι) (h : ∀ i, f i ≤ g i) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    exact Nat.add_le_add (h a) ih

theorem card_small_le (y0 : ℕ) (h : y0 < 256) : (smallP y0).card ≤ mOf y0 := by
  unfold mOf
  have h1 := List.toFinset_card_le (PH.filter (fun p => decide (p ≤ y0)))
  refine le_trans (Finset.card_le_card ?_) h1
  intro p hp
  unfold smallP at hp
  obtain ⟨hp1, hpp⟩ := Finset.mem_filter.mp hp
  have hp2 := Finset.mem_range.mp hp1
  rw [List.mem_toFinset, List.mem_filter]
  exact ⟨prime_mem_PH p hpp (by omega), decide_eq_true (by omega)⟩

theorem card_medium_le (y0 y1 : ℕ) (h : y1 < 256) : (medP y0 y1).card ≤ rOf y0 y1 := by
  unfold rOf
  have h1 := List.toFinset_card_le
    (PH.filter (fun p => decide (y0 < p) && decide (p ≤ y1)))
  refine le_trans (Finset.card_le_card ?_) h1
  intro p hp
  unfold medP at hp
  obtain ⟨hp1, hpp⟩ := Finset.mem_filter.mp hp
  have hp2 := Finset.mem_Ioc.mp hp1
  rw [List.mem_toFinset, List.mem_filter]
  refine ⟨prime_mem_PH p hpp (by omega), ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact hp2

-- H. The binomial inequality for every exponent

theorem bern (m c : ℕ) : (m + c + 1) ^ m * (c + 1) ≤ (m + c) ^ m * (m + c + 1) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    have h1 := ih (c + 1)
    have e1 : m + (c + 1) + 1 = m + c + 2 := by omega
    have e2 : m + (c + 1) = m + c + 1 := by omega
    have e3 : m + 1 + c + 1 = m + c + 2 := by omega
    have e4 : m + 1 + c = m + c + 1 := by omega
    rw [e1, e2] at h1
    rw [e3, e4]
    have h2 : (m + c + 2) * (c + 1) ≤ (m + c + 1) * (c + 2) := by nlinarith
    calc (m + c + 2) ^ (m + 1) * (c + 1)
        = (m + c + 2) ^ m * ((m + c + 2) * (c + 1)) := by ring
      _ ≤ (m + c + 2) ^ m * ((m + c + 1) * (c + 2)) := Nat.mul_le_mul_left _ h2
      _ = (m + c + 1) * ((m + c + 2) ^ m * (c + 2)) := by ring
      _ ≤ (m + c + 1) * ((m + c + 1) ^ m * (m + c + 2)) := Nat.mul_le_mul_left _ h1
      _ = (m + c + 1) ^ (m + 1) * (m + c + 2) := by ring

theorem poly_large (F m r i : ℕ) (hB : (m + 1) * (m + r) + r + 2 ≤ 2 * F) :
    (r + m + i + 1) * (m + i + 2) ≤ (F + m + i) * (i + 2) := by
  have h1 : r + m + 1 ≤ F := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · omega
    · have h2 : m * 1 ≤ m * m := Nat.mul_le_mul_left m hm
      nlinarith [Nat.zero_le (m * r)]
  obtain ⟨t, rfl⟩ : ∃ t, F = r + m + 1 + t := ⟨F - (r + m + 1), by omega⟩
  nlinarith [Nat.zero_le (t * i)]

theorem S_small (F m r j : ℕ) (hj : 2 ≤ j) (hjm : j + 1 ≤ m)
    (hA : (r + m) * 4 ^ m ≤ F * 3 ^ m) :
    (r + j + 1) * (j + 2) ^ m ≤ (F + j) * (j + 1) ^ m := by
  have h1 : (3 * (j + 2)) ^ m ≤ (4 * (j + 1)) ^ m := Nat.pow_le_pow_left (by omega) m
  rw [mul_pow, mul_pow] at h1
  have h3 : 0 < 3 ^ m := pow_pos (by norm_num) m
  refine Nat.le_of_mul_le_mul_right ?_ h3
  calc (r + j + 1) * (j + 2) ^ m * 3 ^ m
      = (r + j + 1) * (3 ^ m * (j + 2) ^ m) := by ring
    _ ≤ (r + m) * (4 ^ m * (j + 1) ^ m) := Nat.mul_le_mul (by omega) h1
    _ = (r + m) * 4 ^ m * (j + 1) ^ m := by ring
    _ ≤ F * 3 ^ m * (j + 1) ^ m := Nat.mul_le_mul_right _ hA
    _ = F * ((j + 1) ^ m * 3 ^ m) := by ring
    _ ≤ (F + j) * ((j + 1) ^ m * 3 ^ m) := Nat.mul_le_mul_right _ (by omega)
    _ = (F + j) * (j + 1) ^ m * 3 ^ m := by ring

theorem S_large (F m r j : ℕ) (hmj : m ≤ j) (hB : (m + 1) * (m + r) + r + 2 ≤ 2 * F) :
    (r + j + 1) * (j + 2) ^ m ≤ (F + j) * (j + 1) ^ m := by
  obtain ⟨i, rfl⟩ : ∃ i, j = m + i := ⟨j - m, by omega⟩
  have h1 := bern m (i + 1)
  have h2 := poly_large F m r i hB
  have e1 : m + (i + 1) + 1 = m + i + 2 := by omega
  have e2 : m + (i + 1) = m + i + 1 := by omega
  have e3 : r + (m + i) + 1 = r + m + i + 1 := by omega
  have e4 : F + (m + i) = F + m + i := by omega
  rw [e1, e2] at h1
  rw [e3, e4]
  have hpos : 0 < (m + i + 2) * (i + 2) := Nat.mul_pos (by omega) (by omega)
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (r + m + i + 1) * (m + i + 2) ^ m * ((m + i + 2) * (i + 2))
      = (r + m + i + 1) * (m + i + 2) * ((m + i + 2) ^ m * (i + 2)) := by ring
    _ ≤ (F + m + i) * (i + 2) * ((m + i + 1) ^ m * (m + i + 2)) := Nat.mul_le_mul h2 h1
    _ = (F + m + i) * (m + i + 1) ^ m * ((m + i + 2) * (i + 2)) := by ring

theorem choose_base (F m r : ℕ) (h1 : 3 ^ m * (r + 1) * (r + 2) < F * (F + 1)) :
    3 ^ m * (r + 2).choose 2 < (F + 1).choose 2 := by
  have e1 : (F + 1).choose 2 * 2 = (F + 1) * F := by
    have h2 := Nat.add_one_mul_choose_eq F 1
    rw [Nat.choose_one_right] at h2
    exact h2.symm
  have e2 : (r + 2).choose 2 * 2 = (r + 2) * (r + 1) := by
    have h2 := Nat.add_one_mul_choose_eq (r + 1) 1
    rw [Nat.choose_one_right] at h2
    exact h2.symm
  have e3 : 3 ^ m * ((r + 2).choose 2 * 2) = 3 ^ m * ((r + 2) * (r + 1)) := by rw [e2]
  nlinarith

theorem choose_step (F m r d : ℕ)
    (hT : (d + 3) ^ m * (r + d + 2).choose (d + 2) < (F + d + 1).choose (d + 2))
    (hS : (r + d + 3) * (d + 4) ^ m ≤ (F + d + 2) * (d + 3) ^ m) :
    (d + 4) ^ m * (r + d + 3).choose (d + 3) < (F + d + 2).choose (d + 3) := by
  have e1 : (r + d + 3) * (r + d + 2).choose (d + 2) = (r + d + 3).choose (d + 3) * (d + 3) :=
    Nat.add_one_mul_choose_eq (r + d + 2) (d + 2)
  have e2 : (F + d + 2) * (F + d + 1).choose (d + 2) = (F + d + 2).choose (d + 3) * (d + 3) :=
    Nat.add_one_mul_choose_eq (F + d + 1) (d + 2)
  have e3 : (d + 4) ^ m * (r + d + 3).choose (d + 3) * (d + 3) =
      (r + d + 3) * (d + 4) ^ m * (r + d + 2).choose (d + 2) := by
    rw [mul_assoc, ← e1]
    ring
  have h1 : (d + 4) ^ m * (r + d + 3).choose (d + 3) * (d + 3) <
      (F + d + 2).choose (d + 3) * (d + 3) := by
    calc (d + 4) ^ m * (r + d + 3).choose (d + 3) * (d + 3)
        = (r + d + 3) * (d + 4) ^ m * (r + d + 2).choose (d + 2) := e3
      _ ≤ (F + d + 2) * (d + 3) ^ m * (r + d + 2).choose (d + 2) := Nat.mul_le_mul_right _ hS
      _ = (F + d + 2) * ((d + 3) ^ m * (r + d + 2).choose (d + 2)) := by ring
      _ < (F + d + 2) * (F + d + 1).choose (d + 2) :=
          Nat.mul_lt_mul_of_pos_left hT (by omega)
      _ = (F + d + 2).choose (d + 3) * (d + 3) := e2
  exact Nat.lt_of_mul_lt_mul_right h1

-- I. The table

set_option maxRecDepth 100000 in
theorem blocks_ok : blocks.all okB = true := by
  decide +kernel

theorem cov_blocks : cov 3 blocks = 30000 := by
  decide +kernel

theorem cov_spec (L : List (ℕ × ℕ × ℕ × ℕ)) (s k : ℕ) (hs : s ≤ k) (hk : k < cov s L) :
    ∃ b ∈ L, b.1 ≤ k ∧ k ≤ b.2.1 := by
  induction L generalizing s with
  | nil =>
    simp only [cov] at hk
    omega
  | cons b bs ih =>
    simp only [cov] at hk
    by_cases hb : b.1 ≤ s
    · rw [if_pos hb] at hk
      by_cases hkb : k ≤ b.2.1
      · exact ⟨b, List.mem_cons.mpr (Or.inl rfl), by omega, hkb⟩
      · obtain ⟨b', hb', h1, h2⟩ := ih (max s (b.2.1 + 1)) (by omega) hk
        exact ⟨b', List.mem_cons.mpr (Or.inr hb'), h1, h2⟩
    · rw [if_neg hb] at hk
      omega

-- Assembly (proved). Do not change anything below this line.

theorem n_large (n k l z : ℕ) (hl : 2 ≤ l) (hk : 0 < k) (hkn : k < n)
    (hz : ∏ t ∈ Ioc n (n + k), t = z ^ l) : k ^ l ≤ n := by
  obtain ⟨p, hp, hkp, hd⟩ := sylvester_block n k hk hkn
  have h1 := pow_le_of_big_prime n k l z p hz hp hkp.le hd
  have h2 := succ_pow_ge k l hl
  have h3 : (k + 1) ^ l ≤ p ^ l := Nat.pow_le_pow_left hkp l
  omega

theorem scaled_powers (n k e A u v : ℕ) (hk : 3 ≤ k) (hn : k ^ (e + 2) ≤ n)
    (hlo : n ^ (e + 1) < A * u ^ (e + 2)) (hhi : A * v ^ (e + 2) ≤ (n + k) ^ (e + 1))
    (huv : u < v) : False := by
  have h1 := gap_lower e A u v huv
  have h2 := coef_lower n k e A u hn hlo
  have h3 := gap_upper n k e hk hn
  have h4 : (e + 2) * k * n ^ e < (e + 2) * (A * u ^ (e + 1)) := by
    rw [mul_assoc]
    exact Nat.mul_lt_mul_of_pos_left h2 (by omega)
  omega

theorem prod_inj (n k c : ℕ) (S T : Multiset ℕ)
    (hS : ∀ x ∈ S, n < x ∧ x ≤ n + k) (hT : ∀ x ∈ T, n < x ∧ x ≤ n + k)
    (hcS : S.card = c) (hcT : T.card = c) (hk1 : 1 ≤ k) (hk : k ^ c ≤ n)
    (h : S.prod = T.prod) : S = T := by
  have h1 : (S - T).prod = (T - S).prod :=
    cancel S T (fun x hx => by have := (hS x hx).1; omega) h
  have h2 : (S - T).card = (T - S).card := card_sub_eq S T (by rw [hcS, hcT])
  have hle : (S - T).card ≤ c := by
    have := Multiset.card_le_card (Multiset.sub_le_self S T)
    omega
  have h3 : S - T = 0 := prod_inj_disjoint n k (S - T) (T - S)
    (fun x hx => hS x (Multiset.mem_of_le (Multiset.sub_le_self S T) hx))
    (fun x hx => hT x (Multiset.mem_of_le (Multiset.sub_le_self T S) hx))
    (sub_disjoint S T) h2 (le_trans (Nat.pow_le_pow_right hk1 hle) hk) h1
  have h4 : T - S = 0 := by
    rw [← Multiset.card_eq_zero, ← h2, h3]
    exact Multiset.card_zero
  exact eq_of_sub_eq_zero S T h3 h4

theorem multiset_rigid (n k e : ℕ) (hk : 3 ≤ k) (hn : k ^ (e + 2) ≤ n) (S T : Multiset ℕ)
    (hS : ∀ x ∈ S, x ∈ Ioc n (n + k)) (hT : ∀ x ∈ T, x ∈ Ioc n (n + k))
    (hcS : S.card = e + 1) (hcT : T.card = e + 1)
    (h : ∀ p, p.Prime → S.prod.factorization p ≡ T.prod.factorization p [MOD e + 2]) :
    S = T := by
  have hS' : ∀ x ∈ S, n < x ∧ x ≤ n + k := fun x hx => Finset.mem_Ioc.mp (hS x hx)
  have hT' : ∀ x ∈ T, n < x ∧ x ≤ n + k := fun x hx => Finset.mem_Ioc.mp (hT x hx)
  obtain ⟨hSl, hSu⟩ := prod_bounds n k S hS' (by omega)
  obtain ⟨hTl, hTu⟩ := prod_bounds n k T hT' (by omega)
  rw [hcS] at hSl hSu
  rw [hcT] at hTl hTu
  obtain ⟨A, u, v, hX, hY⟩ := exists_scaled S.prod T.prod (e + 2) (by omega) (by omega) h
  rw [hX] at hSl hSu
  rw [hY] at hTl hTu
  have huv : u = v := by
    rcases lt_trichotomy u v with h1 | h1 | h1
    · exact (scaled_powers n k e A u v hk hn hSl hTu h1).elim
    · exact h1
    · exact (scaled_powers n k e A v u hk hn hTl hSu h1).elim
  have hprod : S.prod = T.prod := by rw [hX, hY, huv]
  have hk1 : 1 ≤ k := by omega
  have hkc : k ^ (e + 1) ≤ n := le_trans (Nat.pow_le_pow_right hk1 (by omega)) hn
  exact prod_inj n k (e + 1) S T hS' hT' hcS hcT hk1 hkc hprod

theorem collision (e y0 y1 n k m r F : ℕ) (hk : 3 ≤ k) (hn : k ^ (e + 2) ≤ n)
    (hm : (smallP y0).card ≤ m) (hr : (medP y0 y1).card ≤ r)
    (hF : F ≤ (good (e + 2) y0 y1 n k).card)
    (h : (e + 2) ^ m * (r + e + 1).choose (e + 1) < (F + e).choose (e + 1)) : False := by
  have hcount : Fintype.card ({p // p ∈ smallP y0} → Fin (e + 2)) *
      ((insert 0 (medP y0 y1)).card + e).choose (e + 1) <
      ((good (e + 2) y0 y1 n k).card + e).choose (e + 1) := by
    have h1 : Fintype.card ({p // p ∈ smallP y0} → Fin (e + 2)) = (e + 2) ^ (smallP y0).card := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
    have h2 : (e + 2) ^ (smallP y0).card ≤ (e + 2) ^ m := Nat.pow_le_pow_right (by omega) hm
    have h3 : (insert 0 (medP y0 y1)).card + e ≤ r + e + 1 := by
      have := Finset.card_insert_le 0 (medP y0 y1)
      omega
    have h4 := Nat.choose_le_choose (e + 1) h3
    have h5 : F + e ≤ (good (e + 2) y0 y1 n k).card + e := by omega
    have h6 := Nat.choose_le_choose (e + 1) h5
    rw [h1]
    exact lt_of_le_of_lt (Nat.mul_le_mul h2 h4) (lt_of_lt_of_le h h6)
  obtain ⟨S, T, hne, hSG, hTG, hcS, hcT, hf, hg⟩ :=
    multiset_pigeon (good (e + 2) y0 y1 n k) (insert 0 (medP y0 y1)) e
      (fun (M : Multiset ℕ) (p : {p // p ∈ smallP y0}) =>
        (⟨(M.map (fun x => x.factorization p.1)).sum % (e + 2), Nat.mod_lt _ (by omega)⟩ :
          Fin (e + 2)))
      (tag (e + 2) y0 y1) (fun x hx => tag_mem (e + 2) y0 y1 x (mem_good.mp hx).2) hcount
  apply hne
  have hS1 : ∀ x ∈ S, x ∈ Ioc n (n + k) := fun x hx => (mem_good.mp (hSG x hx)).1
  have hT1 : ∀ x ∈ T, x ∈ Ioc n (n + k) := fun x hx => (mem_good.mp (hTG x hx)).1
  have hcong := class_congr (e + 2) y0 y1 S T
    (fun x hx => ⟨by have := Finset.mem_Ioc.mp (hS1 x hx); omega, (mem_good.mp (hSG x hx)).2⟩)
    (fun x hx => ⟨by have := Finset.mem_Ioc.mp (hT1 x hx); omega, (mem_good.mp (hTG x hx)).2⟩)
    (fun p hp => by
      have h7 := congrFun hf ⟨p, hp⟩
      exact congrArg Fin.val h7)
    hg
  exact multiset_rigid n k e hk hn S T hS1 hT1 hcS hcT hcong

theorem bad_witness (l y0 y1 n k z N : ℕ) (hk : k ≤ 30000) (hy1 : y1 < 256)
    (hz : ∏ t ∈ Ioc n (n + k), t = z ^ l) (hN : N ∈ Ioc n (n + k))
    (hbad : ¬ IsGood l y0 y1 N) :
    (∃ i ∈ PL, i ∣ N ∧ (k - 1) / i + 1 ≤ wBig k y1 i) ∨
    (∃ i ∈ PH.product PH, i.1 * i.2 ∣ N ∧ (k - 1) / (i.1 * i.2) + 1 ≤ wPair k y0 y1 i) := by
  rcases not_good_cases l y0 y1 N hbad with
    ⟨p, hp, hy, hnd⟩ | ⟨q, hq, h2⟩ | ⟨q, hq, q', hq', hlt, h1, h2⟩
  · exact Or.inl (big_witness l y1 n k z N p hk hz hN hp hy hnd)
  · exact Or.inr (sq_witness l y0 y1 k N q hy1 hq h2)
  · exact Or.inr (pair_witness l y0 y1 k N q q' hy1 hq hq' hlt h1 h2)

theorem good_card_ge (l y0 y1 n k z : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ 30000) (hy1 : y1 < 256)
    (hz : ∏ t ∈ Ioc n (n + k), t = z ^ l) :
    k ≤ (good l y0 y1 n k).card + badL k y0 y1 := by
  classical
  have h1 : ((Ioc n (n + k)).filter
      (fun N => ∃ i ∈ PL, i ∣ N ∧ (k - 1) / i + 1 ≤ wBig k y1 i)).card ≤
      (PL.map (wBig k y1)).sum :=
    cover_card n k hk1 (fun i => i) (wBig k y1) PL _ (Finset.filter_subset _ _)
      (fun N hN => (Finset.mem_filter.mp hN).2)
  have h2 : ((Ioc n (n + k)).filter (fun N => ∃ i ∈ PH.product PH,
      i.1 * i.2 ∣ N ∧ (k - 1) / (i.1 * i.2) + 1 ≤ wPair k y0 y1 i)).card ≤
      ((PH.product PH).map (wPair k y0 y1)).sum :=
    cover_card n k hk1 (fun i : ℕ × ℕ => i.1 * i.2) (wPair k y0 y1) (PH.product PH) _
      (Finset.filter_subset _ _) (fun N hN => (Finset.mem_filter.mp hN).2)
  have hsub : Ioc n (n + k) ⊆ good l y0 y1 n k ∪
      ((Ioc n (n + k)).filter (fun N => ∃ i ∈ PL, i ∣ N ∧ (k - 1) / i + 1 ≤ wBig k y1 i) ∪
       (Ioc n (n + k)).filter (fun N => ∃ i ∈ PH.product PH,
        i.1 * i.2 ∣ N ∧ (k - 1) / (i.1 * i.2) + 1 ≤ wPair k y0 y1 i)) := by
    intro N hN
    by_cases hg : IsGood l y0 y1 N
    · exact Finset.mem_union_left _ (mem_good.mpr ⟨hN, hg⟩)
    · rcases bad_witness l y0 y1 n k z N hk hy1 hz hN hg with hw | hw
      · exact Finset.mem_union_right _
          (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hN, hw⟩))
      · exact Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hN, hw⟩))
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (good l y0 y1 n k)
      ((Ioc n (n + k)).filter (fun N => ∃ i ∈ PL, i ∣ N ∧ (k - 1) / i + 1 ≤ wBig k y1 i) ∪
       (Ioc n (n + k)).filter (fun N => ∃ i ∈ PH.product PH,
        i.1 * i.2 ∣ N ∧ (k - 1) / (i.1 * i.2) + 1 ≤ wPair k y0 y1 i))
  have hu2 := Finset.card_union_le
      ((Ioc n (n + k)).filter (fun N => ∃ i ∈ PL, i ∣ N ∧ (k - 1) / i + 1 ≤ wBig k y1 i))
      ((Ioc n (n + k)).filter (fun N => ∃ i ∈ PH.product PH,
        i.1 * i.2 ∣ N ∧ (k - 1) / (i.1 * i.2) + 1 ≤ wPair k y0 y1 i))
  have hk' : (Ioc n (n + k)).card = k := by simp
  unfold badL
  omega

theorem badL_mono (K K' y0 y1 : ℕ) (h : K ≤ K') : badL K y0 y1 ≤ badL K' y0 y1 := by
  unfold badL
  exact Nat.add_le_add (map_sum_le _ _ PL (fun p => wBig_mono K K' y1 p h))
    (map_sum_le _ _ (PH.product PH) (fun i => wPair_mono K K' y0 y1 i h))

theorem S_all (F m r j : ℕ) (hj : 2 ≤ j) (hA : (r + m) * 4 ^ m ≤ F * 3 ^ m)
    (hB : (m + 1) * (m + r) + r + 2 ≤ 2 * F) :
    (r + j + 1) * (j + 2) ^ m ≤ (F + j) * (j + 1) ^ m := by
  rcases Nat.lt_or_ge j m with h | h
  · exact S_small F m r j hj h hA
  · exact S_large F m r j h hB

theorem choose_ineq_aux (F m r : ℕ) (hc : condP F m r) (d : ℕ) :
    (d + 3) ^ m * (r + d + 2).choose (d + 2) < (F + d + 1).choose (d + 2) := by
  obtain ⟨h1, hA, hB⟩ := hc
  induction d with
  | zero => exact choose_base F m r h1
  | succ d ih => exact choose_step F m r d ih (S_all F m r (d + 2) (by omega) hA hB)

theorem choose_ineq (F m r e : ℕ) (hc : condP F m r) (he : 1 ≤ e) :
    (e + 2) ^ m * (r + e + 1).choose (e + 1) < (F + e).choose (e + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  exact choose_ineq_aux F m r hc d

theorem odd_case (n k e z : ℕ) (he : 1 ≤ e) (hk : 3 ≤ k) (hk30 : k < 30000) (hkn : k < n)
    (hz : ∏ t ∈ Ioc n (n + k), t = z ^ (e + 2)) : False := by
  have hn := n_large n k (e + 2) z (by omega) (by omega) hkn hz
  obtain ⟨b, hb, hb1, hb2⟩ := cov_spec blocks 3 k hk (by rw [cov_blocks]; exact hk30)
  obtain ⟨hy0, hy1, hK2, hc⟩ := okB_spec b (List.all_eq_true.mp blocks_ok b hb)
  have hG := good_card_ge (e + 2) b.2.2.1 b.2.2.2 n k z (by omega) (by omega) hy1 hz
  have hmono := badL_mono k b.2.1 b.2.2.1 b.2.2.2 hb2
  have hF : b.1 - badL b.2.1 b.2.2.1 b.2.2.2 ≤ (good (e + 2) b.2.2.1 b.2.2.2 n k).card := by
    omega
  exact collision e b.2.2.1 b.2.2.2 n k (mOf b.2.2.1) (rOf b.2.2.1 b.2.2.2)
    (b.1 - badL b.2.1 b.2.2.1 b.2.2.2) hk hn (card_small_le b.2.2.1 hy0)
    (card_medium_le b.2.2.1 b.2.2.2 hy1) hF
    (choose_ineq _ _ _ e hc he)

end OMA.E930

theorem OMA.solution : OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1.H2 := by
  intro n k l hk hkn hl h z hz
  rw [OMA.E930.prod_fin_eq_prod_Ioc] at hz
  by_cases h2 : l = 2
  · subst h2
    obtain ⟨p, hkp, hp, hnd⟩ := OMA.E930.square_of_sylvester n k hk
      (OMA.E930.sylvester_block n k (by omega) hkn)
    apply hnd
    rw [hz, Nat.factorization_pow]
    simp
  · have hl2 := hl.two_le
    have hk30 : k < 30000 := by
      rcases h with h | h
      · exact absurd h h2
      · exact h
    obtain ⟨e, rfl⟩ : ∃ e, l = e + 2 := ⟨l - 2, by omega⟩
    exact OMA.E930.odd_case n k e z (by omega) hk hk30 hkn hz
