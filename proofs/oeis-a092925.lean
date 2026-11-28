import OMAStatements.S_oeis_a092925

/-
Disproof of the OEIS A092925 conjecture at n = 1728.
Author: CubeJerry, with Codex assistance.

For every k from 0 through 1726, the falling product
1728 * 1727 * ... * (1728-k), minus one, is composite.
The certificate list gives 1107 proper divisors and uses 0 for the
remaining 620 base-2 Fermat witnesses. A verified binary modular-power
routine and separate kernel decisions check all certificates exactly.
The source prime set is therefore empty, so its natural infimum is zero.
No minimality assertion is made about the counterexample.
-/


namespace A092925PowMod

def coreModPow : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, m => 1 % m
  | fuel + 1, a, b, m =>
    if b = 0 then 1 % m
    else
      let c := coreModPow fuel a (b / 2) m
      let d := (c * c) % m
      if b % 2 = 0 then d else (d * a) % m

def fastModPow (fuel a b m r : ℕ) : ℕ :=
  (r * coreModPow fuel a b m) % m

theorem coreModPow_eq (fuel a b m : ℕ) (hb : b < 2 ^ fuel) :
    coreModPow fuel a b m = a ^ b % m := by
  induction fuel generalizing a b with
  | zero =>
    have hb0 : b = 0 := by simpa using hb
    simp [coreModPow, hb0]
  | succ fuel ih =>
    by_cases hb0 : b = 0
    · simp [coreModPow, hb0]
    have hb2 : b / 2 < 2 ^ fuel :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa [Nat.pow_succ] using hb)
    simp only [coreModPow, if_neg hb0, ih _ _ hb2]
    split_ifs with heven
    · have heq : b / 2 + b / 2 = b := by omega
      rw [← Nat.mul_mod, ← Nat.pow_add, heq]
    · have heq : b / 2 + b / 2 + 1 = b := by omega
      rw [← Nat.mul_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
        ← Nat.pow_add, ← Nat.pow_succ, Nat.succ_eq_add_one, heq]

theorem fastModPow_eq (fuel a b m r : ℕ) (hb : b < 2 ^ fuel) :
    fastModPow fuel a b m r = (r * a ^ b) % m := by
  rw [fastModPow, coreModPow_eq fuel a b m hb, Nat.mul_mod,
    Nat.mod_mod, ← Nat.mul_mod]

theorem fastModPow_one_eq (fuel a b m : ℕ) (hb : b < 2 ^ fuel) :
    fastModPow fuel a b m 1 = a ^ b % m := by
  simpa only [Nat.one_mul] using fastModPow_eq fuel a b m 1 hb

end A092925PowMod

namespace A092925Compositeness

/-- Check a descending sequence of products using an arbitrary sound local test.
The accumulator avoids recomputing each prefix product in the certificate. -/
def checkDesc (test : ℕ → ℕ → Bool) (n acc : ℕ) : List ℕ → Bool
  | [] => true
  | d :: ds =>
    let next := acc * n
    test (next - 1) d && checkDesc test (n - 1) next ds

def CertifiedDesc (test : ℕ → ℕ → Bool) (n acc : ℕ) : List ℕ → Prop
  | [] => True
  | d :: ds =>
    test (acc * n - 1) d = true ∧ CertifiedDesc test (n - 1) (acc * n) ds

lemma certifiedDesc_check (test : ℕ → ℕ → Bool) (n acc : ℕ) (ds : List ℕ)
    (h : CertifiedDesc test n acc ds) : checkDesc test n acc ds = true := by
  induction ds generalizing n acc with
  | nil => rfl
  | cons d ds ih =>
    rcases h with ⟨hd, ht⟩
    exact Bool.and_eq_true_iff.mpr ⟨hd, ih _ _ ht⟩

end A092925Compositeness

open scoped BigOperators

namespace A092925Compositeness

lemma prime_pow_mod {n : ℕ} (hn : n.Prime) (a : ℕ) :
    a ^ n % n = a % n := by
  change Nat.ModEq n (a ^ n) a
  rw [← Int.natCast_modEq_iff, Nat.cast_pow]
  exact Int.ModEq.pow_prime_eq_self hn a

lemma not_prime_of_fermat {n a r : ℕ} (h : a ^ n % n = r)
    (hr : r ≠ a % n) : ¬ n.Prime := by
  intro hn
  exact hr (h.symm.trans (prime_pow_mod hn a))

lemma not_prime_of_factor {n d : ℕ} (hd : 1 < d) (hdn : d < n)
    (h : n % d = 0) : ¬ n.Prime := by
  intro hn
  have := hn.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero h)
  omega

lemma descFactorial_succ_left (n k : ℕ) :
    n.descFactorial (k + 1) = n * (n - 1).descFactorial k := by
  cases n with
  | zero => simp
  | succ n => simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
      Nat.succ_descFactorial_succ n k

lemma checkDesc_sound (test : ℕ → ℕ → Bool)
    (sound : ∀ n d, test n d = true → ¬ n.Prime)
    (n acc : ℕ) (ds : List ℕ) (h : checkDesc test n acc ds = true) :
    ∀ k < ds.length, ¬ (acc * n.descFactorial (k + 1) - 1).Prime := by
  induction ds generalizing n acc with
  | nil => simp
  | cons d ds ih =>
    have hh : test (acc * n - 1) d = true ∧
        checkDesc test (n - 1) (acc * n) ds = true := by
      simpa only [checkDesc, Bool.and_eq_true] using h
    intro k hk
    cases k with
    | zero => simpa only [Nat.zero_add, Nat.descFactorial_one] using sound _ _ hh.1
    | succ k =>
      have hk' : k < ds.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk
      have ht := ih (n - 1) (acc * n) hh.2 k hk'
      simpa only [Nat.succ_eq_add_one, descFactorial_succ_left, Nat.mul_assoc] using ht

lemma checkDesc_at_offset (test : ℕ → ℕ → Bool)
    (sound : ∀ n d, test n d = true → ¬ n.Prime)
    (n start count : ℕ) (ds : List ℕ)
    (h : checkDesc test (n - start) (n.descFactorial start)
      ((ds.drop start).take count) = true)
    (k : ℕ) (hstart : start ≤ k) (hcount : k < start + count) (hlen : k < ds.length) :
    ¬ (n.descFactorial (k + 1) - 1).Prime := by
  have hi : k - start < ((ds.drop start).take count).length := by
    simp only [List.length_take, List.length_drop, lt_min_iff]
    constructor <;> omega
  have ht := checkDesc_sound test sound (n - start) (n.descFactorial start)
    ((ds.drop start).take count) h (k - start) hi
  have hi' : k - start + 1 = k + 1 - start := by omega
  rw [hi'] at ht
  have hprod := Nat.descFactorial_mul_descFactorial
    (n := n) (k := start) (m := k + 1) (by omega : start ≤ k + 1)
  rw [Nat.mul_comm] at hprod
  rwa [hprod] at ht

lemma infimum_zero_of_no_prime (n : ℕ)
    (h : ∀ k < n - 1, ¬ (n.descFactorial (k + 1) - 1).Prime) :
    sInf {p : ℕ | p.Prime ∧ ∃ k ∈ Finset.range (n - 1),
      p + 1 = ∏ i ∈ Finset.range (k + 1), (n - i)} = 0 := by
  have hempty : {p : ℕ | p.Prime ∧ ∃ k ∈ Finset.range (n - 1),
      p + 1 = ∏ i ∈ Finset.range (k + 1), (n - i)} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro p ⟨hp, k, hk, heq⟩
    apply h k (Finset.mem_range.mp hk)
    rw [← Nat.descFactorial_eq_prod_range] at heq
    have heq' : n.descFactorial (k + 1) - 1 = p := by omega
    rwa [heq']
  rw [hempty, Nat.sInf_empty]

end A092925Compositeness

namespace A092925Certificate

open A092925PowMod A092925Compositeness

/- Zero requests a Fermat certificate to base two; a positive entry is a proper divisor. -/
set_option maxRecDepth 1000000 in
def certificates : List ℕ := [
  11, 5, 5, 127, 181, 17, 37, 47527, 19, 17, 17, 127, 227, 2399, 0, 373,
  6961, 566311, 880907, 461, 0, 139, 11351, 41771, 53, 2748439, 719, 0, 1970599, 137, 1471, 0,
  67, 2447, 2749, 823, 367, 97, 397, 509, 0, 4073, 70877, 449, 0, 74587, 346553, 941,
  83, 1123, 55784207, 401, 0, 0, 2089, 0, 3373, 1231, 0, 1879, 12506969, 0, 181, 0,
  83, 0, 145511, 91771247, 2133059, 170047, 7583, 233, 1061, 40127, 619, 233, 7079, 9059, 1237867, 74411,
  15259, 641, 334231, 74976533, 15601, 2753, 0, 359, 109, 1093, 197, 8831, 389, 0, 293, 12289,
  541, 271, 118691, 1619, 0, 2969699, 22171, 10499, 0, 0, 229, 3433, 0, 179, 23899, 0,
  34019, 0, 0, 691, 8623, 308899, 0, 659, 0, 28661, 937, 11239, 104233, 77477, 193, 1567903,
  1433, 0, 142699, 34667, 6793, 0, 743, 0, 39691373, 0, 6761, 0, 42877139, 9283, 3083, 2549,
  613817, 461, 17789, 4397, 693041, 647, 0, 311, 0, 0, 0, 44651, 2280709, 0, 311, 1223,
  2579, 617, 5521, 73613, 379, 0, 10429, 624847, 0, 173, 173, 28798853, 0, 2129, 0, 79535969,
  684007, 919, 619, 0, 28019, 0, 0, 0, 10789, 1103, 15991, 0, 1617989, 127817, 0, 0,
  11201111, 9769559, 1499, 3469519, 1061, 1075021, 2600407, 2347, 39313, 9203, 5433803, 19997, 0, 607, 5194457, 36709,
  359, 10453, 0, 587, 6481, 2707, 1423, 2389, 172619, 4483, 36457, 0, 260987, 9157, 7529, 0,
  121711, 18353, 67609229, 778357, 2791, 4603, 3767, 2845481, 3259, 4499171, 0, 370493, 0, 997, 1931, 0,
  87473, 12769787, 17921, 479, 1153, 0, 2063, 57436499, 0, 616117, 0, 11969, 1021, 0, 592931, 6841,
  15161, 0, 10313, 12149, 719, 1009, 19323547, 9103, 7883, 599, 40127, 1279, 0, 0, 0, 0,
  54959, 8837753, 2153, 1850939, 54409, 0, 0, 900803, 0, 1163, 0, 0, 22416839, 0, 1455011, 1069,
  175699, 1091, 333491, 0, 0, 0, 48275593, 1039, 0, 822727, 0, 12289, 3449, 9137, 2911361, 0,
  0, 0, 16447, 0, 1153, 0, 0, 0, 0, 61717, 16663099, 20627, 2087, 0, 0, 0,
  72689, 3673, 0, 0, 89236943, 0, 30091, 0, 349, 0, 673, 2503409, 0, 0, 0, 5569,
  3859073, 0, 0, 0, 100153, 11483, 19333, 1051, 0, 919, 2381, 0, 1335007, 375443, 0, 0,
  16363, 3259, 0, 1183349, 0, 17903, 0, 1931, 6829, 1979, 0, 2689, 87721, 1987, 0, 0,
  4603699, 0, 0, 0, 7380491, 413689, 0, 577, 1069, 174481, 77291, 10993, 0, 0, 142787, 1069,
  13799, 0, 0, 9743, 2851, 0, 0, 0, 13392193, 0, 0, 0, 439, 6529, 1049, 26819953,
  2531, 45119, 0, 55704391, 1082209, 5711, 404699, 43933, 47387, 281279, 8356421, 0, 0, 0, 14281, 0,
  1291, 95723, 134033, 4609699, 0, 0, 184489, 238897, 91730729, 679603, 0, 0, 0, 0, 631, 102481,
  8969, 3169, 92669, 157279, 1931, 1861, 57367, 2143, 2273, 5011, 0, 36637, 364643, 0, 0, 0,
  613, 18041, 193957, 35504533, 27337, 2957, 0, 38567, 619, 1131463, 1877, 0, 31193, 112691, 107377, 1747,
  0, 162143, 16649, 0, 1997, 0, 0, 0, 0, 6037, 0, 9547, 61561, 0, 0, 0,
  15359, 1213, 236771, 0, 1201, 0, 9437, 3739, 0, 744451, 68394169, 10729, 24859, 12007, 0, 39191,
  52963, 27109, 5179, 0, 0, 120011, 67759, 343517, 3828751, 56009, 0, 0, 0, 0, 34759, 38552093,
  0, 15139, 0, 0, 3573253, 55487, 31387, 26802427, 1181, 0, 0, 2203, 911, 0, 0, 11789213,
  53490539, 457673, 1533527, 26407, 0, 0, 0, 21378139, 3001, 2269, 537941, 5737, 9281, 1033, 1039, 0,
  1973, 0, 39929, 0, 107071, 502171, 10733, 7873, 89098199, 4507, 0, 0, 1629233, 152287, 1360103, 0,
  0, 26813, 0, 133109, 1811, 110731, 0, 36809, 0, 0, 0, 799837, 0, 12601, 8837, 17551049,
  0, 20912537, 8292461, 0, 141773, 0, 0, 13127, 9209, 1901, 0, 0, 4129, 8209, 937, 2383,
  0, 0, 0, 64137643, 3559, 475679, 0, 0, 0, 315961, 1093, 0, 14303, 0, 0, 0,
  41981, 0, 0, 224881, 61757, 23017, 15643, 97499989, 2917, 11047, 0, 38219, 2749, 2077997, 68329, 18341,
  0, 0, 879617, 677827, 10321, 2999, 47533, 0, 0, 0, 11911013, 0, 0, 108649, 0, 40459,
  8819, 0, 0, 33629, 14737, 0, 13177, 33767, 74861, 9337, 64937, 2423, 18169, 21881, 0, 0,
  9829, 0, 0, 0, 0, 13075589, 55901, 78317, 1753, 48014017, 70687, 0, 0, 3191, 12799, 307693,
  8293, 911, 67957, 0, 1089359, 7549, 25867, 31546717, 0, 13297, 7159, 977, 182579, 0, 2634193, 3733,
  941, 0, 0, 14087, 0, 0, 1889, 0, 0, 941, 41034769, 0, 0, 42349, 0, 49547,
  907073, 2351, 104059, 0, 12743, 74527, 157679, 0, 2083, 3919, 0, 94201, 0, 4549, 0, 3067,
  0, 23418179, 5233, 240943, 904759, 15427, 5507, 600463, 0, 4133, 0, 0, 5081, 0, 86509, 0,
  13604501, 47119, 11516017, 0, 0, 62603, 6653, 184153, 3407, 0, 214087, 854849, 0, 113117, 10631, 78593,
  54101, 255973, 2539, 3705137, 0, 2557, 5749, 8377, 77723, 10133, 0, 7879, 10729, 5651, 11317, 37447,
  0, 0, 8011, 2903203, 14969, 30346969, 0, 768589, 0, 20246297, 5248787, 3671, 3637, 20563, 0, 342697,
  2531, 13536071, 136531, 47598413, 75041, 0, 3299, 401809, 48384541, 33577571, 63559, 5197, 13633, 0, 2897, 68389,
  0, 56519, 0, 18451, 907, 3391, 231701, 0, 3491, 2918897, 0, 0, 0, 277747, 0, 361279,
  0, 0, 10477, 15817, 0, 6192337, 3943, 128237, 0, 0, 0, 77899, 76487, 23333, 90011, 2777,
  8369, 4673, 0, 9757457, 0, 36559, 11311, 50399161, 43577, 96953, 84855839, 118873, 4177, 15661, 3371, 800143,
  0, 0, 0, 0, 0, 0, 1783, 7697351, 375119, 0, 0, 0, 24617539, 6679, 0, 0,
  0, 1299211, 19753, 0, 15809, 1930099, 0, 2131, 6841, 6269, 5279, 3121, 78787, 76259, 2791, 6976051,
  0, 5581, 0, 9721, 89501, 15869801, 9473, 8689, 3823, 0, 0, 19559, 0, 2659, 0, 6427,
  4423, 193013, 7253, 27011, 50159, 0, 0, 0, 8547949, 0, 1706801, 9221, 0, 0, 0, 0,
  82351, 21319, 2083, 0, 0, 0, 0, 74077, 2271593, 3677, 5981, 7561, 2999, 50296139, 3848903, 0,
  0, 2439553, 2010973, 3693973, 1424701, 449437, 128591, 1933, 6661, 29173, 38861, 41670653, 0, 194083, 0, 4415909,
  0, 0, 0, 0, 113117, 2887, 7247, 0, 28549, 9137, 11273, 0, 0, 82483, 82811, 0,
  0, 0, 0, 0, 0, 5596813, 4993, 68709089, 0, 0, 0, 0, 7723003, 47843, 348991, 0,
  27197, 35227, 521777, 4421, 19471, 0, 1789, 0, 0, 2837, 0, 0, 0, 19753, 5189, 75689,
  18217, 8731, 87958063, 39821, 11322203, 2803, 12227, 4003, 10193, 160789, 25516961, 0, 0, 0, 0, 0,
  0, 172721, 29063, 4597, 4518211, 2498449, 2347, 0, 0, 1337891, 0, 7193, 0, 2677, 0, 14423,
  57173, 1012213, 0, 0, 62927, 2953, 2053, 1951, 4261, 408841, 0, 0, 40819, 0, 2207, 73328509,
  9540551, 45137, 21013, 2617, 8087, 0, 18553, 0, 0, 0, 0, 0, 2411, 40357, 53917, 5419,
  24473, 155849, 166399, 5879, 239329, 0, 0, 0, 131713, 0, 5171, 86019121, 2969, 0, 700759, 27017,
  0, 16693, 7019, 0, 0, 65101, 7001, 0, 0, 10589, 178603, 0, 0, 4788197, 1636367, 2778067,
  6151, 0, 827929, 3947, 0, 66403, 8387, 0, 1312391, 0, 0, 0, 0, 0, 0, 746177,
  0, 0, 0, 8837, 76001041, 0, 0, 6469, 6282209, 56149033, 0, 41081, 0, 0, 0, 8369,
  0, 8699, 491983, 74099, 0, 0, 8567939, 4363, 499601, 1741, 6653, 4951, 0, 0, 41621, 0,
  68639, 42953, 3797, 15797, 0, 9803, 1783, 1913, 1873, 50599, 23251, 6198281, 1879, 0, 0, 12583,
  206411, 34961, 0, 0, 72907, 1735883, 2771959, 355559, 0, 1046203, 14767, 0, 0, 0, 0, 6869,
  4597, 3067, 2003, 0, 109049, 0, 0, 0, 103471, 49169, 0, 60161, 9880463, 1753, 0, 0,
  388697, 0, 26731, 5167, 0, 0, 763883, 2039, 14533, 5279, 1601659, 0, 0, 32999, 17573, 0,
  2909, 141629, 0, 0, 0, 302399, 10239179, 0, 2137, 0, 0, 40129, 2207, 0, 0, 169909,
  12161141, 10847, 0, 14797, 35591, 8867, 36899, 2027317, 0, 23623, 5749, 191999, 22637, 7817, 8524823, 0,
  0, 1840171, 5277929, 0, 33349, 95891, 3343, 3067, 229693, 0, 0, 577897, 0, 3257, 0, 5857,
  3906061, 72643, 30763, 51696181, 19427, 0, 0, 0, 7451, 5309, 0, 0, 6829, 9781, 0, 88661,
  2551, 11689, 13883, 0, 3821, 3757601, 0, 0, 3677, 9311, 1999, 0, 22471937, 28477, 6312947, 0,
  0, 108943, 0, 26297, 81611, 21859, 19141, 11027, 2243911, 0, 9901, 383099, 0, 0, 2320547, 0,
  7649, 2791, 0, 2862469, 8951, 0, 0, 49843, 10916429, 5081, 0, 25373, 55982473, 4999, 0, 0,
  11779, 0, 6653, 5197, 24302023, 58541191, 14029, 0, 4093, 2830609, 6521, 1759, 37853, 83267, 1787, 0,
  0, 129281, 5813, 0, 106921, 0, 90059, 0, 0, 42689, 2239, 6329, 2593, 0, 0, 9551,
  35423, 2683, 27563489, 10633009, 0, 0, 7481, 0, 0, 0, 20809, 5077, 4139, 4384271, 1867, 0,
  0, 6581, 0, 0, 194609, 8256223, 0, 5023, 4817, 101987, 0, 0, 315671, 27241, 27017, 0,
  643121, 0, 0, 2617717, 199783, 24677, 0, 0, 146513, 870691, 12941, 172009, 622241, 92173, 0, 342971,
  0, 3109, 0, 1452709, 885331, 3329, 0, 100417, 0, 241603, 0, 0, 63149, 0, 0, 0,
  0, 968159, 20749, 20359, 0, 182261, 0, 0, 9601, 214363, 55482563, 0, 5743, 31319, 0, 20729407,
  17539, 0, 0, 274951, 23671, 3808709, 26729, 2753, 31601, 0, 0, 0, 0, 45433, 920951, 70729,
  0, 0, 888653, 0, 0, 11159, 0, 0, 1125739, 0, 820321, 0, 73757, 0, 1217893, 28643,
  1589281, 0, 0, 0, 0, 23753, 0, 2287, 0, 3989, 8681, 32750429, 29633531, 254753, 0, 52667,
  0, 0, 4139, 0, 3119, 34782487, 3221, 0, 0, 3677, 32609, 6569, 1761689, 0, 0, 0,
  7127, 0, 44819, 23917991, 0, 5333, 0, 0, 5021, 0, 3389, 0, 0, 23059, 0, 0,
  0, 0, 103457, 867011, 0, 0, 1949627, 0, 0, 0, 0, 13649, 3229, 4657, 29387, 0,
  4139, 0, 13145009, 0, 151813, 104773, 0, 2056589, 1415851, 3739, 0, 0, 1811, 4783, 25319347, 5279,
  1474591, 3461, 6269, 212039, 52301, 151897, 24121, 0, 0, 152833, 108863, 0, 1811, 17981, 0, 285697,
  0, 3637, 0, 0, 0, 0, 2551, 0, 0, 2903, 207169, 2203, 63689, 5197, 46488019, 4409,
  0, 7393, 0, 171629, 8089, 512419, 4379483, 0, 0, 959689, 15505393, 0, 3877, 23627, 1993219, 43781,
  0, 0, 44383, 85718851, 2861, 0, 0, 2963, 86131, 98506867, 0, 0, 7547, 90583, 0, 61007,
  0, 18253, 41723503, 4801, 0, 6577, 73303927, 0, 0, 0, 629281, 4099, 0, 6043, 26161633, 0,
  4691, 67801, 0, 2591, 12553, 4765361, 0, 42797813, 0, 0, 163883, 0, 0, 0, 2273, 0,
  0, 28781251, 67369, 30128089, 9840317, 0, 0, 0, 0, 326593, 15887, 3278063, 222799, 6529, 0, 0,
  5693, 65425891, 0, 25243, 14731039, 24439, 5791, 0, 2390623, 0, 0, 19037, 681451, 4211, 0, 0,
  2129, 4583, 47947, 5354123, 17749, 0, 0, 15451, 2549, 3877, 338857, 5417, 3673, 12329, 0, 0,
  8111, 88681, 21683, 0, 7283, 304477, 0, 0, 8476801, 3436241, 0, 1943311, 796459, 76485371, 0, 0,
  967111, 0, 0, 375511, 0, 0, 57283, 2857, 28051, 11124727, 4751, 0, 488353, 0, 142897, 0,
  1823, 2027, 0, 0, 2957, 0, 50285519, 0, 0, 547007, 18911, 0, 0, 0, 4457
]

def localCheck (fuel n d : ℕ) : Bool :=
  if d = 0 then
    decide (n < (1 <<< fuel)) && decide (fastModPow fuel 2 n n 1 ≠ 2 % n)
  else decide (1 < d ∧ d < n ∧ n % d = 0)

set_option maxRecDepth 1000000 in
lemma certificates_length : certificates.length = 1727 := by decide

def Block (j : ℕ) : Prop :=
  CertifiedDesc (localCheck 17000) (1728 - 20 * j) (Nat.descFactorial 1728 (20 * j))
    ((certificates.drop (20 * j)).take 20)

end A092925Certificate

namespace A092925Certificate

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_000 : Block 0 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_001 : Block 1 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_002 : Block 2 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_003 : Block 3 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_004 : Block 4 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_005 : Block 5 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_006 : Block 6 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_007 : Block 7 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_008 : Block 8 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_009 : Block 9 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_010 : Block 10 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_011 : Block 11 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_012 : Block 12 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_013 : Block 13 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_014 : Block 14 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_015 : Block 15 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_016 : Block 16 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_017 : Block 17 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_018 : Block 18 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_019 : Block 19 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_020 : Block 20 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_021 : Block 21 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_022 : Block 22 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_023 : Block 23 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_024 : Block 24 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_025 : Block 25 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_026 : Block 26 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_027 : Block 27 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_028 : Block 28 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_029 : Block 29 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_030 : Block 30 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_031 : Block 31 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_032 : Block 32 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_033 : Block 33 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_034 : Block 34 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_035 : Block 35 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_036 : Block 36 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_037 : Block 37 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_038 : Block 38 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_039 : Block 39 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_040 : Block 40 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_041 : Block 41 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_042 : Block 42 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_043 : Block 43 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_044 : Block 44 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_045 : Block 45 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_046 : Block 46 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_047 : Block 47 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_048 : Block 48 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_049 : Block 49 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_050 : Block 50 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_051 : Block 51 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_052 : Block 52 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_053 : Block 53 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_054 : Block 54 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_055 : Block 55 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_056 : Block 56 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_057 : Block 57 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_058 : Block 58 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_059 : Block 59 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_060 : Block 60 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_061 : Block 61 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_062 : Block 62 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_063 : Block 63 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_064 : Block 64 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_065 : Block 65 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_066 : Block 66 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_067 : Block 67 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_068 : Block 68 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_069 : Block 69 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_070 : Block 70 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_071 : Block 71 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_072 : Block 72 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_073 : Block 73 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_074 : Block 74 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_075 : Block 75 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_076 : Block 76 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_077 : Block 77 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_078 : Block 78 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_079 : Block 79 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_080 : Block 80 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_081 : Block 81 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_082 : Block 82 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_083 : Block 83 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_084 : Block 84 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_085 : Block 85 := by
  iterate 20
    constructor
    · decide +kernel
  trivial


set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma block_086 : Block 86 := by
  iterate 7
    constructor
    · decide +kernel
  trivial


end A092925Certificate

open scoped BigOperators

namespace A092925Final

open A092925PowMod A092925Compositeness A092925Certificate

lemma localCheck_sound (fuel n d : ℕ) (h : localCheck fuel n d = true) : ¬ n.Prime := by
  unfold localCheck at h
  split_ifs at h with hd
  · obtain ⟨hbound, hfermat⟩ := Bool.and_eq_true_iff.mp h
    have hb : n < 2 ^ fuel := by
      simpa only [Nat.one_shiftLeft] using (of_decide_eq_true hbound : n < (1 <<< fuel))
    have hf : fastModPow fuel 2 n n 1 ≠ 2 % n := of_decide_eq_true hfermat
    exact not_prime_of_fermat (fastModPow_one_eq fuel 2 n n hb).symm hf
  · have hf : 1 < d ∧ d < n ∧ n % d = 0 := of_decide_eq_true h
    exact not_prime_of_factor hf.1 hf.2.1 hf.2.2

lemma block_sound (j k : ℕ) (h : Block j)
    (hstart : 20 * j ≤ k) (hcount : k < 20 * j + 20) (hk : k < 1727) :
    ¬ (Nat.descFactorial 1728 (k + 1) - 1).Prime := by
  have hcheck : checkDesc (localCheck 17000) (1728 - 20 * j)
      (Nat.descFactorial 1728 (20 * j)) ((certificates.drop (20 * j)).take 20) = true :=
    certifiedDesc_check _ _ _ _ h
  have hlen : k < certificates.length := by simpa only [certificates_length] using hk
  exact checkDesc_at_offset (localCheck 17000) (localCheck_sound 17000)
    1728 (20 * j) 20 certificates hcheck k hstart hcount hlen

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma all_not_prime : ∀ k < 1727, ¬ (Nat.descFactorial 1728 (k + 1) - 1).Prime := by
  intro k hk
  have hdiv : k / 20 < 87 := by omega
  interval_cases hj : k / 20
  · exact block_sound 0 k block_000 (by omega) (by omega) hk
  · exact block_sound 1 k block_001 (by omega) (by omega) hk
  · exact block_sound 2 k block_002 (by omega) (by omega) hk
  · exact block_sound 3 k block_003 (by omega) (by omega) hk
  · exact block_sound 4 k block_004 (by omega) (by omega) hk
  · exact block_sound 5 k block_005 (by omega) (by omega) hk
  · exact block_sound 6 k block_006 (by omega) (by omega) hk
  · exact block_sound 7 k block_007 (by omega) (by omega) hk
  · exact block_sound 8 k block_008 (by omega) (by omega) hk
  · exact block_sound 9 k block_009 (by omega) (by omega) hk
  · exact block_sound 10 k block_010 (by omega) (by omega) hk
  · exact block_sound 11 k block_011 (by omega) (by omega) hk
  · exact block_sound 12 k block_012 (by omega) (by omega) hk
  · exact block_sound 13 k block_013 (by omega) (by omega) hk
  · exact block_sound 14 k block_014 (by omega) (by omega) hk
  · exact block_sound 15 k block_015 (by omega) (by omega) hk
  · exact block_sound 16 k block_016 (by omega) (by omega) hk
  · exact block_sound 17 k block_017 (by omega) (by omega) hk
  · exact block_sound 18 k block_018 (by omega) (by omega) hk
  · exact block_sound 19 k block_019 (by omega) (by omega) hk
  · exact block_sound 20 k block_020 (by omega) (by omega) hk
  · exact block_sound 21 k block_021 (by omega) (by omega) hk
  · exact block_sound 22 k block_022 (by omega) (by omega) hk
  · exact block_sound 23 k block_023 (by omega) (by omega) hk
  · exact block_sound 24 k block_024 (by omega) (by omega) hk
  · exact block_sound 25 k block_025 (by omega) (by omega) hk
  · exact block_sound 26 k block_026 (by omega) (by omega) hk
  · exact block_sound 27 k block_027 (by omega) (by omega) hk
  · exact block_sound 28 k block_028 (by omega) (by omega) hk
  · exact block_sound 29 k block_029 (by omega) (by omega) hk
  · exact block_sound 30 k block_030 (by omega) (by omega) hk
  · exact block_sound 31 k block_031 (by omega) (by omega) hk
  · exact block_sound 32 k block_032 (by omega) (by omega) hk
  · exact block_sound 33 k block_033 (by omega) (by omega) hk
  · exact block_sound 34 k block_034 (by omega) (by omega) hk
  · exact block_sound 35 k block_035 (by omega) (by omega) hk
  · exact block_sound 36 k block_036 (by omega) (by omega) hk
  · exact block_sound 37 k block_037 (by omega) (by omega) hk
  · exact block_sound 38 k block_038 (by omega) (by omega) hk
  · exact block_sound 39 k block_039 (by omega) (by omega) hk
  · exact block_sound 40 k block_040 (by omega) (by omega) hk
  · exact block_sound 41 k block_041 (by omega) (by omega) hk
  · exact block_sound 42 k block_042 (by omega) (by omega) hk
  · exact block_sound 43 k block_043 (by omega) (by omega) hk
  · exact block_sound 44 k block_044 (by omega) (by omega) hk
  · exact block_sound 45 k block_045 (by omega) (by omega) hk
  · exact block_sound 46 k block_046 (by omega) (by omega) hk
  · exact block_sound 47 k block_047 (by omega) (by omega) hk
  · exact block_sound 48 k block_048 (by omega) (by omega) hk
  · exact block_sound 49 k block_049 (by omega) (by omega) hk
  · exact block_sound 50 k block_050 (by omega) (by omega) hk
  · exact block_sound 51 k block_051 (by omega) (by omega) hk
  · exact block_sound 52 k block_052 (by omega) (by omega) hk
  · exact block_sound 53 k block_053 (by omega) (by omega) hk
  · exact block_sound 54 k block_054 (by omega) (by omega) hk
  · exact block_sound 55 k block_055 (by omega) (by omega) hk
  · exact block_sound 56 k block_056 (by omega) (by omega) hk
  · exact block_sound 57 k block_057 (by omega) (by omega) hk
  · exact block_sound 58 k block_058 (by omega) (by omega) hk
  · exact block_sound 59 k block_059 (by omega) (by omega) hk
  · exact block_sound 60 k block_060 (by omega) (by omega) hk
  · exact block_sound 61 k block_061 (by omega) (by omega) hk
  · exact block_sound 62 k block_062 (by omega) (by omega) hk
  · exact block_sound 63 k block_063 (by omega) (by omega) hk
  · exact block_sound 64 k block_064 (by omega) (by omega) hk
  · exact block_sound 65 k block_065 (by omega) (by omega) hk
  · exact block_sound 66 k block_066 (by omega) (by omega) hk
  · exact block_sound 67 k block_067 (by omega) (by omega) hk
  · exact block_sound 68 k block_068 (by omega) (by omega) hk
  · exact block_sound 69 k block_069 (by omega) (by omega) hk
  · exact block_sound 70 k block_070 (by omega) (by omega) hk
  · exact block_sound 71 k block_071 (by omega) (by omega) hk
  · exact block_sound 72 k block_072 (by omega) (by omega) hk
  · exact block_sound 73 k block_073 (by omega) (by omega) hk
  · exact block_sound 74 k block_074 (by omega) (by omega) hk
  · exact block_sound 75 k block_075 (by omega) (by omega) hk
  · exact block_sound 76 k block_076 (by omega) (by omega) hk
  · exact block_sound 77 k block_077 (by omega) (by omega) hk
  · exact block_sound 78 k block_078 (by omega) (by omega) hk
  · exact block_sound 79 k block_079 (by omega) (by omega) hk
  · exact block_sound 80 k block_080 (by omega) (by omega) hk
  · exact block_sound 81 k block_081 (by omega) (by omega) hk
  · exact block_sound 82 k block_082 (by omega) (by omega) hk
  · exact block_sound 83 k block_083 (by omega) (by omega) hk
  · exact block_sound 84 k block_084 (by omega) (by omega) hk
  · exact block_sound 85 k block_085 (by omega) (by omega) hk
  · exact block_sound 86 k block_086 (by omega) (by omega) hk

lemma zero_value :
    sInf {p : ℕ | p.Prime ∧ ∃ k ∈ Finset.range (1728 - 1),
      p + 1 = ∏ i ∈ Finset.range (k + 1), (1728 - i)} = 0 :=
  infimum_zero_of_no_prime 1728 all_not_prime

theorem disproof : ¬ (∀ n : ℕ, 3 ≤ n →
    0 < sInf {p : ℕ | p.Prime ∧ ∃ k ∈ Finset.range (n - 1),
      p + 1 = ∏ i ∈ Finset.range (k + 1), (n - i)}) := by
  intro h
  have hn := h 1728 (by decide)
  rw [zero_value] at hn
  omega

end A092925Final

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a092925.main) := by
  exact A092925Final.disproof
