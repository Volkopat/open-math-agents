import FormalConjectures.OEIS.«232616»

/-! The powers repeat after 29,400 steps. In each residue class of exponents,
a single linear congruence gives the first possible index for the target residue. -/

namespace PrimeBound

private def wheel (x : ℕ) : ℕ :=
  (x - x / 2) - (x / 3 - x / 3 / 2) -
    ((x / 5 - x / 5 / 2) - (x / 5 / 3 - x / 5 / 3 / 2))

private def count : List ℕ → ℕ → ℕ
  | [], x => wheel x
  | p :: ps, x => if x ≤ p then (if x = 0 then 0 else 1) else count ps x - count ps (x / p)

private def primes : List ℕ := [2927, 2917, 2909, 2903, 2897, 2887, 2879, 2861, 2857, 2851, 2843, 2837, 2833, 2819, 2803, 2801, 2797, 2791, 2789, 2777, 2767, 2753, 2749, 2741, 2731, 2729, 2719, 2713, 2711, 2707, 2699, 2693, 2689, 2687, 2683, 2677, 2671, 2663, 2659, 2657, 2647, 2633, 2621, 2617, 2609, 2593, 2591, 2579, 2557, 2551, 2549, 2543, 2539, 2531, 2521, 2503, 2477, 2473, 2467, 2459, 2447, 2441, 2437, 2423, 2417, 2411, 2399, 2393, 2389, 2383, 2381, 2377, 2371, 2357, 2351, 2347, 2341, 2339, 2333, 2311, 2309, 2297, 2293, 2287, 2281, 2273, 2269, 2267, 2251, 2243, 2239, 2237, 2221, 2213, 2207, 2203, 2179, 2161, 2153, 2143, 2141, 2137, 2131, 2129, 2113, 2111, 2099, 2089, 2087, 2083, 2081, 2069, 2063, 2053, 2039, 2029, 2027, 2017, 2011, 2003, 1999, 1997, 1993, 1987, 1979, 1973, 1951, 1949, 1933, 1931, 1913, 1907, 1901, 1889, 1879, 1877, 1873, 1871, 1867, 1861, 1847, 1831, 1823, 1811, 1801, 1789, 1787, 1783, 1777, 1759, 1753, 1747, 1741, 1733, 1723, 1721, 1709, 1699, 1697, 1693, 1669, 1667, 1663, 1657, 1637, 1627, 1621, 1619, 1613, 1609, 1607, 1601, 1597, 1583, 1579, 1571, 1567, 1559, 1553, 1549, 1543, 1531, 1523, 1511, 1499, 1493, 1489, 1487, 1483, 1481, 1471, 1459, 1453, 1451, 1447, 1439, 1433, 1429, 1427, 1423, 1409, 1399, 1381, 1373, 1367, 1361, 1327, 1321, 1319, 1307, 1303, 1301, 1297, 1291, 1289, 1283, 1279, 1277, 1259, 1249, 1237, 1231, 1229, 1223, 1217, 1213, 1201, 1193, 1187, 1181, 1171, 1163, 1153, 1151, 1129, 1123, 1117, 1109, 1103, 1097, 1093, 1091, 1087, 1069, 1063, 1061, 1051, 1049, 1039, 1033, 1031, 1021, 1019, 1013, 1009, 997, 991, 983, 977, 971, 967, 953, 947, 941, 937, 929, 919, 911, 907, 887, 883, 881, 877, 863, 859, 857, 853, 839, 829, 827, 823, 821, 811, 809, 797, 787, 773, 769, 761, 757, 751, 743, 739, 733, 727, 719, 709, 701, 691, 683, 677, 673, 661, 659, 653, 647, 643, 641, 631, 619, 617, 613, 607, 601, 599, 593, 587, 577, 571, 569, 563, 557, 547, 541, 523, 521, 509, 503, 499, 491, 487, 479, 467, 463, 461, 457, 449, 443, 439, 433, 431, 421, 419, 409, 401, 397, 389, 383, 379, 373, 367, 359, 353, 349, 347, 337, 331, 317, 313, 311, 307, 293, 283, 281, 277, 271, 269, 263, 257, 251, 241, 239, 233, 229, 227, 223, 211, 199, 197, 193, 191, 181, 179, 173, 167, 163, 157, 151, 149, 139, 137, 131, 127, 113, 109, 107, 103, 101, 97, 89, 83, 79, 73, 71, 67, 61, 59, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7]

private def small : List ℕ := [5, 3, 2]

open scoped Classical in
private noncomputable def survivors (ps : List ℕ) (x : ℕ) : Finset ℕ :=
  (Finset.Icc 1 x).filter fun m => ∀ p ∈ ps, ¬ p ∣ m

private theorem mem_survivors {ps : List ℕ} {x m : ℕ} :
    m ∈ survivors ps x ↔ (1 ≤ m ∧ m ≤ x) ∧ ∀ p ∈ ps, ¬ p ∣ m := by
  simp [survivors]

private theorem survivors_cons_card {p x : ℕ} {ps : List ℕ}
    (hp : p.Prime) (hnp : p ∉ ps) (hps : ∀ q ∈ ps, q.Prime) :
    (survivors (p :: ps) x).card = (survivors ps x).card - (survivors ps (x / p)).card := by
  classical
  have hcons : survivors (p :: ps) x = (survivors ps x).filter (fun m => ¬ p ∣ m) := by
    ext m
    simp only [mem_survivors, Finset.mem_filter, List.mem_cons]
    constructor
    · rintro ⟨hm, h⟩
      exact ⟨⟨hm, fun q hq => h q (Or.inr hq)⟩, h p (Or.inl rfl)⟩
    · rintro ⟨⟨hm, hs⟩, hn⟩
      refine ⟨hm, fun q hq => ?_⟩
      rcases hq with rfl | hq
      · exact hn
      · exact hs q hq
  have hfilter : (survivors ps x).filter (fun m => p ∣ m) =
      (survivors ps (x / p)).image (p * ·) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_image, mem_survivors]
    constructor
    · rintro ⟨⟨⟨hm, hmx⟩, hs⟩, u, rfl⟩
      refine ⟨u, ⟨⟨by
        by_contra! hu
        have hu' : u = 0 := by omega
        simp [hu'] at hm, ?_⟩, ?_⟩, rfl⟩
      · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa [mul_comm] using hmx)
      · intro q hq hd
        exact hs q hq (dvd_mul_of_dvd_right hd p)
    · rintro ⟨u, ⟨⟨hu, hux⟩, hs⟩, rfl⟩
      refine ⟨⟨⟨Nat.mul_pos hp.pos hu, ?_⟩, ?_⟩, dvd_mul_right _ _⟩
      · simpa [mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp hux
      · intro q hq hd
        rcases (hps q hq).dvd_mul.mp hd with hd | hd
        · have hqp := (Nat.prime_dvd_prime_iff_eq (hps q hq) hp).mp hd
          exact hnp (hqp ▸ hq)
        · exact hs q hq hd
  have hsum := Finset.card_filter_add_card_filter_not (s := survivors ps x) (p := fun m => p ∣ m)
  rw [← hcons, hfilter, Finset.card_image_of_injective _ (fun _ _ h => Nat.mul_left_cancel hp.pos h)] at hsum
  omega

private theorem wheel_correct (x : ℕ) : wheel x = (survivors small x).card := by
  have base (y : ℕ) : (survivors [] y).card = y := by simp [survivors, Nat.card_Icc]
  unfold small
  simp only [survivors_cons_card (by decide : Nat.Prime 5) (by decide : 5 ∉ [3, 2])
    (by decide : ∀ q ∈ ([3, 2] : List ℕ), q.Prime),
    survivors_cons_card (by decide : Nat.Prime 3) (by decide : 3 ∉ [2])
      (by decide : ∀ q ∈ ([2] : List ℕ), q.Prime),
    survivors_cons_card Nat.prime_two (by decide : 2 ∉ [])
      (by simp : ∀ q ∈ ([] : List ℕ), q.Prime), base]
  rfl

private theorem card_eq_of_covered {ps : List ℕ} {x : ℕ}
    (hp : ∀ q ∈ ps, Nat.Prime q) (hcover : ∀ q ≤ x, Nat.Prime q → q ∈ ps) :
    (survivors ps x).card = if x = 0 then 0 else 1 := by
  classical
  by_cases hx : x = 0
  · subst x
    simp [survivors]
  · have hsingle : survivors ps x = {1} := by
      ext n
      simp only [mem_survivors, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨_, hn⟩, hd⟩
        by_contra! hne
        exact hd n.minFac (hcover _ ((Nat.minFac_le (by omega)).trans hn)
          (Nat.minFac_prime hne)) n.minFac_dvd
      · rintro rfl
        exact ⟨⟨by decide, by omega⟩, fun q hq h => (hp q hq).ne_one (Nat.dvd_one.mp h)⟩
    simp [hx, hsingle]

private theorem count_correct (ps : List ℕ) (x : ℕ)
    (hprime : ∀ q ∈ ps ++ small, Nat.Prime q)
    (hsorted : (ps ++ small).Pairwise (· > ·))
    (hcover : ∀ p ∈ ps ++ small, ∀ q ≤ p, Nat.Prime q → q ∈ ps ++ small) :
    count ps x = (survivors (ps ++ small) x).card := by
  induction ps generalizing x with
  | nil => exact wheel_correct x
  | cons p ps ih =>
    change _ = (survivors (p :: (ps ++ small)) x).card
    have hpt : Nat.Prime p := hprime p (List.mem_cons_self ..)
    have hprt (q : ℕ) (hq : q ∈ ps ++ small) : Nat.Prime q :=
      hprime q (List.mem_cons_of_mem _ hq)
    obtain ⟨hlt, hst⟩ := List.pairwise_cons.mp hsorted
    have htc (t : ℕ) (ht : t ∈ ps ++ small) (q : ℕ) (hq : q ≤ t)
        (hqp : Nat.Prime q) : q ∈ ps ++ small := by
      have hq' := hcover p (List.mem_cons_self ..) q (hq.trans (hlt _ ht).le) hqp
      exact (List.mem_cons.mp hq').resolve_left (by have := hlt _ ht; omega)
    rw [count]
    split
    · rename_i hx
      symm
      exact card_eq_of_covered hprime (fun q hqx => hcover p (List.mem_cons_self ..) q (hqx.trans hx))
    · rw [ih x hprt hst htc, ih (x / p) hprt hst htc]
      exact (survivors_cons_card hpt (fun hm => (lt_irrefl p) (hlt p hm)) hprt).symm

private theorem survivors_card_le_primes (ps : List ℕ) (x : ℕ)
    (hcover : ∀ q ≤ x.sqrt, Nat.Prime q → q ∈ ps) :
    (survivors ps x).card ≤ (x.primesLE).card + 1 := by
  classical
  apply (Finset.card_le_card (t := insert 1 x.primesLE) ?_).trans
  · exact Finset.card_insert_le _ _
  · intro y hy
    obtain ⟨⟨hpos, hyx⟩, hn⟩ := mem_survivors.mp hy
    by_cases h1 : y = 1
    · exact Finset.mem_insert.mpr (Or.inl h1)
    · refine Finset.mem_insert_of_mem (Nat.mem_primesLE.mpr ⟨hyx, ?_⟩)
      by_contra! hnp
      have hmp : y.minFac.Prime := Nat.minFac_prime h1
      have hle : y.minFac ≤ x.sqrt := Nat.le_sqrt.mpr
        (by have := Nat.minFac_sq_le_self (by omega : 0 < y) hnp; simpa [pow_two] using this.trans hyx)
      exact hn _ (hcover _ hle hmp) y.minFac_dvd


private def smallPrimeCheck (q : ℕ) : Bool :=
  decide (2 ≤ q) && (List.range 53).all (fun j => decide (q ≤ j + 2 ∨ q % (j + 2) ≠ 0))

private theorem smallPrimeCheck_correct {q : ℕ} (hq : q < 2928) :
    smallPrimeCheck q = true ↔ q.Prime := by
  simp only [smallPrimeCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hq₂, h⟩
    by_contra! hn
    have hp := Nat.minFac_prime (by omega : q ≠ 1)
    have hs := Nat.minFac_sq_le_self (by omega : 0 < q) hn
    have hlt : q.minFac < 55 := by
      by_contra! hh
      have hmul := Nat.mul_le_mul hh hh
      rw [pow_two] at hs
      omega
    have hm := h (q.minFac - 2) (by have := hp.two_le; omega)
    rw [Nat.sub_add_cancel hp.two_le] at hm
    rcases hm with hm | hm
    · exact (Nat.not_prime_iff_minFac_lt hq₂).mp hn |>.not_ge hm
    · exact hm (Nat.mod_eq_zero_of_dvd q.minFac_dvd)
  · intro hp
    refine ⟨hp.two_le, fun j _ => ?_⟩
    by_cases h : q ≤ j + 2
    · exact Or.inl h
    · refine Or.inr ?_
      intro hd
      obtain hh | hh := hp.eq_one_or_self_of_dvd (j + 2) (Nat.dvd_of_mod_eq_zero hd)
      · omega
      · omega


set_option maxHeartbeats 0 in
private theorem primes_eq : primes ++ small = ((List.range 2928).filter smallPrimeCheck).reverse := by
  decide +kernel

private theorem mem_prime_table {q : ℕ} :
    q ∈ primes ++ small ↔ q < 2928 ∧ q.Prime := by
  rw [primes_eq, List.mem_reverse, List.mem_filter, List.mem_range]
  exact and_congr_right (fun h => smallPrimeCheck_correct h)

set_option maxHeartbeats 0 in
private theorem sieve_value : count primes 8567963 = 574975 := by decide +kernel

theorem nth_prime_le : Nat.nth Nat.Prime 550171 ≤ 8567963 := by
  have hcorrect := count_correct primes 8567963
    (fun _ h => (mem_prime_table.mp h).2)
    (by
      rw [primes_eq, List.pairwise_reverse]
      exact List.pairwise_lt_range.filter smallPrimeCheck)
    (fun _ hp q hqp hq => mem_prime_table.mpr ⟨hqp.trans_lt (mem_prime_table.mp hp).1, hq⟩)
  have hpc := survivors_card_le_primes (primes ++ small) 8567963
    (fun q hq hp => mem_prime_table.mpr
      ⟨hq.trans_lt (Nat.sqrt_lt.mpr (by decide : 8567963 < 2928 * 2928)), hp⟩)
  rw [← hcorrect, sieve_value, Nat.primesLE_card_eq_primeCounting] at hpc
  by_contra! h
  have hle := Nat.monotone_primeCounting' (Nat.succ_le_of_lt h)
  rw [Nat.primeCounting'_nth_eq] at hle
  change Nat.primeCounting 8567963 ≤ 550171 at hle
  omega

end PrimeBound

namespace ResidueWitness
open OeisA232616

private abbrev N := 550172

private theorem periodic (t q : ℕ) (ht : 2 ≤ t) :
    2 ^ (t + 29400 * q) ≡ 2 ^ t [MOD N] := by
  have step (i : ℕ) (hi : 2 ≤ i) : 2^(i+29400) ≡ 2^i [MOD N] := by
    have h0 : 2^(29400+2) ≡ 2^2 [MOD N] := by decide +kernel
    have h := h0.mul_right (2^(i-2))
    rw [← pow_add, ← pow_add] at h
    rwa [show 29400+2+(i-2)=i+29400 by omega, show 2+(i-2)=i by omega] at h
  induction q with
  | zero => exact Nat.ModEq.rfl
  | succ q ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc]
    exact (step _ (by omega)).trans ih

private def allIn (p : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, a => p a
  | d+1, a => allIn p d a && allIn p d (a+2^d)

private theorem allIn_sound {p : ℕ → Bool} {d a : ℕ} (h : allIn p d a = true)
    (i : ℕ) (hlo : a ≤ i) (hhi : i < a+2^d) : p i = true := by
  induction d generalizing a i with
  | zero =>
    have : i = a := by simp at hhi; omega
    exact this ▸ h
  | succ d ih =>
    obtain ⟨hl, hr⟩ := Bool.and_eq_true_iff.mp h
    by_cases hx : i < a+2^d
    · exact ih hl _ hlo hx
    · apply ih hr _ (by omega)
      rw [pow_succ] at hhi
      omega

private def remWord (t r : ℕ) := 2^t % N + 2*N - t - r

private def test (t : ℕ) : Bool :=
  let b := 131 * remWord t 63945 % N
  decide (29402 ≤ t ∨ b % 196 ≠ 0 ∨ 17135927 ≤ t + 29400*(b/196))

set_option maxHeartbeats 4000000 in
private theorem table : allIn test 15 2 = true := by decide +kernel

private theorem value_congr (t q r : ℕ) (ht : 2 ≤ t) (ht' : t < 29402) (hr : r < N) :
    ((2 ^ (t+29400*q) - (t+29400*q) : ℕ) : ZMod N) = (r : ZMod N) ↔
      remWord t r ≡ 29400*q [MOD N] := by
  have castpow := (ZMod.natCast_eq_natCast_iff _ _ _).2 (periodic t q ht)
  have castmod := (ZMod.natCast_eq_natCast_iff _ _ _).2 (Nat.mod_modEq (2^t) N)
  have hlarge : t + r ≤ 2^t % N + 2*N := by dsimp [N] at *; omega
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [Nat.cast_sub (Nat.le_of_lt Nat.lt_two_pow_self), castpow, remWord,
    Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, castmod]
  have hz : (550172 : ZMod N) = 0 := ZMod.natCast_self N
  change _ ↔ (_ + 2 * (550172 : ZMod N) - _ - _ = _)
  rw [hz, mul_zero, add_zero]
  constructor <;> intro h <;> linear_combination h

private theorem missing {k : ℕ} (hk : 0 < k) (hit :
    ((2^k-k : ℕ) : ZMod N) = (63945 : ZMod N)) : 17135927 ≤ k := by
  by_cases hk1 : k=1
  · subst k
    exact False.elim ((by decide : ¬ ((2^1-1 : ℕ) : ZMod N) = 63945) hit)
  let t := 2+(k-2)%29400
  let q := (k-2)/29400
  have ht : 2 ≤ t := by dsimp [t]; omega
  have ht' : t < 29402 := by dsimp [t]; omega
  have he : t+29400*q=k := by dsimp [t,q]; omega
  have h := (value_congr t q 63945 ht ht' (by decide)).1 (he ▸ hit)
  have inv : 131*29400 ≡ 196 [MOD N] := by decide
  have hh := h.mul_left 131
  rw [← Nat.mul_assoc 131 29400 q] at hh
  have hb := hh.trans (inv.mul_right q)
  change 131 * remWord t 63945 % N = 196*q % (196*2807) at hb
  rw [Nat.mul_mod_mul_left] at hb
  have htest := allIn_sound table t ht (by norm_num; omega)
  simp only [test, decide_eq_true_eq, hb] at htest
  omega

private def seed (r : ℕ) : ℕ := (0x78b58eea0229a89e340c9988ed4b0bd85e18a4dc82ea41cc19d68c5a968fe64248b8260c74dda164416d7b0e2c5c93a361450b28de943c978862806bfb17202c90ae79c20b38c73014ad9be8408a38e6581e8880fa09a9b8af88d8959c678048f996f44c8994688368386e1cdad29066ccef18d6f846878a6e084ab876b84ea08464c1885816984084bb68086a8866687ac79865066ac92e3830818561056a584e084ac896e483ec2a66d832b898eac269d8364012829563c0eaaa6ecc02a4a3f48769e81edc6098916302a8e83e04288c97f4c708680734ae8091e24 / 512^(r%196)) % 512

private def seedOk (i : ℕ) : Bool :=
  let t := seed i
  decide (196 ≤ i ∨ 2 ≤ t ∧ t < 512 ∧ (2^t % N + 2*N-t) % 196 = i)

private theorem seed_table : allIn seedOk 8 0 = true := by decide +kernel

private theorem coverage : HasCompleteResidueSystem N 100000000000 := by
  unfold HasCompleteResidueSystem
  ext z
  constructor
  · intro _
    let r := z.val
    have hr : r < N := ZMod.val_lt z
    let i := r%196
    have hi : i < 196 := Nat.mod_lt _ (by decide)
    have hs := allIn_sound seed_table i (Nat.zero_le _) (by norm_num; omega)
    simp only [seedOk, decide_eq_true_eq] at hs
    obtain ⟨ht, ht', hm⟩ := hs.resolve_left (by omega)
    let t := seed i
    let D := remWord t r
    have hmod : D % 196 = 0 := by
      change (2^t % N + 2*N - t) % 196 = r%196 at hm
      dsimp [D,remWord,N] at *
      omega
    let e := D/196
    have hD : D=196*e := by dsimp [e]; omega
    let q := 131*e
    have lin : remWord t r ≡ 29400*q [MOD N] := by
      change D ≡ 29400*(131*e) [MOD N]
      rw [hD]
      rw [← Nat.mul_assoc]
      exact (by decide : 196 ≡ 29400*131 [MOD N]).mul_right e
    have hh := (value_congr t q r ht (by omega) hr).2 lin
    apply Finset.mem_image.mpr
    refine ⟨t + 29400*q, Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
    · have hV : 2^t%N < N := Nat.mod_lt _ (by decide)
      dsimp [D,remWord] at hD
      dsimp [q,N] at *
      omega
    · exact hh.trans (ZMod.natCast_zmod_val z)
  · intro _
    exact Finset.mem_univ z

theorem lower : 17135927 ≤ a N := by
  rw [a, dif_neg (by decide)]
  obtain ⟨m, hm, hmin⟩ := (show ∃ m, HasCompleteResidueSystem N m ∧
      m = sInf {u : ℕ | HasCompleteResidueSystem N u} from
    ⟨_, Nat.sInf_mem (show Set.Nonempty {u : ℕ | HasCompleteResidueSystem N u} from
      ⟨_, coverage⟩), rfl⟩)
  rw [← hmin]
  have hmem := Finset.mem_univ (63945 : ZMod N)
  rw [show (Finset.univ : Finset (ZMod N)) = _ from hm] at hmem
  obtain ⟨k,hk,hit⟩ := Finset.mem_image.mp hmem
  exact (missing (Finset.mem_Icc.mp hk).1 hit).trans (Finset.mem_Icc.mp hk).2

end ResidueWitness

theorem OMA.solution : type_of% @OeisA232616.conjecture_1 := by
  intro h
  have hlt := h 550172 (by decide)
  have hlo := ResidueWitness.lower
  have hp := PrimeBound.nth_prime_le
  change 17135927 ≤ OeisA232616.a 550172 at hlo
  change OeisA232616.a 550172 < 2 * (Nat.nth Nat.Prime 550171 - 1) at hlt
  omega