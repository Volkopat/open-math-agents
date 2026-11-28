import OMAStatements.S_oeis_a085267
import Mathlib

-- Proof of oeis-a085267 (OEIS A085267: Greathouse's conjecture on sums of a positive square
-- and a positive squarefree integer).
-- Statement credit: @dwilfand-sys

/-!
# Proof that the nth term of OEIS A085267 is `n + 11` for all `n > 50`

We prove `termsThrough 61 = 50` and `∀ m ≥ 62, 2 ≤ representations m`.
The lower range `62 ≤ m < 12000400` is verified by a sound chunked squarefree bitmask sieve.
The upper range `m ≥ 12000400` is proved by a completely elementary squarefree sieve
split across nine rational bands `[12000000, 10^17)` and a uniform asymptotic regime `m ≥ 10^17`.
-/

namespace OMA.A085267Proof

open Finset OMA.S_oeis_a085267

-- ## Section 1: Finite Base Cases (termsThrough 61 = 50 and 62 ≤ m < 12000400)

private def sqfreeBool (n : ℕ) : Bool :=
  decide (0 < n) && (List.range n).all (fun d => decide (d < 2) || decide (n % (d * d) ≠ 0))

private lemma sqfreeBool_iff (n : ℕ) : sqfreeBool n = true ↔ Squarefree n := by
  unfold sqfreeBool
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true]
  constructor
  · rintro ⟨hn, hall⟩ d hd
    rw [Nat.isUnit_iff]
    by_contra hd1
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at hd
      omega
    have hd2 : 2 ≤ d := by omega
    have hle : d * d ≤ n := Nat.le_of_dvd hn hd
    have hdlt : d < n := by nlinarith
    have h := hall d hdlt
    rcases h with hlt | hne
    · omega
    · exact hne (Nat.mod_eq_zero_of_dvd hd)
  · intro hsf
    have hn0 : n ≠ 0 := hsf.ne_zero
    refine ⟨by omega, fun d hd => ?_⟩
    by_cases h2 : d < 2
    · exact Or.inl h2
    · right
      intro hmod
      have hdvd : d * d ∣ n := Nat.dvd_of_mod_eq_zero hmod
      have hu := hsf d hdvd
      rw [Nat.isUnit_iff] at hu
      omega

private def repsBool (n : ℕ) : ℕ :=
  ((Finset.range (n.sqrt + 1)).filter
    (fun k => 0 < k ∧ k ^ 2 < n ∧ sqfreeBool (n - k ^ 2) = true)).card

private lemma representations_eq_repsBool (n : ℕ) : representations n = repsBool n := by
  unfold representations repsBool
  congr 1
  ext k
  simp [sqfreeBool_iff]

private def termsThroughBool (m : ℕ) : ℕ :=
  ((Finset.range (m + 1)).filter (fun t => 0 < t ∧ 2 ≤ repsBool t)).card

private lemma termsThrough_eq_bool (m : ℕ) : termsThrough m = termsThroughBool m := by
  unfold termsThrough termsThroughBool
  congr 1
  ext t
  simp [representations_eq_repsBool]

private lemma termsThrough_61 : termsThrough 61 = 50 := by
  rw [termsThrough_eq_bool]
  decide +kernel

private lemma two_le_representations_of_witnesses {m k₁ k₂ : ℕ}
    (hk₁ : 0 < k₁) (hk₁₂ : k₁ < k₂) (hm₁ : k₁ ^ 2 < m) (hm₂ : k₂ ^ 2 < m)
    (hs₁ : Squarefree (m - k₁ ^ 2)) (hs₂ : Squarefree (m - k₂ ^ 2)) :
    2 ≤ representations m := by
  unfold representations
  have hmem₁ : k₁ ∈ (Finset.range (m.sqrt + 1)).filter
      (fun k => 0 < k ∧ k ^ 2 < m ∧ Squarefree (m - k ^ 2)) := by
    rw [mem_filter, mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_sqrt.mpr (by nlinarith)), hk₁, hm₁, hs₁⟩
  have hmem₂ : k₂ ∈ (Finset.range (m.sqrt + 1)).filter
      (fun k => 0 < k ∧ k ^ 2 < m ∧ Squarefree (m - k ^ 2)) := by
    rw [mem_filter, mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_sqrt.mpr (by nlinarith)), by omega, hm₂, hs₂⟩
  have hsub : ({k₁, k₂} : Finset ℕ) ⊆ (Finset.range (m.sqrt + 1)).filter
      (fun k => 0 < k ∧ k ^ 2 < m ∧ Squarefree (m - k ^ 2)) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard : ({k₁, k₂} : Finset ℕ).card = 2 := card_pair (by omega)
  calc 2 = ({k₁, k₂} : Finset ℕ).card := hcard.symm
    _ ≤ _ := card_le_card hsub

-- Chunked GMP-accelerated squarefree bitmask sieve for 62 ≤ m < 12000400

private def isPrimeFastGo (n d : ℕ) : ℕ → Bool
  | 0 => true
  | fuel + 1 =>
    if d * d > n then true
    else if n % d == 0 then false
    else isPrimeFastGo n (d + 2) fuel

private def isPrimeFast (n : ℕ) : Bool :=
  if n < 2 then false
  else if n == 2 then true
  else if n % 2 == 0 then false
  else isPrimeFastGo n 3 n

private lemma isPrimeFastGo_of_prime {n : ℕ} (hn : n.Prime) (d fuel : ℕ) (hd : 2 ≤ d) :
    isPrimeFastGo n d fuel = true := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih =>
    unfold isPrimeFastGo
    split_ifs with h1 h2
    · rfl
    · exfalso
      have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h2)
      rcases hn.eq_one_or_self_of_dvd d hdvd with rfl | rfl
      · omega
      · nlinarith
    · exact ih (d + 2) (by omega)

private lemma isPrimeFast_of_prime {p : ℕ} (hp : p.Prime) : isPrimeFast p = true := by
  unfold isPrimeFast
  have hp2 : 2 ≤ p := hp.two_le
  split_ifs with h1 h2 h3
  · omega
  · rfl
  · exfalso
    have h2dvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h3)
    rcases hp.eq_one_or_self_of_dvd 2 h2dvd with h | h
    · omega
    · exact h2 (beq_iff_eq.mpr h.symm)
  · exact isPrimeFastGo_of_prime hp 3 p (by omega)

private def buildPrimesAux (n : ℕ) : ℕ → List ℕ → List ℕ
  | 0, acc => acc
  | k + 1, acc =>
    let p := n - k
    let acc' := if isPrimeFast p then p :: acc else acc
    buildPrimesAux n k acc'

private lemma mem_buildPrimesAux_acc (n : ℕ) : ∀ (k : ℕ) (acc : List ℕ) (x : ℕ),
    x ∈ acc → x ∈ buildPrimesAux n k acc
  | 0, _, _, hx => hx
  | k + 1, acc, x, hx => by
    unfold buildPrimesAux
    apply mem_buildPrimesAux_acc
    split_ifs
    · exact List.mem_cons_of_mem _ hx
    · exact hx

private lemma mem_buildPrimesAux_of_prime (n : ℕ) : ∀ (k : ℕ) (acc : List ℕ) {p : ℕ},
    p.Prime → n - k < p → p ≤ n → p ∈ buildPrimesAux n k acc
  | 0, _, p, _, h1, h2 => by omega
  | k + 1, acc, p, hp, h1, h2 => by
    unfold buildPrimesAux
    by_cases heq : p = n - k
    · subst heq
      apply mem_buildPrimesAux_acc
      rw [if_pos (isPrimeFast_of_prime hp)]
      exact List.mem_cons_self
    · exact mem_buildPrimesAux_of_prime n k _ hp (by omega) h2

private lemma mem_buildPrimes {N p : ℕ} (hp : p.Prime) (hle : p ≤ N) :
    p ∈ buildPrimesAux N N [] :=
  mem_buildPrimesAux_of_prime N N [] hp (by have := hp.two_le; omega) hle

private def geomMask (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => 1 + (geomMask q k <<< q)

private lemma geomMask_mul_add_one (q : ℕ) (hq : 1 ≤ q) : ∀ k : ℕ,
    (2 ^ q - 1) * geomMask q k + 1 = 2 ^ ((k + 1) * q)
  | 0 => by
    simp only [geomMask, mul_one, zero_add, one_mul]
    have hq1 : 1 ≤ 2 ^ q := Nat.one_le_pow _ _ (by omega)
    omega
  | k + 1 => by
    have ih := geomMask_mul_add_one q hq k
    simp only [geomMask, Nat.shiftLeft_eq]
    have hq1 : 1 ≤ 2 ^ q := Nat.one_le_pow _ _ (by omega)
    have hmul : (2 ^ q - 1) * (1 + geomMask q k * 2 ^ q) + 1 =
        ((2 ^ q - 1) + 1) + ((2 ^ q - 1) * geomMask q k) * 2 ^ q := by ring
    rw [hmul, Nat.sub_add_cancel hq1]
    have hexp : (k + 1 + 1) * q = (k + 1) * q + q := by ring
    rw [hexp, pow_add]
    have h1 : ((2 ^ q - 1) * geomMask q k + 1) * 2 ^ q =
        2 ^ q + (2 ^ q - 1) * geomMask q k * 2 ^ q := by ring
    rw [← h1, ih]

private lemma geomMask_eq_div (q k : ℕ) (hq : 1 ≤ q) :
    ((1 <<< ((k + 1) * q)) - 1) / ((1 <<< q) - 1) = geomMask q k := by
  simp only [Nat.shiftLeft_eq, one_mul]
  have hpos : 0 < 2 ^ q - 1 := by
    have : 2 ≤ 2 ^ q := by
      calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hq
    omega
  have hmul : (2 ^ q - 1) * geomMask q k = 2 ^ ((k + 1) * q) - 1 := by
    have h := geomMask_mul_add_one q hq k
    omega
  rw [← hmul, Nat.mul_div_cancel_left _ hpos]

private lemma testBit_geomMask (q : ℕ) (hq : 1 ≤ q) : ∀ (k i : ℕ), i ≤ k →
    (geomMask q k).testBit (i * q) = true
  | 0, i, hi => by
    have : i = 0 := by omega
    subst this
    simp [geomMask]
  | k + 1, 0, _ => by
    simp only [geomMask, Nat.zero_mul, Nat.testBit_zero, Nat.shiftLeft_eq]
    have h2 : 2 ∣ 2 ^ q := dvd_pow_self 2 (by omega)
    have : (1 + geomMask q k * 2 ^ q) % 2 = 1 := by
      obtain ⟨t, ht⟩ := h2
      have : geomMask q k * 2 ^ q = 2 * (geomMask q k * t) := by rw [ht]; ring
      omega
    simp [this]
  | k + 1, i + 1, hi => by
    have ih := testBit_geomMask q hq k i (by omega)
    simp only [geomMask, Nat.shiftLeft_eq]
    have h2q_gt1 : 1 < 2 ^ q := by
      calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by omega) hq
    have hdiv : (1 + geomMask q k * 2 ^ q) / 2 ^ q = geomMask q k := by
      rw [Nat.add_mul_div_right 1 _ (by positivity), Nat.div_eq_of_lt h2q_gt1, zero_add]
    have hexp : (i + 1) * q = q + i * q := by ring
    rw [hexp, Nat.testBit_eq_decide_div_mod_eq, pow_add, ← Nat.div_div_eq_div_mul, hdiv,
      ← Nat.testBit_eq_decide_div_mod_eq]
    exact ih

private def multMaskOffset (q base len : ℕ) : ℕ :=
  let m0 := ((base + q - 1) / q) * q
  if m0 >= base + len then 0
  else
    let off := m0 - base
    let cnt := (len - 1 - off) / q
    let baseMask := ((1 <<< ((cnt + 1) * q)) - 1) / ((1 <<< q) - 1)
    baseMask <<< off

private lemma testBit_multMaskOffset {q base len n : ℕ}
    (hq : 1 ≤ q) (hdvd : q ∣ n) (hlo : base ≤ n) (hhi : n < base + len) :
    (multMaskOffset q base len).testBit (n - base) = true := by
  unfold multMaskOffset
  dsimp only
  set m0 := ((base + q - 1) / q) * q
  have hm0_ge : base ≤ m0 := by
    have hdiv := Nat.div_add_mod (base + q - 1) q
    have hmod := Nat.mod_lt (base + q - 1) (by omega : 0 < q)
    have hmul : m0 = q * ((base + q - 1) / q) := mul_comm _ _
    omega
  have hm0_le_n : m0 ≤ n := by
    obtain ⟨t, rfl⟩ := hdvd
    have ht : (base + q - 1) / q ≤ t := by
      rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0 < q)]
      omega
    have h1 := Nat.mul_le_mul_right q ht
    simpa [m0, mul_comm] using h1
  have hlt : ¬ (m0 ≥ base + len) := by omega
  rw [if_neg hlt]
  set off := m0 - base
  set cnt := (len - 1 - off) / q
  rw [geomMask_eq_div q cnt hq, Nat.testBit_shiftLeft]
  have hoff_le : off ≤ n - base := by omega
  have hdvd_diff : q ∣ (n - m0) := Nat.dvd_sub hdvd (dvd_mul_left q _)
  obtain ⟨i, hi⟩ := hdvd_diff
  have hsub : n - base - off = i * q := by
    have : n - base - off = n - m0 := by omega
    rw [this, hi, mul_comm]
  have hi_le : i ≤ cnt := by
    change i ≤ (len - 1 - off) / q
    rw [Nat.le_div_iff_mul_le (by omega : 0 < q)]
    have : i * q = n - m0 := by rw [mul_comm, ← hi]
    omega
  simp [hoff_le, hsub, testBit_geomMask q hq cnt i hi_le]

private def buildBadChunk (base len : ℕ) : List ℕ → ℕ → ℕ
  | [], acc => acc
  | p :: ps, acc =>
    let q := p * p
    buildBadChunk base len ps (acc ||| multMaskOffset q base len)

private lemma testBit_buildBadChunk_mono (base len : ℕ) :
    ∀ (ps : List ℕ) (acc idx : ℕ),
    acc.testBit idx = true → (buildBadChunk base len ps acc).testBit idx = true
  | [], _, _, h => h
  | p :: ps, acc, idx, h => by
    unfold buildBadChunk
    apply testBit_buildBadChunk_mono
    rw [Nat.testBit_or, h]
    rfl

private lemma testBit_buildBadChunk_of_mem {base len n p : ℕ} :
    ∀ (ps : List ℕ) (acc : ℕ),
    p ∈ ps → 1 ≤ p → p * p ∣ n → base ≤ n → n < base + len →
    (buildBadChunk base len ps acc).testBit (n - base) = true
  | [], _, hmem, _, _, _, _ => by simp at hmem
  | p' :: ps, acc, hmem, hp1, hdvd, hlo, hhi => by
    unfold buildBadChunk
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | htail
    · apply testBit_buildBadChunk_mono
      rw [Nat.testBit_or]
      have htb := testBit_multMaskOffset (by nlinarith : 1 ≤ p * p) hdvd hlo hhi
      simp [htb]
    · exact testBit_buildBadChunk_of_mem ps _ htail hp1 hdvd hlo hhi

private def checkShiftLoop (allBits good : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, s2 => s2
  | k + 1, s1, s2 =>
    let kk := (k + 1) * (k + 1)
    let sh := (good <<< kk) &&& allBits
    checkShiftLoop allBits good k (s1 ||| sh) (s2 ||| (s1 &&& sh))

private lemma testBit_allBits {len j : ℕ} (hj : j < len) :
    ((1 <<< len) - 1).testBit j = true := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hj

private lemma testBit_allBits_ge {len j : ℕ} (hj : len ≤ j) :
    ((1 <<< len) - 1).testBit j = false := by
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow_sub_one]
  exact decide_eq_false (by omega)

private lemma checkShiftLoop_spec (allBits good : ℕ) :
    ∀ (k s1 s2 j : ℕ),
    (∀ i, s1.testBit i = true → ∃ a, k < a ∧ a * a ≤ i ∧ good.testBit (i - a * a) = true) →
    (∀ i, s2.testBit i = true → ∃ a b, k < a ∧ a < b ∧ a * a ≤ i ∧ b * b ≤ i ∧
      good.testBit (i - a * a) = true ∧ good.testBit (i - b * b) = true) →
    (checkShiftLoop allBits good k s1 s2).testBit j = true →
    ∃ a b, 0 < a ∧ a < b ∧ a * a ≤ j ∧ b * b ≤ j ∧
      good.testBit (j - a * a) = true ∧ good.testBit (j - b * b) = true
  | 0, s1, s2, j, _, hs2, h => hs2 j h
  | k + 1, s1, s2, j, hs1, hs2, h => by
    unfold checkShiftLoop at h
    apply checkShiftLoop_spec allBits good k _ _ j _ _ h
    · intro i hi
      rw [Nat.testBit_or, Bool.or_eq_true] at hi
      rcases hi with h1 | hsh
      · obtain ⟨a, ha, hsq, hg⟩ := hs1 i h1
        exact ⟨a, by omega, hsq, hg⟩
      · rw [Nat.testBit_and, Bool.and_eq_true, Nat.testBit_shiftLeft, Bool.and_eq_true] at hsh
        exact ⟨k + 1, by omega, decide_eq_true_eq.mp hsh.1.1, hsh.1.2⟩
    · intro i hi
      rw [Nat.testBit_or, Bool.or_eq_true] at hi
      rcases hi with h2 | hboth
      · obtain ⟨a, b, ha, hab, hsqa, hsqb, hga, hgb⟩ := hs2 i h2
        exact ⟨a, b, by omega, hab, hsqa, hsqb, hga, hgb⟩
      · rw [Nat.testBit_and, Bool.and_eq_true] at hboth
        obtain ⟨b, hb, hsqb, hgb⟩ := hs1 i hboth.1
        have hsh := hboth.2
        rw [Nat.testBit_and, Bool.and_eq_true, Nat.testBit_shiftLeft, Bool.and_eq_true] at hsh
        exact ⟨k + 1, b, by omega, hb, decide_eq_true_eq.mp hsh.1.1, hsqb, hsh.1.2, hgb⟩

private def checkFirstChunk (ps : List ℕ) (lo width Kmax : ℕ) : Bool :=
  let len := lo + width
  let allBits := (1 <<< len) - 1
  let bad := buildBadChunk 0 len ps 0
  let bad0 := bad ||| 1
  let good := allBits ^^^ (bad0 &&& allBits)
  let s2 := checkShiftLoop allBits good Kmax 0 0
  let target := (1 <<< width) - 1
  ((s2 >>> lo) &&& target) == target

private def checkChunk (ps : List ℕ) (lo width Kmax : ℕ) : Bool :=
  let pad := Kmax * Kmax
  let base := lo - pad
  let len := width + pad
  let allBits := (1 <<< len) - 1
  let bad := buildBadChunk base len ps 0
  let good := allBits ^^^ (bad &&& allBits)
  let s2 := checkShiftLoop allBits good Kmax 0 0
  let target := (1 <<< width) - 1
  ((s2 >>> pad) &&& target) == target

private def checkAllChunks (ps : List ℕ) (lo width Kmax : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 =>
    if checkChunk ps lo width Kmax then
      checkAllChunks ps (lo + width) width Kmax n
    else false

private lemma squarefree_of_not_prime_sq_dvd {n N : ℕ} (hn : 0 < n) (hnN : n ≤ N * N)
    (h : ∀ p, p.Prime → p ≤ N → ¬ p * p ∣ n) : Squarefree n := by
  intro d hd
  rw [Nat.isUnit_iff]
  by_contra hd1
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd; omega
  have hd2 : 2 ≤ d := by omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  have hpp : p * p ∣ n := dvd_trans (Nat.mul_dvd_mul hpd hpd) hd
  have hp_sq : p * p ≤ n := Nat.le_of_dvd hn hpp
  have hpN : p ≤ N := by nlinarith
  exact h p hp hpN hpp

private lemma checkFirstChunk_spec {ps : List ℕ} {lo width Kmax Pmax : ℕ}
    (hps : ∀ p, p.Prime → p ≤ Pmax → p ∈ ps)
    (hPmax : lo + width ≤ Pmax * Pmax)
    (hchk : checkFirstChunk ps lo width Kmax = true) :
    ∀ m, lo ≤ m → m < lo + width → 2 ≤ representations m := by
  intro m hmlo hmhi
  unfold checkFirstChunk at hchk
  dsimp only at hchk
  set len := lo + width
  set allBits := (1 <<< len) - 1
  set bad := buildBadChunk 0 len ps 0
  set bad0 := bad ||| 1
  set good := allBits ^^^ (bad0 &&& allBits)
  set s2 := checkShiftLoop allBits good Kmax 0 0
  set target := (1 <<< width) - 1
  have heq := beq_iff_eq.mp hchk
  have hbit : s2.testBit m = true := by
    have ht := congrArg (fun x => x.testBit (m - lo)) heq
    rw [Nat.testBit_and, Nat.testBit_shiftRight] at ht
    have htb : target.testBit (m - lo) = true := testBit_allBits (by omega)
    rw [htb, Bool.and_true] at ht
    have hadd : lo + (m - lo) = m := by omega
    rwa [hadd] at ht
  obtain ⟨a, b, ha, hab, hsqa, hsqb, hga, hgb⟩ :=
    checkShiftLoop_spec allBits good Kmax 0 0 m (by simp) (by simp) hbit
  have hgood_sf : ∀ x, good.testBit x = true → 0 < x ∧ Squarefree x := by
    intro x hx
    have hxlt : x < len := by
      by_contra hge
      have h1 : allBits.testBit x = false := testBit_allBits_ge (by omega)
      have : good.testBit x = false := by
        simp [good, Nat.testBit_xor, Nat.testBit_and, h1]
      rw [hx] at this
      exact Bool.noConfusion this
    have hall : allBits.testBit x = true := testBit_allBits hxlt
    have hbad0 : bad0.testBit x = false := by
      have : good.testBit x = (allBits.testBit x != (bad0.testBit x && allBits.testBit x)) := by
        simp [good, Nat.testBit_xor, Nat.testBit_and]
      rw [hx, hall, Bool.and_true] at this
      cases h : bad0.testBit x
      · rfl
      · simp [h] at this
    have hxpos : 0 < x := by
      by_contra h0
      have hx0 : x = 0 := by omega
      subst hx0
      have : bad0.testBit 0 = true := by simp [bad0]
      rw [this] at hbad0
      exact Bool.noConfusion hbad0
    have hbad : bad.testBit x = false := by
      have : bad0.testBit x = (bad.testBit x || (1 : ℕ).testBit x) := Nat.testBit_or bad 1 x
      rw [hbad0] at this
      cases h : bad.testBit x
      · rfl
      · simp [h] at this
    refine ⟨hxpos, squarefree_of_not_prime_sq_dvd (N := Pmax) hxpos (by omega) ?_⟩
    intro p hp hpP hpp
    have htb := testBit_buildBadChunk_of_mem ps 0 (hps p hp hpP) hp.one_le hpp (Nat.zero_le x)
      (by omega : x < 0 + len)
    rw [Nat.sub_zero] at htb
    rw [htb] at hbad
    exact Bool.noConfusion hbad
  have h1 := hgood_sf (m - a * a) hga
  have h2 := hgood_sf (m - b * b) hgb
  rw [← sq] at h1 h2
  exact two_le_representations_of_witnesses ha hab (by omega) (by omega) h1.2 h2.2

private lemma checkChunk_spec {ps : List ℕ} {lo width Kmax Pmax : ℕ}
    (hps : ∀ p, p.Prime → p ≤ Pmax → p ∈ ps)
    (hpad : Kmax * Kmax < lo)
    (hPmax : lo + width ≤ Pmax * Pmax)
    (hchk : checkChunk ps lo width Kmax = true) :
    ∀ m, lo ≤ m → m < lo + width → 2 ≤ representations m := by
  intro m hmlo hmhi
  unfold checkChunk at hchk
  dsimp only at hchk
  set pad := Kmax * Kmax
  set base := lo - pad
  set len := width + pad
  set allBits := (1 <<< len) - 1
  set bad := buildBadChunk base len ps 0
  set good := allBits ^^^ (bad &&& allBits)
  set s2 := checkShiftLoop allBits good Kmax 0 0
  set target := (1 <<< width) - 1
  have hbase_pos : 0 < base := by omega
  have heq := beq_iff_eq.mp hchk
  have hbit : s2.testBit (m - base) = true := by
    have ht := congrArg (fun x => x.testBit (m - lo)) heq
    rw [Nat.testBit_and, Nat.testBit_shiftRight] at ht
    have htb : target.testBit (m - lo) = true := testBit_allBits (by omega)
    rw [htb, Bool.and_true] at ht
    have hadd : pad + (m - lo) = m - base := by omega
    rwa [hadd] at ht
  obtain ⟨a, b, ha, hab, hsqa, hsqb, hga, hgb⟩ :=
    checkShiftLoop_spec allBits good Kmax 0 0 (m - base) (by simp) (by simp) hbit
  have hgood_sf : ∀ j, good.testBit j = true → Squarefree (base + j) := by
    intro j hj
    have hjlt : j < len := by
      by_contra hge
      have h1 : allBits.testBit j = false := testBit_allBits_ge (by omega)
      have : good.testBit j = false := by
        simp [good, Nat.testBit_xor, Nat.testBit_and, h1]
      rw [hj] at this
      exact Bool.noConfusion this
    have hall : allBits.testBit j = true := testBit_allBits hjlt
    have hbad : bad.testBit j = false := by
      have : good.testBit j = (allBits.testBit j != (bad.testBit j && allBits.testBit j)) := by
        simp [good, Nat.testBit_xor, Nat.testBit_and]
      rw [hj, hall, Bool.and_true] at this
      cases h : bad.testBit j
      · rfl
      · simp [h] at this
    refine squarefree_of_not_prime_sq_dvd (N := Pmax) (by omega) (by omega) ?_
    intro p hp hpP hpp
    have htb := testBit_buildBadChunk_of_mem ps 0 (hps p hp hpP) hp.one_le hpp
      (by omega : base ≤ base + j) (by omega : base + j < base + len)
    rw [Nat.add_sub_cancel_left] at htb
    rw [htb] at hbad
    exact Bool.noConfusion hbad
  have h1 := hgood_sf (m - base - a * a) hga
  have h2 := hgood_sf (m - base - b * b) hgb
  have heq1 : base + (m - base - a * a) = m - a ^ 2 := by rw [sq]; omega
  have heq2 : base + (m - base - b * b) = m - b ^ 2 := by rw [sq]; omega
  rw [heq1] at h1
  rw [heq2] at h2
  exact two_le_representations_of_witnesses ha hab (by rw [sq]; omega) (by rw [sq]; omega) h1 h2

private lemma checkAllChunks_spec {ps : List ℕ} {width Kmax Pmax : ℕ}
    (hps : ∀ p, p.Prime → p ≤ Pmax → p ∈ ps) :
    ∀ (n lo : ℕ),
    Kmax * Kmax < lo →
    lo + n * width ≤ Pmax * Pmax →
    checkAllChunks ps lo width Kmax n = true →
    ∀ m, lo ≤ m → m < lo + n * width → 2 ≤ representations m
  | 0, lo, _, _, _, m, h1, h2 => by omega
  | n + 1, lo, hpad, hPmax, hchk, m, hmlo, hmhi => by
    unfold checkAllChunks at hchk
    split_ifs at hchk with hfirst
    · by_cases hlt : m < lo + width
      · exact checkChunk_spec hps hpad (by nlinarith) hfirst m hmlo hlt
      · exact checkAllChunks_spec hps n (lo + width) (by omega)
          (by linarith) hchk m (by omega) (by linarith)

private def primes20 : List ℕ := buildPrimesAux 20 20 []
private def primes3465 : List ℕ := buildPrimesAux 3465 3465 []

private lemma small_range_62_400 : ∀ m, 62 ≤ m → m < 400 → 2 ≤ representations m := by
  have hchk : checkFirstChunk primes20 62 338 19 = true := by decide +kernel
  exact checkFirstChunk_spec (fun p hp hle => mem_buildPrimes hp hle) (by norm_num) hchk

private lemma small_range_400_12000400 : ∀ m, 400 ≤ m → m < 12000400 → 2 ≤ representations m := by
  have hchk : checkAllChunks primes3465 400 100000 19 120 = true := by decide +kernel
  exact checkAllChunks_spec (fun p hp hle => mem_buildPrimes hp hle) 120 400
    (by norm_num) (by norm_num) hchk

private lemma small_range_ok : ∀ m, 62 ≤ m → m < 12000400 → 2 ≤ representations m := by
  intro m h1 h2
  by_cases h : m < 400
  · exact small_range_62_400 m h1 h
  · exact small_range_400_12000400 m (by omega) h2

/- ## Section 2: Master Elementary Squarefree Sieve -/

-- 2.1 Counting integers in Icc 1 K in a congruence class and avoiding a finite set of primes

private lemma card_Icc_mod_approx (K M a : ℕ) (hM : 0 < M) :
    |(((Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M])).card : ℚ) - (K : ℚ) / (M : ℚ)| ≤ 1 := by
  set r := if a % M = 0 then M else a % M
  have hr1 : 1 ≤ r := by
    dsimp [r]; split_ifs with h <;> omega
  have hrM : r ≤ M := by
    dsimp [r]; split_ifs with h
    · exact le_rfl
    · exact le_of_lt (Nat.mod_lt a hM)
  have hr_mod : r % M = a % M := by
    dsimp [r]; split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_eq_of_lt (Nat.mod_lt a hM)
  have hiff : ∀ k, k ≡ a [MOD M] ↔ k % M = r % M := by
    intro k; change k % M = a % M ↔ k % M = r % M; rw [hr_mod]
  by_cases hKr : K < r
  · have hemp : (Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M]) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro k hk hmod
      rw [Finset.mem_Icc] at hk
      rw [hiff] at hmod
      have hklt : k < M := by omega
      rw [Nat.mod_eq_of_lt hklt] at hmod
      dsimp [r] at hmod hKr
      split_ifs at hmod hKr with h0
      · rw [Nat.mod_self] at hmod; omega
      · rw [Nat.mod_eq_of_lt (Nat.mod_lt a hM)] at hmod; omega
    rw [hemp, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg]
    have hKM : (K : ℚ) / (M : ℚ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast (by omega : K ≤ M)
    rw [abs_of_nonneg (by positivity)]
    exact hKM
  · push Not at hKr
    set C := (K - r) / M + 1
    have hcard : ((Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M])).card = C := by
      have hbij : (Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M]) =
          (Finset.range C).image (fun t => r + t * M) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨⟨hk1, hkK⟩, hmod⟩
          rw [hiff] at hmod
          have hkr : r ≤ k := by
            by_contra hlt
            push Not at hlt
            have hklt : k < M := by omega
            rw [Nat.mod_eq_of_lt hklt] at hmod
            dsimp [r] at hmod hlt
            split_ifs at hmod hlt with h0
            · rw [Nat.mod_self] at hmod; omega
            · rw [Nat.mod_eq_of_lt (Nat.mod_lt a hM)] at hmod; omega
          have hdvd : M ∣ (k - r) := (Nat.modEq_iff_dvd' hkr).mp hmod.symm
          obtain ⟨t, ht⟩ := hdvd
          have ht' : k - r = t * M := by rw [mul_comm]; exact ht
          refine ⟨t, ?_, by omega⟩
          change t < (K - r) / M + 1
          rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hM]
          omega
        · rintro ⟨t, ht, rfl⟩
          have ht' : t ≤ (K - r) / M := Nat.lt_succ_iff.mp ht
          have hmul : t * M ≤ K - r := (Nat.le_div_iff_mul_le hM).mp ht'
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [hiff, Nat.add_mul_mod_self_right]
      rw [hbij, Finset.card_image_of_injective, Finset.card_range]
      intro t₁ t₂ h
      dsimp only at h
      have : t₁ * M = t₂ * M := by omega
      exact Nat.eq_of_mul_eq_mul_right hM this
    rw [hcard]
    have hMpos : (0 : ℚ) < (M : ℚ) := by positivity
    have h1 : M * ((K - r) / M) ≤ K - r := Nat.mul_div_le (K - r) M
    have h2 : K - r < M * ((K - r) / M + 1) := by
      have := Nat.lt_div_mul_add hM (a := K - r)
      linarith
    have hMC_eq : M * C = M * ((K - r) / M) + M := by dsimp [C]; ring
    have hC1 : (M : ℚ) * (C : ℚ) ≤ (K : ℚ) + (M : ℚ) := by
      have : M * C ≤ K + M := by omega
      exact_mod_cast this
    have hC2 : (K : ℚ) ≤ (M : ℚ) * (C : ℚ) + (M : ℚ) := by
      have h2' : K - r < M * C := by simpa [C] using h2
      have : K ≤ M * C + M := by omega
      exact_mod_cast this
    have hKM : ((K : ℚ) / (M : ℚ)) * (M : ℚ) = (K : ℚ) := div_mul_cancel₀ _ hMpos.ne'
    rw [abs_le]
    constructor <;> nlinarith

private lemma card_Icc_mod_coprime_approx (K : ℕ) :
    ∀ (P : Finset ℕ) (M a : ℕ), 0 < M →
    (∀ p ∈ P, p.Prime) → (∀ p ∈ P, ¬ p ∣ M) →
    |(((Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M] ∧ ∀ p ∈ P, ¬ p ∣ k)).card : ℚ) -
      ((K : ℚ) / (M : ℚ)) * ∏ p ∈ P, (1 - 1 / (p : ℚ))| ≤ (2 : ℚ) ^ P.card := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro M a hM _ _
    simpa using card_Icc_mod_approx K M a hM
  | @insert p P hpP ih =>
    intro M a hM hprime hndvd
    have hp : p.Prime := hprime p (Finset.mem_insert_self p P)
    have hpM : ¬ p ∣ M := hndvd p (Finset.mem_insert_self p P)
    have hPprime : ∀ q ∈ P, q.Prime := fun q hq => hprime q (Finset.mem_insert_of_mem hq)
    have hPndvd : ∀ q ∈ P, ¬ q ∣ M := fun q hq => hndvd q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p M := hp.coprime_iff_not_dvd.mpr hpM
    have hPndvd' : ∀ q ∈ P, ¬ q ∣ (p * M) := by
      intro q hq hqpm
      rcases (hPprime q hq).dvd_mul.mp hqpm with hqp | hqM
      · rcases hp.eq_one_or_self_of_dvd q hqp with h1 | h2
        · exact (hPprime q hq).ne_one h1
        · subst h2; exact hpP hq
      · exact hPndvd q hq hqM
    let crt := Nat.chineseRemainder hcop 0 a
    set a' := crt.val
    have ha'_p : a' ≡ 0 [MOD p] := crt.property.1
    have ha'_M : a' ≡ a [MOD M] := crt.property.2
    have hsplit :
        ((Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M] ∧ ∀ q ∈ insert p P, ¬ q ∣ k)).card +
        ((Finset.Icc 1 K).filter (fun k => k ≡ a' [MOD (p * M)] ∧ ∀ q ∈ P, ¬ q ∣ k)).card =
        ((Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M] ∧ ∀ q ∈ P, ¬ q ∣ k)).card := by
      set A := (Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M] ∧ ∀ q ∈ P, ¬ q ∣ k)
      have h1 : (Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M] ∧ ∀ q ∈ insert p P, ¬ q ∣ k) =
          A.filter (fun k => ¬ p ∣ k) := by
        ext k; simp [A, and_assoc, and_left_comm, and_comm]
      have h2 : (Finset.Icc 1 K).filter (fun k => k ≡ a' [MOD (p * M)] ∧ ∀ q ∈ P, ¬ q ∣ k) =
          A.filter (fun k => p ∣ k) := by
        ext k
        simp only [A, Finset.mem_filter, Finset.mem_Icc]
        constructor
        · rintro ⟨hk, hmod, hP⟩
          have hp_k : k ≡ a' [MOD p] := hmod.of_dvd (dvd_mul_right p M)
          have hM_k : k ≡ a' [MOD M] := hmod.of_dvd (dvd_mul_left M p)
          exact ⟨⟨hk, hM_k.trans ha'_M, hP⟩, Nat.dvd_of_mod_eq_zero (hp_k.trans ha'_p)⟩
        · rintro ⟨⟨hk, hM_k, hP⟩, hpk⟩
          have hp_k : k ≡ a' [MOD p] :=
            (Nat.modEq_zero_iff_dvd.mpr hpk).trans ha'_p.symm
          have hM_k' : k ≡ a' [MOD M] := hM_k.trans ha'_M.symm
          exact ⟨hk, (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hp_k, hM_k'⟩, hP⟩
      rw [h1, h2, ← Finset.card_union_of_disjoint]
      · congr 1; ext k; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      · rw [Finset.disjoint_left]; intro k hk1 hk2
        exact (Finset.mem_filter.mp hk1).2 (Finset.mem_filter.mp hk2).2
    have hih1 := ih M a hM hPprime hPndvd
    have hih2 := ih (p * M) a' (Nat.mul_pos hp.pos hM) hPprime hPndvd'
    rw [Finset.prod_insert hpP, Finset.card_insert_of_notMem hpP]
    have hcard_q :
        (((Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M] ∧ ∀ q ∈ insert p P, ¬ q ∣ k)).card : ℚ) =
        (((Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M] ∧ ∀ q ∈ P, ¬ q ∣ k)).card : ℚ) -
        (((Finset.Icc 1 K).filter (fun k => k ≡ a' [MOD (p * M)] ∧ ∀ q ∈ P, ¬ q ∣ k)).card : ℚ) := by
      have hq : (((Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M] ∧ ∀ q ∈ insert p P, ¬ q ∣ k)).card : ℚ) +
          (((Finset.Icc 1 K).filter (fun k => k ≡ a' [MOD (p * M)] ∧ ∀ q ∈ P, ¬ q ∣ k)).card : ℚ) =
          (((Finset.Icc 1 K).filter (fun k => k ≡ a [MOD M] ∧ ∀ q ∈ P, ¬ q ∣ k)).card : ℚ) := by
        exact_mod_cast hsplit
      linarith
    have hmain : ((K : ℚ) / (M : ℚ)) * ((1 - 1 / (p : ℚ)) * ∏ q ∈ P, (1 - 1 / (q : ℚ))) =
        ((K : ℚ) / (M : ℚ)) * ∏ q ∈ P, (1 - 1 / (q : ℚ)) -
        ((K : ℚ) / ((p * M : ℕ) : ℚ)) * ∏ q ∈ P, (1 - 1 / (q : ℚ)) := by
      push_cast
      have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      have hM0 : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
      field_simp
    rw [hcard_q, hmain]
    have htri : ∀ x y a₁ a₂ : ℚ, |x - a₁| ≤ (2 : ℚ) ^ P.card → |y - a₂| ≤ (2 : ℚ) ^ P.card →
        |(x - y) - (a₁ - a₂)| ≤ (2 : ℚ) ^ (P.card + 1) := by
      intro x y a₁ a₂ h1 h2
      rw [show (x - y) - (a₁ - a₂) = (x - a₁) - (y - a₂) by ring, pow_succ]
      calc |(x - a₁) - (y - a₂)| ≤ |x - a₁| + |y - a₂| := abs_sub _ _
        _ ≤ (2 : ℚ) ^ P.card + (2 : ℚ) ^ P.card := add_le_add h1 h2
        _ = (2 : ℚ) ^ P.card * 2 := by ring
    exact htri _ _ _ _ hih1 hih2

-- 2.2 Congruence roots mod q^a (pure ℕ on Finset.range — zero Fintype/ZMod headaches!)

private lemma card_sq_mod_odd_prime_pow_le_two {q a c : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (ha : 1 ≤ a) :
    ((Finset.range (q ^ a)).filter
      (fun x => x ^ 2 ≡ c [MOD q ^ a] ∧ (2 ≤ a → ¬ q ∣ x))).card ≤ 2 := by
  set N := q ^ a
  have hNpos : 0 < N := pow_pos hq.pos a
  set F := (Finset.range N).filter (fun x => x ^ 2 ≡ c [MOD N] ∧ (2 ≤ a → ¬ q ∣ x))
  by_cases hemp : F = ∅
  · simp [hemp]
  · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
    have hx₀_lt : x₀ < N := Finset.mem_range.mp (Finset.mem_filter.mp hx₀).1
    have hx₀_mod : x₀ ^ 2 ≡ c [MOD N] := (Finset.mem_filter.mp hx₀).2.1
    have hsub : F ⊆ {x₀, N - x₀} := by
      intro x hx
      have hx_lt : x < N := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hx_mod : x ^ 2 ≡ x₀ ^ 2 [MOD N] := (Finset.mem_filter.mp hx).2.1.trans hx₀_mod.symm
      have hdvd_z : ((q : ℤ) ^ a) ∣ ((x : ℤ) - (x₀ : ℤ)) * ((x : ℤ) + (x₀ : ℤ)) := by
        have h1 : ((x : ℤ) ^ 2) ≡ ((x₀ : ℤ) ^ 2) [ZMOD ((q : ℤ) ^ a)] := by
          exact_mod_cast hx_mod
        have h2 := Int.modEq_iff_dvd.mp h1.symm
        have heq : ((x : ℤ) - (x₀ : ℤ)) * ((x : ℤ) + (x₀ : ℤ)) = (x : ℤ) ^ 2 - (x₀ : ℤ) ^ 2 := by ring
        rw [heq]; exact h2
      have hq_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
      have hor : ((q : ℤ) ^ a) ∣ ((x : ℤ) - (x₀ : ℤ)) ∨ ((q : ℤ) ^ a) ∣ ((x : ℤ) + (x₀ : ℤ)) := by
        by_cases ha1 : a = 1
        · subst ha1
          simpa using hq_int.dvd_or_dvd (by simpa using hdvd_z)
        · have ha2 : 2 ≤ a := by omega
          have hqx₀ : ¬ q ∣ x₀ := (Finset.mem_filter.mp hx₀).2.2 ha2
          have hnotboth : ¬ ((q : ℤ) ∣ ((x : ℤ) - (x₀ : ℤ)) ∧ (q : ℤ) ∣ ((x : ℤ) + (x₀ : ℤ))) := by
            rintro ⟨hd1, hd2⟩
            have hsum := dvd_sub hd2 hd1
            have h2x0 : (q : ℤ) ∣ 2 * (x₀ : ℤ) := by
              have : ((x : ℤ) + (x₀ : ℤ)) - ((x : ℤ) - (x₀ : ℤ)) = 2 * (x₀ : ℤ) := by ring
              rwa [this] at hsum
            have hnat : q ∣ 2 * x₀ := Int.ofNat_dvd.mp (by exact_mod_cast h2x0)
            rcases hq.dvd_mul.mp hnat with h2 | hx0
            · rcases Nat.prime_two.eq_one_or_self_of_dvd q h2 with h | h
              · exact hq.ne_one h
              · exact hq2 h
            · exact hqx₀ hx0
          by_cases h1 : (q : ℤ) ∣ ((x : ℤ) - (x₀ : ℤ))
          · left
            have h2 : ¬ (q : ℤ) ∣ ((x : ℤ) + (x₀ : ℤ)) := fun h2 => hnotboth ⟨h1, h2⟩
            exact ((hq_int.coprime_iff_not_dvd.mpr h2).pow_left).dvd_of_dvd_mul_right hdvd_z
          · right
            exact ((hq_int.coprime_iff_not_dvd.mpr h1).pow_left).dvd_of_dvd_mul_left hdvd_z
      have hNz : (0 : ℤ) < (q : ℤ) ^ a := by have := hq.pos; positivity
      have hxz : (x : ℤ) < (q : ℤ) ^ a := by exact_mod_cast hx_lt
      have hx0z : (x₀ : ℤ) < (q : ℤ) ^ a := by exact_mod_cast hx₀_lt
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hor with ⟨k, hk⟩ | ⟨k, hk⟩
      · left
        have hk0 : k = 0 := by nlinarith
        have : (x : ℤ) = (x₀ : ℤ) := by rw [hk0, mul_zero] at hk; linarith
        exact_mod_cast this
      · by_cases hx0_0 : x₀ = 0
        · left
          subst hx0_0
          have hk0 : k = 0 := by
            simp only [Nat.cast_zero, add_zero] at hk
            nlinarith
          have : (x : ℤ) = 0 := by simp only [Nat.cast_zero, add_zero, hk0, mul_zero] at hk; exact hk
          exact_mod_cast this
        · right
          have hk1 : k = 1 := by
            have : (0 : ℤ) < (x₀ : ℤ) := by omega
            nlinarith
          have hsum_eq : (x : ℤ) + (x₀ : ℤ) = (q : ℤ) ^ a := by rw [hk1, mul_one] at hk; exact hk
          have hnat : x + x₀ = N := by exact_mod_cast hsum_eq
          omega
    calc F.card ≤ ({x₀, N - x₀} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two

private lemma sq_mod_prime_sq_card_le_two {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) :
    ((Finset.range (p ^ 2)).filter (fun x => x ^ 2 ≡ m [MOD p ^ 2])).card ≤ 2 := by
  have hsub : (Finset.range (p ^ 2)).filter (fun x => x ^ 2 ≡ m [MOD p ^ 2]) ⊆
      (Finset.range (p ^ 2)).filter (fun x => x ^ 2 ≡ m [MOD p ^ 2] ∧ (2 ≤ 2 → ¬ p ∣ x)) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    refine ⟨hx.1, hx.2, fun _ hpx => ?_⟩
    have hp2x : p ^ 2 ∣ x ^ 2 := pow_dvd_pow_of_dvd hpx 2
    have hpm2 : p ^ 2 ∣ m :=
      Nat.modEq_zero_iff_dvd.mp (hx.2.symm.trans (Nat.modEq_zero_iff_dvd.mpr hp2x))
    exact hpm (dvd_trans (dvd_pow_self p (by norm_num)) hpm2)
  exact le_trans (Finset.card_le_card hsub) (card_sq_mod_odd_prime_pow_le_two hp hp2 (by norm_num))

private def twoPowRootBound (e : ℕ) : ℕ :=
  if e ≤ 1 then 1 else if e = 2 then 2 else 4

private lemma card_sq_mod_two_pow_le (e c : ℕ) :
    ((Finset.range (2 ^ e)).filter
      (fun x => x ^ 2 ≡ c [MOD 2 ^ e] ∧ (2 ≤ e → x % 2 = 1))).card ≤ twoPowRootBound e := by
  unfold twoPowRootBound
  rcases e with _ | _ | _ | e'
  · simp only [Nat.zero_le, ↓reduceIte, pow_zero]
    calc _ ≤ (Finset.range 1).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 1 := Finset.card_range 1
  · simp only [le_refl, ↓reduceIte]
    set F := (Finset.range 2).filter (fun x => x ^ 2 ≡ c [MOD 2] ∧ (2 ≤ 1 → x % 2 = 1))
    have hsub : F ⊆ {c % 2} := by
      intro x hx
      have hxlt : x < 2 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hmod : x ^ 2 % 2 = c % 2 := (Finset.mem_filter.mp hx).2.1
      rw [Finset.mem_singleton]
      have : x = 0 ∨ x = 1 := by omega
      rcases this with rfl | rfl <;> simpa using hmod
    calc F.card ≤ ({c % 2} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
  · simp only [show ¬ (2 ≤ 1) by omega, ↓reduceIte, pow_two]
    set F := (Finset.range (2 * 2)).filter (fun x => x ^ 2 ≡ c [MOD 2 * 2] ∧ (2 ≤ 2 → x % 2 = 1))
    have hsub : F ⊆ {1, 3} := by
      intro x hx
      have hxlt : x < 4 := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hodd : x % 2 = 1 := (Finset.mem_filter.mp hx).2.2 le_rfl
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    calc F.card ≤ ({1, 3} : Finset ℕ).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  · set e := e' + 3
    have he3 : 3 ≤ e := by omega
    have he2 : 2 ≤ e := by omega
    simp only [show ¬ (e ≤ 1) by omega, show e ≠ 2 by omega, ↓reduceIte]
    set N := 2 ^ e
    set H := 2 ^ (e - 1)
    have hNH : N = 2 * H := by
      have he_eq : e = (e' + 2) + 1 := rfl
      have hH_eq : H = 2 ^ (e' + 2) := rfl
      rw [show N = 2 ^ e from rfl, he_eq, pow_add, pow_one, mul_comm, ← hH_eq]
    set F := (Finset.range N).filter (fun x => x ^ 2 ≡ c [MOD N] ∧ (2 ≤ e → x % 2 = 1))
    by_cases hemp : F = ∅
    · simp [hemp]
    · obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hx₀_lt : x₀ < N := Finset.mem_range.mp (Finset.mem_filter.mp hx₀).1
      have hx₀_mod : x₀ ^ 2 ≡ c [MOD N] := (Finset.mem_filter.mp hx₀).2.1
      have hx₀_odd : x₀ % 2 = 1 := (Finset.mem_filter.mp hx₀).2.2 he2
      have hsub : F ⊆ {x₀ % H, x₀ % H + H, H - x₀ % H, 2 * H - x₀ % H} := by
        intro x hx
        have hx_lt : x < N := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
        have hx_mod : x ^ 2 ≡ x₀ ^ 2 [MOD N] := (Finset.mem_filter.mp hx).2.1.trans hx₀_mod.symm
        have hx_odd : x % 2 = 1 := (Finset.mem_filter.mp hx).2.2 he2
        have hdvd_z : ((2 : ℤ) ^ e) ∣ ((x : ℤ) - (x₀ : ℤ)) * ((x : ℤ) + (x₀ : ℤ)) := by
          have h1 : ((x : ℤ) ^ 2) ≡ ((x₀ : ℤ) ^ 2) [ZMOD ((2 : ℤ) ^ e)] := by exact_mod_cast hx_mod
          have h2 := Int.modEq_iff_dvd.mp h1.symm
          have heq : ((x : ℤ) - (x₀ : ℤ)) * ((x : ℤ) + (x₀ : ℤ)) = (x : ℤ) ^ 2 - (x₀ : ℤ) ^ 2 := by ring
          rw [heq]; exact h2
        have hnot4 : ¬ ((4 : ℤ) ∣ ((x : ℤ) - (x₀ : ℤ)) ∧ (4 : ℤ) ∣ ((x : ℤ) + (x₀ : ℤ))) := by
          rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
          omega
        have hdvd_H : (H : ℤ) ∣ ((x : ℤ) - (x₀ : ℤ)) ∨ (H : ℤ) ∣ ((x : ℤ) + (x₀ : ℤ)) := by
          have ha_ex : (2 : ℤ) ∣ ((x : ℤ) - (x₀ : ℤ)) := ⟨((x : ℤ) - (x₀ : ℤ)) / 2, by omega⟩
          have hb_ex : (2 : ℤ) ∣ ((x : ℤ) + (x₀ : ℤ)) := ⟨((x : ℤ) + (x₀ : ℤ)) / 2, by omega⟩
          obtain ⟨a, ha⟩ := ha_ex
          obtain ⟨b, hb⟩ := hb_ex
          have hpow : (2 : ℤ) ^ e = 4 * (2 : ℤ) ^ (e - 2) := by
            have : e = (e - 2) + 2 := by omega
            rw [this, pow_add]; norm_num; ring
          have hHz : (H : ℤ) = 2 * (2 : ℤ) ^ (e - 2) := by
            have : e - 1 = (e - 2) + 1 := by omega
            dsimp [H]; rw [this, pow_add, pow_one, mul_comm]
          have h2ab : (2 : ℤ) ^ (e - 2) ∣ a * b := by
            rw [ha, hb, hpow] at hdvd_z
            have : 4 * (2 : ℤ) ^ (e - 2) ∣ 4 * (a * b) := by
              simpa [show 2 * a * (2 * b) = 4 * (a * b) by ring] using hdvd_z
            exact (mul_dvd_mul_iff_left (by norm_num : (4 : ℤ) ≠ 0)).mp this
          have h2prime : Prime (2 : ℤ) := Nat.prime_iff_prime_int.mp Nat.prime_two
          by_cases ha2 : (2 : ℤ) ∣ a
          · left
            have hb2 : ¬ (2 : ℤ) ∣ b := by
              intro ⟨b', hb'⟩
              obtain ⟨a', ha'⟩ := ha2
              exact hnot4 ⟨⟨a', by omega⟩, ⟨b', by omega⟩⟩
            have hda := ((h2prime.coprime_iff_not_dvd.mpr hb2).pow_left).dvd_of_dvd_mul_right h2ab
            rw [hHz, ha]; exact mul_dvd_mul_left 2 hda
          · right
            have hdb := ((h2prime.coprime_iff_not_dvd.mpr ha2).pow_left).dvd_of_dvd_mul_left h2ab
            rw [hHz, hb]; exact mul_dvd_mul_left 2 hdb
        have hHpos : 0 < H := pow_pos (by norm_num) _
        have hx0m_lt : x₀ % H < H := Nat.mod_lt x₀ hHpos
        have hx0m_pos : 0 < x₀ % H := by
          have h2H : 2 ∣ H := dvd_pow_self 2 (by omega)
          have : (x₀ % H) % 2 = 1 := by rw [Nat.mod_mod_of_dvd x₀ h2H]; exact hx₀_odd
          omega
        have hx_lt2H : x < 2 * H := hNH ▸ hx_lt
        have hdiv := Nat.div_add_mod x H
        have hq : x / H < 2 := (Nat.div_lt_iff_lt_mul hHpos).mpr (by linarith)
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hdvd_H with hd | hd
        · have hmodH : x % H = x₀ % H := by
            have hz : (x : ℤ) ≡ (x₀ : ℤ) [ZMOD (H : ℤ)] := (Int.modEq_iff_dvd.mpr hd).symm
            exact_mod_cast hz
          have hq01 : x / H = 0 ∨ x / H = 1 :=
            Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hq)
          rcases hq01 with h0 | h1
          · left; rw [h0, mul_zero, zero_add] at hdiv; omega
          · right; left; rw [h1, mul_one] at hdiv; omega
        · have hsum_dvd : H ∣ (x + x₀) := Int.ofNat_dvd.mp (by exact_mod_cast hd)
          have hsum_mod : (x % H + x₀ % H) % H = 0 := by
            rw [← Nat.add_mod]; exact Nat.mod_eq_zero_of_dvd hsum_dvd
          have hxm : x % H = H - x₀ % H := by
            have hlt : x % H < H := Nat.mod_lt x hHpos
            have hne0 : x % H + x₀ % H ≠ 0 := by omega
            have hlt2 : x % H + x₀ % H < 2 * H := by omega
            obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero hsum_mod
            have ht_ge1 : 1 ≤ t := by
              by_contra h0; have ht0 : t = 0 := by omega
              rw [ht0, mul_zero] at ht; omega
            have ht1 : t = 1 := by nlinarith
            rw [ht1, mul_one] at ht; omega
          have hq01 : x / H = 0 ∨ x / H = 1 :=
            Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.lt_succ_iff.mp hq)
          rcases hq01 with h0 | h1
          · right; right; left; rw [h0, mul_zero, zero_add] at hdiv; omega
          · right; right; right; rw [h1, mul_one] at hdiv; omega
      calc F.card ≤ ({x₀ % H, x₀ % H + H, H - x₀ % H, 2 * H - x₀ % H} : Finset ℕ).card :=
            Finset.card_le_card hsub
        _ ≤ 4 := by
          have h1 := Finset.card_insert_le (x₀ % H) {x₀ % H + H, H - x₀ % H, 2 * H - x₀ % H}
          have h2 := Finset.card_insert_le (x₀ % H + H) {H - x₀ % H, 2 * H - x₀ % H}
          have h3 := Finset.card_le_two (a := H - x₀ % H) (b := 2 * H - x₀ % H)
          omega

-- Pure ℕ CRT product bound on Finset.range (a * b)
private lemma card_filter_range_mul_le {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (Pa Pb Pab : ℕ → Prop) [DecidablePred Pa] [DecidablePred Pb] [DecidablePred Pab]
    (himp : ∀ x < a * b, Pab x → Pa (x % a) ∧ Pb (x % b)) :
    ((Finset.range (a * b)).filter Pab).card ≤
      ((Finset.range a).filter Pa).card * ((Finset.range b).filter Pb).card := by
  have h1 : ((Finset.range (a * b)).filter Pab).card ≤
      (((Finset.range a).filter Pa) ×ˢ ((Finset.range b).filter Pb)).card := by
    refine Finset.card_le_card_of_injOn (fun x => (x % a, x % b)) ?_ ?_
    · intro x hx
      have hxlt : x < a * b := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
      have hP := (Finset.mem_filter.mp hx).2
      have ⟨hPa, hPb⟩ := himp x hxlt hP
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨Nat.mod_lt x ha, hPa⟩, ⟨Nat.mod_lt x hb, hPb⟩⟩
    · intro x₁ hx₁ x₂ hx₂ heq
      have h1lt : x₁ < a * b := Finset.mem_range.mp (Finset.mem_filter.mp hx₁).1
      have h2lt : x₂ < a * b := Finset.mem_range.mp (Finset.mem_filter.mp hx₂).1
      have ha_eq : x₁ ≡ x₂ [MOD a] := congrArg Prod.fst heq
      have hb_eq : x₁ ≡ x₂ [MOD b] := congrArg Prod.snd heq
      have hab : x₁ ≡ x₂ [MOD a * b] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨ha_eq, hb_eq⟩
      change x₁ % (a * b) = x₂ % (a * b) at hab
      rwa [Nat.mod_eq_of_lt h1lt, Nat.mod_eq_of_lt h2lt] at hab
  simpa [Finset.card_product] using h1

private lemma card_sq_mod_odd_prod_le :
    ∀ (Q : Finset ℕ) (f : ℕ → ℕ),
    (∀ q ∈ Q, q.Prime ∧ q ≠ 2 ∧ 1 ≤ f q) →
    ∀ (c : ℕ),
    ((Finset.range (∏ q ∈ Q, q ^ f q)).filter
      (fun x => x ^ 2 ≡ c [MOD ∏ q ∈ Q, q ^ f q] ∧
        ∀ q ∈ Q, 2 ≤ f q → ¬ q ∣ x)).card ≤ 2 ^ Q.card := by
  intro Q
  induction Q using Finset.induction_on with
  | empty =>
    intro f _ c
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero]
    calc _ ≤ (Finset.range 1).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 1 := Finset.card_range 1
  | @insert q Q hqQ ih =>
    intro f hf c
    have hq : q.Prime := (hf q (Finset.mem_insert_self q Q)).1
    have hq2 : q ≠ 2 := (hf q (Finset.mem_insert_self q Q)).2.1
    have hfq : 1 ≤ f q := (hf q (Finset.mem_insert_self q Q)).2.2
    have hQ : ∀ p ∈ Q, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f p := fun p hp => hf p (Finset.mem_insert_of_mem hp)
    set M := ∏ p ∈ Q, p ^ f p
    have hMpos : 0 < M := Finset.prod_pos fun p hp => pow_pos (hQ p hp).1.pos _
    have hcop : Nat.Coprime (q ^ f q) M := by
      refine Nat.Coprime.prod_right fun p hp => ?_
      have hp_pr := (hQ p hp).1
      have hne : q ≠ p := fun h => hqQ (h ▸ hp)
      exact ((hq.coprime_iff_not_dvd.mpr fun hd =>
        hne ((hp_pr.eq_one_or_self_of_dvd q hd).resolve_left hq.ne_one)).pow_left _).pow_right _
    rw [Finset.prod_insert hqQ, Finset.card_insert_of_notMem hqQ, pow_succ']
    have hcrt := card_filter_range_mul_le (pow_pos hq.pos _) hMpos hcop
      (fun x => x ^ 2 ≡ c [MOD q ^ f q] ∧ (2 ≤ f q → ¬ q ∣ x))
      (fun y => y ^ 2 ≡ c [MOD M] ∧ ∀ p ∈ Q, 2 ≤ f p → ¬ p ∣ y)
      (fun x => x ^ 2 ≡ c [MOD q ^ f q * M] ∧ ∀ p ∈ insert q Q, 2 ≤ f p → ¬ p ∣ x)
      (by
        intro x _ ⟨hxsq, hxnd⟩
        constructor
        · refine ⟨?_, fun hfq2 hqdvd => ?_⟩
          · have h1 : (x % q ^ f q) ^ 2 ≡ x ^ 2 [MOD q ^ f q] := (Nat.mod_modEq x _).pow 2
            exact h1.trans (hxsq.of_dvd (dvd_mul_right _ _))
          · have hqpow : q ∣ q ^ f q := dvd_pow_self q (by omega)
            have hdiv := Nat.div_add_mod x (q ^ f q)
            have : q ∣ x := by
              have h1 := dvd_add (dvd_mul_of_dvd_left hqpow (x / q ^ f q)) hqdvd
              rwa [hdiv] at h1
            exact hxnd q (Finset.mem_insert_self q Q) hfq2 this
        · refine ⟨?_, fun p hp hfp2 hpdvd => ?_⟩
          · have h1 : (x % M) ^ 2 ≡ x ^ 2 [MOD M] := (Nat.mod_modEq x M).pow 2
            exact h1.trans (hxsq.of_dvd (dvd_mul_left M _))
          · have hpM : p ∣ M :=
              dvd_trans (dvd_pow_self p (by omega)) (Finset.dvd_prod_of_mem _ hp)
            have hdiv := Nat.div_add_mod x M
            have : p ∣ x := by
              have h1 := dvd_add (dvd_mul_of_dvd_left hpM (x / M)) hpdvd
              rwa [hdiv] at h1
            exact hxnd p (Finset.mem_insert_of_mem hp) hfp2 this)
    exact le_trans hcrt (Nat.mul_le_mul (card_sq_mod_odd_prime_pow_le_two hq hq2 hfq) (ih f hQ c))

private lemma card_sq_mod_m_le {m : ℕ} (hm : 0 < m) (c : ℕ) :
    let e := m.factorization 2
    let m_odd := m / 2 ^ e
    let Q := m_odd.primeFactors
    ((Finset.range m).filter
      (fun x => x ^ 2 ≡ c [MOD m] ∧ (2 ≤ e → x % 2 = 1) ∧
        ∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ x)).card ≤
      twoPowRootBound e * 2 ^ Q.card := by
  intro e m_odd Q
  have h2dvd : 2 ^ e ∣ m := Nat.ordProj_dvd m 2
  have hm_eq : 2 ^ e * m_odd = m := Nat.mul_div_cancel' h2dvd
  have hm_odd_pos : 0 < m_odd := by
    by_contra h0
    have hm0 : m_odd = 0 := Nat.eq_zero_of_not_pos h0
    rw [hm0, mul_zero] at hm_eq
    omega
  have h2ndvd : ¬ 2 ∣ m_odd := by
    intro ⟨t, ht⟩
    have h2e1 : 2 ^ (e + 1) ∣ m := ⟨t, by rw [← hm_eq, ht, pow_succ]; ring⟩
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm.ne').mp h2e1
    omega
  have hcop : Nat.Coprime (2 ^ e) m_odd :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr h2ndvd).pow_left e
  have hfact_eq : ∀ q ∈ Q, m_odd.factorization q = m.factorization q := by
    intro q hq
    have hq2 : q ≠ 2 := by rintro rfl; exact h2ndvd (Nat.dvd_of_mem_primeFactors hq)
    rw [← hm_eq, Nat.factorization_mul (pow_ne_zero e (by norm_num)) hm_odd_pos.ne',
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_of_ne hq2, zero_add]
  have hm_odd_prod : ∏ q ∈ Q, q ^ m.factorization q = m_odd := by
    calc ∏ q ∈ Q, q ^ m.factorization q
        = ∏ q ∈ Q, q ^ m_odd.factorization q :=
          Finset.prod_congr rfl (fun q hq => by rw [hfact_eq q hq])
      _ = m_odd := Nat.prod_factorization_pow_eq_self hm_odd_pos.ne'
  have hQ_ok : ∀ q ∈ Q, q.Prime ∧ q ≠ 2 ∧ 1 ≤ m.factorization q := by
    intro q hq
    have hq_pr := Nat.prime_of_mem_primeFactors hq
    have hq2 : q ≠ 2 := by rintro rfl; exact h2ndvd (Nat.dvd_of_mem_primeFactors hq)
    have hpos : 0 < m_odd.factorization q :=
      Nat.Prime.factorization_pos_of_dvd hq_pr hm_odd_pos.ne' (Nat.dvd_of_mem_primeFactors hq)
    rw [hfact_eq q hq] at hpos
    exact ⟨hq_pr, hq2, hpos⟩
  have hfilt : (Finset.range m).filter
      (fun x => x ^ 2 ≡ c [MOD m] ∧ (2 ≤ e → x % 2 = 1) ∧
        ∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ x) =
      (Finset.range (2 ^ e * m_odd)).filter
      (fun x => x ^ 2 ≡ c [MOD 2 ^ e * m_odd] ∧ (2 ≤ e → x % 2 = 1) ∧
        ∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ x) := by
    simp only [hm_eq]
  rw [hfilt]
  have hcrt := card_filter_range_mul_le (pow_pos (by norm_num) e) hm_odd_pos hcop
    (fun x => x ^ 2 ≡ c [MOD 2 ^ e] ∧ (2 ≤ e → x % 2 = 1))
    (fun y => y ^ 2 ≡ c [MOD m_odd] ∧ ∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ y)
    (fun x => x ^ 2 ≡ c [MOD 2 ^ e * m_odd] ∧ (2 ≤ e → x % 2 = 1) ∧
      ∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ x)
    (by
      intro x _ ⟨hxsq, hxodd, hxnd⟩
      constructor
      · refine ⟨((Nat.mod_modEq x _).pow 2).trans (hxsq.of_dvd (dvd_mul_right _ _)), fun he2 => ?_⟩
        rw [Nat.mod_mod_of_dvd x (dvd_pow_self 2 (by omega))]
        exact hxodd he2
      · refine ⟨((Nat.mod_modEq x _).pow 2).trans (hxsq.of_dvd (dvd_mul_left _ _)),
          fun q hq hfq hqdvd => ?_⟩
        have hqm : q ∣ m_odd := Nat.dvd_of_mem_primeFactors hq
        have hdiv := Nat.div_add_mod x m_odd
        have : q ∣ x := by
          have h1 := dvd_add (dvd_mul_of_dvd_left hqm (x / m_odd)) hqdvd
          rwa [hdiv] at h1
        exact hxnd q hq hfq this)
  have hodd : ((Finset.range m_odd).filter
      (fun y => y ^ 2 ≡ c [MOD m_odd] ∧ ∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ y)).card ≤
      2 ^ Q.card := by
    rw [← hm_odd_prod]
    exact card_sq_mod_odd_prod_le Q (fun q => m.factorization q) hQ_ok c
  exact le_trans hcrt (Nat.mul_le_mul (card_sq_mod_two_pow_le e c) hodd)

-- 2.3 Brahmagupta-Fibonacci solution bound for fixed y: k^2 + y * p^2 = m

private lemma brahmagupta_sol_bound {m y : ℕ} (hm : 4 ≤ m) (hy : 1 ≤ y) :
    let e := m.factorization 2
    let m_odd := m / 2 ^ e
    let Q := m_odd.primeFactors
    let par := if 4 ∣ m then 1 else 0
    let Sol := ((Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m)).filter (fun kp =>
      kp.1 % 2 = par ∧ kp.2.Prime ∧ kp.2 ≠ 2 ∧ ¬ kp.2 ∣ m ∧
      (∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ kp.1) ∧
      kp.1 ^ 2 + y * kp.2 ^ 2 = m)
    2 * Sol.card ≤ twoPowRootBound e * 2 ^ Q.card := by
  intro e m_odd Q par Sol
  have hm_pos : 0 < m := by omega
  have : NeZero m := ⟨hm_pos.ne'⟩
  -- Target c in ℕ representing -y mod m: c = (m - y % m) % m
  set c := (m - y % m) % m
  have hc_zmod : (c : ZMod m) = -(y : ZMod m) := by
    have hylt : y % m < m := Nat.mod_lt y hm_pos
    have hsum : (c : ZMod m) + (y : ZMod m) = 0 := by
      have : (c + y) % m = 0 := by
        dsimp [c]
        rw [Nat.add_mod, Nat.mod_mod]
        by_cases hy0 : y % m = 0
        · rw [hy0, Nat.sub_zero, Nat.mod_self, zero_add, Nat.zero_mod]
        · have hlt : m - y % m < m := Nat.sub_lt hm_pos (Nat.pos_of_ne_zero hy0)
          rw [Nat.mod_eq_of_lt hlt, Nat.sub_add_cancel (le_of_lt hylt), Nat.mod_self]
      have hdvd : m ∣ c + y := Nat.dvd_of_mod_eq_zero this
      exact_mod_cast (ZMod.natCast_eq_zero_iff (c + y) m).mpr hdvd
    exact eq_neg_of_add_eq_zero_left hsum
  set R := (Finset.range m).filter (fun x =>
    x ^ 2 ≡ c [MOD m] ∧ (2 ≤ e → x % 2 = 1) ∧
    ∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ x)
  let fz : ℕ × ℕ → ZMod m := fun kp => (kp.1 : ZMod m) * ((kp.2 : ZMod m)⁻¹)
  let f : ℕ × ℕ → ℕ := fun kp => (fz kp).val
  let g : ℕ × ℕ → ℕ := fun kp => (-(fz kp)).val
  have hf_unit : ∀ kp ∈ Sol, IsUnit (kp.2 : ZMod m) := by
    intro kp hkp
    have hpr : kp.2.Prime := (Finset.mem_filter.mp hkp).2.2.1
    have hnd : ¬ kp.2 ∣ m := (Finset.mem_filter.mp hkp).2.2.2.2.1
    exact (ZMod.isUnit_iff_coprime kp.2 m).mpr (hpr.coprime_iff_not_dvd.mpr hnd)
  have hf_mul : ∀ kp ∈ Sol, fz kp * (kp.2 : ZMod m) = (kp.1 : ZMod m) := by
    intro kp hkp
    dsimp [fz]
    rw [mul_assoc, ZMod.inv_mul_of_unit _ (hf_unit kp hkp), mul_one]
  have hf_sq : ∀ kp ∈ Sol, (fz kp) ^ 2 = (c : ZMod m) := by
    intro kp hkp
    have heq : kp.1 ^ 2 + y * kp.2 ^ 2 = m := (Finset.mem_filter.mp hkp).2.2.2.2.2.2
    have hcast : ((kp.1 : ZMod m) ^ 2) + (y : ZMod m) * ((kp.2 : ZMod m) ^ 2) = 0 := by
      have : ((kp.1 ^ 2 + y * kp.2 ^ 2 : ℕ) : ZMod m) = (m : ZMod m) := by rw [heq]
      rw [ZMod.natCast_self] at this
      push_cast at this; exact this
    have h0 : (fz kp ^ 2 + (y : ZMod m)) * (kp.2 : ZMod m) ^ 2 = 0 := by
      calc (fz kp ^ 2 + (y : ZMod m)) * (kp.2 : ZMod m) ^ 2
          = (fz kp * (kp.2 : ZMod m)) ^ 2 + (y : ZMod m) * (kp.2 : ZMod m) ^ 2 := by ring
        _ = (kp.1 : ZMod m) ^ 2 + (y : ZMod m) * (kp.2 : ZMod m) ^ 2 := by rw [hf_mul kp hkp]
        _ = 0 := hcast
    have h1 : fz kp ^ 2 + (y : ZMod m) = 0 := ((hf_unit kp hkp).pow 2).mul_left_eq_zero.mp h0
    rw [hc_zmod]
    exact eq_neg_of_add_eq_zero_left h1
  have hmem_R : ∀ (z : ZMod m), z ^ 2 = (c : ZMod m) →
      (2 ≤ e → z.val % 2 = 1) →
      (∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ z.val) → z.val ∈ R := by
    intro z hzsq hzodd hznd
    simp only [R, Finset.mem_filter, Finset.mem_range]
    refine ⟨z.val_lt, ?_, hzodd, hznd⟩
    exact (ZMod.natCast_eq_natCast_iff _ _ m).mp (by push_cast; rw [ZMod.natCast_zmod_val, hzsq])
  have hf_mem : ∀ kp ∈ Sol, f kp ∈ R := by
    intro kp hkp
    have hmem := (Finset.mem_filter.mp hkp).2
    have hmul := hf_mul kp hkp
    apply hmem_R (fz kp) (hf_sq kp hkp)
    · intro he2
      have h4m : 4 ∣ m := dvd_trans (Nat.pow_dvd_pow 2 he2) (Nat.ordProj_dvd m 2)
      have h2m : 2 ∣ m := dvd_trans (by norm_num : 2 ∣ 4) h4m
      have hk_odd : kp.1 % 2 = 1 := by simp [par, h4m] at hmem; exact hmem.1
      have hmod2 : ((fz kp).val * kp.2) % 2 = kp.1 % 2 := by
        have hzeq : (((fz kp).val * kp.2 : ℕ) : ZMod m) = (kp.1 : ZMod m) := by
          push_cast; rw [ZMod.natCast_zmod_val]; exact hmul
        exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hzeq).of_dvd h2m
      by_contra hnot
      have h0 : (fz kp).val % 2 = 0 := by omega
      have : ((fz kp).val * kp.2) % 2 = 0 := by rw [Nat.mul_mod, h0]; simp
      omega
    · intro q hq hfq hqdvd
      have hqm : q ∣ m :=
        dvd_trans (Nat.dvd_of_mem_primeFactors hq) (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m 2))
      have hzeq : (((fz kp).val * kp.2 : ℕ) : ZMod m) = (kp.1 : ZMod m) := by
        push_cast; rw [ZMod.natCast_zmod_val]; exact hmul
      have hmodq : (fz kp).val * kp.2 ≡ kp.1 [MOD q] :=
        ((ZMod.natCast_eq_natCast_iff _ _ _).mp hzeq).of_dvd hqm
      have hq_k : q ∣ kp.1 :=
        Nat.modEq_zero_iff_dvd.mp (hmodq.symm.trans (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hqdvd _)))
      exact hmem.2.2.2.2.1 q hq hfq hq_k
  have hg_mem : ∀ kp ∈ Sol, g kp ∈ R := by
    intro kp hkp
    have hfR := hf_mem kp hkp
    have hf_props := (Finset.mem_filter.mp hfR).2
    apply hmem_R (-(fz kp)) (by rw [neg_sq]; exact hf_sq kp hkp)
    · intro he2
      have h2m : 2 ∣ m :=
        dvd_trans (by norm_num : 2 ∣ 4) (dvd_trans (Nat.pow_dvd_pow 2 he2) (Nat.ordProj_dvd m 2))
      have hodd : (fz kp).val % 2 = 1 := hf_props.2.1 he2
      rw [ZMod.neg_val]
      split_ifs with h0
      · exfalso; rw [h0] at hodd; simp at hodd
      · have hlt := (fz kp).val_lt
        obtain ⟨t, ht⟩ := h2m
        omega
    · intro q hq hfq hqdvd
      have hqm : q ∣ m :=
        dvd_trans (Nat.dvd_of_mem_primeFactors hq) (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m 2))
      have hnd : ¬ q ∣ (fz kp).val := hf_props.2.2 q hq hfq
      rw [ZMod.neg_val] at hqdvd
      split_ifs at hqdvd with h0
      · exact hnd (by rw [h0]; simp)
      · have hlt := (fz kp).val_lt
        have : q ∣ (fz kp).val := by
          have := Nat.dvd_sub hqm hqdvd
          rwa [Nat.sub_sub_self (le_of_lt hlt)] at this
        exact hnd this
  have hfz_inj : Set.InjOn fz Sol := by
    intro kp₁ h₁ kp₂ h₂ hfeq
    have hm₁ := (Finset.mem_filter.mp h₁).2
    have hm₂ := (Finset.mem_filter.mp h₂).2
    have heq₁ : kp₁.1 ^ 2 + y * kp₁.2 ^ 2 = m := hm₁.2.2.2.2.2
    have heq₂ : kp₂.1 ^ 2 + y * kp₂.2 ^ 2 = m := hm₂.2.2.2.2.2
    have hcross : ((kp₁.1 : ZMod m) * (kp₂.2 : ZMod m)) = ((kp₂.1 : ZMod m) * (kp₁.2 : ZMod m)) := by
      calc (kp₁.1 : ZMod m) * (kp₂.2 : ZMod m)
          = (fz kp₁ * (kp₁.2 : ZMod m)) * (kp₂.2 : ZMod m) := by rw [hf_mul kp₁ h₁]
        _ = (fz kp₂ * (kp₂.2 : ZMod m)) * (kp₁.2 : ZMod m) := by rw [hfeq]; ring
        _ = (kp₂.1 : ZMod m) * (kp₁.2 : ZMod m) := by rw [hf_mul kp₂ h₂]
    have hmod : kp₁.1 * kp₂.2 ≡ kp₂.1 * kp₁.2 [MOD m] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).mp (by push_cast; exact hcross)
    have hk1_pos : 1 ≤ kp₁.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₁).1).1).1
    have hk2_pos : 1 ≤ kp₂.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₂).1).1).1
    have hp1_pos : 0 < kp₁.2 := hm₁.2.1.pos
    have hp2_pos : 0 < kp₂.2 := hm₂.2.1.pos
    have hlt₁ : kp₁.1 * kp₂.2 < m := by
      have hk1 : kp₁.1 ^ 2 < m := by nlinarith
      have hp2 : kp₂.2 ^ 2 < m := by nlinarith
      have : (kp₁.1 * kp₂.2) ^ 2 < m ^ 2 := by
        calc (kp₁.1 * kp₂.2) ^ 2 = kp₁.1 ^ 2 * kp₂.2 ^ 2 := by ring
          _ < m * m := Nat.mul_lt_mul_of_lt_of_lt hk1 hp2
          _ = m ^ 2 := (sq m).symm
      nlinarith
    have hlt₂ : kp₂.1 * kp₁.2 < m := by
      have hk2 : kp₂.1 ^ 2 < m := by nlinarith
      have hp1 : kp₁.2 ^ 2 < m := by nlinarith
      have : (kp₂.1 * kp₁.2) ^ 2 < m ^ 2 := by
        calc (kp₂.1 * kp₁.2) ^ 2 = kp₂.1 ^ 2 * kp₁.2 ^ 2 := by ring
          _ < m * m := Nat.mul_lt_mul_of_lt_of_lt hk2 hp1
          _ = m ^ 2 := (sq m).symm
      nlinarith
    have hprod_eq : kp₁.1 * kp₂.2 = kp₂.1 * kp₁.2 := by
      change (kp₁.1 * kp₂.2) % m = (kp₂.1 * kp₁.2) % m at hmod
      rwa [Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂] at hmod
    have hcop₁ : Nat.Coprime kp₁.1 kp₁.2 := by
      rw [Nat.coprime_comm, hm₁.2.1.coprime_iff_not_dvd]
      intro hd
      exact hm₁.2.2.2.1 (by
        rw [← heq₁]; exact dvd_add (dvd_pow hd (by norm_num))
          (dvd_mul_of_dvd_right (dvd_pow_self _ (by norm_num)) _))
    have hcop₂ : Nat.Coprime kp₂.1 kp₂.2 := by
      rw [Nat.coprime_comm, hm₂.2.1.coprime_iff_not_dvd]
      intro hd
      exact hm₂.2.2.2.1 (by
        rw [← heq₂]; exact dvd_add (dvd_pow hd (by norm_num))
          (dvd_mul_of_dvd_right (dvd_pow_self _ (by norm_num)) _))
    have hp_eq : kp₁.2 = kp₂.2 := Nat.dvd_antisymm
      (hcop₁.symm.dvd_of_dvd_mul_left ⟨kp₂.1, by linarith⟩)
      (hcop₂.symm.dvd_of_dvd_mul_left ⟨kp₁.1, by linarith⟩)
    have hk_eq : kp₁.1 = kp₂.1 :=
      Nat.eq_of_mul_eq_mul_right hp2_pos (by rw [hp_eq] at hprod_eq; exact hprod_eq)
    exact Prod.ext hk_eq hp_eq
  have hf_inj : Set.InjOn f Sol := fun _ h₁ _ h₂ h =>
    hfz_inj h₁ h₂ (ZMod.val_injective m h)
  have hg_inj : Set.InjOn g Sol := fun _ h₁ _ h₂ h =>
    hfz_inj h₁ h₂ (neg_inj.mp (ZMod.val_injective m h))
  have hf_disj : Disjoint (Sol.image f) (Sol.image g) := by
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    obtain ⟨kp₁, h₁, rfl⟩ := Finset.mem_image.mp hx₁
    obtain ⟨kp₂, h₂, hgeq⟩ := Finset.mem_image.mp hx₂
    have hfeq : -(fz kp₂) = fz kp₁ := ZMod.val_injective m hgeq
    have hm₁ := (Finset.mem_filter.mp h₁).2
    have hm₂ := (Finset.mem_filter.mp h₂).2
    have heq₁ : kp₁.1 ^ 2 + y * kp₁.2 ^ 2 = m := hm₁.2.2.2.2.2
    have heq₂ : kp₂.1 ^ 2 + y * kp₂.2 ^ 2 = m := hm₂.2.2.2.2.2
    have hsum0 : ((kp₁.1 * kp₂.2 + kp₂.1 * kp₁.2 : ℕ) : ZMod m) = 0 := by
      push_cast
      calc (kp₁.1 : ZMod m) * (kp₂.2 : ZMod m) + (kp₂.1 : ZMod m) * (kp₁.2 : ZMod m)
          = (fz kp₁ * (kp₁.2 : ZMod m)) * (kp₂.2 : ZMod m) +
            (fz kp₂ * (kp₂.2 : ZMod m)) * (kp₁.2 : ZMod m) := by rw [hf_mul kp₁ h₁, hf_mul kp₂ h₂]
        _ = (fz kp₁ + fz kp₂) * ((kp₁.2 : ZMod m) * (kp₂.2 : ZMod m)) := by ring
        _ = (-(fz kp₂) + fz kp₂) * ((kp₁.2 : ZMod m) * (kp₂.2 : ZMod m)) := by rw [← hfeq]
        _ = 0 := by ring
    have hmdvd : m ∣ (kp₁.1 * kp₂.2 + kp₂.1 * kp₁.2) :=
      (ZMod.natCast_eq_zero_iff _ _).mp hsum0
    have hpos : 0 < kp₁.1 * kp₂.2 + kp₂.1 * kp₁.2 := by
      have hk1 : 1 ≤ kp₁.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp h₁).1).1).1
      have hp2 : 1 ≤ kp₂.2 := hm₂.2.1.one_le
      nlinarith
    have hge_m : m ≤ kp₁.1 * kp₂.2 + kp₂.1 * kp₁.2 := Nat.le_of_dvd hpos hmdvd
    set A : ℤ := (kp₁.1 : ℤ) * (kp₂.1 : ℤ) - (y : ℤ) * (kp₁.2 : ℤ) * (kp₂.2 : ℤ)
    set B : ℤ := (kp₁.1 : ℤ) * (kp₂.2 : ℤ) + (kp₂.1 : ℤ) * (kp₁.2 : ℤ)
    have hbf : A ^ 2 + (y : ℤ) * B ^ 2 = (m : ℤ) ^ 2 := by
      have h1z : (kp₁.1 : ℤ) ^ 2 + (y : ℤ) * (kp₁.2 : ℤ) ^ 2 = (m : ℤ) := by exact_mod_cast heq₁
      have h2z : (kp₂.1 : ℤ) ^ 2 + (y : ℤ) * (kp₂.2 : ℤ) ^ 2 = (m : ℤ) := by exact_mod_cast heq₂
      calc A ^ 2 + (y : ℤ) * B ^ 2
          = ((kp₁.1 : ℤ) ^ 2 + (y : ℤ) * (kp₁.2 : ℤ) ^ 2) *
            ((kp₂.1 : ℤ) ^ 2 + (y : ℤ) * (kp₂.2 : ℤ) ^ 2) := by dsimp [A, B]; ring
        _ = (m : ℤ) * (m : ℤ) := by rw [h1z, h2z]
        _ = (m : ℤ) ^ 2 := (sq _).symm
    have hBm : (m : ℤ) ≤ B := by dsimp [B]; exact_mod_cast hge_m
    have hB2 : (m : ℤ) ^ 2 ≤ B ^ 2 := by
      have hm_nn : (0 : ℤ) ≤ (m : ℤ) := Nat.cast_nonneg m
      rw [sq, sq]
      exact mul_le_mul hBm hBm hm_nn (le_trans hm_nn hBm)
    have hA2 : 0 ≤ A ^ 2 := sq_nonneg A
    by_cases hy2 : 2 ≤ y
    · have hy2z : (2 : ℤ) ≤ (y : ℤ) := by exact_mod_cast hy2
      have hm2pos : (0 : ℤ) < (m : ℤ) ^ 2 := by
        have : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm_pos
        positivity
      have hmul2 : 2 * (m : ℤ) ^ 2 ≤ (y : ℤ) * B ^ 2 :=
        mul_le_mul hy2z hB2 (le_of_lt hm2pos) (by omega)
      linarith
    · have hy1 : y = 1 := by omega
      have hnot4 : ¬ 4 ∣ m := by
        intro h4m
        have hk1 : kp₁.1 % 2 = 1 := by simp [par, h4m] at hm₁; exact hm₁.1
        have hp1 : kp₁.2 % 2 = 1 := (hm₁.2.1.eq_two_or_odd).resolve_left hm₁.2.2.1
        have hsq1 : (kp₁.1 ^ 2 + 1 * kp₁.2 ^ 2) % 4 = 2 := by
          have : kp₁.1 % 4 = 1 ∨ kp₁.1 % 4 = 3 := by omega
          have : kp₁.2 % 4 = 1 ∨ kp₁.2 % 4 = 3 := by omega
          rcases ‹kp₁.1 % 4 = 1 ∨ kp₁.1 % 4 = 3› with h1' | h1' <;>
          rcases ‹kp₁.2 % 4 = 1 ∨ kp₁.2 % 4 = 3› with h2' | h2' <;>
          simp [Nat.add_mod, Nat.pow_mod, h1', h2']
        rw [hy1] at heq₁
        have hm0 : m % 4 = 0 := Nat.mod_eq_zero_of_dvd h4m
        omega
      have hk1_even : kp₁.1 % 2 = 0 := by simp [par, hnot4] at hm₁; exact hm₁.1
      have hp1_odd : kp₁.2 % 2 = 1 := (hm₁.2.1.eq_two_or_odd).resolve_left hm₁.2.2.1
      have hp2_odd : kp₂.2 % 2 = 1 := (hm₂.2.1.eq_two_or_odd).resolve_left hm₂.2.2.1
      have hA_ne : A ≠ 0 := by
        intro hA0
        have heq_z : (kp₁.1 : ℤ) * (kp₂.1 : ℤ) = (kp₁.2 : ℤ) * (kp₂.2 : ℤ) := by
          dsimp [A] at hA0; rw [hy1, Nat.cast_one] at hA0; linarith
        have hnat : kp₁.1 * kp₂.1 = kp₁.2 * kp₂.2 := by exact_mod_cast heq_z
        have hl : (kp₁.1 * kp₂.1) % 2 = 0 := by rw [Nat.mul_mod, hk1_even]; simp
        have hr : (kp₁.2 * kp₂.2) % 2 = 1 := by rw [Nat.mul_mod, hp1_odd, hp2_odd]
        omega
      have hA_pos : 1 ≤ A ^ 2 := by
        have h1 : (1 : ℤ) ≤ |A| := Int.one_le_abs hA_ne
        rw [← sq_abs, sq]
        simpa using mul_le_mul h1 h1 (by norm_num : (0 : ℤ) ≤ 1) (abs_nonneg A)
      rw [hy1, Nat.cast_one, one_mul] at hbf
      linarith
  have hsub_union : Sol.image f ∪ Sol.image g ⊆ R := by
    intro x hx
    rcases Finset.mem_union.mp hx with h | h
    · obtain ⟨kp, hkp, rfl⟩ := Finset.mem_image.mp h; exact hf_mem kp hkp
    · obtain ⟨kp, hkp, rfl⟩ := Finset.mem_image.mp h; exact hg_mem kp hkp
  calc 2 * Sol.card
      = Sol.card + Sol.card := by ring
    _ = (Sol.image f).card + (Sol.image g).card := by
        rw [Finset.card_image_of_injOn hf_inj, Finset.card_image_of_injOn hg_inj]
    _ = (Sol.image f ∪ Sol.image g).card := (Finset.card_union_of_disjoint hf_disj).symm
    _ ≤ R.card := Finset.card_le_card hsub_union
    _ ≤ twoPowRootBound e * 2 ^ Q.card := card_sq_mod_m_le hm_pos c

-- 2.4 Master Elementary Sieve Theorem

private lemma bad_prime_exists {m k : ℕ}
    (hk0 : 0 < k) (hk2 : k ^ 2 < m)
    (hpar : k % 2 = if 4 ∣ m then 1 else 0)
    (hcop : ∀ q ∈ m.primeFactors, q ≠ 2 → q ^ 2 ∣ m → ¬ q ∣ k)
    (hnsf : ¬ Squarefree (m - k ^ 2)) :
    ∃ p, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ m ∧ p ≤ (m - 1).sqrt ∧ p ^ 2 ∣ m - k ^ 2 := by
  have hpos : 0 < m - k ^ 2 := by omega
  have hex : ∃ p, p.Prime ∧ p ^ 2 ∣ m - k ^ 2 := by
    by_contra hall
    push Not at hall
    apply hnsf
    intro d hd
    rw [Nat.isUnit_iff]
    by_contra hd1
    have hd0 : d ≠ 0 := by rintro rfl; simp at hd; omega
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
    have hp2 : p ^ 2 ∣ m - k ^ 2 := by
      rw [sq]; exact dvd_trans (Nat.mul_dvd_mul hpd hpd) hd
    exact hall p hp hp2
  obtain ⟨p, hp, hp2dvd⟩ := hex
  have hp_ne2 : p ≠ 2 := by
    rintro rfl
    have h4 : 4 ∣ m - k ^ 2 := by simpa using hp2dvd
    by_cases h4m : 4 ∣ m
    · rw [if_pos h4m] at hpar
      have hk4 : k % 4 = 1 ∨ k % 4 = 3 := by omega
      have hsq4 : k ^ 2 % 4 = 1 := by
        rcases hk4 with h | h <;> simp [Nat.pow_mod, h]
      have hm4 : m % 4 = 0 := Nat.mod_eq_zero_of_dvd h4m
      have hd4 : (m - k ^ 2) % 4 = 0 := Nat.mod_eq_zero_of_dvd h4
      omega
    · rw [if_neg h4m] at hpar
      have h2k : 2 ∣ k := Nat.dvd_of_mod_eq_zero hpar
      have h4k : 4 ∣ k ^ 2 := by obtain ⟨t, rfl⟩ := h2k; exact ⟨t ^ 2, by ring⟩
      have : 4 ∣ m := by
        have := dvd_add h4 h4k
        rwa [Nat.sub_add_cancel (le_of_lt hk2)] at this
      exact h4m this
  have hndvd_m : ¬ p ∣ m := by
    intro hpm
    have hpk2 : p ∣ k ^ 2 := by
      have hp_sub : p ∣ m - k ^ 2 := dvd_trans (dvd_pow_self p (by norm_num)) hp2dvd
      have := Nat.dvd_sub hpm hp_sub
      rwa [Nat.sub_sub_self (le_of_lt hk2)] at this
    have hpk : p ∣ k := hp.dvd_of_dvd_pow hpk2
    have hp2k : p ^ 2 ∣ k ^ 2 := pow_dvd_pow_of_dvd hpk 2
    have hp2m : p ^ 2 ∣ m := by
      have := dvd_add hp2dvd hp2k
      rwa [Nat.sub_add_cancel (le_of_lt hk2)] at this
    have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, by omega⟩
    exact hcop p hmem hp_ne2 hp2m hpk
  have hp_le : p ≤ (m - 1).sqrt := by
    rw [Nat.le_sqrt]
    have h1 : p ^ 2 ≤ m - k ^ 2 := Nat.le_of_dvd hpos hp2dvd
    have : 1 ≤ k ^ 2 := by nlinarith
    rw [← sq]; omega
  exact ⟨p, hp, hp_ne2, hndvd_m, hp_le, hp2dvd⟩

private lemma bad_small_prime_card {m : ℕ} (P : Finset ℕ) (hP_pr : ∀ q ∈ P, q.Prime)
    (hP_odd : ∀ q ∈ P, q ≠ 2) (hP_dvd : ∀ q ∈ P, q ∣ m)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) :
    let K := (m - 1).sqrt
    let par := if 4 ∣ m then 1 else 0
    let S := (Finset.Icc 1 K).filter (fun k => k % 2 = par ∧ ∀ q ∈ P, ¬ q ∣ k)
    ((S.filter (fun k => p ^ 2 ∣ m - k ^ 2)).card : ℚ) ≤
      (2 / (p : ℚ) ^ 2) * (((K : ℚ) / 2) * ∏ q ∈ P, (1 - 1 / (q : ℚ))) +
        2 * (2 : ℚ) ^ P.card := by
  intro K par S
  set Roots := (Finset.range (p ^ 2)).filter (fun x => x ^ 2 ≡ m [MOD p ^ 2])
  have hRoots_le : Roots.card ≤ 2 := sq_mod_prime_sq_card_le_two hp hp2 hpm
  have hcop2p : Nat.Coprime 2 (p ^ 2) :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr fun h2p =>
      hp2 ((hp.eq_one_or_self_of_dvd 2 h2p).resolve_left (by norm_num)).symm).pow_right 2
  have hcover : S.filter (fun k => p ^ 2 ∣ m - k ^ 2) ⊆
      Roots.biUnion (fun x =>
        (Finset.Icc 1 K).filter (fun k =>
          k ≡ (Nat.chineseRemainder hcop2p par x).val [MOD (2 * p ^ 2)] ∧ ∀ q ∈ P, ¬ q ∣ k)) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rcases hk with ⟨hkS, hp2dvd⟩
    rw [Finset.mem_filter] at hkS
    rcases hkS with ⟨hkIcc, hkpar, hkP⟩
    have hk2_lt : k ^ 2 < m := by
      have hkK : k ≤ (m - 1).sqrt := (Finset.mem_Icc.mp hkIcc).2
      have hsq : k * k ≤ m - 1 := Nat.le_sqrt.mp hkK
      have hm1 : 1 ≤ m := by
        by_contra h0
        have hm0 : m = 0 := by omega
        subst hm0
        simp only [Nat.zero_sub, Nat.sqrt_zero] at hkK
        have := (Finset.mem_Icc.mp hkIcc).1; omega
      rw [sq]; omega
    have hk_sq_mod : k ^ 2 ≡ m [MOD p ^ 2] := by
      have hd : p ^ 2 ∣ m - k ^ 2 := hp2dvd
      exact (Nat.modEq_iff_dvd' (le_of_lt hk2_lt)).mpr hd
    set x := k % p ^ 2
    have hx_mem : x ∈ Roots := by
      simp only [Roots, Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt k (pow_pos hp.pos 2), ?_⟩
      exact ((Nat.mod_modEq k (p ^ 2)).pow 2).trans hk_sq_mod
    rw [Finset.mem_biUnion]
    refine ⟨x, hx_mem, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨hkIcc, ?_, hkP⟩
    set crt := Nat.chineseRemainder hcop2p par x
    have h2_eq : k ≡ crt.val [MOD 2] := by
      have h1 : k ≡ par [MOD 2] := by
        change k % 2 = par % 2
        rw [hkpar]
        dsimp [par]; split_ifs <;> rfl
      exact h1.trans crt.property.1.symm
    have hp_eq : k ≡ crt.val [MOD p ^ 2] :=
      (Nat.mod_modEq k (p ^ 2)).symm.trans crt.property.2.symm
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop2p).mp ⟨h2_eq, hp_eq⟩
  have hPndvd : ∀ q ∈ P, ¬ q ∣ (2 * p ^ 2) := by
    intro q hq hqmul
    rcases (hP_pr q hq).dvd_mul.mp hqmul with hq2 | hqp2
    · exact hP_odd q hq ((Nat.prime_two.eq_one_or_self_of_dvd q hq2).resolve_left (hP_pr q hq).ne_one)
    · have hqp : q ∣ p := (hP_pr q hq).dvd_of_dvd_pow hqp2
      have hqp_eq : q = p := (hp.eq_one_or_self_of_dvd q hqp).resolve_left (hP_pr q hq).ne_one
      subst hqp_eq
      exact hpm (hP_dvd q hq)
  have hsum_le : ((S.filter (fun k => p ^ 2 ∣ m - k ^ 2)).card : ℚ) ≤
      ∑ x ∈ Roots, (((Finset.Icc 1 K).filter (fun k =>
        k ≡ (Nat.chineseRemainder hcop2p par x).val [MOD (2 * p ^ 2)] ∧ ∀ q ∈ P, ¬ q ∣ k)).card : ℚ) := by
    exact_mod_cast le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
  have hterm : ∀ x ∈ Roots,
      (((Finset.Icc 1 K).filter (fun k =>
        k ≡ (Nat.chineseRemainder hcop2p par x).val [MOD (2 * p ^ 2)] ∧ ∀ q ∈ P, ¬ q ∣ k)).card : ℚ) ≤
      ((K : ℚ) / (2 * (p : ℚ) ^ 2)) * ∏ q ∈ P, (1 - 1 / (q : ℚ)) + (2 : ℚ) ^ P.card := by
    intro x _
    have ha := card_Icc_mod_coprime_approx K P (2 * p ^ 2)
      (Nat.chineseRemainder hcop2p par x).val (Nat.mul_pos (by norm_num) (pow_pos hp.pos 2)) hP_pr hPndvd
    have hle := (abs_le.mp ha).2
    push_cast at hle
    linarith
  set phiP : ℚ := ∏ q ∈ P, (1 - 1 / (q : ℚ))
  have hprod_nn : 0 ≤ phiP := by
    apply Finset.prod_nonneg
    intro q hq
    have hq1 : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast (hP_pr q hq).one_le
    rw [sub_nonneg, div_le_one (by linarith)]
    exact hq1
  calc ((S.filter (fun k => p ^ 2 ∣ m - k ^ 2)).card : ℚ)
      ≤ ∑ x ∈ Roots, (((K : ℚ) / (2 * (p : ℚ) ^ 2)) * phiP + (2 : ℚ) ^ P.card) :=
        le_trans hsum_le (Finset.sum_le_sum hterm)
    _ = (Roots.card : ℚ) * (((K : ℚ) / (2 * (p : ℚ) ^ 2)) * phiP + (2 : ℚ) ^ P.card) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℚ) * (((K : ℚ) / (2 * (p : ℚ) ^ 2)) * phiP + (2 : ℚ) ^ P.card) := by
        have hnn : 0 ≤ ((K : ℚ) / (2 * (p : ℚ) ^ 2)) * phiP + (2 : ℚ) ^ P.card := by
          have : 0 ≤ (K : ℚ) / (2 * (p : ℚ) ^ 2) := by positivity
          have : 0 ≤ (2 : ℚ) ^ P.card := by positivity
          nlinarith
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hRoots_le) hnn
    _ = (2 / (p : ℚ) ^ 2) * (((K : ℚ) / 2) * phiP) + 2 * (2 : ℚ) ^ P.card := by
        ring

private lemma bad_mid_prime_card_le {m : ℕ} (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) :
    let K := (m - 1).sqrt
    let par := if 4 ∣ m then 1 else 0
    let S := (Finset.Icc 1 K).filter (fun k => k % 2 = par ∧ ∀ q ∈ P, ¬ q ∣ k)
    ((S.filter (fun k => p ^ 2 ∣ m - k ^ 2)).card : ℚ) ≤ (K : ℚ) / (p : ℚ) ^ 2 + 2 := by
  intro K par S
  set S0 := (Finset.Icc 1 K).filter (fun k => k % 2 = par ∧ ∀ q ∈ (∅ : Finset ℕ), ¬ q ∣ k)
  have hsub : S.filter (fun k => p ^ 2 ∣ m - k ^ 2) ⊆ S0.filter (fun k => p ^ 2 ∣ m - k ^ 2) := by
    intro k hk
    rw [Finset.mem_filter] at hk ⊢
    refine ⟨?_, hk.2⟩
    have hkS := Finset.mem_filter.mp hk.1
    exact Finset.mem_filter.mpr ⟨hkS.1, hkS.2.1, fun q hq => (Finset.notMem_empty q hq).elim⟩
  have hcard_le : ((S.filter (fun k => p ^ 2 ∣ m - k ^ 2)).card : ℚ) ≤
      ((S0.filter (fun k => p ^ 2 ∣ m - k ^ 2)).card : ℚ) := by
    exact_mod_cast Finset.card_le_card hsub
  have h0 := bad_small_prime_card (m := m) (∅ : Finset ℕ)
    (fun _ h => (Finset.notMem_empty _ h).elim)
    (fun _ h => (Finset.notMem_empty _ h).elim)
    (fun _ h => (Finset.notMem_empty _ h).elim) hp hp2 hpm
  change ((S0.filter (fun k => p ^ 2 ∣ m - k ^ 2)).card : ℚ) ≤
    (2 / (p : ℚ) ^ 2) * (((K : ℚ) / 2) * ∏ q ∈ (∅ : Finset ℕ), (1 - 1 / (q : ℚ))) +
      2 * (2 : ℚ) ^ (∅ : Finset ℕ).card at h0
  rw [Finset.prod_empty, mul_one, Finset.card_empty, pow_zero] at h0
  have heq : 2 / (p : ℚ) ^ 2 * ((K : ℚ) / 2) + 2 * 1 = (K : ℚ) / (p : ℚ) ^ 2 + 2 := by ring
  linarith

private lemma bad_mid_prime_card_gt_sqrt {m : ℕ} (P : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpm : ¬ p ∣ m) (hgt : (m - 1).sqrt < p ^ 2) :
    let K := (m - 1).sqrt
    let par := if 4 ∣ m then 1 else 0
    let S := (Finset.Icc 1 K).filter (fun k => k % 2 = par ∧ ∀ q ∈ P, ¬ q ∣ k)
    (S.filter (fun k => p ^ 2 ∣ m - k ^ 2)).card ≤ 1 := by
  intro K par S
  rw [Finset.card_le_one]
  intro k₁ hk₁ k₂ hk₂
  by_contra hne
  wlog hlt : k₁ < k₂ generalizing k₁ k₂
  · exact this k₂ hk₂ k₁ hk₁ (Ne.symm hne) (by omega)
  have h1S := (Finset.mem_filter.mp hk₁).1
  have h2S := (Finset.mem_filter.mp hk₂).1
  have hd1 : p ^ 2 ∣ m - k₁ ^ 2 := (Finset.mem_filter.mp hk₁).2
  have hd2 : p ^ 2 ∣ m - k₂ ^ 2 := (Finset.mem_filter.mp hk₂).2
  have hk1_I := (Finset.mem_filter.mp h1S).1
  have hk2_I := (Finset.mem_filter.mp h2S).1
  have hk1_par : k₁ % 2 = par := (Finset.mem_filter.mp h1S).2.1
  have hk2_par : k₂ % 2 = par := (Finset.mem_filter.mp h2S).2.1
  have hm1 : 1 ≤ m := by
    have hk2K : k₂ ≤ (m - 1).sqrt := (Finset.mem_Icc.mp hk2_I).2
    by_contra h0
    have hm0 : m = 0 := by omega
    subst hm0
    simp only [Nat.zero_sub, Nat.sqrt_zero] at hk2K
    have := (Finset.mem_Icc.mp hk1_I).1; omega
  have hk2_sq_lt : k₂ ^ 2 < m := by
    have hsq : k₂ * k₂ ≤ m - 1 := Nat.le_sqrt.mp (Finset.mem_Icc.mp hk2_I).2
    rw [sq]; omega
  have hk1_sq_le_hk2_sq : k₁ ^ 2 ≤ k₂ ^ 2 := Nat.pow_le_pow_left (le_of_lt hlt) 2
  have hk1_sq_lt : k₁ ^ 2 < m := by omega
  have hdvd_diff : p ^ 2 ∣ (k₂ - k₁) * (k₂ + k₁) := by
    have hsub_le : m - k₂ ^ 2 ≤ m - k₁ ^ 2 := by omega
    have heq : (k₂ - k₁) * (k₂ + k₁) = (m - k₁ ^ 2) - (m - k₂ ^ 2) := by
      zify [le_of_lt hlt, le_of_lt hk1_sq_lt, le_of_lt hk2_sq_lt, hsub_le]
      ring
    rw [heq]
    exact Nat.dvd_sub hd1 hd2
  -- Both k₂ - k₁ and k₂ + k₁ are even!
  have h2sub : 2 ∣ k₂ - k₁ := by omega
  have h2add : 2 ∣ k₂ + k₁ := by omega
  obtain ⟨u, hu⟩ := h2sub
  obtain ⟨v, hv⟩ := h2add
  have hupos : 0 < u := by omega
  have hvpos : 0 < v := by omega
  have hvlt : v < K := by
    have hk2K : k₂ ≤ K := (Finset.mem_Icc.mp hk2_I).2
    omega
  have hult : u < K := by omega
  have hp2_uv : p ^ 2 ∣ u * v := by
    have hmul : (k₂ - k₁) * (k₂ + k₁) = 4 * (u * v) := by rw [hu, hv]; ring
    rw [hmul] at hdvd_diff
    have hcop : Nat.Coprime (p ^ 2) 4 := by
      have h2p : Nat.Coprime p 2 := hp.coprime_iff_not_dvd.mpr fun h =>
        hp2 ((Nat.prime_two.eq_one_or_self_of_dvd p h).resolve_left hp.ne_one)
      simpa using (h2p.pow_left 2).pow_right 2
    exact hcop.dvd_of_dvd_mul_left hdvd_diff
  have hnotboth : ¬ (p ∣ u ∧ p ∣ v) := by
    rintro ⟨hpu, hpv⟩
    have hpk2 : p ∣ k₂ := by
      have : k₂ = u + v := by omega
      rw [this]; exact dvd_add hpu hpv
    have : p ∣ m := by
      have h1 : p ∣ m - k₂ ^ 2 := dvd_trans (dvd_pow_self p (by norm_num)) hd2
      have h2 : p ∣ k₂ ^ 2 := dvd_pow hpk2 (by norm_num)
      have h3 := dvd_add h1 h2
      rwa [Nat.sub_add_cancel (le_of_lt hk2_sq_lt)] at h3
    exact hpm this
  have hor : p ^ 2 ∣ u ∨ p ^ 2 ∣ v := by
    by_cases hpu : p ∣ u
    · left
      have hpv : ¬ p ∣ v := fun hpv => hnotboth ⟨hpu, hpv⟩
      exact ((hp.coprime_iff_not_dvd.mpr hpv).pow_left 2).dvd_of_dvd_mul_right hp2_uv
    · right
      exact ((hp.coprime_iff_not_dvd.mpr hpu).pow_left 2).dvd_of_dvd_mul_left hp2_uv
  rcases hor with hd | hd
  · have := Nat.le_of_dvd hupos hd; omega
  · have := Nat.le_of_dvd hvpos hd; omega

-- Count of y in Icc 1 Y matching a congruence class mod M
private lemma card_Icc_filter_mod_le (Y M r : ℕ) (hM : 0 < M) (hr : 1 ≤ r) (hrM : r ≤ M) :
    ((Finset.Icc 1 Y).filter (fun y => y % M = r % M)).card ≤ (Y + M - r) / M := by
  by_cases hYr : Y < r
  · have hemp : (Finset.Icc 1 Y).filter (fun y => y % M = r % M) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro y hy hmod
      rw [Finset.mem_Icc] at hy
      have hylt : y < M := by omega
      rw [Nat.mod_eq_of_lt hylt] at hmod
      by_cases hrm : r = M
      · rw [hrm, Nat.mod_self] at hmod; omega
      · rw [Nat.mod_eq_of_lt (by omega)] at hmod; omega
    rw [hemp, Finset.card_empty]; exact Nat.zero_le _
  · push Not at hYr
    have hcard : ((Finset.Icc 1 Y).filter (fun y => y % M = r % M)).card = (Y - r) / M + 1 := by
      have hbij : (Finset.Icc 1 Y).filter (fun y => y % M = r % M) =
          (Finset.range ((Y - r) / M + 1)).image (fun t => r + t * M) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨⟨hy1, hyY⟩, hmod⟩
          have hyr : r ≤ y := by
            by_contra hlt; push Not at hlt
            have hylt : y < M := by omega
            rw [Nat.mod_eq_of_lt hylt] at hmod
            by_cases hrm : r = M
            · rw [hrm, Nat.mod_self] at hmod; omega
            · rw [Nat.mod_eq_of_lt (by omega)] at hmod; omega
          obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hyr).mp hmod.symm
          have ht' : y - r = t * M := by rw [mul_comm]; exact ht
          refine ⟨t, ?_, by omega⟩
          rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hM]; omega
        · rintro ⟨t, ht, rfl⟩
          have hmul : t * M ≤ Y - r := (Nat.le_div_iff_mul_le hM).mp (Nat.lt_succ_iff.mp ht)
          exact ⟨⟨by omega, by omega⟩, by rw [Nat.add_mul_mod_self_right]⟩
      rw [hbij, Finset.card_image_of_injective, Finset.card_range]
      intro t₁ t₂ h; dsimp only at h
      exact Nat.eq_of_mul_eq_mul_right hM (by omega)
    rw [hcard]
    have heq : Y + M - r = (Y - r) + M := by omega
    rw [heq, Nat.add_div_right _ hM]

private def largeTailBound (m W : ℕ) : ℚ :=
  let e := m.factorization 2
  let m_odd := m / 2 ^ e
  let w := m_odd.primeFactors.card
  let Y := (m - 1) / W ^ 2
  if e ≤ 1 then (((Y + 3) / 4 : ℕ) : ℚ) * ((2 : ℚ) ^ w / 2)
  else if e = 2 then (((Y + 5) / 8 : ℕ) : ℚ) * (2 : ℚ) ^ w
  else (((Y + 1) / 8 : ℕ) : ℚ) * (2 * (2 : ℚ) ^ w)

private lemma bad_large_card {m W : ℕ} (hm : 4 ≤ m) (hW : 1 ≤ W) :
    let K := (m - 1).sqrt
    let par := if 4 ∣ m then 1 else 0
    let P := m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)
    let S := (Finset.Icc 1 K).filter (fun k => k % 2 = par ∧ ∀ q ∈ P, ¬ q ∣ k)
    let BadLarge := S.filter (fun k =>
      ∃ p ∈ Finset.Ioc W K, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2)
    (BadLarge.card : ℚ) ≤ largeTailBound m W := by
  intro K par P S BadLarge
  set e := m.factorization 2
  set m_odd := m / 2 ^ e
  set Q := m_odd.primeFactors
  set Y := (m - 1) / W ^ 2
  have hm_pos : 0 < m := by omega
  have h2dvd : 2 ^ e ∣ m := Nat.ordProj_dvd m 2
  have hm_eq : 2 ^ e * m_odd = m := Nat.mul_div_cancel' h2dvd
  have h2ndvd : ¬ 2 ∣ m_odd := by
    intro ⟨t, ht⟩
    have h2e1 : 2 ^ (e + 1) ∣ m := ⟨t, by rw [← hm_eq, ht, pow_succ]; ring⟩
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm_pos.ne').mp h2e1
    omega
  -- For each k ∈ BadLarge, choose p and y = (m - k^2) / p^2
  -- First define the set of all valid pairs (k, p) with p > W
  set Pairs := ((Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m)).filter (fun kp =>
    kp.1 % 2 = par ∧ kp.2.Prime ∧ kp.2 ≠ 2 ∧ ¬ kp.2 ∣ m ∧
    (∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ kp.1) ∧
    W < kp.2 ∧ kp.1 ^ 2 < m ∧ kp.2 ^ 2 ∣ m - kp.1 ^ 2)
  -- Inject BadLarge into Pairs via Classical.choose
  have hBL_le_Pairs : BadLarge.card ≤ Pairs.card := by
    have hex : ∀ k ∈ BadLarge, ∃ p ∈ Finset.Ioc W K,
        p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2 :=
      fun k hk => (Finset.mem_filter.mp hk).2
    let pick : ℕ → ℕ := fun k => if h : k ∈ BadLarge then (hex k h).choose else 0
    refine Finset.card_le_card_of_injOn (fun k => (k, pick k)) ?_ ?_
    · intro k hk
      have hkS := (Finset.mem_filter.mp hk).1
      have hkIcc := (Finset.mem_filter.mp hkS).1
      have hkpar := (Finset.mem_filter.mp hkS).2.1
      have hkP := (Finset.mem_filter.mp hkS).2.2
      have hp_spec := (hex k hk).choose_spec
      set p := pick k
      have hp_eq : p = (hex k hk).choose := dif_pos hk
      rw [← hp_eq] at hp_spec
      rcases hp_spec with ⟨hpIoc, hpr, hp2, hpm, hp2dvd⟩
      have hk_sq_lt : k ^ 2 < m := by
        have hsq : k * k ≤ m - 1 := Nat.le_sqrt.mp (Finset.mem_Icc.mp hkIcc).2
        rw [sq]; omega
      have hk_le_m : k ≤ m := by nlinarith
      have hp_le_m : p ≤ m := by
        have hsq : p * p ≤ m - 1 := Nat.le_sqrt.mp (Finset.mem_Ioc.mp hpIoc).2
        have hle : p ≤ p * p := Nat.le_mul_self p
        omega
      simp only [Pairs, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      refine ⟨⟨⟨(Finset.mem_Icc.mp hkIcc).1, hk_le_m⟩, ⟨hpr.one_le, hp_le_m⟩⟩,
        hkpar, hpr, hp2, hpm, ?_, (Finset.mem_Ioc.mp hpIoc).1, hk_sq_lt, hp2dvd⟩
      intro q hq hfq
      have hq_pr := Nat.prime_of_mem_primeFactors hq
      have hq2 : q ≠ 2 := by rintro rfl; exact h2ndvd (Nat.dvd_of_mem_primeFactors hq)
      have hq2m : q ^ 2 ∣ m :=
        dvd_trans (Nat.pow_dvd_pow q hfq) (Nat.ordProj_dvd m q)
      have hqm : q ∣ m := dvd_trans (dvd_pow_self q (by norm_num)) hq2m
      have hqP : q ∈ P := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hq_pr, hqm, hm_pos.ne'⟩, hq2, hq2m⟩
      exact hkP q hqP
    · intro k₁ _ k₂ _ h; exact congrArg Prod.fst h
  -- Now partition Pairs by y = (m - k^2) / p^2 ∈ Yset!
  -- Every (k, p) ∈ Pairs has 1 ≤ y ≤ Y and satisfies congruence mod 4 (or mod 8 if 4 ∣ m)
  have hy_bound : ∀ kp ∈ Pairs,
      let y := (m - kp.1 ^ 2) / kp.2 ^ 2
      1 ≤ y ∧ y ≤ Y ∧ kp.1 ^ 2 + y * kp.2 ^ 2 = m := by
    intro kp hkp
    have hm_kp := (Finset.mem_filter.mp hkp).2
    rcases hm_kp with ⟨_, hpr, _, _, _, hpW, hk2lt, hp2dvd⟩
    dsimp only
    have hmul : (m - kp.1 ^ 2) / kp.2 ^ 2 * kp.2 ^ 2 = m - kp.1 ^ 2 :=
      Nat.div_mul_cancel hp2dvd
    have hy1 : 1 ≤ (m - kp.1 ^ 2) / kp.2 ^ 2 :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hp2dvd) (pow_pos hpr.pos 2)
    have hyY : (m - kp.1 ^ 2) / kp.2 ^ 2 ≤ Y := by
      dsimp [Y]
      have hk1 : 1 ≤ kp.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hkp).1).1).1
      have h1sq : 1 ≤ kp.1 ^ 2 := by rw [sq]; exact Nat.mul_le_mul hk1 hk1
      have hnum : m - kp.1 ^ 2 ≤ m - 1 := by omega
      have hden : W ^ 2 ≤ kp.2 ^ 2 := Nat.pow_le_pow_left (le_of_lt hpW) 2
      exact le_trans (Nat.div_le_div_right hnum) (Nat.div_le_div_left hden (pow_pos hW 2))
    exact ⟨hy1, hyY, by omega⟩
  -- Define congruence filter on Yset depending on e
  have h4_iff : 4 ∣ m ↔ 2 ≤ e := by
    have := Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm_pos.ne' (k := 2)
    simpa [e] using this
  have h8_iff : 8 ∣ m ↔ 3 ≤ e := by
    have := Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hm_pos.ne' (k := 3)
    simpa [e] using this
  -- Helper: fiber cardinality over a set Yset of y values
  have hfiber : ∀ (Yset : Finset ℕ), (∀ y ∈ Yset, 1 ≤ y) →
      (∀ kp ∈ Pairs, (m - kp.1 ^ 2) / kp.2 ^ 2 ∈ Yset) →
      (Pairs.card : ℚ) ≤ (Yset.card : ℚ) * ((twoPowRootBound e : ℚ) * (2 : ℚ) ^ Q.card / 2) := by
    intro Yset hYpos hYmem
    have hcov : Pairs ⊆ Yset.biUnion (fun y =>
        ((Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m)).filter (fun kp =>
          kp.1 % 2 = par ∧ kp.2.Prime ∧ kp.2 ≠ 2 ∧ ¬ kp.2 ∣ m ∧
          (∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ kp.1) ∧
          kp.1 ^ 2 + y * kp.2 ^ 2 = m)) := by
      intro kp hkp
      rw [Finset.mem_biUnion]
      refine ⟨(m - kp.1 ^ 2) / kp.2 ^ 2, hYmem kp hkp, ?_⟩
      have hm_kp := Finset.mem_filter.mp hkp
      have hb := hy_bound kp hkp
      rw [Finset.mem_filter]
      exact ⟨hm_kp.1, hm_kp.2.1, hm_kp.2.2.1, hm_kp.2.2.2.1, hm_kp.2.2.2.2.1,
        hm_kp.2.2.2.2.2.1, hb.2.2⟩
    have hsum_le : (Pairs.card : ℚ) ≤
        ∑ y ∈ Yset, ((((Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m)).filter (fun kp =>
          kp.1 % 2 = par ∧ kp.2.Prime ∧ kp.2 ≠ 2 ∧ ¬ kp.2 ∣ m ∧
          (∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ kp.1) ∧
          kp.1 ^ 2 + y * kp.2 ^ 2 = m)).card : ℚ) := by
      exact_mod_cast le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
    have hterm : ∀ y ∈ Yset,
        ((((Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m)).filter (fun kp =>
          kp.1 % 2 = par ∧ kp.2.Prime ∧ kp.2 ≠ 2 ∧ ¬ kp.2 ∣ m ∧
          (∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ kp.1) ∧
          kp.1 ^ 2 + y * kp.2 ^ 2 = m)).card : ℚ) ≤
        (twoPowRootBound e : ℚ) * (2 : ℚ) ^ Q.card / 2 := by
      intro y hy
      have hb := brahmagupta_sol_bound hm (hYpos y hy)
      have hbq : (2 : ℚ) * ((((Finset.Icc 1 m) ×ˢ (Finset.Icc 1 m)).filter (fun kp =>
          kp.1 % 2 = par ∧ kp.2.Prime ∧ kp.2 ≠ 2 ∧ ¬ kp.2 ∣ m ∧
          (∀ q ∈ Q, 2 ≤ m.factorization q → ¬ q ∣ kp.1) ∧
          kp.1 ^ 2 + y * kp.2 ^ 2 = m)).card : ℚ) ≤
          (twoPowRootBound e : ℚ) * (2 : ℚ) ^ Q.card := by exact_mod_cast hb
      linarith
    calc (Pairs.card : ℚ)
        ≤ ∑ _ ∈ Yset, ((twoPowRootBound e : ℚ) * (2 : ℚ) ^ Q.card / 2) :=
          le_trans hsum_le (Finset.sum_le_sum hterm)
      _ = (Yset.card : ℚ) * ((twoPowRootBound e : ℚ) * (2 : ℚ) ^ Q.card / 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Split by e ≤ 1, e = 2, e ≥ 3
  have hBL_q : (BadLarge.card : ℚ) ≤ (Pairs.card : ℚ) := by exact_mod_cast hBL_le_Pairs
  unfold largeTailBound
  dsimp only
  change (BadLarge.card : ℚ) ≤
    if e ≤ 1 then (((Y + 3) / 4 : ℕ) : ℚ) * ((2 : ℚ) ^ Q.card / 2)
    else if e = 2 then (((Y + 5) / 8 : ℕ) : ℚ) * (2 : ℚ) ^ Q.card
    else (((Y + 1) / 8 : ℕ) : ℚ) * (2 * (2 : ℚ) ^ Q.card)
  split_ifs with he1 he2
  · -- e ≤ 1: 4 ∤ m, k even, y ≡ m % 4 (mod 4) with m % 4 ∈ {1, 2, 3}
    have hnot4 : ¬ 4 ∣ m := fun h => by have := h4_iff.mp h; omega
    have hm4_pos : 1 ≤ m % 4 := by
      have : m % 4 ≠ 0 := fun h => hnot4 (Nat.dvd_of_mod_eq_zero h); omega
    set r4 := m % 4
    have hr4_pos : 1 ≤ r4 := hm4_pos
    have hr4_le : r4 ≤ 4 := by dsimp [r4]; omega
    set Yset := (Finset.Icc 1 Y).filter (fun y => y % 4 = r4 % 4)
    have hYcard : Yset.card ≤ (Y + 3) / 4 := by
      have h1 := card_Icc_filter_mod_le Y 4 r4 (by norm_num) hr4_pos hr4_le
      have hle : Y + 4 - r4 ≤ Y + 3 := Nat.sub_le_sub_left hr4_pos (Y + 4)
      exact le_trans h1 (Nat.div_le_div_right hle)
    have hYmem : ∀ kp ∈ Pairs, (m - kp.1 ^ 2) / kp.2 ^ 2 ∈ Yset := by
      intro kp hkp
      have hb := hy_bound kp hkp
      have hkp_m := (Finset.mem_filter.mp hkp).2
      have hk_even : kp.1 % 2 = 0 := by simp [par, hnot4] at hkp_m; exact hkp_m.1
      have hp_odd : kp.2 % 2 = 1 := (hkp_m.2.1.eq_two_or_odd).resolve_left hkp_m.2.2.1
      have hk2_4 : kp.1 ^ 2 % 4 = 0 := by
        have : kp.1 % 4 = 0 ∨ kp.1 % 4 = 2 := by omega
        rcases this with h | h <;> simp [Nat.pow_mod, h]
      have hp2_4 : kp.2 ^ 2 % 4 = 1 := by
        have : kp.2 % 4 = 1 ∨ kp.2 % 4 = 3 := by omega
        rcases this with h | h <;> simp [Nat.pow_mod, h]
      have hmod4 : ((m - kp.1 ^ 2) / kp.2 ^ 2) % 4 = m % 4 := by
        have h := congrArg (· % 4) hb.2.2
        rw [Nat.add_mod, hk2_4, zero_add, Nat.mod_mod, Nat.mul_mod, hp2_4, mul_one, Nat.mod_mod] at h
        exact h
      simp only [Yset, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨hb.1, hb.2.1⟩, ?_⟩
      rw [hmod4]; simp [r4]
    have htb : twoPowRootBound e = 1 := by simp [twoPowRootBound, he1]
    have hf := hfiber Yset (fun y hy => (Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1).1) hYmem
    rw [htb, Nat.cast_one, one_mul] at hf
    have hY_q : (Yset.card : ℚ) ≤ (((Y + 3) / 4 : ℕ) : ℚ) := by exact_mod_cast hYcard
    calc (BadLarge.card : ℚ) ≤ (Pairs.card : ℚ) := hBL_q
      _ ≤ (Yset.card : ℚ) * ((2 : ℚ) ^ Q.card / 2) := hf
      _ ≤ (((Y + 3) / 4 : ℕ) : ℚ) * ((2 : ℚ) ^ Q.card / 2) :=
          mul_le_mul_of_nonneg_right hY_q (by positivity)
  · -- e = 2: 4 ∣ m, 8 ∤ m -> m % 8 = 4, k odd -> k^2 ≡ 1 (mod 8), p^2 ≡ 1 (mod 8) -> y ≡ 3 (mod 8)!
    have h4m : 4 ∣ m := h4_iff.mpr (by omega)
    have hnot8 : ¬ 8 ∣ m := fun h => by have := h8_iff.mp h; omega
    have hm8 : m % 8 = 4 := by
      have : m % 4 = 0 := Nat.mod_eq_zero_of_dvd h4m
      have : m % 8 ≠ 0 := fun h => hnot8 (Nat.dvd_of_mod_eq_zero h)
      omega
    set Yset := (Finset.Icc 1 Y).filter (fun y => y % 8 = 3 % 8)
    have hYcard : Yset.card ≤ (Y + 5) / 8 :=
      card_Icc_filter_mod_le Y 8 3 (by norm_num) (by norm_num) (by norm_num)
    have hYmem : ∀ kp ∈ Pairs, (m - kp.1 ^ 2) / kp.2 ^ 2 ∈ Yset := by
      intro kp hkp
      have hb := hy_bound kp hkp
      have hkp_m := (Finset.mem_filter.mp hkp).2
      have hk_odd : kp.1 % 2 = 1 := by simp [par, h4m] at hkp_m; exact hkp_m.1
      have hp_odd : kp.2 % 2 = 1 := (hkp_m.2.1.eq_two_or_odd).resolve_left hkp_m.2.2.1
      have hsq8 : ∀ n : ℕ, n % 2 = 1 → n ^ 2 % 8 = 1 := by
        intro n hn
        have : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
        rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]
      have hk2_8 := hsq8 kp.1 hk_odd
      have hp2_8 := hsq8 kp.2 hp_odd
      have hmod8 : ((m - kp.1 ^ 2) / kp.2 ^ 2) % 8 = 3 := by
        have h := congrArg (· % 8) hb.2.2
        rw [hm8, Nat.add_mod, hk2_8, Nat.mul_mod, hp2_8, mul_one, Nat.mod_mod] at h
        omega
      simp only [Yset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hb.1, hb.2.1⟩, by rw [hmod8]⟩
    have htb : twoPowRootBound e = 2 := by simp [twoPowRootBound, he2]
    have hf := hfiber Yset (fun y hy => (Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1).1) hYmem
    rw [htb] at hf
    have hsimpl : ((2 : ℕ) : ℚ) * (2 : ℚ) ^ Q.card / 2 = (2 : ℚ) ^ Q.card := by push_cast; ring
    rw [hsimpl] at hf
    have hY_q : (Yset.card : ℚ) ≤ (((Y + 5) / 8 : ℕ) : ℚ) := by exact_mod_cast hYcard
    calc (BadLarge.card : ℚ) ≤ (Pairs.card : ℚ) := hBL_q
      _ ≤ (Yset.card : ℚ) * (2 : ℚ) ^ Q.card := hf
      _ ≤ (((Y + 5) / 8 : ℕ) : ℚ) * (2 : ℚ) ^ Q.card :=
          mul_le_mul_of_nonneg_right hY_q (by positivity)
  · -- e ≥ 3: 8 ∣ m -> m % 8 = 0, k odd, p odd -> y ≡ 7 (mod 8)!
    have h4m : 4 ∣ m := h4_iff.mpr (by omega)
    have h8m : 8 ∣ m := h8_iff.mpr (by omega)
    have hm8 : m % 8 = 0 := Nat.mod_eq_zero_of_dvd h8m
    set Yset := (Finset.Icc 1 Y).filter (fun y => y % 8 = 7 % 8)
    have hYcard : Yset.card ≤ (Y + 1) / 8 :=
      card_Icc_filter_mod_le Y 8 7 (by norm_num) (by norm_num) (by norm_num)
    have hYmem : ∀ kp ∈ Pairs, (m - kp.1 ^ 2) / kp.2 ^ 2 ∈ Yset := by
      intro kp hkp
      have hb := hy_bound kp hkp
      have hkp_m := (Finset.mem_filter.mp hkp).2
      have hk_odd : kp.1 % 2 = 1 := by simp [par, h4m] at hkp_m; exact hkp_m.1
      have hp_odd : kp.2 % 2 = 1 := (hkp_m.2.1.eq_two_or_odd).resolve_left hkp_m.2.2.1
      have hsq8 : ∀ n : ℕ, n % 2 = 1 → n ^ 2 % 8 = 1 := by
        intro n hn
        have : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by omega
        rcases this with h | h | h | h <;> simp [Nat.pow_mod, h]
      have hk2_8 := hsq8 kp.1 hk_odd
      have hp2_8 := hsq8 kp.2 hp_odd
      have hmod8 : ((m - kp.1 ^ 2) / kp.2 ^ 2) % 8 = 7 := by
        have h := congrArg (· % 8) hb.2.2
        rw [hm8, Nat.add_mod, hk2_8, Nat.mul_mod, hp2_8, mul_one, Nat.mod_mod] at h
        omega
      simp only [Yset, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hb.1, hb.2.1⟩, by rw [hmod8]⟩
    have htb : twoPowRootBound e = 4 := by simp [twoPowRootBound, he1, he2]
    have hf := hfiber Yset (fun y hy => (Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1).1) hYmem
    rw [htb] at hf
    have hsimpl : ((4 : ℕ) : ℚ) * (2 : ℚ) ^ Q.card / 2 = 2 * (2 : ℚ) ^ Q.card := by norm_num; ring
    rw [hsimpl] at hf
    have hY_q : (Yset.card : ℚ) ≤ (((Y + 1) / 8 : ℕ) : ℚ) := by exact_mod_cast hYcard
    calc (BadLarge.card : ℚ) ≤ (Pairs.card : ℚ) := hBL_q
      _ ≤ (Yset.card : ℚ) * (2 * (2 : ℚ) ^ Q.card) := hf
      _ ≤ (((Y + 1) / 8 : ℕ) : ℚ) * (2 * (2 : ℚ) ^ Q.card) :=
          mul_le_mul_of_nonneg_right hY_q (by positivity)

-- Master Sieve Theorem!
private lemma master_sieve {m Z W : ℕ} (hm : 16 ≤ m) (hZ : 2 ≤ Z) (hZW : Z ≤ W) :
    let K := (m - 1).sqrt
    let P := m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)
    let phiP : ℚ := ∏ q ∈ P, (1 - 1 / (q : ℚ))
    let Psmall := (Finset.Icc 3 Z).filter (fun p => p.Prime ∧ ¬ p ∣ m)
    let Pmid1 := (Finset.Ioc Z (min W K.sqrt)).filter (fun p => p.Prime)
    let Pmid2 := (Finset.Ioc (max Z K.sqrt) W).filter (fun p => p.Prime)
    (representations m : ℚ) ≥
      ((K : ℚ) / 2) * phiP * (1 - ∑ p ∈ Psmall, (2 / (p : ℚ) ^ 2))
      - (1 + 2 * (Psmall.card : ℚ)) * (2 : ℚ) ^ P.card
      - (K : ℚ) * (∑ p ∈ Pmid1, (1 / (p : ℚ) ^ 2))
      - 2 * (Pmid1.card : ℚ) - (Pmid2.card : ℚ)
      - largeTailBound m W := by
  intro K P phiP Psmall Pmid1 Pmid2
  set par := if 4 ∣ m then 1 else 0
  set S := (Finset.Icc 1 K).filter (fun k => k % 2 = par ∧ ∀ q ∈ P, ¬ q ∣ k)
  set Good := S.filter (fun k => Squarefree (m - k ^ 2))
  set BadSmall := S.filter (fun k => ∃ p ∈ Psmall, p ^ 2 ∣ m - k ^ 2)
  set BadMid1 := S.filter (fun k => ∃ p ∈ Pmid1, ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2)
  set BadMid2 := S.filter (fun k => ∃ p ∈ Pmid2, ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2)
  set BadLarge := S.filter (fun k =>
    ∃ p ∈ Finset.Ioc W K, p.Prime ∧ p ≠ 2 ∧ ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2)
  -- 1) Good ⊆ representations filter
  have hGood_le_rep : Good.card ≤ representations m := by
    unfold representations
    refine Finset.card_le_card fun k hk => ?_
    have hkS := (Finset.mem_filter.mp hk).1
    have hsf := (Finset.mem_filter.mp hk).2
    have hkIcc := (Finset.mem_filter.mp hkS).1
    have hk1 := (Finset.mem_Icc.mp hkIcc).1
    have hkK := (Finset.mem_Icc.mp hkIcc).2
    have hsq : k ^ 2 < m := by
      have : k * k ≤ m - 1 := Nat.le_sqrt.mp hkK
      rw [sq]; omega
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.le_sqrt.mpr (by rw [← sq]; omega)), hk1, hsq, hsf⟩
  -- 2) S ⊆ Good ∪ BadSmall ∪ BadMid1 ∪ BadMid2 ∪ BadLarge
  have hScover : S ⊆ Good ∪ BadSmall ∪ BadMid1 ∪ BadMid2 ∪ BadLarge := by
    intro k hkS
    by_cases hsf : Squarefree (m - k ^ 2)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hkS, hsf⟩))))
    · have hkIcc := (Finset.mem_filter.mp hkS).1
      have hkpar := (Finset.mem_filter.mp hkS).2.1
      have hkP := (Finset.mem_filter.mp hkS).2.2
      have hk1 := (Finset.mem_Icc.mp hkIcc).1
      have hkK := (Finset.mem_Icc.mp hkIcc).2
      have hsq : k ^ 2 < m := by
        have : k * k ≤ m - 1 := Nat.le_sqrt.mp hkK
        rw [sq]; omega
      obtain ⟨p, hp, hp2, hpm, hpK, hp2dvd⟩ := bad_prime_exists hk1 hsq hkpar
        (fun q hq hq2 hq2m => hkP q (Finset.mem_filter.mpr ⟨hq, hq2, hq2m⟩)) hsf
      have hp3 : 3 ≤ p := by have := hp.two_le; omega
      by_cases hpZ : p ≤ Z
      · have hpS : p ∈ Psmall :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hpZ⟩, hp, hpm⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hkS, p, hpS, hp2dvd⟩))))
      · by_cases hpW : p ≤ W
        · by_cases hpsq : p ≤ K.sqrt
          · have hpM1 : p ∈ Pmid1 :=
              Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, le_min hpW hpsq⟩, hp⟩
            exact Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hkS, p, hpM1, hpm, hp2dvd⟩)))
          · have hpM2 : p ∈ Pmid2 :=
              Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨max_lt (by omega) (by omega), hpW⟩, hp⟩
            exact Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hkS, p, hpM2, hpm, hp2dvd⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨hkS, p, Finset.mem_Ioc.mpr ⟨by omega, hpK⟩, hp, hp2, hpm, hp2dvd⟩)
  have hS_le : S.card ≤ Good.card + BadSmall.card + BadMid1.card + BadMid2.card + BadLarge.card := by
    calc S.card ≤ (Good ∪ BadSmall ∪ BadMid1 ∪ BadMid2 ∪ BadLarge).card := Finset.card_le_card hScover
      _ ≤ (Good ∪ BadSmall ∪ BadMid1 ∪ BadMid2).card + BadLarge.card := Finset.card_union_le _ _
      _ ≤ (Good ∪ BadSmall ∪ BadMid1).card + BadMid2.card + BadLarge.card := by
          have := Finset.card_union_le (Good ∪ BadSmall ∪ BadMid1) BadMid2; omega
      _ ≤ (Good ∪ BadSmall).card + BadMid1.card + BadMid2.card + BadLarge.card := by
          have := Finset.card_union_le (Good ∪ BadSmall) BadMid1; omega
      _ ≤ Good.card + BadSmall.card + BadMid1.card + BadMid2.card + BadLarge.card := by
          have := Finset.card_union_le Good BadSmall; omega
  -- 3) Lower bound on S.card
  have hP_pr : ∀ q ∈ P, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hP_odd : ∀ q ∈ P, q ≠ 2 := fun q hq => (Finset.mem_filter.mp hq).2.1
  have hP_dvd : ∀ q ∈ P, q ∣ m := fun q hq => Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hq).1
  have hP_ndvd2 : ∀ q ∈ P, ¬ q ∣ 2 := fun q hq h =>
    hP_odd q hq ((Nat.prime_two.eq_one_or_self_of_dvd q h).resolve_left (hP_pr q hq).ne_one)
  have hS_eq : S = (Finset.Icc 1 K).filter (fun k => k ≡ par [MOD 2] ∧ ∀ q ∈ P, ¬ q ∣ k) := by
    ext k; simp only [S, Finset.mem_filter]
    have hpar_mod : par % 2 = par := by dsimp [par]; split_ifs <;> rfl
    change (k ∈ Finset.Icc 1 K ∧ k % 2 = par ∧ _) ↔ (k ∈ Finset.Icc 1 K ∧ k % 2 = par % 2 ∧ _)
    rw [hpar_mod]
  have hS_lower : ((K : ℚ) / 2) * phiP - (2 : ℚ) ^ P.card ≤ (S.card : ℚ) := by
    have h := (abs_le.mp (card_Icc_mod_coprime_approx K P 2 par (by norm_num) hP_pr hP_ndvd2)).1
    rw [← hS_eq, show ((2 : ℕ) : ℚ) = 2 by norm_num] at h
    linarith
  -- 4) Upper bound on BadSmall.card
  have hBS_le : (BadSmall.card : ℚ) ≤
      (∑ p ∈ Psmall, (2 / (p : ℚ) ^ 2)) * (((K : ℚ) / 2) * phiP) +
        2 * (Psmall.card : ℚ) * (2 : ℚ) ^ P.card := by
    have hcov : BadSmall ⊆ Psmall.biUnion (fun p => S.filter (fun k => p ^ 2 ∣ m - k ^ 2)) := by
      intro k hk
      obtain ⟨hkS, p, hp, hdvd⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hkS, hdvd⟩⟩
    have h1 : (BadSmall.card : ℚ) ≤ ∑ p ∈ Psmall, ((S.filter (fun k => p ^ 2 ∣ m - k ^ 2)).card : ℚ) := by
      exact_mod_cast le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
    have h2 : ∑ p ∈ Psmall, ((S.filter (fun k => p ^ 2 ∣ m - k ^ 2)).card : ℚ) ≤
        ∑ p ∈ Psmall, ((2 / (p : ℚ) ^ 2) * (((K : ℚ) / 2) * phiP) + 2 * (2 : ℚ) ^ P.card) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hpI := (Finset.mem_filter.mp hp).1
      have hpr := (Finset.mem_filter.mp hp).2.1
      have hpm := (Finset.mem_filter.mp hp).2.2
      have hp2 : p ≠ 2 := by have := (Finset.mem_Icc.mp hpI).1; omega
      exact bad_small_prime_card P hP_pr hP_odd hP_dvd hpr hp2 hpm
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul] at h2
    linarith
  -- 5) Upper bound on BadMid1.card
  have hBM1_le : (BadMid1.card : ℚ) ≤ (K : ℚ) * (∑ p ∈ Pmid1, (1 / (p : ℚ) ^ 2)) + 2 * (Pmid1.card : ℚ) := by
    have hcov : BadMid1 ⊆ Pmid1.biUnion (fun p => S.filter (fun k => ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2)) := by
      intro k hk
      obtain ⟨hkS, p, hp, hpm, hdvd⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hkS, hpm, hdvd⟩⟩
    have h1 : (BadMid1.card : ℚ) ≤
        ∑ p ∈ Pmid1, ((S.filter (fun k => ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2)).card : ℚ) := by
      exact_mod_cast le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
    have h2 : ∑ p ∈ Pmid1, ((S.filter (fun k => ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2)).card : ℚ) ≤
        ∑ p ∈ Pmid1, ((K : ℚ) / (p : ℚ) ^ 2 + 2) := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hpI := (Finset.mem_filter.mp hp).1
      have hpr := (Finset.mem_filter.mp hp).2
      have hp2 : p ≠ 2 := by have := (Finset.mem_Ioc.mp hpI).1; omega
      by_cases hpm : p ∣ m
      · have hemp : S.filter (fun k => ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro k _ h; exact h.1 hpm
        rw [hemp, Finset.card_empty, Nat.cast_zero]; positivity
      · have hsub : S.filter (fun k => ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2) ⊆
            S.filter (fun k => p ^ 2 ∣ m - k ^ 2) :=
          fun _ hk => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2.2⟩
        exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (bad_mid_prime_card_le P hpr hp2 hpm)
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h2
    have hmul : ∑ p ∈ Pmid1, (K : ℚ) / (p : ℚ) ^ 2 = (K : ℚ) * ∑ p ∈ Pmid1, (1 / (p : ℚ) ^ 2) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
    rw [hmul] at h2
    linarith
  -- 6) Upper bound on BadMid2.card
  have hBM2_le : (BadMid2.card : ℚ) ≤ (Pmid2.card : ℚ) := by
    have hcov : BadMid2 ⊆ Pmid2.biUnion (fun p => S.filter (fun k => ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2)) := by
      intro k hk
      obtain ⟨hkS, p, hp, hpm, hdvd⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hkS, hpm, hdvd⟩⟩
    have h1 : BadMid2.card ≤
        ∑ p ∈ Pmid2, (S.filter (fun k => ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2)).card :=
      le_trans (Finset.card_le_card hcov) Finset.card_biUnion_le
    have h2 : ∑ p ∈ Pmid2, (S.filter (fun k => ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2)).card ≤
        ∑ _ ∈ Pmid2, 1 := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hpI := (Finset.mem_filter.mp hp).1
      have hpr := (Finset.mem_filter.mp hp).2
      have hp_gt : max Z K.sqrt < p := (Finset.mem_Ioc.mp hpI).1
      have hp2 : p ≠ 2 := by omega
      have hgt : K < p ^ 2 := by
        have hlt : K.sqrt < p := lt_of_le_of_lt (le_max_right Z K.sqrt) hp_gt
        have hK : K < (K.sqrt + 1) * (K.sqrt + 1) := Nat.lt_succ_sqrt K
        have : K.sqrt + 1 ≤ p := hlt
        rw [sq]; nlinarith
      by_cases hpm : p ∣ m
      · have hemp : S.filter (fun k => ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2) = ∅ := by
          rw [Finset.filter_eq_empty_iff]; intro k _ h; exact h.1 hpm
        rw [hemp, Finset.card_empty]; exact Nat.zero_le 1
      · have hsub : S.filter (fun k => ¬ p ∣ m ∧ p ^ 2 ∣ m - k ^ 2) ⊆
            S.filter (fun k => p ^ 2 ∣ m - k ^ 2) :=
          fun _ hk => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hk).1, (Finset.mem_filter.mp hk).2.2⟩
        exact le_trans (Finset.card_le_card hsub) (bad_mid_prime_card_gt_sqrt P hpr hp2 hpm hgt)
    rw [Finset.sum_const, smul_eq_mul, mul_one] at h2
    exact_mod_cast le_trans h1 h2
  -- 7) Upper bound on BadLarge.card
  have hBL_le : (BadLarge.card : ℚ) ≤ largeTailBound m W :=
    bad_large_card (by omega) (by omega)
  -- Combine all!
  have hS_q : (S.card : ℚ) ≤ (representations m : ℚ) + (BadSmall.card : ℚ) +
      (BadMid1.card : ℚ) + (BadMid2.card : ℚ) + (BadLarge.card : ℚ) := by
    have : S.card ≤ representations m + BadSmall.card + BadMid1.card + BadMid2.card + BadLarge.card := by
      omega
    exact_mod_cast this
  linarith

-- ## Section 3: Prime Reciprocal-Square Tails, Wheel Bounds, Primorials, and Multiplicative Bounds

-- 3.1 Telescoping tail bound for odd integers and primes

private lemma sum_inv_sq_odd_tail (N M : ℕ) (hN : 1 ≤ N) :
    ∑ j ∈ Finset.Ico N M, (1 : ℚ) / (2 * (j : ℚ) + 1) ^ 2 ≤
      1 / (2 * (2 * (N : ℚ) - 1)) := by
  have hle : ∀ j ∈ Finset.Ico N M,
      (1 : ℚ) / (2 * (j : ℚ) + 1) ^ 2 ≤
        1 / (2 * (2 * (j : ℚ) - 1)) - 1 / (2 * (2 * (j : ℚ) + 1)) := by
    intro j hj
    have hj1 : (1 : ℚ) ≤ (j : ℚ) := by exact_mod_cast le_trans hN (Finset.mem_Ico.mp hj).1
    have hpos1 : (0 : ℚ) < 2 * (j : ℚ) - 1 := by linarith
    have hpos2 : (0 : ℚ) < 2 * (j : ℚ) + 1 := by linarith
    have heq : 1 / (2 * (2 * (j : ℚ) - 1)) - 1 / (2 * (2 * (j : ℚ) + 1)) =
        1 / ((2 * (j : ℚ) - 1) * (2 * (j : ℚ) + 1)) := by
      field_simp
      ring
    rw [heq]
    exact one_div_le_one_div_of_le (mul_pos hpos1 hpos2) (by nlinarith)
  have htel : ∀ k : ℕ,
      ∑ j ∈ Finset.Ico N (N + k),
        (1 / (2 * (2 * (j : ℚ) - 1)) - 1 / (2 * (2 * (j : ℚ) + 1))) =
      1 / (2 * (2 * (N : ℚ) - 1)) - 1 / (2 * (2 * ((N + k : ℕ) : ℚ) - 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show N + (k + 1) = (N + k) + 1 by omega, Finset.sum_Ico_succ_top (by omega), ih]
      push_cast
      ring
  by_cases hNM : M ≤ N
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]
    have hN1 : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
    have : (0 : ℚ) < 2 * (2 * (N : ℚ) - 1) := by linarith
    positivity
  · have hM_eq : M = N + (M - N) := by omega
    calc ∑ j ∈ Finset.Ico N M, (1 : ℚ) / (2 * (j : ℚ) + 1) ^ 2
        ≤ ∑ j ∈ Finset.Ico N M,
            (1 / (2 * (2 * (j : ℚ) - 1)) - 1 / (2 * (2 * (j : ℚ) + 1))) :=
          Finset.sum_le_sum hle
      _ = 1 / (2 * (2 * (N : ℚ) - 1)) - 1 / (2 * (2 * (M : ℚ) - 1)) := by
          rw [hM_eq, htel (M - N)]
      _ ≤ 1 / (2 * (2 * (N : ℚ) - 1)) := by
          have hM1 : (1 : ℚ) ≤ (M : ℚ) := by exact_mod_cast (by omega : 1 ≤ M)
          have : (0 : ℚ) < 2 * (2 * (M : ℚ) - 1) := by linarith
          have : (0 : ℚ) ≤ 1 / (2 * (2 * (M : ℚ) - 1)) := by positivity
          linarith

private lemma sum_inv_sq_primes_gt_le (Z B : ℕ) (hZ : 2 ≤ Z) :
    ∑ p ∈ (Finset.Ioc Z B).filter Nat.Prime, (1 : ℚ) / (p : ℚ) ^ 2 ≤
      1 / (2 * ((Z : ℚ) - 1)) := by
  set N := (Z + 1) / 2
  have hN1 : 1 ≤ N := by omega
  have hsub : (Finset.Ioc Z B).filter Nat.Prime ⊆
      (Finset.Ico N (B + 1)).image (fun j => 2 * j + 1) := by
    intro p hp
    have hpI := (Finset.mem_filter.mp hp).1
    have hpr := (Finset.mem_filter.mp hp).2
    have hpZ : Z < p := (Finset.mem_Ioc.mp hpI).1
    have hpB : p ≤ B := (Finset.mem_Ioc.mp hpI).2
    have hp_odd : p % 2 = 1 := (hpr.eq_two_or_odd).resolve_left (by omega)
    rw [Finset.mem_image]
    refine ⟨p / 2, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
  have hinj : Set.InjOn (fun j : ℕ => 2 * j + 1) (Finset.Ico N (B + 1) : Set ℕ) := by
    intro a _ b _ h; dsimp only at h; omega
  have hle1 : ∑ p ∈ (Finset.Ioc Z B).filter Nat.Prime, (1 : ℚ) / (p : ℚ) ^ 2 ≤
      ∑ j ∈ Finset.Ico N (B + 1), (1 : ℚ) / (2 * (j : ℚ) + 1) ^ 2 := by
    calc ∑ p ∈ (Finset.Ioc Z B).filter Nat.Prime, (1 : ℚ) / (p : ℚ) ^ 2
        ≤ ∑ p ∈ (Finset.Ico N (B + 1)).image (fun j : ℕ => 2 * j + 1), (1 : ℚ) / (p : ℚ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = ∑ j ∈ Finset.Ico N (B + 1), (1 : ℚ) / (2 * (j : ℚ) + 1) ^ 2 := by
          rw [Finset.sum_image hinj]
          refine Finset.sum_congr rfl fun j _ => by push_cast; ring
  have hle2 := sum_inv_sq_odd_tail N (B + 1) hN1
  have hZN : (Z : ℚ) - 1 ≤ 2 * (N : ℚ) - 1 := by
    have : Z ≤ 2 * N := by omega
    have hq : (Z : ℚ) ≤ 2 * (N : ℚ) := by exact_mod_cast this
    linarith
  have hZpos : (0 : ℚ) < 2 * ((Z : ℚ) - 1) := by
    have : (2 : ℚ) ≤ (Z : ℚ) := by exact_mod_cast hZ
    linarith
  exact le_trans (le_trans hle1 hle2) (one_div_le_one_div_of_le hZpos (by linarith))

-- 3.2 Fast sound prime upper-candidate filter (exact for n < 113^2 = 12769) and concrete tail bounds

private def smallPrimes32 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

private def primeCand32 (n : ℕ) : Bool :=
  decide (2 ≤ n) && smallPrimes32.all (fun d => decide (n ≤ d) || decide (n % d ≠ 0))

private lemma primeCand32_of_prime {p : ℕ} (hp : p.Prime) : primeCand32 p = true := by
  unfold primeCand32
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
  refine ⟨hp.two_le, fun d hd => ?_⟩
  by_cases hle : p ≤ d
  · exact Or.inl hle
  · right; intro hmod
    have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
    rcases hp.eq_one_or_self_of_dvd d hdvd with rfl | rfl
    · simp [smallPrimes32] at hd
    · omega

private def scaledInvSqSum (Z : ℕ) : ℕ :=
  let rec go (n fuel acc : ℕ) : ℕ :=
    match fuel with
    | 0 => acc
    | fuel' + 1 =>
      let acc' := if primeCand32 n then acc + (1000000000 / (n * n) + 1) else acc
      go (n + 1) fuel' acc'
  go (Z + 1) (1000 - Z) 0

private lemma scaledInvSqSum_go_eq (n fuel acc : ℕ) :
    scaledInvSqSum.go n fuel acc =
      acc + ∑ p ∈ (Finset.Ico n (n + fuel)).filter (fun p => primeCand32 p = true),
        (1000000000 / (p * p) + 1) := by
  induction fuel generalizing n acc with
  | zero => simp [scaledInvSqSum.go]
  | succ fuel' ih =>
    unfold scaledInvSqSum.go
    rw [ih]
    have hIco : Finset.Ico n (n + (fuel' + 1)) = insert n (Finset.Ico (n + 1) (n + 1 + fuel')) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnotmem : n ∉ Finset.Ico (n + 1) (n + 1 + fuel') := by simp
    have hnotmem' : n ∉ (Finset.Ico (n + 1) (n + 1 + fuel')).filter (fun p => primeCand32 p = true) :=
      fun h => hnotmem (Finset.mem_filter.mp h).1
    rw [hIco, Finset.filter_insert]
    by_cases hc : primeCand32 n = true
    · simp only [hc, ↓reduceIte, Finset.sum_insert hnotmem']
      omega
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]

private lemma sum_inv_sq_primes_gt_via_1000 (Z B num : ℕ) (hZ : 2 ≤ Z) (hZ1000 : Z ≤ 1000)
    (hchk : scaledInvSqSum Z * 10000 * 1998 + 1000000000 * 10000 ≤ num * 1000000000 * 1998) :
    ∑ p ∈ (Finset.Ioc Z B).filter Nat.Prime, (1 : ℚ) / (p : ℚ) ^ 2 ≤ (num : ℚ) / 10000 := by
  set S := (Finset.Ioc Z B).filter Nat.Prime
  set S1 := (Finset.Ioc Z 1000).filter Nat.Prime
  set S2 := (Finset.Ioc 1000 B).filter Nat.Prime
  have hsub : S ⊆ S1 ∪ S2 := by
    intro p hp
    have hpI := (Finset.mem_filter.mp hp).1
    have hpr := (Finset.mem_filter.mp hp).2
    have hpZ := (Finset.mem_Ioc.mp hpI).1
    have hpB := (Finset.mem_Ioc.mp hpI).2
    by_cases hle : p ≤ 1000
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpZ, hle⟩, hpr⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hpB⟩, hpr⟩)
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h1).1).2
    have := (Finset.mem_Ioc.mp (Finset.mem_filter.mp h2).1).1
    omega
  have hsplit : ∑ p ∈ S, (1 : ℚ) / (p : ℚ) ^ 2 ≤
      ∑ p ∈ S1, (1 : ℚ) / (p : ℚ) ^ 2 + ∑ p ∈ S2, (1 : ℚ) / (p : ℚ) ^ 2 := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  -- Bound S2 using sum_inv_sq_primes_gt_le at Z = 1000
  have hS2 : ∑ p ∈ S2, (1 : ℚ) / (p : ℚ) ^ 2 ≤ 1 / 1998 := by
    have h := sum_inv_sq_primes_gt_le 1000 B (by norm_num)
    exact le_trans h (by norm_num)
  -- Bound S1 using scaledInvSqSum Z
  have hS1_sub : S1 ⊆ (Finset.Ico (Z + 1) (Z + 1 + (1000 - Z))).filter (fun p => primeCand32 p = true) := by
    intro p hp
    have hpI := (Finset.mem_filter.mp hp).1
    have hpr := (Finset.mem_filter.mp hp).2
    have hpZ := (Finset.mem_Ioc.mp hpI).1
    have hp1000 := (Finset.mem_Ioc.mp hpI).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, primeCand32_of_prime hpr⟩
  have hterm : ∀ p ∈ (Finset.Ico (Z + 1) (Z + 1 + (1000 - Z))).filter (fun p => primeCand32 p = true),
      (1 : ℚ) / (p : ℚ) ^ 2 ≤ ((1000000000 / (p * p) + 1 : ℕ) : ℚ) / 1000000000 := by
    intro p hp
    have hp_pos : 0 < p := by have := (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1; omega
    have hpp_pos : 0 < p * p := Nat.mul_pos hp_pos hp_pos
    have hnat : 1000000000 ≤ (1000000000 / (p * p) + 1) * (p * p) := by
      have := le_of_lt (Nat.lt_mul_div_succ 1000000000 hpp_pos)
      rwa [Nat.mul_comm] at this
    have hq : (1000000000 : ℚ) ≤ ((1000000000 / (p * p) + 1 : ℕ) : ℚ) * (p : ℚ) ^ 2 := by
      have : (1000000000 : ℚ) ≤ ((1000000000 / (p * p) + 1 : ℕ) : ℚ) * ((p * p : ℕ) : ℚ) := by
        exact_mod_cast hnat
      simpa [sq] using this
    have hp2_pos : (0 : ℚ) < (p : ℚ) ^ 2 := by positivity
    rw [div_le_div_iff₀ hp2_pos (by norm_num : (0 : ℚ) < 1000000000)]
    linarith
  have hS1 : ∑ p ∈ S1, (1 : ℚ) / (p : ℚ) ^ 2 ≤ (scaledInvSqSum Z : ℚ) / 1000000000 := by
    have hsum_eq : scaledInvSqSum Z =
        ∑ p ∈ (Finset.Ico (Z + 1) (Z + 1 + (1000 - Z))).filter (fun p => primeCand32 p = true),
          (1000000000 / (p * p) + 1) := by
      unfold scaledInvSqSum
      rw [scaledInvSqSum_go_eq, zero_add]
    calc ∑ p ∈ S1, (1 : ℚ) / (p : ℚ) ^ 2
        ≤ ∑ p ∈ (Finset.Ico (Z + 1) (Z + 1 + (1000 - Z))).filter (fun p => primeCand32 p = true),
            (1 : ℚ) / (p : ℚ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hS1_sub (fun _ _ _ => by positivity)
      _ ≤ ∑ p ∈ (Finset.Ico (Z + 1) (Z + 1 + (1000 - Z))).filter (fun p => primeCand32 p = true),
            (((1000000000 / (p * p) + 1 : ℕ) : ℚ) / 1000000000) :=
          Finset.sum_le_sum hterm
      _ = (∑ p ∈ (Finset.Ico (Z + 1) (Z + 1 + (1000 - Z))).filter (fun p => primeCand32 p = true),
            ((1000000000 / (p * p) + 1 : ℕ) : ℚ)) / 1000000000 := by
          rw [Finset.sum_div]
      _ = (scaledInvSqSum Z : ℚ) / 1000000000 := by rw [hsum_eq]; push_cast; rfl
  have hchk_q : (scaledInvSqSum Z : ℚ) * 10000 * 1998 + 1000000000 * 10000 ≤
      (num : ℚ) * 1000000000 * 1998 := by exact_mod_cast hchk
  have hcomb : (scaledInvSqSum Z : ℚ) / 1000000000 + 1 / 1998 ≤ (num : ℚ) / 10000 := by linarith
  linarith

private lemma tail_check_all :
    scaledInvSqSum 2 * 10000 * 1998 + 1000000000 * 10000 ≤ 2027 * 1000000000 * 1998 ∧
    scaledInvSqSum 3 * 10000 * 1998 + 1000000000 * 10000 ≤ 916 * 1000000000 * 1998 ∧
    scaledInvSqSum 7 * 10000 * 1998 + 1000000000 * 10000 ≤ 312 * 1000000000 * 1998 ∧
    scaledInvSqSum 13 * 10000 * 1998 + 1000000000 * 10000 ≤ 170 * 1000000000 * 1998 ∧
    scaledInvSqSum 19 * 10000 * 1998 + 1000000000 * 10000 ≤ 107 * 1000000000 * 1998 ∧
    scaledInvSqSum 29 * 10000 * 1998 + 1000000000 * 10000 ≤ 77 * 1000000000 * 1998 ∧
    scaledInvSqSum 47 * 10000 * 1998 + 1000000000 * 10000 ≤ 43 * 1000000000 * 1998 ∧
    scaledInvSqSum 250 * 10000 * 1998 + 1000000000 * 10000 ≤ 10 * 1000000000 * 1998 ∧
    scaledInvSqSum 500 * 10000 * 1998 + 1000000000 * 10000 ≤ 7 * 1000000000 * 1998 := by
  decide +kernel

private lemma sum_2_inv_sq_primes_ge3 (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p) :
    ∑ p ∈ S, (2 : ℚ) / (p : ℚ) ^ 2 ≤ 41 / 100 := by
  set B := S.sup id
  have hsub : S ⊆ (Finset.Ioc 2 B).filter Nat.Prime := by
    intro p hp
    have ⟨hpr, hp3⟩ := hS p hp
    have hle : p ≤ B := Finset.le_sup (f := id) hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hle⟩, hpr⟩
  have h1 : ∑ p ∈ S, (1 : ℚ) / (p : ℚ) ^ 2 ≤ 2027 / 10000 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
      (sum_inv_sq_primes_gt_via_1000 2 B 2027 (by norm_num) (by norm_num) tail_check_all.1)
  have heq : ∑ p ∈ S, (2 : ℚ) / (p : ℚ) ^ 2 = 2 * ∑ p ∈ S, (1 : ℚ) / (p : ℚ) ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
  linarith

private lemma sum_2_inv_sq_primes_ge5 (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 5 ≤ p) :
    ∑ p ∈ S, (2 : ℚ) / (p : ℚ) ^ 2 ≤ 19 / 100 := by
  set B := S.sup id
  have hsub : S ⊆ (Finset.Ioc 3 B).filter Nat.Prime := by
    intro p hp
    have ⟨hpr, hp5⟩ := hS p hp
    have hle : p ≤ B := Finset.le_sup (f := id) hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, hle⟩, hpr⟩
  have h1 : ∑ p ∈ S, (1 : ℚ) / (p : ℚ) ^ 2 ≤ 916 / 10000 :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity))
      (sum_inv_sq_primes_gt_via_1000 3 B 916 (by norm_num) (by norm_num) tail_check_all.2.1)
  have heq : ∑ p ∈ S, (2 : ℚ) / (p : ℚ) ^ 2 = 2 * ∑ p ∈ S, (1 : ℚ) / (p : ℚ) ^ 2 := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
  linarith

-- 3.3 Prime counting function pi(N) and wheel / linear upper bounds

private def piCount (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter Nat.Prime).card

private lemma card_Icc_coprime_le (N M : ℕ) (hM : 0 < M) :
    ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n M)).card ≤
      (N / M + 1) * ((Finset.range M).filter (fun r => Nat.Coprime r M)).card := by
  set T := (Finset.range (N / M + 1)) ×ˢ ((Finset.range M).filter (fun r => Nat.Coprime r M))
  let f : ℕ → ℕ × ℕ := fun n => (n / M, n % M)
  have hmaps : ∀ n ∈ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n M), f n ∈ T := by
    intro n hn
    have hnI := (Finset.mem_filter.mp hn).1
    have hcop := (Finset.mem_filter.mp hn).2
    have hnN : n ≤ N := (Finset.mem_Icc.mp hnI).2
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.lt_succ_of_le (Nat.div_le_div_right hnN), Nat.mod_lt n hM, ?_⟩
    rw [Nat.Coprime, ← Nat.gcd_rec, Nat.gcd_comm]
    exact hcop
  have hinj : Set.InjOn f ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n M) : Set ℕ) := by
    intro a _ b _ hab
    have h1 : a / M = b / M := congrArg Prod.fst hab
    have h2 : a % M = b % M := congrArg Prod.snd hab
    have ha := Nat.div_add_mod a M
    have hb := Nat.div_add_mod b M
    rw [← ha, ← hb, h1, h2]
  calc ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n M)).card
      ≤ T.card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = (N / M + 1) * ((Finset.range M).filter (fun r => Nat.Coprime r M)).card := by
        rw [Finset.card_product, Finset.card_range]

private lemma piCount_le_wheel6 (N : ℕ) :
    (piCount N : ℚ) ≤ (N : ℚ) / 3 + 4 := by
  have hsub : (Finset.Icc 1 N).filter Nat.Prime ⊆
      ({2, 3} : Finset ℕ) ∪ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n 6) := by
    intro p hp
    have hpI := (Finset.mem_filter.mp hp).1
    have hpr := (Finset.mem_filter.mp hp).2
    by_cases h2 : p = 2
    · exact Finset.mem_union_left _ (by simp [h2])
    · by_cases h3 : p = 3
      · exact Finset.mem_union_left _ (by simp [h3])
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpI, ?_⟩)
        have hc2 : Nat.Coprime p 2 := hpr.coprime_iff_not_dvd.mpr fun h =>
          h2 ((Nat.prime_two.eq_one_or_self_of_dvd p h).resolve_left hpr.ne_one)
        have hc3 : Nat.Coprime p 3 := hpr.coprime_iff_not_dvd.mpr fun h =>
          h3 ((Nat.prime_three.eq_one_or_self_of_dvd p h).resolve_left hpr.ne_one)
        exact Nat.Coprime.mul_right hc2 hc3
  have hphi6 : ((Finset.range 6).filter (fun r => Nat.Coprime r 6)).card = 2 := by decide
  have hnat : piCount N ≤ 2 + (N / 6 + 1) * 2 := by
    calc piCount N
        ≤ (({2, 3} : Finset ℕ) ∪ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n 6)).card :=
          Finset.card_le_card hsub
      _ ≤ ({2, 3} : Finset ℕ).card + ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n 6)).card :=
          Finset.card_union_le _ _
      _ ≤ 2 + (N / 6 + 1) * 2 := by
          have h1 : ({2, 3} : Finset ℕ).card ≤ 2 := Finset.card_le_two
          have h2 := card_Icc_coprime_le N 6 (by norm_num)
          rw [hphi6] at h2
          omega
  have hdiv : ((N / 6 : ℕ) : ℚ) ≤ (N : ℚ) / 6 := by
    have : (N / 6) * 6 ≤ N := Nat.div_mul_le_self N 6
    have hq : ((N / 6 : ℕ) : ℚ) * 6 ≤ (N : ℚ) := by exact_mod_cast this
    linarith
  have hq : (piCount N : ℚ) ≤ 2 + (((N / 6 : ℕ) : ℚ) + 1) * 2 := by exact_mod_cast hnat
  linarith

private lemma piCount_le_wheel2310 (N : ℕ) :
    (piCount N : ℚ) ≤ 16 * (N : ℚ) / 77 + 485 := by
  set S5 : Finset ℕ := {2, 3, 5, 7, 11}
  have hsub : (Finset.Icc 1 N).filter Nat.Prime ⊆
      S5 ∪ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n 2310) := by
    intro p hp
    have hpI := (Finset.mem_filter.mp hp).1
    have hpr := (Finset.mem_filter.mp hp).2
    by_cases hmem : p ∈ S5
    · exact Finset.mem_union_left _ hmem
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hpI, ?_⟩)
      have hndvd : ∀ q ∈ S5, ¬ p ∣ q := by
        intro q hq h
        have hqp : q.Prime := by
          simp only [S5, Finset.mem_insert, Finset.mem_singleton] at hq
          rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num
        have heq : p = q := (hqp.eq_one_or_self_of_dvd p h).resolve_left hpr.ne_one
        exact hmem (heq ▸ hq)
      have hc2 : Nat.Coprime p 2 := hpr.coprime_iff_not_dvd.mpr (hndvd 2 (by simp [S5]))
      have hc3 : Nat.Coprime p 3 := hpr.coprime_iff_not_dvd.mpr (hndvd 3 (by simp [S5]))
      have hc5 : Nat.Coprime p 5 := hpr.coprime_iff_not_dvd.mpr (hndvd 5 (by simp [S5]))
      have hc7 : Nat.Coprime p 7 := hpr.coprime_iff_not_dvd.mpr (hndvd 7 (by simp [S5]))
      have hc11 : Nat.Coprime p 11 := hpr.coprime_iff_not_dvd.mpr (hndvd 11 (by simp [S5]))
      have : 2310 = 2 * (3 * (5 * (7 * 11))) := by norm_num
      rw [this]
      exact hc2.mul_right (hc3.mul_right (hc5.mul_right (hc7.mul_right hc11)))
  have hphi2310 : ((Finset.range 2310).filter (fun r => Nat.Coprime r 2310)).card = 480 := by
    decide +kernel
  have hS5 : S5.card = 5 := by decide
  have hnat : piCount N ≤ 5 + (N / 2310 + 1) * 480 := by
    calc piCount N
        ≤ (S5 ∪ (Finset.Icc 1 N).filter (fun n => Nat.Coprime n 2310)).card :=
          Finset.card_le_card hsub
      _ ≤ S5.card + ((Finset.Icc 1 N).filter (fun n => Nat.Coprime n 2310)).card :=
          Finset.card_union_le _ _
      _ ≤ 5 + (N / 2310 + 1) * 480 := by
          have h2 := card_Icc_coprime_le N 2310 (by norm_num)
          rw [hphi2310] at h2
          omega
  have hdiv : ((N / 2310 : ℕ) : ℚ) ≤ (N : ℚ) / 2310 := by
    have : (N / 2310) * 2310 ≤ N := Nat.div_mul_le_self N 2310
    have hq : ((N / 2310 : ℕ) : ℚ) * 2310 ≤ (N : ℚ) := by exact_mod_cast this
    linarith
  have hq : (piCount N : ℚ) ≤ 5 + (((N / 2310 : ℕ) : ℚ) + 1) * 480 := by exact_mod_cast hnat
  linarith

-- Linear pi(x) checker for x <= 12648 using primeCand113 (exact up to 113^2 - 1 = 12768)

private def smallPrimes113 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109]

private def primeCand113 (n : ℕ) : Bool :=
  decide (2 ≤ n) && smallPrimes113.all (fun d => decide (n ≤ d) || decide (n % d ≠ 0))

private lemma primeCand113_of_prime {p : ℕ} (hp : p.Prime) : primeCand113 p = true := by
  unfold primeCand113
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true]
  refine ⟨hp.two_le, fun d hd => ?_⟩
  by_cases hle : p ≤ d
  · exact Or.inl hle
  · right; intro hmod
    have hdvd : d ∣ p := Nat.dvd_of_mod_eq_zero hmod
    rcases hp.eq_one_or_self_of_dvd d hdvd with rfl | rfl
    · simp [smallPrimes113] at hd
    · omega

private def checkPiLin (lo hi num den b : ℕ) : Bool :=
  let rec go (n fuel cnt : ℕ) : Bool :=
    match fuel with
    | 0 => true
    | fuel' + 1 =>
      let cnt' := if primeCand113 n then cnt + 1 else cnt
      let ok := if lo ≤ n then decide (cnt' * den ≤ num * n + b * den) else true
      ok && go (n + 1) fuel' cnt'
  go 1 hi 0

private lemma checkPiLin_go_spec (lo num den b n fuel cnt : ℕ)
    (hcnt : cnt = ((Finset.Ico 1 n).filter (fun p => primeCand113 p = true)).card)
    (hn1 : 1 ≤ n)
    (hgo : checkPiLin.go lo num den b n fuel cnt = true) :
    ∀ x, n ≤ x → x < n + fuel → lo ≤ x →
      ((Finset.Icc 1 x).filter (fun p => primeCand113 p = true)).card * den ≤
        num * x + b * den := by
  induction fuel generalizing n cnt with
  | zero => intro x h1 h2; omega
  | succ fuel' ih =>
    unfold checkPiLin.go at hgo
    simp only [Bool.and_eq_true] at hgo
    rcases hgo with ⟨hok, hrest⟩
    set cnt' := if primeCand113 n then cnt + 1 else cnt
    have hIco : Finset.Ico 1 (n + 1) = insert n (Finset.Ico 1 n) := by
      ext y; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
    have hnotmem : n ∉ Finset.Ico 1 n := by simp
    have hnotmem' : n ∉ (Finset.Ico 1 n).filter (fun p => primeCand113 p = true) :=
      fun h => hnotmem (Finset.mem_filter.mp h).1
    have hcnt' : cnt' = ((Finset.Ico 1 (n + 1)).filter (fun p => primeCand113 p = true)).card := by
      rw [hIco, Finset.filter_insert]
      by_cases hc : primeCand113 n = true
      · simp only [cnt', hc, ↓reduceIte, Finset.card_insert_of_notMem hnotmem', hcnt]
      · simp only [cnt', hc, Bool.false_eq_true, ↓reduceIte, hcnt]
    intro x hnx hxf hlox
    by_cases hxn : x = n
    · subst hxn
      simp only [hlox, ↓reduceIte, decide_eq_true_eq] at hok
      have hIcc : Finset.Icc 1 x = Finset.Ico 1 (x + 1) := by
        ext y; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [hIcc, ← hcnt']
      exact hok
    · exact ih (n + 1) cnt' hcnt' (by omega) hrest x (by omega) (by omega) hlox

private lemma piCount_le_linear_of_check {lo hi num den b : ℕ} (hden : 0 < den)
    (hchk : checkPiLin lo hi num den b = true) {x : ℕ} (hlo : lo ≤ x) (hhi : x ≤ hi) :
    (piCount x : ℚ) ≤ ((num : ℚ) / (den : ℚ)) * (x : ℚ) + (b : ℚ) := by
  by_cases hx0 : x = 0
  · subst hx0; simp [piCount]
  · have hnat := checkPiLin_go_spec lo num den b 1 hi 0 (by simp) (by norm_num) hchk x
      (by omega) (by omega) hlo
    have hsub : (Finset.Icc 1 x).filter Nat.Prime ⊆
        (Finset.Icc 1 x).filter (fun p => primeCand113 p = true) :=
      fun p hp => Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hp).1, primeCand113_of_prime (Finset.mem_filter.mp hp).2⟩
    have hle : piCount x * den ≤ num * x + b * den :=
      le_trans (Nat.mul_le_mul_right den (Finset.card_le_card hsub)) hnat
    have hq : (piCount x : ℚ) * (den : ℚ) ≤ (num : ℚ) * (x : ℚ) + (b : ℚ) * (den : ℚ) := by
      exact_mod_cast hle
    have hden_pos : (0 : ℚ) < (den : ℚ) := by exact_mod_cast hden
    rw [← le_div_iff₀ hden_pos] at hq
    have heq : ((num : ℚ) * (x : ℚ) + (b : ℚ) * (den : ℚ)) / (den : ℚ) =
        ((num : ℚ) / (den : ℚ)) * (x : ℚ) + (b : ℚ) := by
      field_simp
    linarith

private lemma checkPiLin_bands :
    checkPiLin 1385 1999 147 1000 19 = true ∧
    checkPiLin 1999 3577 135 1000 35 = true ∧
    checkPiLin 4472 8660 120 1000 73 = true ∧
    checkPiLin 6928 12648 115 1000 97 = true := by
  decide +kernel

-- 3.4 Primorial Lemma (pure Finset.sdiff + Finset.inter, zero sorting!)

private lemma primorial_card_lt {S A : Finset ℕ} {M : ℕ}
    (hS_pos : ∀ s ∈ S, 1 ≤ s)
    (hA_le : ∀ a ∈ A, a ≤ M)
    (hS_gt : ∀ s ∈ S, s ∉ A → M < s)
    (hprod : ∏ s ∈ S, s < ∏ a ∈ A, a) :
    S.card < A.card := by
  by_contra hge
  push Not at hge
  have hcard_diff : (A \ S).card ≤ (S \ A).card := by
    have h1 := Finset.card_sdiff_add_card_inter A S
    have h2 := Finset.card_sdiff_add_card_inter S A
    rw [Finset.inter_comm] at h2
    omega
  have hSprod_pos : 1 ≤ ∏ s ∈ S, s := Nat.one_le_iff_ne_zero.mpr
    (Finset.prod_ne_zero_iff.mpr fun s hs => by have := hS_pos s hs; omega)
  have hMpos : 1 ≤ M := by
    by_cases hemp : A = ∅
    · subst hemp; simp at hprod; omega
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hpos : 0 < ∏ x ∈ A, x := by omega
      have ha_pos : 0 < a := Nat.pos_of_ne_zero fun h0 => by
        have : ∏ x ∈ A, x = 0 := Finset.prod_eq_zero (f := id) ha h0
        omega
      have := hA_le a ha
      omega
  have h1 : ∏ a ∈ A \ S, a ≤ M ^ (A \ S).card :=
    Finset.prod_le_pow_card (A \ S) _ M (fun a ha => hA_le a (Finset.mem_sdiff.mp ha).1)
  have h2 : M ^ (A \ S).card ≤ M ^ (S \ A).card :=
    Nat.pow_le_pow_right hMpos hcard_diff
  have h3 : M ^ (S \ A).card ≤ ∏ s ∈ S \ A, s :=
    Finset.pow_card_le_prod (S \ A) _ M (fun s hs => le_of_lt (hS_gt s (Finset.mem_sdiff.mp hs).1 (Finset.mem_sdiff.mp hs).2))
  have hdiff : ∏ a ∈ A \ S, a ≤ ∏ s ∈ S \ A, s := le_trans h1 (le_trans h2 h3)
  have hA_eq : ∏ a ∈ A, a = (∏ a ∈ A \ S, a) * (∏ x ∈ A ∩ S, x) := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff_inter A S), Finset.sdiff_union_inter]
  have hS_eq : ∏ s ∈ S, s = (∏ s ∈ S \ A, s) * (∏ x ∈ A ∩ S, x) := by
    rw [Finset.inter_comm A S, ← Finset.prod_union (Finset.disjoint_sdiff_inter S A), Finset.sdiff_union_inter]
  have hge_prod : ∏ a ∈ A, a ≤ ∏ s ∈ S, s := by
    rw [hA_eq, hS_eq]
    exact Nat.mul_le_mul_right _ hdiff
  omega

private lemma primorial_phi_ge {S B : Finset ℕ} {M' : ℕ}
    (hB_pos : ∀ b ∈ B, 1 ≤ b)
    (hB_le : ∀ b ∈ B, b ≤ M')
    (hS_gt : ∀ s ∈ S, s ∉ B → M' < s)
    (hcard : S.card ≤ B.card) :
    ∏ b ∈ B, (1 - 1 / (b : ℚ)) ≤ ∏ s ∈ S, (1 - 1 / (s : ℚ)) := by
  by_cases hM'0 : M' = 0
  · subst hM'0
    have hBe : B = ∅ := by
      ext b; simp only [Finset.notMem_empty, iff_false]; intro hb
      have := hB_pos b hb; have := hB_le b hb; omega
    have hSe : S = ∅ := Finset.card_eq_zero.mp (by rw [hBe, Finset.card_empty] at hcard; omega)
    simp [hBe, hSe]
  · have hM'1 : (1 : ℚ) ≤ (M' : ℚ) := by exact_mod_cast (by omega : 1 ≤ M')
    have hM'pos : (0 : ℚ) < (M' : ℚ) := by linarith
    set c : ℚ := 1 - 1 / (M' : ℚ)
    have hc_nn : 0 ≤ c := by dsimp [c]; rw [sub_nonneg, div_le_one hM'pos]; exact hM'1
    have hc_le1 : c ≤ 1 := by
      dsimp [c]
      have : (0 : ℚ) ≤ 1 / (M' : ℚ) := by positivity
      linarith
    have hcard_diff : (S \ B).card ≤ (B \ S).card := by
      have h1 := Finset.card_sdiff_add_card_inter B S
      have h2 := Finset.card_sdiff_add_card_inter S B
      rw [Finset.inter_comm] at h2
      omega
    have h1 : ∏ b ∈ B \ S, (1 - 1 / (b : ℚ)) ≤ c ^ (B \ S).card := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod (fun b hb => ?_) (fun b hb => ?_)
      · have hb1 : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hB_pos b (Finset.mem_sdiff.mp hb).1
        rw [sub_nonneg, div_le_one (by linarith)]; exact hb1
      · have hb1 : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hB_pos b (Finset.mem_sdiff.mp hb).1
        have hble : (b : ℚ) ≤ (M' : ℚ) := by exact_mod_cast hB_le b (Finset.mem_sdiff.mp hb).1
        have : 1 / (M' : ℚ) ≤ 1 / (b : ℚ) := one_div_le_one_div_of_le hb1 hble
        dsimp [c]; linarith
    have h2 : c ^ (B \ S).card ≤ c ^ (S \ B).card :=
      pow_le_pow_of_le_one hc_nn hc_le1 hcard_diff
    have h3 : c ^ (S \ B).card ≤ ∏ s ∈ S \ B, (1 - 1 / (s : ℚ)) := by
      rw [← Finset.prod_const]
      refine Finset.prod_le_prod (fun _ _ => hc_nn) (fun s hs => ?_)
      have hsgt : (M' : ℚ) ≤ (s : ℚ) := by
        exact_mod_cast le_of_lt (hS_gt s (Finset.mem_sdiff.mp hs).1 (Finset.mem_sdiff.mp hs).2)
      have : 1 / (s : ℚ) ≤ 1 / (M' : ℚ) := one_div_le_one_div_of_le hM'pos hsgt
      dsimp [c]; linarith
    have hdiff : ∏ b ∈ B \ S, (1 - 1 / (b : ℚ)) ≤ ∏ s ∈ S \ B, (1 - 1 / (s : ℚ)) :=
      le_trans h1 (le_trans h2 h3)
    have hinter_nn : 0 ≤ ∏ x ∈ B ∩ S, (1 - 1 / (x : ℚ)) := by
      refine Finset.prod_nonneg fun x hx => ?_
      have hx1 : (1 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hB_pos x (Finset.mem_inter.mp hx).1
      rw [sub_nonneg, div_le_one (by linarith)]; exact hx1
    have hB_eq : ∏ b ∈ B, (1 - 1 / (b : ℚ)) =
        (∏ b ∈ B \ S, (1 - 1 / (b : ℚ))) * (∏ x ∈ B ∩ S, (1 - 1 / (x : ℚ))) := by
      rw [← Finset.prod_union (Finset.disjoint_sdiff_inter B S), Finset.sdiff_union_inter]
    have hS_eq : ∏ s ∈ S, (1 - 1 / (s : ℚ)) =
        (∏ s ∈ S \ B, (1 - 1 / (s : ℚ))) * (∏ x ∈ B ∩ S, (1 - 1 / (x : ℚ))) := by
      rw [Finset.inter_comm B S, ← Finset.prod_union (Finset.disjoint_sdiff_inter S B), Finset.sdiff_union_inter]
    rw [hB_eq, hS_eq]
    exact mul_le_mul_of_nonneg_right hdiff hinter_nn

-- 3.4b Prime-block wrapper for primorial bounds

private def primeBlock (lo M : ℕ) : Finset ℕ :=
  (Finset.Icc lo M).filter Nat.Prime

private lemma primeBlock_card_le {S : Finset ℕ} {lo M c : ℕ}
    (hS : ∀ s ∈ S, s.Prime ∧ lo ≤ s)
    (hprod : ∏ s ∈ S, s < ∏ a ∈ primeBlock lo M, a)
    (hcardA : (primeBlock lo M).card = c + 1) :
    S.card ≤ c := by
  have hlt : S.card < (primeBlock lo M).card := by
    refine primorial_card_lt (M := M) (fun s hs => (hS s hs).1.one_le)
      (fun a ha => (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2)
      (fun s hs hnot => ?_) hprod
    by_contra hle
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hS s hs).2, by omega⟩, (hS s hs).1⟩)
  omega

private lemma primeBlock_phi_ge {S : Finset ℕ} {lo M' : ℕ}
    (hS : ∀ s ∈ S, s.Prime ∧ lo ≤ s)
    (hcard : S.card ≤ (primeBlock lo M').card) :
    ∏ b ∈ primeBlock lo M', (1 - 1 / (b : ℚ)) ≤ ∏ s ∈ S, (1 - 1 / (s : ℚ)) := by
  refine primorial_phi_ge (M' := M')
    (fun b hb => (Finset.mem_filter.mp hb).2.one_le)
    (fun b hb => (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2)
    (fun s hs hnot => ?_) hcard
  by_contra hle
  exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hS s hs).2, by omega⟩, (hS s hs).1⟩)

-- 3.5 Pure-ℕ/ℚ Multiplicative Bounds for Asymptotic Regime (m >= 10^17)

private lemma nat_sub_one_pow12_ge_pow11 (q : ℕ) (hq : 7 ≤ q) : q ^ 11 ≤ (q - 1) ^ 12 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hq
  rw [show t + 7 - 1 = t + 6 by omega]
  have hid : (t + 6) ^ 12 = (t + 7) ^ 11 +
      (t ^ 12 + 71 * t ^ 11 + 2299 * t ^ 10 + 44825 * t ^ 9 + 584925 * t ^ 8 +
       5366262 * t ^ 7 + 35345310 * t ^ 6 + 167355474 * t ^ 5 + 559640730 * t ^ 4 +
       1265900955 * t ^ 3 + 1771319231 * t ^ 2 + 1246336933 * t + 199455593) := by ring
  omega

private lemma prod_rat_ge_one {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℚ)
    (hf : ∀ x ∈ S, (1 : ℚ) ≤ f x) : (1 : ℚ) ≤ ∏ x ∈ S, f x := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : (1 : ℚ) ≤ f a := hf a (Finset.mem_insert_self a s)
    have h2 : (1 : ℚ) ≤ ∏ x ∈ s, f x := ih (fun x hx => hf x (Finset.mem_insert_of_mem hx))
    nlinarith

private lemma phi_odd_pow12 (P : Finset ℕ) (hP : ∀ q ∈ P, q.Prime ∧ q ≠ 2) :
    (66 / 100 : ℚ) ^ 12 ≤ (∏ q ∈ P, (q : ℚ)) * (∏ q ∈ P, (1 - 1 / (q : ℚ))) ^ 12 := by
  have hrhs : (∏ q ∈ P, (q : ℚ)) * (∏ q ∈ P, (1 - 1 / (q : ℚ))) ^ 12 =
      ∏ q ∈ P, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  rw [hrhs]
  set S35 : Finset ℕ := {3, 5}
  have hsplit : ∏ q ∈ P, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12) =
      (∏ q ∈ P ∩ S35, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12)) *
      (∏ q ∈ P \ S35, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12)) := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff_inter P S35).symm,
      Finset.union_comm, Finset.sdiff_union_inter]
  have hge1 : (1 : ℚ) ≤ ∏ q ∈ P \ S35, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12) := by
    refine prod_rat_ge_one (P \ S35) _ fun q hq => ?_
    have hqP := (Finset.mem_sdiff.mp hq).1
    have hqNot := (Finset.mem_sdiff.mp hq).2
    have ⟨hpr, hne2⟩ := hP q hqP
    have hq7 : 7 ≤ q := by
      have h2 := hpr.two_le
      have hne3 : q ≠ 3 := fun h => hqNot (by simp [S35, h])
      have hne5 : q ≠ 5 := fun h => hqNot (by simp [S35, h])
      have hodd : q % 2 = 1 := (hpr.eq_two_or_odd).resolve_left hne2
      omega
    have hpow : (q : ℚ) ^ 11 ≤ ((q - 1 : ℕ) : ℚ) ^ 12 := by
      exact_mod_cast nat_sub_one_pow12_ge_pow11 q hq7
    have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hpr.pos
    have hsub : 1 - 1 / (q : ℚ) = ((q - 1 : ℕ) : ℚ) / (q : ℚ) := by
      rw [Nat.cast_sub hpr.one_le, Nat.cast_one]
      field_simp
    rw [hsub, div_pow]
    rw [show (q : ℚ) * (((q - 1 : ℕ) : ℚ) ^ 12 / (q : ℚ) ^ 12) =
        ((q - 1 : ℕ) : ℚ) ^ 12 / (q : ℚ) ^ 11 by field_simp]
    rw [one_le_div (by positivity)]
    exact hpow
  have hS35_le : ∏ q ∈ S35, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12) ≤
      ∏ q ∈ P ∩ S35, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12) := by
    have hsub : P ∩ S35 ⊆ S35 := Finset.inter_subset_right
    have heq : ∏ q ∈ S35, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12) =
        (∏ q ∈ P ∩ S35, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12)) *
        (∏ q ∈ S35 \ (P ∩ S35), ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12)) := by
      rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
    rw [heq]
    have hnn : 0 ≤ ∏ q ∈ P ∩ S35, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12) := by
      refine Finset.prod_nonneg fun q hq => ?_
      have hq35 := (Finset.mem_inter.mp hq).2
      simp only [S35, Finset.mem_insert, Finset.mem_singleton] at hq35
      rcases hq35 with rfl | rfl <;> norm_num
    have hle1 : ∏ q ∈ S35 \ (P ∩ S35), ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12) ≤ 1 := by
      refine Finset.prod_le_one (fun q hq => ?_) (fun q hq => ?_)
      · have hq35 := (Finset.mem_sdiff.mp hq).1
        simp only [S35, Finset.mem_insert, Finset.mem_singleton] at hq35
        rcases hq35 with rfl | rfl <;> norm_num
      · have hq35 := (Finset.mem_sdiff.mp hq).1
        simp only [S35, Finset.mem_insert, Finset.mem_singleton] at hq35
        rcases hq35 with rfl | rfl <;> norm_num
    nlinarith
  have hval : (66 / 100 : ℚ) ^ 12 ≤ ∏ q ∈ S35, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12) := by
    simp only [S35, Finset.prod_pair (by norm_num : (3 : ℕ) ≠ 5)]
    norm_num
  have hS35_nn : (0 : ℚ) ≤ ∏ q ∈ P ∩ S35, ((q : ℚ) * (1 - 1 / (q : ℚ)) ^ 12) :=
    le_trans (by positivity) (le_trans hval hS35_le)
  rw [hsplit]
  nlinarith

private lemma two_pow_card_odd_pow6 (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime ∧ q ≠ 2) :
    ((2 : ℚ) ^ Q.card) ^ 6 ≤ (22 : ℚ) ^ 6 * ∏ q ∈ Q, (q : ℚ) := by
  have hprod_pos : (0 : ℚ) < ∏ q ∈ Q, (q : ℚ) :=
    Finset.prod_pos fun q hq => by exact_mod_cast (hQ q hq).1.pos
  have hratio : ∏ q ∈ Q, ((64 : ℚ) / (q : ℚ)) = ((2 : ℚ) ^ Q.card) ^ 6 / ∏ q ∈ Q, (q : ℚ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const]
    congr 1
    rw [show (64 : ℚ) = (2 : ℚ) ^ 6 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  rw [← div_le_iff₀ hprod_pos, ← hratio]
  set S61 : Finset ℕ := (Finset.Icc 3 61).filter Nat.Prime
  have hsplit : ∏ q ∈ Q, ((64 : ℚ) / (q : ℚ)) =
      (∏ q ∈ Q ∩ S61, ((64 : ℚ) / (q : ℚ))) * (∏ q ∈ Q \ S61, ((64 : ℚ) / (q : ℚ))) := by
    rw [← Finset.prod_union (Finset.disjoint_sdiff_inter Q S61).symm,
      Finset.union_comm, Finset.sdiff_union_inter]
  have hle1 : ∏ q ∈ Q \ S61, ((64 : ℚ) / (q : ℚ)) ≤ 1 := by
    refine Finset.prod_le_one (fun q hq => by positivity) (fun q hq => ?_)
    have hqQ := (Finset.mem_sdiff.mp hq).1
    have hqNot := (Finset.mem_sdiff.mp hq).2
    have ⟨hpr, hne2⟩ := hQ q hqQ
    have hq3 : 3 ≤ q := by have := hpr.two_le; omega
    have hq62 : 62 ≤ q := by
      by_contra hlt
      exact hqNot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq3, by omega⟩, hpr⟩)
    have hq64 : 64 ≤ q := by
      have hne62 : q ≠ 62 := fun h => by subst h; norm_num at hpr
      have hne63 : q ≠ 63 := fun h => by subst h; norm_num at hpr
      omega
    have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hpr.pos
    rw [div_le_one hq_pos]
    exact_mod_cast hq64
  have hS61_eq : S61 = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61} := by
    decide +kernel
  have hS61_ge1 : ∀ q ∈ S61, (1 : ℚ) ≤ (64 : ℚ) / (q : ℚ) := by
    intro q hq
    have hqI := (Finset.mem_filter.mp hq).1
    have hq_pos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast (by have := (Finset.mem_Icc.mp hqI).1; omega : 0 < q)
    have hq_le : (q : ℚ) ≤ 64 := by exact_mod_cast (by have := (Finset.mem_Icc.mp hqI).2; omega : q ≤ 64)
    rw [one_le_div hq_pos]; exact hq_le
  have hpart_le : ∏ q ∈ Q ∩ S61, ((64 : ℚ) / (q : ℚ)) ≤ ∏ q ∈ S61, ((64 : ℚ) / (q : ℚ)) := by
    have hsub : Q ∩ S61 ⊆ S61 := Finset.inter_subset_right
    have heq : ∏ q ∈ S61, ((64 : ℚ) / (q : ℚ)) =
        (∏ q ∈ Q ∩ S61, ((64 : ℚ) / (q : ℚ))) * (∏ q ∈ S61 \ (Q ∩ S61), ((64 : ℚ) / (q : ℚ))) := by
      rw [← Finset.prod_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hsub]
    rw [heq]
    have hnn : 0 ≤ ∏ q ∈ Q ∩ S61, ((64 : ℚ) / (q : ℚ)) := Finset.prod_nonneg fun _ _ => by positivity
    have hge : 1 ≤ ∏ q ∈ S61 \ (Q ∩ S61), ((64 : ℚ) / (q : ℚ)) :=
      prod_rat_ge_one (S61 \ (Q ∩ S61)) _ fun q hq => hS61_ge1 q (Finset.mem_sdiff.mp hq).1
    nlinarith
  have hval : ∏ q ∈ S61, ((64 : ℚ) / (q : ℚ)) ≤ (22 : ℚ) ^ 6 := by
    rw [hS61_eq]
    norm_num
  have hnn_part : 0 ≤ ∏ q ∈ Q ∩ S61, ((64 : ℚ) / (q : ℚ)) :=
    Finset.prod_nonneg fun _ _ => by positivity
  rw [hsplit]
  nlinarith

-- ## Section 4: Unified Band Lemma (9 Bands [12000000, 10^17]) and Asymptotic Regime (m ≥ 10^17)

-- 4.1 Basic product bounds on P (odd squared prime divisors of m) and Q (odd prime divisors of m)

private lemma prod_P_sq_le {m : ℕ} (hm : 1 ≤ m) :
    (∏ q ∈ m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m), q) ^ 2 ≤ m := by
  set P := m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)
  rw [← Finset.prod_pow]
  have hdvd : ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime ∧ q ^ 2 ∣ m) → (∏ q ∈ S, q ^ 2) ∣ m := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hS
      rw [Finset.prod_insert ha]
      have ha_info := hS a (Finset.mem_insert_self a s)
      have hs_dvd : (∏ q ∈ s, q ^ 2) ∣ m := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
      have hcop : Nat.Coprime (a ^ 2) (∏ q ∈ s, q ^ 2) := by
        refine Nat.Coprime.prod_right fun q hq => ?_
        have hq_pr := (hS q (Finset.mem_insert_of_mem hq)).1
        have hne : a ≠ q := fun h => ha (h ▸ hq)
        exact ((Nat.coprime_primes ha_info.1 hq_pr).mpr hne).pow 2 2
      exact hcop.mul_dvd_of_dvd_of_dvd ha_info.2 hs_dvd
  have hPdvd : (∏ q ∈ P, q ^ 2) ∣ m := hdvd P fun q hq =>
    ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2.2⟩
  exact Nat.le_of_dvd (by omega) hPdvd

private lemma prod_P_le_sqrt {m : ℕ} (hm : 1 ≤ m) :
    ∏ q ∈ m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m), q ≤ m.sqrt := by
  have h := prod_P_sq_le hm
  rw [sq] at h
  exact Nat.le_sqrt.mpr h

private lemma prod_Q_le_odd_part {m : ℕ} (hm : 1 ≤ m) :
    let e := m.factorization 2
    let m_odd := m / 2 ^ e
    ∏ q ∈ m_odd.primeFactors, q ≤ m_odd ∧
    m_odd ≤ m ∧
    (2 ≤ e → m_odd ≤ m / 4) ∧
    (3 ≤ e → m_odd ≤ m / 8) := by
  intro e m_odd
  have h2dvd : 2 ^ e ∣ m := Nat.ordProj_dvd m 2
  have hm_eq : 2 ^ e * m_odd = m := Nat.mul_div_cancel' h2dvd
  have hmodd_pos : 0 < m_odd := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0, mul_zero] at hm_eq
    omega
  refine ⟨Nat.le_of_dvd hmodd_pos (Nat.prod_primeFactors_dvd m_odd), ?_, ?_, ?_⟩
  · exact Nat.div_le_self m (2 ^ e)
  · intro he2
    have h4le : 4 ≤ 2 ^ e := by
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) he2
      norm_num at this; exact this
    have hmul : 4 * m_odd ≤ m := by nlinarith
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
  · intro he3
    have h8le : 8 ≤ 2 ^ e := by
      have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) he3
      norm_num at this; exact this
    have hmul : 8 * m_odd ≤ m := by nlinarith
    exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)

private lemma Q_all_odd_prime {m : ℕ} (hm : 1 ≤ m) :
    let e := m.factorization 2
    let m_odd := m / 2 ^ e
    ∀ q ∈ m_odd.primeFactors, q.Prime ∧ q ≠ 2 ∧ 3 ≤ q := by
  intro e m_odd q hq
  have hpr : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hdvd : q ∣ m_odd := Nat.dvd_of_mem_primeFactors hq
  have h2ndvd : ¬ 2 ∣ m_odd := Nat.not_dvd_ordCompl Nat.prime_two (by omega)
  have hne2 : q ≠ 2 := fun h => h2ndvd (h ▸ hdvd)
  have h3 : 3 ≤ q := by have := hpr.two_le; omega
  exact ⟨hpr, hne2, h3⟩

private lemma largeTailBound_le_of_bounds {m W Y_max c0 c2 c3 : ℕ} {lg : ℚ}
    (hY : (m - 1) / W ^ 2 ≤ Y_max)
    (hc0 : (m / 2 ^ (m.factorization 2)).primeFactors.card ≤ c0)
    (hc2 : 2 ≤ m.factorization 2 → (m / 2 ^ (m.factorization 2)).primeFactors.card ≤ c2)
    (hc3 : 3 ≤ m.factorization 2 → (m / 2 ^ (m.factorization 2)).primeFactors.card ≤ c3)
    (hlg0 : (((Y_max + 3) / 4 : ℕ) : ℚ) * ((2 : ℚ) ^ c0 / 2) ≤ lg)
    (hlg2 : (((Y_max + 5) / 8 : ℕ) : ℚ) * (2 : ℚ) ^ c2 ≤ lg)
    (hlg3 : (((Y_max + 1) / 8 : ℕ) : ℚ) * (2 * (2 : ℚ) ^ c3) ≤ lg) :
    largeTailBound m W ≤ lg := by
  unfold largeTailBound
  dsimp only
  set e := m.factorization 2
  set Q := (m / 2 ^ e).primeFactors
  set Y : ℕ := (m - 1) / W ^ 2
  split_ifs with he1 he2
  · have h1 : (((Y + 3) / 4 : ℕ) : ℚ) ≤ (((Y_max + 3) / 4 : ℕ) : ℚ) := by
      exact_mod_cast Nat.div_le_div_right (by omega : Y + 3 ≤ Y_max + 3)
    have h2 : (2 : ℚ) ^ Q.card / 2 ≤ (2 : ℚ) ^ c0 / 2 := by
      have hp : (2 : ℚ) ^ Q.card ≤ (2 : ℚ) ^ c0 := pow_le_pow_right₀ (by norm_num) hc0
      linarith
    exact le_trans (mul_le_mul h1 h2 (by positivity) (by positivity)) hlg0
  · have h1 : (((Y + 5) / 8 : ℕ) : ℚ) ≤ (((Y_max + 5) / 8 : ℕ) : ℚ) := by
      exact_mod_cast Nat.div_le_div_right (by omega : Y + 5 ≤ Y_max + 5)
    have h2 : (2 : ℚ) ^ Q.card ≤ (2 : ℚ) ^ c2 := pow_le_pow_right₀ (by norm_num) (hc2 (by omega))
    exact le_trans (mul_le_mul h1 h2 (by positivity) (by positivity)) hlg2
  · have h1 : (((Y + 1) / 8 : ℕ) : ℚ) ≤ (((Y_max + 1) / 8 : ℕ) : ℚ) := by
      exact_mod_cast Nat.div_le_div_right (by omega : Y + 1 ≤ Y_max + 1)
    have h2 : 2 * (2 : ℚ) ^ Q.card ≤ 2 * (2 : ℚ) ^ c3 := by
      have hp : (2 : ℚ) ^ Q.card ≤ (2 : ℚ) ^ c3 := pow_le_pow_right₀ (by norm_num) (hc3 (by omega))
      linarith
    exact le_trans (mul_le_mul h1 h2 (by positivity) (by positivity)) hlg3

private lemma largeTailBound_le_uniform (m W : ℕ) :
    largeTailBound m W ≤
      ((((m - 1) / W ^ 2 : ℕ) : ℚ) / 4 + 1) *
        (2 : ℚ) ^ (m / 2 ^ (m.factorization 2)).primeFactors.card := by
  unfold largeTailBound
  dsimp only
  set Q := (m / 2 ^ (m.factorization 2)).primeFactors
  set Y : ℕ := (m - 1) / W ^ 2
  have hY_nn : (0 : ℚ) ≤ (Y : ℚ) := Nat.cast_nonneg Y
  have hQ_nn : (0 : ℚ) ≤ (2 : ℚ) ^ Q.card := by positivity
  split_ifs
  · have hd : (((Y + 3) / 4 : ℕ) : ℚ) ≤ ((Y : ℚ) + 3) / 4 := by
      have hnat : ((Y + 3) / 4) * 4 ≤ Y + 3 := Nat.div_mul_le_self (Y + 3) 4
      have hq : (((Y + 3) / 4 : ℕ) : ℚ) * 4 ≤ (Y : ℚ) + 3 := by exact_mod_cast hnat
      linarith
    have hcoef : (((Y + 3) / 4 : ℕ) : ℚ) / 2 ≤ (Y : ℚ) / 4 + 1 := by linarith
    have heq : (((Y + 3) / 4 : ℕ) : ℚ) * ((2 : ℚ) ^ Q.card / 2) =
        ((((Y + 3) / 4 : ℕ) : ℚ) / 2) * (2 : ℚ) ^ Q.card := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hcoef hQ_nn
  · have hd : (((Y + 5) / 8 : ℕ) : ℚ) ≤ ((Y : ℚ) + 5) / 8 := by
      have hnat : ((Y + 5) / 8) * 8 ≤ Y + 5 := Nat.div_mul_le_self (Y + 5) 8
      have hq : (((Y + 5) / 8 : ℕ) : ℚ) * 8 ≤ (Y : ℚ) + 5 := by exact_mod_cast hnat
      linarith
    have hcoef : (((Y + 5) / 8 : ℕ) : ℚ) ≤ (Y : ℚ) / 4 + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hcoef hQ_nn
  · have hd : (((Y + 1) / 8 : ℕ) : ℚ) ≤ ((Y : ℚ) + 1) / 8 := by
      have hnat : ((Y + 1) / 8) * 8 ≤ Y + 1 := Nat.div_mul_le_self (Y + 1) 8
      have hq : (((Y + 1) / 8 : ℕ) : ℚ) * 8 ≤ (Y : ℚ) + 1 := by exact_mod_cast hnat
      linarith
    have hcoef : 2 * (((Y + 1) / 8 : ℕ) : ℚ) ≤ (Y : ℚ) / 4 + 1 := by linarith
    have heq : (((Y + 1) / 8 : ℕ) : ℚ) * (2 * (2 : ℚ) ^ Q.card) =
        (2 * (((Y + 1) / 8 : ℕ) : ℚ)) * (2 : ℚ) ^ Q.card := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hcoef hQ_nn

-- 4.2 Unified Band Lemma

private lemma band_lemma {m Z W K_lo ps_cnt c3 c5 : ℕ}
    {tail_q pi_slope pi_const pmid1_slope pmid1_const lg phi3 phi5 : ℚ}
    (hm : 16 ≤ m) (hZ3 : 3 ≤ Z) (hZW : Z ≤ W) (hK_lo : K_lo ≤ (m - 1).sqrt)
    (hTail : ∑ p ∈ (Finset.Ioc Z (min W (m - 1).sqrt.sqrt)).filter Nat.Prime,
        (1 : ℚ) / (p : ℚ) ^ 2 ≤ tail_q)
    (hPi : (piCount W : ℚ) ≤ pi_slope * ((m - 1).sqrt : ℚ) + pi_const)
    (hPmid1 : (((Finset.Ioc Z (min W (m - 1).sqrt.sqrt)).filter Nat.Prime).card : ℚ) ≤
        pmid1_slope * ((m - 1).sqrt : ℚ) + pmid1_const)
    (hLg : largeTailBound m W ≤ lg)
    (hPs : ((Finset.Icc 3 Z).filter Nat.Prime).card ≤ ps_cnt)
    (h3in : 3 ∈ m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m) →
        (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ c3 ∧
        phi3 ≤ ∏ q ∈ m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m), (1 - 1 / (q : ℚ)))
    (h3out : 3 ∉ m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m) →
        (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ c5 ∧
        phi5 ≤ ∏ q ∈ m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m), (1 - 1 / (q : ℚ)))
    (hpos3 : 0 ≤ phi3 * (81 / 200) - tail_q - pi_slope - pmid1_slope)
    (hmarg3 : 2 ≤ (phi3 * (81 / 200) - tail_q - pi_slope - pmid1_slope) * (K_lo : ℚ) -
        ((1 + 2 * ((ps_cnt - 1 : ℕ) : ℚ)) * (2 : ℚ) ^ c3 + pi_const + pmid1_const + lg))
    (hpos5 : 0 ≤ phi5 * (59 / 200) - tail_q - pi_slope - pmid1_slope)
    (hmarg5 : 2 ≤ (phi5 * (59 / 200) - tail_q - pi_slope - pmid1_slope) * (K_lo : ℚ) -
        ((1 + 2 * (ps_cnt : ℚ)) * (2 : ℚ) ^ c5 + pi_const + pmid1_const + lg)) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  set P := m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)
  set phiP : ℚ := ∏ q ∈ P, (1 - 1 / (q : ℚ))
  set Psmall := (Finset.Icc 3 Z).filter (fun p => p.Prime ∧ ¬ p ∣ m)
  set Pmid1 := (Finset.Ioc Z (min W K.sqrt)).filter (fun p => p.Prime)
  set Pmid2 := (Finset.Ioc (max Z K.sqrt) W).filter (fun p => p.Prime)
  have hms := master_sieve hm (by omega : 2 ≤ Z) hZW
  change (representations m : ℚ) ≥
      ((K : ℚ) / 2) * phiP * (1 - ∑ p ∈ Psmall, (2 / (p : ℚ) ^ 2))
      - (1 + 2 * (Psmall.card : ℚ)) * (2 : ℚ) ^ P.card
      - (K : ℚ) * (∑ p ∈ Pmid1, (1 / (p : ℚ) ^ 2))
      - 2 * (Pmid1.card : ℚ) - (Pmid2.card : ℚ)
      - largeTailBound m W at hms
  have hdisj : Disjoint Pmid1 Pmid2 := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have hp1 : p ≤ K.sqrt := le_trans (Finset.mem_Ioc.mp (Finset.mem_filter.mp h1).1).2 (min_le_right _ _)
    have hp2 : K.sqrt < p := lt_of_le_of_lt (le_max_right Z K.sqrt) (Finset.mem_Ioc.mp (Finset.mem_filter.mp h2).1).1
    omega
  have hunion_sub : Pmid1 ∪ Pmid2 ⊆ (Finset.Icc 1 W).filter Nat.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · have hI := (Finset.mem_filter.mp h).1
      have hpr := (Finset.mem_filter.mp h).2
      have hgt := (Finset.mem_Ioc.mp hI).1
      have hle := le_trans (Finset.mem_Ioc.mp hI).2 (min_le_left _ _)
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, hpr⟩
    · have hI := (Finset.mem_filter.mp h).1
      have hpr := (Finset.mem_filter.mp h).2
      have hgt := lt_of_le_of_lt (le_max_left Z K.sqrt) (Finset.mem_Ioc.mp hI).1
      have hle := (Finset.mem_Ioc.mp hI).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hle⟩, hpr⟩
  have hmid_sum : (Pmid1.card : ℚ) + (Pmid2.card : ℚ) ≤ (piCount W : ℚ) := by
    have hnat : Pmid1.card + Pmid2.card ≤ piCount W := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hunion_sub
    exact_mod_cast hnat
  have hK_nn : (0 : ℚ) ≤ (K : ℚ) := Nat.cast_nonneg K
  have hK_lo_q : (K_lo : ℚ) ≤ (K : ℚ) := by exact_mod_cast hK_lo
  have htail_mul : (K : ℚ) * (∑ p ∈ Pmid1, (1 / (p : ℚ) ^ 2)) ≤ (K : ℚ) * tail_q :=
    mul_le_mul_of_nonneg_left hTail hK_nn
  have hrep_q : (2 : ℚ) ≤ (representations m : ℚ) := by
    by_cases h3 : 3 ∈ P
    · obtain ⟨hPcard, hphi⟩ := h3in h3
      have h3dvd : 3 ∣ m := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp h3).1
      have hPsmall_ge5 : ∀ p ∈ Psmall, p.Prime ∧ 5 ≤ p := by
        intro p hp
        have hI := (Finset.mem_filter.mp hp).1
        have hpr := (Finset.mem_filter.mp hp).2.1
        have hndvd := (Finset.mem_filter.mp hp).2.2
        have hp3 : 3 ≤ p := (Finset.mem_Icc.mp hI).1
        have hne3 : p ≠ 3 := fun h => hndvd (h ▸ h3dvd)
        have hne4 : p ≠ 4 := fun h => by subst h; norm_num at hpr
        exact ⟨hpr, by omega⟩
      have hsum_small : ∑ p ∈ Psmall, (2 : ℚ) / (p : ℚ) ^ 2 ≤ 19 / 100 :=
        sum_2_inv_sq_primes_ge5 Psmall hPsmall_ge5
      have hPs_sub : Psmall ⊆ ((Finset.Icc 3 Z).filter Nat.Prime).erase 3 := by
        intro p hp
        have hI := (Finset.mem_filter.mp hp).1
        have hpr := (Finset.mem_filter.mp hp).2.1
        have hndvd := (Finset.mem_filter.mp hp).2.2
        have hne3 : p ≠ 3 := fun h => hndvd (h ▸ h3dvd)
        exact Finset.mem_erase.mpr ⟨hne3, Finset.mem_filter.mpr ⟨hI, hpr⟩⟩
      have h3mem : 3 ∈ (Finset.Icc 3 Z).filter Nat.Prime :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hZ3⟩, Nat.prime_three⟩
      have hPsmall_card : (Psmall.card : ℚ) ≤ ((ps_cnt - 1 : ℕ) : ℚ) := by
        have h1 : Psmall.card ≤ ((Finset.Icc 3 Z).filter Nat.Prime).card - 1 := by
          rw [← Finset.card_erase_of_mem h3mem]
          exact Finset.card_le_card hPs_sub
        exact_mod_cast le_trans h1 (Nat.sub_le_sub_right hPs 1)
      have hpow : (2 : ℚ) ^ P.card ≤ (2 : ℚ) ^ c3 := pow_le_pow_right₀ (by norm_num) hPcard
      have hsmall_err : (1 + 2 * (Psmall.card : ℚ)) * (2 : ℚ) ^ P.card ≤
          (1 + 2 * ((ps_cnt - 1 : ℕ) : ℚ)) * (2 : ℚ) ^ c3 :=
        mul_le_mul (by linarith) hpow (by positivity) (by positivity)
      have hphi_nn : 0 ≤ phiP := Finset.prod_nonneg fun q hq => by
        have hq1 : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).one_le
        rw [sub_nonneg, div_le_one (by linarith)]; exact hq1
      have hmain : ((K : ℚ) / 2) * phiP * (1 - ∑ p ∈ Psmall, (2 / (p : ℚ) ^ 2)) ≥
          (K : ℚ) * (phi3 * (81 / 200)) := by
        have h1 : ((K : ℚ) / 2) * phiP * (81 / 100) ≤
            ((K : ℚ) / 2) * phiP * (1 - ∑ p ∈ Psmall, (2 / (p : ℚ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h2 : (K : ℚ) * (phi3 * (81 / 200)) ≤ ((K : ℚ) / 2) * phiP * (81 / 100) := by
          have : phi3 * (81 / 200) ≤ phiP * (81 / 200) := mul_le_mul_of_nonneg_right hphi (by norm_num)
          have hmul := mul_le_mul_of_nonneg_left this hK_nn
          linarith
        linarith
      have hK_step : (phi3 * (81 / 200) - tail_q - pi_slope - pmid1_slope) * (K_lo : ℚ) ≤
          (phi3 * (81 / 200) - tail_q - pi_slope - pmid1_slope) * (K : ℚ) :=
        mul_le_mul_of_nonneg_left hK_lo_q hpos3
      linarith
    · obtain ⟨hPcard, hphi⟩ := h3out h3
      have hPsmall_ge3 : ∀ p ∈ Psmall, p.Prime ∧ 3 ≤ p := fun p hp =>
        ⟨(Finset.mem_filter.mp hp).2.1, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩
      have hsum_small : ∑ p ∈ Psmall, (2 : ℚ) / (p : ℚ) ^ 2 ≤ 41 / 100 :=
        sum_2_inv_sq_primes_ge3 Psmall hPsmall_ge3
      have hPs_sub : Psmall ⊆ (Finset.Icc 3 Z).filter Nat.Prime := fun p hp =>
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.1⟩
      have hPsmall_card : (Psmall.card : ℚ) ≤ (ps_cnt : ℚ) := by
        exact_mod_cast le_trans (Finset.card_le_card hPs_sub) hPs
      have hpow : (2 : ℚ) ^ P.card ≤ (2 : ℚ) ^ c5 := pow_le_pow_right₀ (by norm_num) hPcard
      have hsmall_err : (1 + 2 * (Psmall.card : ℚ)) * (2 : ℚ) ^ P.card ≤
          (1 + 2 * (ps_cnt : ℚ)) * (2 : ℚ) ^ c5 :=
        mul_le_mul (by linarith) hpow (by positivity) (by positivity)
      have hphi_nn : 0 ≤ phiP := Finset.prod_nonneg fun q hq => by
        have hq1 : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).one_le
        rw [sub_nonneg, div_le_one (by linarith)]; exact hq1
      have hmain : ((K : ℚ) / 2) * phiP * (1 - ∑ p ∈ Psmall, (2 / (p : ℚ) ^ 2)) ≥
          (K : ℚ) * (phi5 * (59 / 200)) := by
        have h1 : ((K : ℚ) / 2) * phiP * (59 / 100) ≤
            ((K : ℚ) / 2) * phiP * (1 - ∑ p ∈ Psmall, (2 / (p : ℚ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h2 : (K : ℚ) * (phi5 * (59 / 200)) ≤ ((K : ℚ) / 2) * phiP * (59 / 100) := by
          have : phi5 * (59 / 200) ≤ phiP * (59 / 200) := mul_le_mul_of_nonneg_right hphi (by norm_num)
          have hmul := mul_le_mul_of_nonneg_left this hK_nn
          linarith
        linarith
      have hK_step : (phi5 * (59 / 200) - tail_q - pi_slope - pmid1_slope) * (K_lo : ℚ) ≤
          (phi5 * (59 / 200) - tail_q - pi_slope - pmid1_slope) * (K : ℚ) :=
        mul_le_mul_of_nonneg_left hK_lo_q hpos5
      linarith
  exact_mod_cast hrep_q

-- 4.3 Helper lemmas for instantiating the 9 bands cleanly

private lemma div_W_Y_bound {m K_lo wn wd Y_max : ℕ}
    (hK_lo : K_lo ≤ (m - 1).sqrt) (hwd : 0 < wd) (hwnK : wd ≤ wn * K_lo)
    (hquad : ∀ t : ℤ, 0 ≤ t →
      (wd : ℤ) ^ 2 * ((K_lo : ℤ) + t + 1) ^ 2 ≤
        ((Y_max : ℤ) + 1) * ((wn : ℤ) * ((K_lo : ℤ) + t) - ((wd : ℤ) - 1)) ^ 2) :
    (m - 1) / (wn * (m - 1).sqrt / wd) ^ 2 ≤ Y_max := by
  set K := (m - 1).sqrt
  set W := wn * K / wd
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hK_lo
  have hW_pos : 0 < W := Nat.div_pos (by nlinarith) hwd
  have hW_mul : wn * K ≤ wd * W + (wd - 1) := by
    have hdm : wd * W + wn * K % wd = wn * K := Nat.div_add_mod (wn * K) wd
    have hlt : wn * K % wd ≤ wd - 1 := Nat.le_sub_one_of_lt (Nat.mod_lt (wn * K) hwd)
    omega
  have hsub_z : (wn : ℤ) * ((K_lo : ℤ) + (t : ℤ)) - ((wd : ℤ) - 1) ≤ (wd : ℤ) * (W : ℤ) := by
    have h1 : (wn : ℤ) * (K : ℤ) ≤ (wd : ℤ) * (W : ℤ) + ((wd - 1 : ℕ) : ℤ) := by exact_mod_cast hW_mul
    have h2 : ((wd - 1 : ℕ) : ℤ) = (wd : ℤ) - 1 := by rw [Nat.cast_sub hwd, Nat.cast_one]
    have h3 : (K : ℤ) = (K_lo : ℤ) + (t : ℤ) := by exact_mod_cast ht
    rw [h3, h2] at h1
    linarith
  have hsub_nn : (0 : ℤ) ≤ (wn : ℤ) * ((K_lo : ℤ) + (t : ℤ)) - ((wd : ℤ) - 1) := by
    have h1 : (wd : ℤ) ≤ (wn : ℤ) * (K_lo : ℤ) := by exact_mod_cast hwnK
    have h2 : (0 : ℤ) ≤ (wn : ℤ) * (t : ℤ) := by positivity
    linarith
  have hsq_z : ((wn : ℤ) * ((K_lo : ℤ) + (t : ℤ)) - ((wd : ℤ) - 1)) ^ 2 ≤ ((wd : ℤ) * (W : ℤ)) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul hsub_z hsub_z hsub_nn (le_trans hsub_nn hsub_z)
  have hm1_lt : ((m - 1 : ℕ) : ℤ) < ((K_lo : ℤ) + (t : ℤ) + 1) ^ 2 := by
    have h1 : m - 1 < (K + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt (m - 1)
    have h2 : ((m - 1 : ℕ) : ℤ) < ((K : ℤ) + 1) ^ 2 := by exact_mod_cast h1
    have h3 : (K : ℤ) = (K_lo : ℤ) + (t : ℤ) := by exact_mod_cast ht
    rw [h3] at h2
    exact h2
  have hq := hquad (t : ℤ) (Nat.cast_nonneg t)
  have hwd2_pos : (0 : ℤ) < (wd : ℤ) ^ 2 := by positivity
  have hlt_mul_z : (wd : ℤ) ^ 2 * ((m - 1 : ℕ) : ℤ) <
      (wd : ℤ) ^ 2 * (((Y_max : ℤ) + 1) * (W : ℤ) ^ 2) := by
    have h1 : (wd : ℤ) ^ 2 * ((m - 1 : ℕ) : ℤ) < (wd : ℤ) ^ 2 * ((K_lo : ℤ) + (t : ℤ) + 1) ^ 2 :=
      mul_lt_mul_of_pos_left hm1_lt hwd2_pos
    have h2 : ((Y_max : ℤ) + 1) * ((wn : ℤ) * ((K_lo : ℤ) + (t : ℤ)) - ((wd : ℤ) - 1)) ^ 2 ≤
        ((Y_max : ℤ) + 1) * ((wd : ℤ) * (W : ℤ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq_z (by positivity)
    have h3 : ((Y_max : ℤ) + 1) * ((wd : ℤ) * (W : ℤ)) ^ 2 =
        (wd : ℤ) ^ 2 * (((Y_max : ℤ) + 1) * (W : ℤ) ^ 2) := by ring
    linarith
  have hlt_z : ((m - 1 : ℕ) : ℤ) < ((Y_max : ℤ) + 1) * (W : ℤ) ^ 2 :=
    lt_of_mul_lt_mul_left hlt_mul_z (le_of_lt hwd2_pos)
  have hlt : m - 1 < (Y_max + 1) * W ^ 2 := by exact_mod_cast hlt_z
  have hdiv_lt : (m - 1) / W ^ 2 < Y_max + 1 :=
    (Nat.div_lt_iff_lt_mul (pow_pos hW_pos 2)).mpr hlt
  omega

private lemma pmid1_card_le_ksqrt_div {m Z W s : ℕ} (hs_pos : 1 ≤ s) (hs : s * s ≤ (m - 1).sqrt) :
    (((Finset.Ioc Z (min W (m - 1).sqrt.sqrt)).filter Nat.Prime).card : ℚ) ≤
      (1 / (s : ℚ)) * ((m - 1).sqrt : ℚ) + 0 := by
  set K := (m - 1).sqrt
  have hsub : (Finset.Ioc Z (min W K.sqrt)).filter Nat.Prime ⊆ Finset.Icc 1 K.sqrt := by
    intro p hp
    have hI := (Finset.mem_filter.mp hp).1
    have hpr := (Finset.mem_filter.mp hp).2
    exact Finset.mem_Icc.mpr ⟨hpr.one_le, le_trans (Finset.mem_Ioc.mp hI).2 (min_le_right _ _)⟩
  have hcard : ((Finset.Ioc Z (min W K.sqrt)).filter Nat.Prime).card ≤ K.sqrt := by
    calc ((Finset.Ioc Z (min W K.sqrt)).filter Nat.Prime).card
        ≤ (Finset.Icc 1 K.sqrt).card := Finset.card_le_card hsub
      _ = K.sqrt := by simp
  have hsq_le : s ≤ K.sqrt := Nat.le_sqrt.mpr hs
  have hmul : s * K.sqrt ≤ K :=
    le_trans (Nat.mul_le_mul_right K.sqrt hsq_le) (Nat.sqrt_le K)
  have hs_qpos : (0 : ℚ) < (s : ℚ) := by exact_mod_cast hs_pos
  have hmul_q : (s : ℚ) * (K.sqrt : ℚ) ≤ (K : ℚ) := by exact_mod_cast hmul
  have hcard_q : (((Finset.Ioc Z (min W K.sqrt)).filter Nat.Prime).card : ℚ) ≤ (K.sqrt : ℚ) := by
    exact_mod_cast hcard
  have hdiv : (K.sqrt : ℚ) ≤ (1 / (s : ℚ)) * (K : ℚ) := by
    rw [one_div_mul_eq_div, le_div_iff₀ hs_qpos]
    linarith
  linarith

private lemma pmid1_card_le_pi_hi {m Z W s : ℕ} (hs : (m - 1).sqrt < (s + 1) * (s + 1)) :
    (((Finset.Ioc Z (min W (m - 1).sqrt.sqrt)).filter Nat.Prime).card : ℚ) ≤
      0 * ((m - 1).sqrt : ℚ) + (piCount s : ℚ) := by
  have hksq_le : (m - 1).sqrt.sqrt ≤ s := Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr (by rw [sq]; exact hs))
  have hsub : (Finset.Ioc Z (min W (m - 1).sqrt.sqrt)).filter Nat.Prime ⊆
      (Finset.Icc 1 s).filter Nat.Prime := by
    intro p hp
    have hI := (Finset.mem_filter.mp hp).1
    have hpr := (Finset.mem_filter.mp hp).2
    have hle : p ≤ s := le_trans (le_trans (Finset.mem_Ioc.mp hI).2 (min_le_right _ _)) hksq_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpr.one_le, hle⟩, hpr⟩
  have hnat : ((Finset.Ioc Z (min W (m - 1).sqrt.sqrt)).filter Nat.Prime).card ≤ piCount s :=
    Finset.card_le_card hsub
  have hq : (((Finset.Ioc Z (min W (m - 1).sqrt.sqrt)).filter Nat.Prime).card : ℚ) ≤
      (piCount s : ℚ) := by exact_mod_cast hnat
  linarith

private lemma P_all_primes {m : ℕ} :
    let P := m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)
    (∀ q ∈ P, q.Prime ∧ 3 ≤ q) ∧ (3 ∉ P → ∀ q ∈ P, q.Prime ∧ 5 ≤ q) := by
  intro P
  refine ⟨fun q hq => ?_, fun hnot3 q hq => ?_⟩
  · have hpr : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    have hne2 : q ≠ 2 := (Finset.mem_filter.mp hq).2.1
    exact ⟨hpr, by have := hpr.two_le; omega⟩
  · have hpr : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1
    have hne2 : q ≠ 2 := (Finset.mem_filter.mp hq).2.1
    have hne3 : q ≠ 3 := fun h => hnot3 (h ▸ hq)
    have hne4 : q ≠ 4 := fun h => by subst h; norm_num at hpr
    exact ⟨hpr, by have := hpr.two_le; omega⟩

-- Concrete primeBlock facts (all verified in milliseconds by decide +kernel)

private lemma primeBlock_card_prod_facts :
    -- For P3 (lo = 3)
    ((primeBlock 3 13).card = 5 ∧ ∏ a ∈ primeBlock 3 13, a = 15015) ∧
    ((primeBlock 3 17).card = 6 ∧ ∏ a ∈ primeBlock 3 17, a = 255255) ∧
    ((primeBlock 3 19).card = 7 ∧ ∏ a ∈ primeBlock 3 19, a = 4849845) ∧
    ((primeBlock 3 23).card = 8 ∧ ∏ a ∈ primeBlock 3 23, a = 111546435) ∧
    ((primeBlock 3 29).card = 9 ∧ ∏ a ∈ primeBlock 3 29, a = 3234846615) ∧
    -- For P5 (lo = 5)
    ((primeBlock 5 13).card = 4 ∧ ∏ a ∈ primeBlock 5 13, a = 5005) ∧
    ((primeBlock 5 17).card = 5 ∧ ∏ a ∈ primeBlock 5 17, a = 85085) ∧
    ((primeBlock 5 19).card = 6 ∧ ∏ a ∈ primeBlock 5 19, a = 1616615) ∧
    ((primeBlock 5 23).card = 7 ∧ ∏ a ∈ primeBlock 5 23, a = 37182145) ∧
    ((primeBlock 5 29).card = 8 ∧ ∏ a ∈ primeBlock 5 29, a = 1078282205) ∧
    -- For Q (lo = 3)
    ((primeBlock 3 31).card = 10 ∧ ∏ a ∈ primeBlock 3 31, a = 100280245065) ∧
    ((primeBlock 3 37).card = 11 ∧ ∏ a ∈ primeBlock 3 37, a = 3710369067405) ∧
    ((primeBlock 3 41).card = 12 ∧ ∏ a ∈ primeBlock 3 41, a = 152125131763605) ∧
    ((primeBlock 3 43).card = 13 ∧ ∏ a ∈ primeBlock 3 43, a = 6541380665835015) ∧
    ((primeBlock 3 47).card = 14 ∧ ∏ a ∈ primeBlock 3 47, a = 307444891294245705) := by
  decide +kernel

private lemma primeBlock_phi_vals :
    ((primeBlock 3 11).card = 4 ∧ ∏ b ∈ primeBlock 3 11, (1 - 1 / (b : ℚ)) = 32 / 77) ∧
    ((primeBlock 3 13).card = 5 ∧ ∏ b ∈ primeBlock 3 13, (1 - 1 / (b : ℚ)) = 384 / 1001) ∧
    ((primeBlock 3 17).card = 6 ∧ ∏ b ∈ primeBlock 3 17, (1 - 1 / (b : ℚ)) = 6144 / 17017) ∧
    ((primeBlock 3 19).card = 7 ∧ ∏ b ∈ primeBlock 3 19, (1 - 1 / (b : ℚ)) = 110592 / 323323) ∧
    ((primeBlock 3 23).card = 8 ∧ ∏ b ∈ primeBlock 3 23, (1 - 1 / (b : ℚ)) = 221184 / 676039) ∧
    ((primeBlock 5 11).card = 3 ∧ ∏ b ∈ primeBlock 5 11, (1 - 1 / (b : ℚ)) = 48 / 77) ∧
    ((primeBlock 5 13).card = 4 ∧ ∏ b ∈ primeBlock 5 13, (1 - 1 / (b : ℚ)) = 576 / 1001) ∧
    ((primeBlock 5 17).card = 5 ∧ ∏ b ∈ primeBlock 5 17, (1 - 1 / (b : ℚ)) = 9216 / 17017) ∧
    ((primeBlock 5 19).card = 6 ∧ ∏ b ∈ primeBlock 5 19, (1 - 1 / (b : ℚ)) = 165888 / 323323) ∧
    ((primeBlock 5 23).card = 7 ∧ ∏ b ∈ primeBlock 5 23, (1 - 1 / (b : ℚ)) = 331776 / 676039) := by
  have h1 : primeBlock 3 11 = {3, 5, 7, 11} := by decide
  have h2 : primeBlock 3 13 = {3, 5, 7, 11, 13} := by decide
  have h3 : primeBlock 3 17 = {3, 5, 7, 11, 13, 17} := by decide
  have h4 : primeBlock 3 19 = {3, 5, 7, 11, 13, 17, 19} := by decide
  have h5 : primeBlock 3 23 = {3, 5, 7, 11, 13, 17, 19, 23} := by decide
  have h6 : primeBlock 5 11 = {5, 7, 11} := by decide
  have h7 : primeBlock 5 13 = {5, 7, 11, 13} := by decide
  have h8 : primeBlock 5 17 = {5, 7, 11, 13, 17} := by decide
  have h9 : primeBlock 5 19 = {5, 7, 11, 13, 17, 19} := by decide
  have h10 : primeBlock 5 23 = {5, 7, 11, 13, 17, 19, 23} := by decide
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
  norm_num

private lemma small_pi_counts :
    ((Finset.Icc 3 7).filter Nat.Prime).card = 3 ∧
    ((Finset.Icc 3 13).filter Nat.Prime).card = 5 ∧
    ((Finset.Icc 3 19).filter Nat.Prime).card = 7 ∧
    ((Finset.Icc 3 29).filter Nat.Prime).card = 9 ∧
    ((Finset.Icc 3 47).filter Nat.Prime).card = 14 ∧
    ((Finset.Icc 3 250).filter Nat.Prime).card = 52 ∧
    ((Finset.Icc 3 500).filter Nat.Prime).card = 94 ∧
    piCount 70 = 19 ∧ piCount 94 = 24 ∧ piCount 131 = 32 ∧ piCount 177 = 40 := by
  decide +kernel

-- 4.4 The Nine Middle Bands covering [12,000,000, 10^17]

private lemma band1_ok {m : ℕ} (hlo : 12000000 ≤ m) (hhi : m ≤ 25000000) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  set W := 2 * K / 5
  have hK_lo : 3464 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hK_hi : K ≤ 4999 := by have : K < 5000 := Nat.sqrt_lt'.mpr (by omega); omega
  have hW_lo : 1385 ≤ W := by omega
  have hW_hi : W ≤ 1999 := by omega
  have hm_sq : m.sqrt ≤ 5000 := by have : m.sqrt < 5001 := Nat.sqrt_lt'.mpr (by omega); omega
  have hY : (m - 1) / W ^ 2 ≤ 6 :=
    div_W_Y_bound hK_lo (by norm_num) (by norm_num) (fun t ht => by push_cast; nlinarith)
  have hP := P_all_primes (m := m)
  have hPprod := le_trans (prod_P_le_sqrt (by omega)) hm_sq
  have hQ := prod_Q_le_odd_part (m := m) (by omega)
  have hQpr := Q_all_odd_prime (m := m) (by omega)
  have hQ_all : ∀ q ∈ (m / 2 ^ (m.factorization 2)).primeFactors, q.Prime ∧ 3 ≤ q :=
    fun q hq => ⟨(hQpr q hq).1, (hQpr q hq).2.2⟩
  refine band_lemma (Z := 7) (W := W) (K_lo := 3464) (ps_cnt := 3) (c3 := 4) (c5 := 3)
    (tail_q := 312 / 10000) (pi_slope := (147 / 1000) * (2 / 5)) (pi_const := 19)
    (pmid1_slope := 0) (pmid1_const := 19) (lg := 128) (phi3 := 32 / 77) (phi5 := 48 / 77)
    (by omega) (by norm_num) (by omega) hK_lo
    (sum_inv_sq_primes_gt_via_1000 7 _ 312 (by norm_num) (by norm_num) tail_check_all.2.2.1)
    ?_ ?_ ?_ (by rw [small_pi_counts.1]) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hpi := piCount_le_linear_of_check (by norm_num) checkPiLin_bands.1 hW_lo hW_hi
    have hWq : (W : ℚ) ≤ (2 / 5 : ℚ) * (K : ℚ) := by
      have : 5 * W ≤ 2 * K := by omega
      have hq : (5 : ℚ) * (W : ℚ) ≤ 2 * (K : ℚ) := by exact_mod_cast this
      linarith
    linarith
  · have hpm := pmid1_card_le_pi_hi (m := m) (Z := 7) (W := W) (s := 70) (by omega)
    rw [small_pi_counts.2.2.2.2.2.2.2.1] at hpm
    simpa using hpm
  · refine largeTailBound_le_of_bounds (Y_max := 6) (c0 := 7) (c2 := 7) (c3 := 6) hY ?_ ?_ ?_
      (by norm_num) (by norm_num) (by norm_num)
    · exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.1.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.1.1
    · intro he3; have h8 := hQ.2.2.2 he3
      exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.1.1
  · intro _
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 4 :=
      primeBlock_card_le hP.1 (by have := primeBlock_card_prod_facts.1.2; omega)
        primeBlock_card_prod_facts.1.1
    have hph := primeBlock_phi_ge (lo := 3) (M' := 11) hP.1 (by rw [primeBlock_phi_vals.1.1]; exact hc)
    rw [primeBlock_phi_vals.1.2] at hph
    exact ⟨hc, hph⟩
  · intro hnot3
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 3 :=
      primeBlock_card_le (hP.2 hnot3) (by have := primeBlock_card_prod_facts.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 5) (M' := 11) (hP.2 hnot3)
      (by rw [primeBlock_phi_vals.2.2.2.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.2.2.1.2] at hph
    exact ⟨hc, hph⟩

private lemma band2_ok {m : ℕ} (hlo : 25000000 ≤ m) (hhi : m ≤ 80000000) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  set W := 2 * K / 5
  have hK_lo : 4999 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hK_hi : K ≤ 8944 := by have : K < 8945 := Nat.sqrt_lt'.mpr (by omega); omega
  have hW_lo : 1999 ≤ W := by omega
  have hW_hi : W ≤ 3577 := by omega
  have hm_sq : m.sqrt ≤ 8944 := by have : m.sqrt < 8945 := Nat.sqrt_lt'.mpr (by omega); omega
  have hY : (m - 1) / W ^ 2 ≤ 6 :=
    div_W_Y_bound hK_lo (by norm_num) (by norm_num) (fun t ht => by push_cast; nlinarith)
  have hP := P_all_primes (m := m)
  have hPprod := le_trans (prod_P_le_sqrt (by omega)) hm_sq
  have hQ := prod_Q_le_odd_part (m := m) (by omega)
  have hQpr := Q_all_odd_prime (m := m) (by omega)
  have hQ_all : ∀ q ∈ (m / 2 ^ (m.factorization 2)).primeFactors, q.Prime ∧ 3 ≤ q :=
    fun q hq => ⟨(hQpr q hq).1, (hQpr q hq).2.2⟩
  refine band_lemma (Z := 13) (W := W) (K_lo := 4999) (ps_cnt := 5) (c3 := 4) (c5 := 4)
    (tail_q := 170 / 10000) (pi_slope := (135 / 1000) * (2 / 5)) (pi_const := 35)
    (pmid1_slope := 0) (pmid1_const := 24) (lg := 128) (phi3 := 32 / 77) (phi5 := 576 / 1001)
    (by omega) (by norm_num) (by omega) hK_lo
    (sum_inv_sq_primes_gt_via_1000 13 _ 170 (by norm_num) (by norm_num) tail_check_all.2.2.2.1)
    ?_ ?_ ?_ (by rw [small_pi_counts.2.1]) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hpi := piCount_le_linear_of_check (by norm_num) checkPiLin_bands.2.1 hW_lo hW_hi
    have hWq : (W : ℚ) ≤ (2 / 5 : ℚ) * (K : ℚ) := by
      have : 5 * W ≤ 2 * K := by omega
      have hq : (5 : ℚ) * (W : ℚ) ≤ 2 * (K : ℚ) := by exact_mod_cast this
      linarith
    linarith
  · have hpm := pmid1_card_le_pi_hi (m := m) (Z := 13) (W := W) (s := 94) (by omega)
    rw [small_pi_counts.2.2.2.2.2.2.2.2.1] at hpm
    simpa using hpm
  · refine largeTailBound_le_of_bounds (Y_max := 6) (c0 := 7) (c2 := 7) (c3 := 7) hY ?_ ?_ ?_
      (by norm_num) (by norm_num) (by norm_num)
    · exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.1.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.1.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.1.1
  · intro _
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 4 :=
      primeBlock_card_le hP.1 (by have := primeBlock_card_prod_facts.1.2; omega)
        primeBlock_card_prod_facts.1.1
    have hph := primeBlock_phi_ge (lo := 3) (M' := 11) hP.1 (by rw [primeBlock_phi_vals.1.1]; exact hc)
    rw [primeBlock_phi_vals.1.2] at hph
    exact ⟨hc, hph⟩
  · intro hnot3
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 4 :=
      primeBlock_card_le (hP.2 hnot3) (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 5) (M' := 13) (hP.2 hnot3)
      (by rw [primeBlock_phi_vals.2.2.2.2.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.2.2.2.1.2] at hph
    exact ⟨hc, hph⟩

private lemma band3_ok {m : ℕ} (hlo : 80000000 ≤ m) (hhi : m ≤ 300000000) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  set W := K / 2
  have hK_lo : 8944 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hK_hi : K ≤ 17320 := by have : K < 17321 := Nat.sqrt_lt'.mpr (by omega); omega
  have hW_lo : 4472 ≤ W := by omega
  have hW_hi : W ≤ 8660 := by omega
  have hm_sq : m.sqrt ≤ 17320 := by have : m.sqrt < 17321 := Nat.sqrt_lt'.mpr (by omega); omega
  have hY : (m - 1) / W ^ 2 ≤ 4 := by
    have h := div_W_Y_bound (wn := 1) (wd := 2) (Y_max := 4) hK_lo (by norm_num) (by norm_num)
      (fun t ht => by push_cast; nlinarith)
    simpa [W] using h
  have hP := P_all_primes (m := m)
  have hPprod := le_trans (prod_P_le_sqrt (by omega)) hm_sq
  have hQ := prod_Q_le_odd_part (m := m) (by omega)
  have hQpr := Q_all_odd_prime (m := m) (by omega)
  have hQ_all : ∀ q ∈ (m / 2 ^ (m.factorization 2)).primeFactors, q.Prime ∧ 3 ≤ q :=
    fun q hq => ⟨(hQpr q hq).1, (hQpr q hq).2.2⟩
  refine band_lemma (Z := 7) (W := W) (K_lo := 8944) (ps_cnt := 3) (c3 := 5) (c5 := 4)
    (tail_q := 312 / 10000) (pi_slope := (120 / 1000) * (1 / 2)) (pi_const := 73)
    (pmid1_slope := 0) (pmid1_const := 32) (lg := 128) (phi3 := 384 / 1001) (phi5 := 576 / 1001)
    (by omega) (by norm_num) (by omega) hK_lo
    (sum_inv_sq_primes_gt_via_1000 7 _ 312 (by norm_num) (by norm_num) tail_check_all.2.2.1)
    ?_ ?_ ?_ (by rw [small_pi_counts.1]) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hpi := piCount_le_linear_of_check (by norm_num) checkPiLin_bands.2.2.1 hW_lo hW_hi
    have hWq : (W : ℚ) ≤ (1 / 2 : ℚ) * (K : ℚ) := by
      have : 2 * W ≤ K := by omega
      have hq : (2 : ℚ) * (W : ℚ) ≤ (K : ℚ) := by exact_mod_cast this
      linarith
    linarith
  · have hpm := pmid1_card_le_pi_hi (m := m) (Z := 7) (W := W) (s := 131) (by omega)
    rw [small_pi_counts.2.2.2.2.2.2.2.2.2.1] at hpm
    simpa using hpm
  · refine largeTailBound_le_of_bounds (Y_max := 4) (c0 := 8) (c2 := 7) (c3 := 7) hY ?_ ?_ ?_
      (by norm_num) (by norm_num) (by norm_num)
    · exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.1.1
    · intro he2; have h4 := hQ.2.2.1 he2
      exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.1.1
    · intro he3; have h8 := hQ.2.2.2 he3
      exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.1.1
  · intro _
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 5 :=
      primeBlock_card_le hP.1 (by have := primeBlock_card_prod_facts.2.1.2; omega)
        primeBlock_card_prod_facts.2.1.1
    have hph := primeBlock_phi_ge (lo := 3) (M' := 13) hP.1 (by rw [primeBlock_phi_vals.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.1.2] at hph
    exact ⟨hc, hph⟩
  · intro hnot3
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 4 :=
      primeBlock_card_le (hP.2 hnot3) (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 5) (M' := 13) (hP.2 hnot3)
      (by rw [primeBlock_phi_vals.2.2.2.2.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.2.2.2.1.2] at hph
    exact ⟨hc, hph⟩

private lemma band4_ok {m : ℕ} (hlo : 300000000 ≤ m) (hhi : m ≤ 1000000000) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  set W := 2 * K / 5
  have hK_lo : 17320 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hK_hi : K ≤ 31622 := by have : K < 31623 := Nat.sqrt_lt'.mpr (by omega); omega
  have hW_lo : 6928 ≤ W := by omega
  have hW_hi : W ≤ 12648 := by omega
  have hm_sq : m.sqrt ≤ 31622 := by have : m.sqrt < 31623 := Nat.sqrt_lt'.mpr (by omega); omega
  have hY : (m - 1) / W ^ 2 ≤ 6 :=
    div_W_Y_bound hK_lo (by norm_num) (by norm_num) (fun t ht => by push_cast; nlinarith)
  have hP := P_all_primes (m := m)
  have hPprod := le_trans (prod_P_le_sqrt (by omega)) hm_sq
  have hQ := prod_Q_le_odd_part (m := m) (by omega)
  have hQpr := Q_all_odd_prime (m := m) (by omega)
  have hQ_all : ∀ q ∈ (m / 2 ^ (m.factorization 2)).primeFactors, q.Prime ∧ 3 ≤ q :=
    fun q hq => ⟨(hQpr q hq).1, (hQpr q hq).2.2⟩
  refine band_lemma (Z := 13) (W := W) (K_lo := 17320) (ps_cnt := 5) (c3 := 5) (c5 := 4)
    (tail_q := 170 / 10000) (pi_slope := (115 / 1000) * (2 / 5)) (pi_const := 97)
    (pmid1_slope := 0) (pmid1_const := 40) (lg := 256) (phi3 := 384 / 1001) (phi5 := 576 / 1001)
    (by omega) (by norm_num) (by omega) hK_lo
    (sum_inv_sq_primes_gt_via_1000 13 _ 170 (by norm_num) (by norm_num) tail_check_all.2.2.2.1)
    ?_ ?_ ?_ (by rw [small_pi_counts.2.1]) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hpi := piCount_le_linear_of_check (by norm_num) checkPiLin_bands.2.2.2 hW_lo hW_hi
    have hWq : (W : ℚ) ≤ (2 / 5 : ℚ) * (K : ℚ) := by
      have : 5 * W ≤ 2 * K := by omega
      have hq : (5 : ℚ) * (W : ℚ) ≤ 2 * (K : ℚ) := by exact_mod_cast this
      linarith
    linarith
  · have hpm := pmid1_card_le_pi_hi (m := m) (Z := 13) (W := W) (s := 177) (by omega)
    rw [small_pi_counts.2.2.2.2.2.2.2.2.2.2] at hpm
    simpa using hpm
  · refine largeTailBound_le_of_bounds (Y_max := 6) (c0 := 8) (c2 := 8) (c3 := 8) hY ?_ ?_ ?_
      (by norm_num) (by norm_num) (by norm_num)
    · exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.1.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.1.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.1.1
  · intro _
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 5 :=
      primeBlock_card_le hP.1 (by have := primeBlock_card_prod_facts.2.1.2; omega)
        primeBlock_card_prod_facts.2.1.1
    have hph := primeBlock_phi_ge (lo := 3) (M' := 13) hP.1 (by rw [primeBlock_phi_vals.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.1.2] at hph
    exact ⟨hc, hph⟩
  · intro hnot3
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 4 :=
      primeBlock_card_le (hP.2 hnot3) (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 5) (M' := 13) (hP.2 hnot3)
      (by rw [primeBlock_phi_vals.2.2.2.2.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.2.2.2.1.2] at hph
    exact ⟨hc, hph⟩

private lemma band5_ok {m : ℕ} (hlo : 1000000000 ≤ m) (hhi : m ≤ 10000000000) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  set W := K / 4
  have hK_lo : 31622 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hm_sq : m.sqrt ≤ 100000 := by have : m.sqrt < 100001 := Nat.sqrt_lt'.mpr (by omega); omega
  have hY : (m - 1) / W ^ 2 ≤ 16 := by
    have h := div_W_Y_bound (wn := 1) (wd := 4) (Y_max := 16) hK_lo (by norm_num) (by norm_num)
      (fun t ht => by push_cast; nlinarith)
    simpa [W] using h
  have hP := P_all_primes (m := m)
  have hPprod := le_trans (prod_P_le_sqrt (by omega)) hm_sq
  have hQ := prod_Q_le_odd_part (m := m) (by omega)
  have hQpr := Q_all_odd_prime (m := m) (by omega)
  have hQ_all : ∀ q ∈ (m / 2 ^ (m.factorization 2)).primeFactors, q.Prime ∧ 3 ≤ q :=
    fun q hq => ⟨(hQpr q hq).1, (hQpr q hq).2.2⟩
  refine band_lemma (Z := 19) (W := W) (K_lo := 31622) (ps_cnt := 7) (c3 := 5) (c5 := 5)
    (tail_q := 107 / 10000) (pi_slope := (16 / 77) * (1 / 4)) (pi_const := 485)
    (pmid1_slope := 1 / 177) (pmid1_const := 0) (lg := 1024) (phi3 := 384 / 1001) (phi5 := 9216 / 17017)
    (by omega) (by norm_num) (by omega) hK_lo
    (sum_inv_sq_primes_gt_via_1000 19 _ 107 (by norm_num) (by norm_num) tail_check_all.2.2.2.2.1)
    ?_ ?_ ?_ (by rw [small_pi_counts.2.2.1]) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hpi := piCount_le_wheel2310 W
    have hWq : (W : ℚ) ≤ (1 / 4 : ℚ) * (K : ℚ) := by
      have : 4 * W ≤ K := by omega
      have hq : (4 : ℚ) * (W : ℚ) ≤ (K : ℚ) := by exact_mod_cast this
      linarith
    linarith
  · have hpm := pmid1_card_le_ksqrt_div (m := m) (Z := 19) (W := W) (s := 177) (by norm_num) (by omega)
    simpa using hpm
  · refine largeTailBound_le_of_bounds (Y_max := 16) (c0 := 9) (c2 := 8) (c3 := 8) hY ?_ ?_ ?_
      (by norm_num) (by norm_num) (by norm_num)
    · exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.1.1
    · intro he2; have h4 := hQ.2.2.1 he2
      exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.1.1
    · intro he3; have h8 := hQ.2.2.2 he3
      exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.1.1
  · intro _
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 5 :=
      primeBlock_card_le hP.1 (by have := primeBlock_card_prod_facts.2.1.2; omega)
        primeBlock_card_prod_facts.2.1.1
    have hph := primeBlock_phi_ge (lo := 3) (M' := 13) hP.1 (by rw [primeBlock_phi_vals.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.1.2] at hph
    exact ⟨hc, hph⟩
  · intro hnot3
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 5 :=
      primeBlock_card_le (hP.2 hnot3) (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 5) (M' := 17) (hP.2 hnot3)
      (by rw [primeBlock_phi_vals.2.2.2.2.2.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.2.2.2.2.1.2] at hph
    exact ⟨hc, hph⟩

private lemma band6_ok {m : ℕ} (hlo : 10000000000 ≤ m) (hhi : m ≤ 1000000000000) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  set W := K / 3
  have hK_lo : 99999 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hm_sq : m.sqrt ≤ 1000000 := by have : m.sqrt < 1000001 := Nat.sqrt_lt'.mpr (by omega); omega
  have hY : (m - 1) / W ^ 2 ≤ 9 := by
    have h := div_W_Y_bound (wn := 1) (wd := 3) (Y_max := 9) hK_lo (by norm_num) (by norm_num)
      (fun t ht => by push_cast; nlinarith)
    simpa [W] using h
  have hP := P_all_primes (m := m)
  have hPprod := le_trans (prod_P_le_sqrt (by omega)) hm_sq
  have hQ := prod_Q_le_odd_part (m := m) (by omega)
  have hQpr := Q_all_odd_prime (m := m) (by omega)
  have hQ_all : ∀ q ∈ (m / 2 ^ (m.factorization 2)).primeFactors, q.Prime ∧ 3 ≤ q :=
    fun q hq => ⟨(hQpr q hq).1, (hQpr q hq).2.2⟩
  refine band_lemma (Z := 29) (W := W) (K_lo := 99999) (ps_cnt := 9) (c3 := 6) (c5 := 5)
    (tail_q := 77 / 10000) (pi_slope := (16 / 77) * (1 / 3)) (pi_const := 485)
    (pmid1_slope := 1 / 316) (pmid1_const := 0) (lg := 2048) (phi3 := 6144 / 17017) (phi5 := 9216 / 17017)
    (by omega) (by norm_num) (by omega) hK_lo
    (sum_inv_sq_primes_gt_via_1000 29 _ 77 (by norm_num) (by norm_num) tail_check_all.2.2.2.2.2.1)
    ?_ ?_ ?_ (by rw [small_pi_counts.2.2.2.1]) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hpi := piCount_le_wheel2310 W
    have hWq : (W : ℚ) ≤ (1 / 3 : ℚ) * (K : ℚ) := by
      have : 3 * W ≤ K := by omega
      have hq : (3 : ℚ) * (W : ℚ) ≤ (K : ℚ) := by exact_mod_cast this
      linarith
    linarith
  · have hpm := pmid1_card_le_ksqrt_div (m := m) (Z := 29) (W := W) (s := 316) (by norm_num) (by omega)
    simpa using hpm
  · refine largeTailBound_le_of_bounds (Y_max := 9) (c0 := 10) (c2 := 10) (c3 := 10) hY ?_ ?_ ?_
      (by norm_num) (by norm_num) (by norm_num)
    · exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.1.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.1.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.1.1
  · intro _
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 6 :=
      primeBlock_card_le hP.1 (by have := primeBlock_card_prod_facts.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 3) (M' := 17) hP.1 (by rw [primeBlock_phi_vals.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.1.2] at hph
    exact ⟨hc, hph⟩
  · intro hnot3
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 5 :=
      primeBlock_card_le (hP.2 hnot3) (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 5) (M' := 17) (hP.2 hnot3)
      (by rw [primeBlock_phi_vals.2.2.2.2.2.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.2.2.2.2.1.2] at hph
    exact ⟨hc, hph⟩

private lemma band7_ok {m : ℕ} (hlo : 1000000000000 ≤ m) (hhi : m ≤ 100000000000000) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  set W := K / 6
  have hK_lo : 999999 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hm_sq : m.sqrt ≤ 10000000 := by have : m.sqrt < 10000001 := Nat.sqrt_lt'.mpr (by omega); omega
  have hY : (m - 1) / W ^ 2 ≤ 36 := by
    have h := div_W_Y_bound (wn := 1) (wd := 6) (Y_max := 36) hK_lo (by norm_num) (by norm_num)
      (fun t ht => by push_cast; nlinarith)
    simpa [W] using h
  have hP := P_all_primes (m := m)
  have hPprod := le_trans (prod_P_le_sqrt (by omega)) hm_sq
  have hQ := prod_Q_le_odd_part (m := m) (by omega)
  have hQpr := Q_all_odd_prime (m := m) (by omega)
  have hQ_all : ∀ q ∈ (m / 2 ^ (m.factorization 2)).primeFactors, q.Prime ∧ 3 ≤ q :=
    fun q hq => ⟨(hQpr q hq).1, (hQpr q hq).2.2⟩
  refine band_lemma (Z := 47) (W := W) (K_lo := 999999) (ps_cnt := 14) (c3 := 7) (c5 := 6)
    (tail_q := 43 / 10000) (pi_slope := (16 / 77) * (1 / 6)) (pi_const := 485)
    (pmid1_slope := 1 / 999) (pmid1_const := 0) (lg := 16384)
    (phi3 := 110592 / 323323) (phi5 := 165888 / 323323)
    (by omega) (by norm_num) (by omega) hK_lo
    (sum_inv_sq_primes_gt_via_1000 47 _ 43 (by norm_num) (by norm_num) tail_check_all.2.2.2.2.2.2.1)
    ?_ ?_ ?_ (by rw [small_pi_counts.2.2.2.2.1]) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hpi := piCount_le_wheel2310 W
    have hWq : (W : ℚ) ≤ (1 / 6 : ℚ) * (K : ℚ) := by
      have : 6 * W ≤ K := by omega
      have hq : (6 : ℚ) * (W : ℚ) ≤ (K : ℚ) := by exact_mod_cast this
      linarith
    linarith
  · have hpm := pmid1_card_le_ksqrt_div (m := m) (Z := 47) (W := W) (s := 999) (by norm_num) (by omega)
    simpa using hpm
  · refine largeTailBound_le_of_bounds (Y_max := 36) (c0 := 11) (c2 := 11) (c3 := 11) hY ?_ ?_ ?_
      (by norm_num) (by norm_num) (by norm_num)
    · exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.1.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.1.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  · intro _
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 7 :=
      primeBlock_card_le hP.1 (by have := primeBlock_card_prod_facts.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 3) (M' := 19) hP.1 (by rw [primeBlock_phi_vals.2.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.1.2] at hph
    exact ⟨hc, hph⟩
  · intro hnot3
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 6 :=
      primeBlock_card_le (hP.2 hnot3) (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 5) (M' := 19) (hP.2 hnot3)
      (by rw [primeBlock_phi_vals.2.2.2.2.2.2.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.2.2.2.2.2.1.2] at hph
    exact ⟨hc, hph⟩

private lemma band8_ok {m : ℕ} (hlo : 100000000000000 ≤ m) (hhi : m ≤ 10000000000000000) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  set W := K / 10
  have hK_lo : 9999999 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hm_sq : m.sqrt ≤ 100000000 := by have : m.sqrt < 100000001 := Nat.sqrt_lt'.mpr (by omega); omega
  have hY : (m - 1) / W ^ 2 ≤ 100 := by
    have h := div_W_Y_bound (wn := 1) (wd := 10) (Y_max := 100) hK_lo (by norm_num) (by norm_num)
      (fun t ht => by push_cast; nlinarith)
    simpa [W] using h
  have hP := P_all_primes (m := m)
  have hPprod := le_trans (prod_P_le_sqrt (by omega)) hm_sq
  have hQ := prod_Q_le_odd_part (m := m) (by omega)
  have hQpr := Q_all_odd_prime (m := m) (by omega)
  have hQ_all : ∀ q ∈ (m / 2 ^ (m.factorization 2)).primeFactors, q.Prime ∧ 3 ≤ q :=
    fun q hq => ⟨(hQpr q hq).1, (hQpr q hq).2.2⟩
  refine band_lemma (Z := 250) (W := W) (K_lo := 9999999) (ps_cnt := 52) (c3 := 7) (c5 := 7)
    (tail_q := 10 / 10000) (pi_slope := (16 / 77) * (1 / 10)) (pi_const := 485)
    (pmid1_slope := 1 / 3162) (pmid1_const := 0) (lg := 102400)
    (phi3 := 110592 / 323323) (phi5 := 331776 / 676039)
    (by omega) (by norm_num) (by omega) hK_lo
    (sum_inv_sq_primes_gt_via_1000 250 _ 10 (by norm_num) (by norm_num) tail_check_all.2.2.2.2.2.2.2.1)
    ?_ ?_ ?_ (by rw [small_pi_counts.2.2.2.2.2.1]) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hpi := piCount_le_wheel2310 W
    have hWq : (W : ℚ) ≤ (1 / 10 : ℚ) * (K : ℚ) := by
      have : 10 * W ≤ K := by omega
      have hq : (10 : ℚ) * (W : ℚ) ≤ (K : ℚ) := by exact_mod_cast this
      linarith
    linarith
  · have hpm := pmid1_card_le_ksqrt_div (m := m) (Z := 250) (W := W) (s := 3162) (by norm_num) (by omega)
    rw [show ((3162 : ℕ) : ℚ) = 3162 by norm_num] at hpm; exact hpm
  · refine largeTailBound_le_of_bounds (Y_max := 100) (c0 := 13) (c2 := 12) (c3 := 12) hY ?_ ?_ ?_
      (by norm_num) (by norm_num) (by norm_num)
    · exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · intro he2; have h4 := hQ.2.2.1 he2
      exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
    · intro he3; have h8 := hQ.2.2.2 he3
      exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1.1
  · intro _
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 7 :=
      primeBlock_card_le hP.1 (by have := primeBlock_card_prod_facts.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 3) (M' := 19) hP.1 (by rw [primeBlock_phi_vals.2.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.1.2] at hph
    exact ⟨hc, hph⟩
  · intro hnot3
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 7 :=
      primeBlock_card_le (hP.2 hnot3) (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 5) (M' := 23) (hP.2 hnot3)
      (by rw [primeBlock_phi_vals.2.2.2.2.2.2.2.2.2.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.2.2.2.2.2.2.2] at hph
    exact ⟨hc, hph⟩

private lemma band9_ok {m : ℕ} (hlo : 10000000000000000 ≤ m) (hhi : m ≤ 100000000000000000) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  set W := K / 16
  have hK_lo : 99999999 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hm_sq : m.sqrt ≤ 316227766 := by have : m.sqrt < 316227767 := Nat.sqrt_lt'.mpr (by omega); omega
  have hY : (m - 1) / W ^ 2 ≤ 256 := by
    have h := div_W_Y_bound (wn := 1) (wd := 16) (Y_max := 256) hK_lo (by norm_num) (by norm_num)
      (fun t ht => by push_cast; nlinarith)
    simpa [W] using h
  have hP := P_all_primes (m := m)
  have hPprod := le_trans (prod_P_le_sqrt (by omega)) hm_sq
  have hQ := prod_Q_le_odd_part (m := m) (by omega)
  have hQpr := Q_all_odd_prime (m := m) (by omega)
  have hQ_all : ∀ q ∈ (m / 2 ^ (m.factorization 2)).primeFactors, q.Prime ∧ 3 ≤ q :=
    fun q hq => ⟨(hQpr q hq).1, (hQpr q hq).2.2⟩
  refine band_lemma (Z := 500) (W := W) (K_lo := 99999999) (ps_cnt := 94) (c3 := 8) (c5 := 7)
    (tail_q := 7 / 10000) (pi_slope := (16 / 77) * (1 / 16)) (pi_const := 485)
    (pmid1_slope := 1 / 9999) (pmid1_const := 0) (lg := 524288)
    (phi3 := 221184 / 676039) (phi5 := 331776 / 676039)
    (by omega) (by norm_num) (by omega) hK_lo
    (sum_inv_sq_primes_gt_via_1000 500 _ 7 (by norm_num) (by norm_num) tail_check_all.2.2.2.2.2.2.2.2)
    ?_ ?_ ?_ (by rw [small_pi_counts.2.2.2.2.2.2.1]) ?_ ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · have hpi := piCount_le_wheel2310 W
    have hWq : (W : ℚ) ≤ (1 / 16 : ℚ) * (K : ℚ) := by
      have : 16 * W ≤ K := by omega
      have hq : (16 : ℚ) * (W : ℚ) ≤ (K : ℚ) := by exact_mod_cast this
      linarith
    linarith
  · have hpm := pmid1_card_le_ksqrt_div (m := m) (Z := 500) (W := W) (s := 9999) (by norm_num) (by omega)
    rw [show ((9999 : ℕ) : ℚ) = 9999 by norm_num] at hpm; exact hpm
  · refine largeTailBound_le_of_bounds (Y_max := 256) (c0 := 13) (c2 := 13) (c3 := 13) hY ?_ ?_ ?_
      (by norm_num) (by norm_num) (by norm_num)
    · exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    · intro _; exact primeBlock_card_le hQ_all (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · intro _
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 8 :=
      primeBlock_card_le hP.1 (by have := primeBlock_card_prod_facts.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 3) (M' := 23) hP.1 (by rw [primeBlock_phi_vals.2.2.2.2.1.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.2.1.2] at hph
    exact ⟨hc, hph⟩
  · intro hnot3
    have hc : (m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)).card ≤ 7 :=
      primeBlock_card_le (hP.2 hnot3) (by have := primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.1.2; omega)
        primeBlock_card_prod_facts.2.2.2.2.2.2.2.2.2.1.1
    have hph := primeBlock_phi_ge (lo := 5) (M' := 23) (hP.2 hnot3)
      (by rw [primeBlock_phi_vals.2.2.2.2.2.2.2.2.2.1]; exact hc)
    rw [primeBlock_phi_vals.2.2.2.2.2.2.2.2.2.2] at hph
    exact ⟨hc, hph⟩

-- 4.5 Pure-ℕ/ℚ Asymptotic Proof for ALL m ≥ 10^17 (zero Real numbers!)

private lemma large_m_params {m : ℕ} (hm : 100000000000000000 ≤ m) :
    let K := (m - 1).sqrt
    let P := m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)
    let Q := (m / 2 ^ (m.factorization 2)).primeFactors
    ∃ v Z W : ℕ,
      52 ≤ v ∧
      140 ≤ Z ∧ Z ≤ W ∧
      (78 / 100 : ℚ) * ((v : ℚ) ^ 12 / 1000000000000) ≤ (K : ℚ) ∧
      (Z : ℚ) ≤ (v : ℚ) ^ 3 / 1000 ∧
      (v : ℚ) ^ 3 / 1100 ≤ (Z : ℚ) - 1 ∧
      (W : ℚ) ≤ 6 * (K : ℚ) / (Z : ℚ) ∧
      5 * (K : ℚ) / (Z : ℚ) ≤ (W : ℚ) ∧
      (33 / (5 * (v : ℚ))) ≤ ∏ q ∈ P, (1 - 1 / (q : ℚ)) ∧
      (2 : ℚ) ^ P.card ≤ 22 * (v : ℚ) ^ 2 / 100 ∧
      (2 : ℚ) ^ Q.card ≤ 22 * (v : ℚ) ^ 4 / 10000 := by
  intro K P Q
  have hK_min : 316227765 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hm_le_K1sq : m ≤ (K + 1) ^ 2 := by
    have : m - 1 < (K + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt (m - 1)
    omega
  have hex_v : ∃ v : ℕ, 1000000000000 * (K + 1) ≤ v ^ 12 := by
    refine ⟨10 * (K + 1), ?_⟩
    have h11 : 1 ≤ (K + 1) ^ 11 := one_le_pow₀ (by omega)
    have heq : (10 * (K + 1)) ^ 12 = 1000000000000 * (K + 1) * (K + 1) ^ 11 := by ring
    rw [heq]; exact Nat.le_mul_of_pos_right _ h11
  set v := Nat.find hex_v
  have hv_ub : 1000000000000 * (K + 1) ≤ v ^ 12 := Nat.find_spec hex_v
  have hv_ge52 : 52 ≤ v := by
    by_contra hlt
    have hpow : v ^ 12 ≤ 51 ^ 12 := Nat.pow_le_pow_left (by omega) 12
    have : 51 ^ 12 < 1000000000000 * 316227766 := by norm_num
    omega
  have hv_lb : (v - 1) ^ 12 < 1000000000000 * (K + 1) := by
    have hnot := Nat.find_min hex_v (by omega : v - 1 < v)
    omega
  have hv_q : (52 : ℚ) ≤ (v : ℚ) := by exact_mod_cast hv_ge52
  have hK1_le_vq : ((K + 1 : ℕ) : ℚ) ≤ ((v : ℚ) / 10) ^ 12 := by
    have hq : (1000000000000 : ℚ) * ((K + 1 : ℕ) : ℚ) ≤ (v : ℚ) ^ 12 := by exact_mod_cast hv_ub
    have heq : ((v : ℚ) / 10) ^ 12 = (v : ℚ) ^ 12 / 1000000000000 := by ring
    rw [heq]; linarith
  have hv1_ge : (51 / 52 : ℚ) * (v : ℚ) ≤ ((v - 1 : ℕ) : ℚ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ v), Nat.cast_one]; linarith
  have hK_ge_vq : (78 / 100 : ℚ) * ((v : ℚ) ^ 12 / 1000000000000) ≤ (K : ℚ) := by
    have h1 : (51 / 52 : ℚ) ^ 12 * (v : ℚ) ^ 12 ≤ ((v - 1 : ℕ) : ℚ) ^ 12 := by
      have := pow_le_pow_left₀ (by positivity) hv1_ge 12
      simpa [mul_pow] using this
    have h2 : ((v - 1 : ℕ) : ℚ) ^ 12 ≤ (1000000000000 : ℚ) * ((K : ℚ) + 1) := by
      have : (v - 1) ^ 12 ≤ 1000000000000 * (K + 1) := le_of_lt hv_lb
      exact_mod_cast this
    have h51 : (79 / 100 : ℚ) ≤ (51 / 52 : ℚ) ^ 12 := by norm_num
    have hv12_ge : (390000000000000 : ℚ) ≤ (v : ℚ) ^ 12 := by
      have h52 : (52 : ℚ) ^ 12 ≤ (v : ℚ) ^ 12 := pow_le_pow_left₀ (by norm_num) hv_q 12
      have : (390000000000000 : ℚ) ≤ (52 : ℚ) ^ 12 := by norm_num
      linarith
    have h3 : (79 / 100 : ℚ) * (v : ℚ) ^ 12 ≤ (1000000000000 : ℚ) * ((K : ℚ) + 1) := by
      have := mul_le_mul_of_nonneg_right h51 (by positivity : (0 : ℚ) ≤ (v : ℚ) ^ 12)
      linarith
    linarith
  set Z := v ^ 3 / 1000
  have hv3_ge : 140608 ≤ v ^ 3 := by
    have : 52 ^ 3 ≤ v ^ 3 := Nat.pow_le_pow_left hv_ge52 3
    norm_num at this; exact this
  have hZ_ge140 : 140 ≤ Z := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have hZ_ub : (Z : ℚ) ≤ (v : ℚ) ^ 3 / 1000 := by
    have hq : (1000 : ℚ) * (Z : ℚ) ≤ (v : ℚ) ^ 3 := by exact_mod_cast Nat.mul_div_le (v ^ 3) 1000
    linarith
  have hZ_sub1_lb : (v : ℚ) ^ 3 / 1100 ≤ (Z : ℚ) - 1 := by
    have hq : (v : ℚ) ^ 3 ≤ 1000 * ((Z : ℚ) + 1) := by
      exact_mod_cast le_of_lt (Nat.lt_mul_div_succ (v ^ 3) (by norm_num : 0 < 1000))
    have hv3q : (140608 : ℚ) ≤ (v : ℚ) ^ 3 := by exact_mod_cast hv3_ge
    linarith
  have hKZ_large : 1000 * Z ≤ K / Z := by
    have hZ2 : (Z : ℚ) ^ 2 ≤ (v : ℚ) ^ 6 / 1000000 := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg Z) hZ_ub 2
      have heq : ((v : ℚ) ^ 3 / 1000) ^ 2 = (v : ℚ) ^ 6 / 1000000 := by ring
      linarith
    have hv6_ge : (19770609664 : ℚ) ≤ (v : ℚ) ^ 6 := by
      have h52 : (52 : ℚ) ^ 6 ≤ (v : ℚ) ^ 6 := pow_le_pow_left₀ (by norm_num) hv_q 6
      have : (19770609664 : ℚ) ≤ (52 : ℚ) ^ 6 := by norm_num
      linarith
    have hK_ge_v6 : (1 / 100 : ℚ) * (v : ℚ) ^ 6 ≤ (K : ℚ) := by
      have hmul : (19770609664 : ℚ) * (v : ℚ) ^ 6 ≤ (v : ℚ) ^ 12 := by
        have := mul_le_mul_of_nonneg_right hv6_ge (by positivity : (0 : ℚ) ≤ (v : ℚ) ^ 6)
        simpa [show (v : ℚ) ^ 6 * (v : ℚ) ^ 6 = (v : ℚ) ^ 12 by ring] using this
      linarith
    have hnat : 1000 * Z * Z ≤ K := by
      have hq : ((1000 * Z * Z : ℕ) : ℚ) ≤ (K : ℚ) := by
        push_cast; rw [show (1000 : ℚ) * (Z : ℚ) * (Z : ℚ) = 1000 * (Z : ℚ) ^ 2 by ring]; linarith
      exact_mod_cast hq
    exact (Nat.le_div_iff_mul_le (by omega : 0 < Z)).mpr hnat
  set W := 6 * (K / Z)
  have hZW : Z ≤ W := by omega
  have hZpos : (0 : ℚ) < (Z : ℚ) := by exact_mod_cast (by omega : 0 < Z)
  have hW_ub : (W : ℚ) ≤ 6 * (K : ℚ) / (Z : ℚ) := by
    have hq : (Z : ℚ) * ((K / Z : ℕ) : ℚ) ≤ (K : ℚ) := by exact_mod_cast Nat.mul_div_le K Z
    have hdiv : ((K / Z : ℕ) : ℚ) ≤ (K : ℚ) / (Z : ℚ) := (le_div_iff₀ hZpos).mpr (by linarith)
    have hWq : (W : ℚ) = 6 * ((K / Z : ℕ) : ℚ) := by dsimp [W]; push_cast; ring
    have hassoc : 6 * ((K : ℚ) / (Z : ℚ)) = 6 * (K : ℚ) / (Z : ℚ) := by ring
    linarith
  have hW_lb : 5 * (K : ℚ) / (Z : ℚ) ≤ (W : ℚ) := by
    have hq : (K : ℚ) ≤ (Z : ℚ) * (((K / Z : ℕ) : ℚ) + 1) := by
      exact_mod_cast le_of_lt (Nat.lt_mul_div_succ K (by omega : 0 < Z))
    have hdiv : (K : ℚ) / (Z : ℚ) ≤ ((K / Z : ℕ) : ℚ) + 1 := (div_le_iff₀ hZpos).mpr (by linarith)
    have hge6 : (6 : ℚ) ≤ ((K / Z : ℕ) : ℚ) := by exact_mod_cast (by omega : 6 ≤ K / Z)
    have hWq : (W : ℚ) = 6 * ((K / Z : ℕ) : ℚ) := by dsimp [W]; push_cast; ring
    have hassoc : 5 * ((K : ℚ) / (Z : ℚ)) = 5 * (K : ℚ) / (Z : ℚ) := by ring
    linarith
  have hP_odd : ∀ q ∈ P, q.Prime ∧ q ≠ 2 := fun q hq =>
    ⟨Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2.1⟩
  have hQ_odd : ∀ q ∈ Q, q.Prime ∧ q ≠ 2 := fun q hq =>
    ⟨(Q_all_odd_prime (m := m) (by omega) q hq).1, (Q_all_odd_prime (m := m) (by omega) q hq).2.1⟩
  have hP_prod_le : (∏ q ∈ P, (q : ℚ)) ≤ ((v : ℚ) / 10) ^ 12 := by
    have hsq : (∏ q ∈ P, q) ^ 2 ≤ (K + 1) ^ 2 := le_trans (prod_P_sq_le (by omega)) hm_le_K1sq
    have hnat : ∏ q ∈ P, q ≤ K + 1 := by
      by_contra hlt
      have : (K + 1) ^ 2 < (∏ q ∈ P, q) ^ 2 := by rw [sq, sq]; nlinarith
      omega
    have hq : (∏ q ∈ P, (q : ℚ)) ≤ ((K + 1 : ℕ) : ℚ) := by
      rw [← Nat.cast_prod]; exact_mod_cast hnat
    linarith
  have hQ_prod_le : (∏ q ∈ Q, (q : ℚ)) ≤ ((v : ℚ) / 10) ^ 24 := by
    have hnat : ∏ q ∈ Q, q ≤ (K + 1) ^ 2 :=
      le_trans (le_trans (prod_Q_le_odd_part (m := m) (by omega)).1
        (prod_Q_le_odd_part (m := m) (by omega)).2.1) hm_le_K1sq
    have hq : (∏ q ∈ Q, (q : ℚ)) ≤ (((K + 1 : ℕ) : ℚ)) ^ 2 := by
      rw [← Nat.cast_prod]; exact_mod_cast hnat
    have hsq := pow_le_pow_left₀ (by positivity) hK1_le_vq 2
    rw [← pow_mul] at hsq
    exact le_trans hq hsq
  have hphi_nn : 0 ≤ ∏ q ∈ P, (1 - 1 / (q : ℚ)) := Finset.prod_nonneg fun q hq => by
    have hq1 : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast (hP_odd q hq).1.one_le
    rw [sub_nonneg, div_le_one (by linarith)]; exact hq1
  have hphi_lb : (33 / (5 * (v : ℚ))) ≤ ∏ q ∈ P, (1 - 1 / (q : ℚ)) := by
    have h12 := phi_odd_pow12 P hP_odd
    have hpow : (66 / 100 : ℚ) ^ 12 ≤ ((v : ℚ) / 10) ^ 12 * (∏ q ∈ P, (1 - 1 / (q : ℚ))) ^ 12 :=
      le_trans h12 (mul_le_mul_of_nonneg_right hP_prod_le (by positivity))
    have hpow' : (33 / (5 * (v : ℚ))) ^ 12 ≤ (∏ q ∈ P, (1 - 1 / (q : ℚ))) ^ 12 := by
      have hv_pos : (0 : ℚ) < (v : ℚ) := by linarith
      have hv12_pos : (0 : ℚ) < ((v : ℚ) / 10) ^ 12 := by positivity
      have heq : (33 / (5 * (v : ℚ))) ^ 12 * ((v : ℚ) / 10) ^ 12 = (66 / 100 : ℚ) ^ 12 := by
        rw [← mul_pow]; congr 1; field_simp; ring
      exact le_of_mul_le_mul_right (by linarith) hv12_pos
    exact (pow_le_pow_iff_left₀ (by positivity) hphi_nn (by norm_num : 12 ≠ 0)).mp hpow'
  have h2P_ub : (2 : ℚ) ^ P.card ≤ 22 * (v : ℚ) ^ 2 / 100 := by
    have h6 := two_pow_card_odd_pow6 P hP_odd
    have hpow : ((2 : ℚ) ^ P.card) ^ 6 ≤ (22 * (v : ℚ) ^ 2 / 100) ^ 6 := by
      have h1 : (22 : ℚ) ^ 6 * ((v : ℚ) / 10) ^ 12 = (22 * (v : ℚ) ^ 2 / 100) ^ 6 := by ring
      rw [← h1]; exact le_trans h6 (mul_le_mul_of_nonneg_left hP_prod_le (by positivity))
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 6 ≠ 0)).mp hpow
  have h2Q_ub : (2 : ℚ) ^ Q.card ≤ 22 * (v : ℚ) ^ 4 / 10000 := by
    have h6 := two_pow_card_odd_pow6 Q hQ_odd
    have hpow : ((2 : ℚ) ^ Q.card) ^ 6 ≤ (22 * (v : ℚ) ^ 4 / 10000) ^ 6 := by
      have h1 : (22 : ℚ) ^ 6 * ((v : ℚ) / 10) ^ 24 = (22 * (v : ℚ) ^ 4 / 10000) ^ 6 := by ring
      rw [← h1]; exact le_trans h6 (mul_le_mul_of_nonneg_left hQ_prod_le (by positivity))
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : 6 ≠ 0)).mp hpow
  exact ⟨v, Z, W, hv_ge52, hZ_ge140, hZW, hK_ge_vq, hZ_ub, hZ_sub1_lb, hW_ub, hW_lb,
    hphi_lb, h2P_ub, h2Q_ub⟩

private lemma large_m_v_poly {v : ℕ} (hv_ge52 : 52 ≤ v) :
    (44 / 100000 : ℚ) * (v : ℚ) ^ 5 ≤ (2 / 1000000000000 : ℚ) * (v : ℚ) ^ 10 ∧
    (22 / 10000 : ℚ) * (v : ℚ) ^ 4 ≤ (1 / 1000000000000 : ℚ) * (v : ℚ) ^ 10 ∧
    (22 / 100 : ℚ) * (v : ℚ) ^ 2 ≤ (1 / 1000000000000 : ℚ) * (v : ℚ) ^ 10 ∧
    (100000000000000000 : ℚ) ≤ (v : ℚ) ^ 10 := by
  have hv_q : (52 : ℚ) ≤ (v : ℚ) := by exact_mod_cast hv_ge52
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hv5_nn : (0 : ℚ) ≤ (v : ℚ) ^ 5 := by positivity
    have h52 : (52 : ℚ) ^ 5 ≤ (v : ℚ) ^ 5 := pow_le_pow_left₀ (by norm_num) hv_q 5
    have hmul : (52 : ℚ) ^ 5 * (v : ℚ) ^ 5 ≤ (v : ℚ) ^ 10 := by
      have h := mul_le_mul_of_nonneg_right h52 hv5_nn
      rw [show (v : ℚ) ^ 5 * (v : ℚ) ^ 5 = (v : ℚ) ^ 10 by ring] at h
      exact h
    have : (380000000 : ℚ) * (v : ℚ) ^ 5 ≤ (v : ℚ) ^ 10 := by
      have h1 : (380000000 : ℚ) ≤ (52 : ℚ) ^ 5 := by norm_num
      have := mul_le_mul_of_nonneg_right h1 hv5_nn
      linarith
    linarith
  · have hv4_nn : (0 : ℚ) ≤ (v : ℚ) ^ 4 := by positivity
    have h52 : (52 : ℚ) ^ 6 ≤ (v : ℚ) ^ 6 := pow_le_pow_left₀ (by norm_num) hv_q 6
    have hmul : (52 : ℚ) ^ 6 * (v : ℚ) ^ 4 ≤ (v : ℚ) ^ 10 := by
      have h := mul_le_mul_of_nonneg_right h52 hv4_nn
      rw [show (v : ℚ) ^ 6 * (v : ℚ) ^ 4 = (v : ℚ) ^ 10 by ring] at h
      exact h
    have : (19000000000 : ℚ) * (v : ℚ) ^ 4 ≤ (v : ℚ) ^ 10 := by
      have h1 : (19000000000 : ℚ) ≤ (52 : ℚ) ^ 6 := by norm_num
      have := mul_le_mul_of_nonneg_right h1 hv4_nn
      linarith
    linarith
  · have hv2_nn : (0 : ℚ) ≤ (v : ℚ) ^ 2 := by positivity
    have h52 : (52 : ℚ) ^ 8 ≤ (v : ℚ) ^ 8 := pow_le_pow_left₀ (by norm_num) hv_q 8
    have hmul : (52 : ℚ) ^ 8 * (v : ℚ) ^ 2 ≤ (v : ℚ) ^ 10 := by
      have h := mul_le_mul_of_nonneg_right h52 hv2_nn
      rw [show (v : ℚ) ^ 8 * (v : ℚ) ^ 2 = (v : ℚ) ^ 10 by ring] at h
      exact h
    have : (50000000000000 : ℚ) * (v : ℚ) ^ 2 ≤ (v : ℚ) ^ 10 := by
      have h1 : (50000000000000 : ℚ) ≤ (52 : ℚ) ^ 8 := by norm_num
      have := mul_le_mul_of_nonneg_right h1 hv2_nn
      linarith
    linarith
  · have h52 : (52 : ℚ) ^ 10 ≤ (v : ℚ) ^ 10 := pow_le_pow_left₀ (by norm_num) hv_q 10
    have : (100000000000000000 : ℚ) ≤ (52 : ℚ) ^ 10 := by norm_num
    linarith

private lemma large_m_ge_1e17 {m : ℕ} (hm : 100000000000000000 ≤ m) :
    2 ≤ representations m := by
  set K := (m - 1).sqrt
  have hK_min : 316227765 ≤ K := Nat.le_sqrt.mpr (by omega)
  have hm_le_K1sq : m ≤ (K + 1) ^ 2 := by
    have : m - 1 < (K + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt (m - 1)
    omega
  obtain ⟨v, Z, W, hv_ge52, hZ_ge140, hZW, hK_ge_vq, hZ_ub, hZ_sub1_lb, hW_ub, hW_lb,
    hphi_lb, h2P_ub, h2Q_ub⟩ := large_m_params hm
  change (78 / 100 : ℚ) * ((v : ℚ) ^ 12 / 1000000000000) ≤ (K : ℚ) at hK_ge_vq
  change (W : ℚ) ≤ 6 * (K : ℚ) / (Z : ℚ) at hW_ub
  change 5 * (K : ℚ) / (Z : ℚ) ≤ (W : ℚ) at hW_lb
  have hv_q : (52 : ℚ) ≤ (v : ℚ) := by exact_mod_cast hv_ge52
  have hv_pos : (0 : ℚ) < (v : ℚ) := by linarith
  have hZ_lb : (v : ℚ) ^ 3 / 1100 ≤ (Z : ℚ) := by linarith
  have hK_nn : (0 : ℚ) ≤ (K : ℚ) := Nat.cast_nonneg K
  have hv2_ge : (2704 : ℚ) ≤ (v : ℚ) ^ 2 := by
    have h52 : (52 : ℚ) ^ 2 ≤ (v : ℚ) ^ 2 := pow_le_pow_left₀ (by norm_num) hv_q 2
    linarith
  have hv3_ge_2704v : (2704 : ℚ) * (v : ℚ) ≤ (v : ℚ) ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hv2_ge (le_of_lt hv_pos)
    rw [show (v : ℚ) ^ 2 * (v : ℚ) = (v : ℚ) ^ 3 by ring] at h
    exact h
  -- Apply master_sieve!
  set P := m.primeFactors.filter (fun q => q ≠ 2 ∧ q ^ 2 ∣ m)
  set phiP : ℚ := ∏ q ∈ P, (1 - 1 / (q : ℚ))
  set Psmall := (Finset.Icc 3 Z).filter (fun p => p.Prime ∧ ¬ p ∣ m)
  set Pmid1 := (Finset.Ioc Z (min W K.sqrt)).filter (fun p => p.Prime)
  set Pmid2 := (Finset.Ioc (max Z K.sqrt) W).filter (fun p => p.Prime)
  set Q := (m / 2 ^ (m.factorization 2)).primeFactors
  have hms := master_sieve (m := m) (Z := Z) (W := W) (by omega) (by omega) hZW
  change (representations m : ℚ) ≥
      ((K : ℚ) / 2) * phiP * (1 - ∑ p ∈ Psmall, (2 / (p : ℚ) ^ 2))
      - (1 + 2 * (Psmall.card : ℚ)) * (2 : ℚ) ^ P.card
      - (K : ℚ) * (∑ p ∈ Pmid1, (1 / (p : ℚ) ^ 2))
      - 2 * (Pmid1.card : ℚ) - (Pmid2.card : ℚ)
      - largeTailBound m W at hms
  -- 1) Main term >= (1947 / (1000 * v)) * K
  have hsum_small : ∑ p ∈ Psmall, (2 : ℚ) / (p : ℚ) ^ 2 ≤ 41 / 100 :=
    sum_2_inv_sq_primes_ge3 Psmall fun p hp =>
      ⟨(Finset.mem_filter.mp hp).2.1, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩
  have hmain : (1947 / (1000 * (v : ℚ))) * (K : ℚ) ≤
      ((K : ℚ) / 2) * phiP * (1 - ∑ p ∈ Psmall, (2 / (p : ℚ) ^ 2)) := by
    have hphi_nn : 0 ≤ phiP := le_trans (by positivity) hphi_lb
    have h1 : ((K : ℚ) / 2) * phiP * (59 / 100) ≤
        ((K : ℚ) / 2) * phiP * (1 - ∑ p ∈ Psmall, (2 / (p : ℚ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : ((K : ℚ) / 2) * (33 / (5 * (v : ℚ))) * (59 / 100) ≤
        ((K : ℚ) / 2) * phiP * (59 / 100) := by
      have := mul_le_mul_of_nonneg_left hphi_lb (by positivity : (0 : ℚ) ≤ (K : ℚ) / 2)
      exact mul_le_mul_of_nonneg_right this (by norm_num)
    have heq : ((K : ℚ) / 2) * (33 / (5 * (v : ℚ))) * (59 / 100) =
        (1947 / (1000 * (v : ℚ))) * (K : ℚ) := by ring
    linarith
  -- 2) Tail term <= (204 / (1000 * v)) * K
  have htail_mid : (K : ℚ) * (∑ p ∈ Pmid1, (1 / (p : ℚ) ^ 2)) ≤
      (204 / (1000 * (v : ℚ))) * (K : ℚ) := by
    have h1 := sum_inv_sq_primes_gt_le Z (min W K.sqrt) (by omega)
    have h2 : 1 / (2 * ((Z : ℚ) - 1)) ≤ 550 / (v : ℚ) ^ 3 := by
      have hle := one_div_le_one_div_of_le (by positivity : (0 : ℚ) < 2 * ((v : ℚ) ^ 3 / 1100))
        (by linarith : 2 * ((v : ℚ) ^ 3 / 1100) ≤ 2 * ((Z : ℚ) - 1))
      have heq : 1 / (2 * ((v : ℚ) ^ 3 / 1100)) = 550 / (v : ℚ) ^ 3 := by field_simp; ring
      linarith
    have h3 : 550 / (v : ℚ) ^ 3 ≤ 204 / (1000 * (v : ℚ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hmul := mul_le_mul_of_nonneg_left (le_trans h1 (le_trans h2 h3)) hK_nn
    have hcomm : (K : ℚ) * (204 / (1000 * (v : ℚ))) = (204 / (1000 * (v : ℚ))) * (K : ℚ) := by ring
    linarith
  -- 3) Pmid1 + Pmid2 <= (814 / (1000 * v)) * K + 4
  have hdisj : Disjoint Pmid1 Pmid2 := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have hp1 : p ≤ K.sqrt := le_trans (Finset.mem_Ioc.mp (Finset.mem_filter.mp h1).1).2 (min_le_right _ _)
    have hp2 : K.sqrt < p := lt_of_le_of_lt (le_max_right Z K.sqrt) (Finset.mem_Ioc.mp (Finset.mem_filter.mp h2).1).1
    omega
  have hunion_sub : Pmid1 ∪ Pmid2 ⊆ (Finset.Icc 1 W).filter Nat.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · have hI := (Finset.mem_filter.mp h).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_filter.mp h).2.one_le, le_trans (Finset.mem_Ioc.mp hI).2 (min_le_left _ _)⟩,
        (Finset.mem_filter.mp h).2⟩
    · have hI := (Finset.mem_filter.mp h).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨(Finset.mem_filter.mp h).2.one_le, (Finset.mem_Ioc.mp hI).2⟩, (Finset.mem_filter.mp h).2⟩
  have hmid_pi : (Pmid1.card : ℚ) + (Pmid2.card : ℚ) ≤ (814 / (1000 * (v : ℚ))) * (K : ℚ) + 4 := by
    have hnat : Pmid1.card + Pmid2.card ≤ piCount W := by
      rw [← Finset.card_union_of_disjoint hdisj]; exact Finset.card_le_card hunion_sub
    have hq : (Pmid1.card : ℚ) + (Pmid2.card : ℚ) ≤ (W : ℚ) / 3 + 4 :=
      le_trans (by exact_mod_cast hnat) (piCount_le_wheel6 W)
    have h2Z : 2 / (Z : ℚ) ≤ 2200 / (v : ℚ) ^ 3 := by
      have hle := one_div_le_one_div_of_le (by positivity : (0 : ℚ) < (v : ℚ) ^ 3 / 1100) hZ_lb
      have heq : 2 * (1 / ((v : ℚ) ^ 3 / 1100)) = 2200 / (v : ℚ) ^ 3 := by field_simp; ring
      have heq2 : 2 / (Z : ℚ) = 2 * (1 / (Z : ℚ)) := by ring
      linarith
    have h2200 : 2200 / (v : ℚ) ^ 3 ≤ 814 / (1000 * (v : ℚ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hKZ : 2 * (K : ℚ) / (Z : ℚ) ≤ (814 / (1000 * (v : ℚ))) * (K : ℚ) := by
      rw [show 2 * (K : ℚ) / (Z : ℚ) = (2 / (Z : ℚ)) * (K : ℚ) by ring]
      exact mul_le_mul_of_nonneg_right (le_trans h2Z h2200) hK_nn
    have hW3 : (W : ℚ) / 3 ≤ 2 * (K : ℚ) / (Z : ℚ) := by
      have heq : (6 * (K : ℚ) / (Z : ℚ)) / 3 = 2 * (K : ℚ) / (Z : ℚ) := by ring
      linarith
    linarith
  -- 4) Extra Pmid1.card <= (5 / (1000 * v)) * K
  have hmid1_extra : (Pmid1.card : ℚ) ≤ (5 / (1000 * (v : ℚ))) * (K : ℚ) := by
    have hsub : Pmid1 ⊆ Finset.Icc 1 K.sqrt := fun p hp =>
      Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hp).2.one_le,
        le_trans (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2 (min_le_right _ _)⟩
    have hcard : (Pmid1.card : ℚ) ≤ (K.sqrt : ℚ) := by
      have : Pmid1.card ≤ K.sqrt := by
        calc Pmid1.card ≤ (Finset.Icc 1 K.sqrt).card := Finset.card_le_card hsub
          _ = K.sqrt := by simp
      exact_mod_cast this
    have hv10_ge : (144555105949057024 : ℚ) ≤ (v : ℚ) ^ 10 := by
      have h52 : (52 : ℚ) ^ 10 ≤ (v : ℚ) ^ 10 := pow_le_pow_left₀ (by norm_num) hv_q 10
      have : (144555105949057024 : ℚ) ≤ (52 : ℚ) ^ 10 := by norm_num
      linarith
    have h200v_sq : (200 * (v : ℚ)) ^ 2 ≤ (K : ℚ) := by
      have hmul : (144555105949057024 : ℚ) * (v : ℚ) ^ 2 ≤ (v : ℚ) ^ 12 := by
        have := mul_le_mul_of_nonneg_right hv10_ge (by positivity : (0 : ℚ) ≤ (v : ℚ) ^ 2)
        simpa [show (v : ℚ) ^ 10 * (v : ℚ) ^ 2 = (v : ℚ) ^ 12 by ring] using this
      have heq : (200 * (v : ℚ)) ^ 2 = 40000 * (v : ℚ) ^ 2 := by ring
      linarith
    have hksq_le : ((K.sqrt : ℚ)) ^ 2 ≤ (K : ℚ) := by
      have hq : (K.sqrt : ℚ) * (K.sqrt : ℚ) ≤ (K : ℚ) := by exact_mod_cast Nat.sqrt_le K
      rw [sq]; exact hq
    have hprod_sq : (200 * (v : ℚ) * (K.sqrt : ℚ)) ^ 2 ≤ (K : ℚ) ^ 2 := by
      have heq : (200 * (v : ℚ) * (K.sqrt : ℚ)) ^ 2 = (200 * (v : ℚ)) ^ 2 * (K.sqrt : ℚ) ^ 2 := by ring
      rw [heq, sq (K : ℚ)]
      exact mul_le_mul h200v_sq hksq_le (by positivity) hK_nn
    have hlin : 200 * (v : ℚ) * (K.sqrt : ℚ) ≤ (K : ℚ) :=
      (pow_le_pow_iff_left₀ (by positivity) hK_nn (by norm_num : 2 ≠ 0)).mp hprod_sq
    have hdiv : (K.sqrt : ℚ) ≤ (5 / (1000 * (v : ℚ))) * (K : ℚ) := by
      have heq : (5 / (1000 * (v : ℚ))) * (K : ℚ) = (K : ℚ) / (200 * (v : ℚ)) := by field_simp; ring
      rw [heq, le_div_iff₀ (by positivity)]
      linarith
    linarith
  -- 5) Small prime error <= (44 / 100000) * v^5 + (22 / 100) * v^2
  have hsmall_err : (1 + 2 * (Psmall.card : ℚ)) * (2 : ℚ) ^ P.card ≤
      (44 / 100000 : ℚ) * (v : ℚ) ^ 5 + (22 / 100 : ℚ) * (v : ℚ) ^ 2 := by
    have hPs_le : (Psmall.card : ℚ) ≤ (Z : ℚ) := by
      have hsub : Psmall ⊆ Finset.Icc 1 Z := fun p hp =>
        Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega,
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2⟩
      have : Psmall.card ≤ Z := by
        calc Psmall.card ≤ (Finset.Icc 1 Z).card := Finset.card_le_card hsub
          _ = Z := by simp
      exact_mod_cast this
    have h1 : 1 + 2 * (Psmall.card : ℚ) ≤ 1 + 2 * ((v : ℚ) ^ 3 / 1000) := by linarith
    have hmul := mul_le_mul h1 h2P_ub (by positivity) (by positivity)
    have heq : (1 + 2 * ((v : ℚ) ^ 3 / 1000)) * (22 * (v : ℚ) ^ 2 / 100) =
        (44 / 100000 : ℚ) * (v : ℚ) ^ 5 + (22 / 100 : ℚ) * (v : ℚ) ^ 2 := by ring
    linarith
  -- 6) Large prime error <= (23 / 10^12) * v^10 + (22 / 10^4) * v^4
  have hlarge_err : largeTailBound m W ≤
      (23 / 1000000000000 : ℚ) * (v : ℚ) ^ 10 + (22 / 10000 : ℚ) * (v : ℚ) ^ 4 := by
    have huni := largeTailBound_le_uniform m W
    set Y : ℕ := (m - 1) / W ^ 2
    have hY_le : (Y : ℚ) ≤ (Z : ℚ) ^ 2 / 24 := by
      have hY_mul : Y * W ^ 2 ≤ m - 1 := Nat.div_mul_le_self (m - 1) (W ^ 2)
      have hYq : (Y : ℚ) * (W : ℚ) ^ 2 ≤ ((K : ℚ) + 1) ^ 2 := by
        have h1 : (Y : ℚ) * (W : ℚ) ^ 2 ≤ ((m - 1 : ℕ) : ℚ) := by exact_mod_cast hY_mul
        have h2 : ((m - 1 : ℕ) : ℚ) ≤ ((K : ℚ) + 1) ^ 2 := by
          have : m - 1 ≤ (K + 1) ^ 2 := by omega
          exact_mod_cast this
        linarith
      have hK1_le : ((K : ℚ) + 1) ^ 2 ≤ (25 / 24 : ℚ) * (K : ℚ) ^ 2 := by
        have hKq : (316227765 : ℚ) ≤ (K : ℚ) := by exact_mod_cast hK_min
        have h1 : (2 : ℚ) * (K : ℚ) + 1 ≤ (1 / 24 : ℚ) * (K : ℚ) * (K : ℚ) := by
          have h2 : (316227765 : ℚ) * (K : ℚ) ≤ (K : ℚ) * (K : ℚ) :=
            mul_le_mul_of_nonneg_right hKq hK_nn
          linarith
        have heq : ((K : ℚ) + 1) ^ 2 = (K : ℚ) ^ 2 + 2 * (K : ℚ) + 1 := by ring
        rw [sq (K : ℚ)] at heq ⊢
        linarith
      have hW2_lb : 25 * (K : ℚ) ^ 2 / (Z : ℚ) ^ 2 ≤ (W : ℚ) ^ 2 := by
        have h := pow_le_pow_left₀ (by positivity) hW_lb 2
        have heq : (5 * (K : ℚ) / (Z : ℚ)) ^ 2 = 25 * (K : ℚ) ^ 2 / (Z : ℚ) ^ 2 := by ring
        linarith
      have h1 : (Y : ℚ) * (25 * (K : ℚ) ^ 2 / (Z : ℚ) ^ 2) ≤ (25 / 24 : ℚ) * (K : ℚ) ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_left hW2_lb (Nat.cast_nonneg Y)) (le_trans hYq hK1_le)
      have hKpos : (0 : ℚ) < (K : ℚ) := by
        have : (316227765 : ℚ) ≤ (K : ℚ) := by exact_mod_cast hK_min
        linarith
      have hZpos : (0 : ℚ) < (Z : ℚ) := by exact_mod_cast (by omega : 0 < Z)
      have hdiv : (Y : ℚ) ≤ ((25 / 24 : ℚ) * (K : ℚ) ^ 2) / (25 * (K : ℚ) ^ 2 / (Z : ℚ) ^ 2) :=
        (le_div_iff₀ (by positivity)).mpr h1
      have heq : ((25 / 24 : ℚ) * (K : ℚ) ^ 2) / (25 * (K : ℚ) ^ 2 / (Z : ℚ) ^ 2) = (Z : ℚ) ^ 2 / 24 := by
        field_simp
      linarith
    have hZ2_ub : (Z : ℚ) ^ 2 ≤ (v : ℚ) ^ 6 / 1000000 := by
      have h := pow_le_pow_left₀ (Nat.cast_nonneg Z) hZ_ub 2
      have heq : ((v : ℚ) ^ 3 / 1000) ^ 2 = (v : ℚ) ^ 6 / 1000000 := by ring
      linarith
    have hY4 : (Y : ℚ) / 4 + 1 ≤ (v : ℚ) ^ 6 / 96000000 + 1 := by linarith
    have hmul := mul_le_mul hY4 h2Q_ub (by positivity) (by positivity)
    have heq : ((v : ℚ) ^ 6 / 96000000 + 1) * (22 * (v : ℚ) ^ 4 / 10000) =
        (22 / 960000000000 : ℚ) * (v : ℚ) ^ 10 + (22 / 10000 : ℚ) * (v : ℚ) ^ 4 := by ring
    have hv10_nn : (0 : ℚ) ≤ (v : ℚ) ^ 10 := by positivity
    linarith
  -- 7) Final comparison in powers of v^10!
  have hK_net : (9 / (10 * (v : ℚ))) * (K : ℚ) ≤
      (1947 / (1000 * (v : ℚ))) * (K : ℚ)
      - (204 / (1000 * (v : ℚ))) * (K : ℚ)
      - (814 / (1000 * (v : ℚ))) * (K : ℚ)
      - (5 / (1000 * (v : ℚ))) * (K : ℚ) := by
    have hcoef : (9 / (10 * (v : ℚ))) ≤
        (1947 / (1000 * (v : ℚ))) - (204 / (1000 * (v : ℚ))) -
        (814 / (1000 * (v : ℚ))) - (5 / (1000 * (v : ℚ))) := by
      have heq : (1947 / (1000 * (v : ℚ))) - (204 / (1000 * (v : ℚ))) -
          (814 / (1000 * (v : ℚ))) - (5 / (1000 * (v : ℚ))) = 924 / (1000 * (v : ℚ)) := by ring
      rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have := mul_le_mul_of_nonneg_right hcoef hK_nn
    linarith
  have hmain_v10 : (36 / 1000000000000 : ℚ) * (v : ℚ) ^ 10 ≤ (9 / (10 * (v : ℚ))) * (K : ℚ) := by
    have hv10_nn : (0 : ℚ) ≤ (v : ℚ) ^ 10 := by positivity
    have h1 : (9 / (10 * (v : ℚ))) * ((78 / 100 : ℚ) * ((v : ℚ) ^ 12 / 1000000000000)) ≤
        (9 / (10 * (v : ℚ))) * (K : ℚ) :=
      mul_le_mul_of_nonneg_left hK_ge_vq (by positivity)
    have heq : (9 / (10 * (v : ℚ))) * ((78 / 100 : ℚ) * ((v : ℚ) ^ 12 / 1000000000000)) =
        (702 / 1000000000000000 : ℚ) * (v : ℚ) ^ 11 := by field_simp; ring
    have hv11 : (52 : ℚ) * (v : ℚ) ^ 10 ≤ (v : ℚ) ^ 11 := by
      have h := mul_le_mul_of_nonneg_right hv_q hv10_nn
      rw [show (v : ℚ) * (v : ℚ) ^ 10 = (v : ℚ) ^ 11 by ring] at h
      exact h
    linarith
  obtain ⟨hv5_le, hv4_le, hv2_le, hv10_big⟩ := large_m_v_poly hv_ge52
  have hrep_q : (2 : ℚ) ≤ (representations m : ℚ) := by linarith
  exact_mod_cast hrep_q

private lemma large_range_ok {m : ℕ} (hm : 12000000 ≤ m) : 2 ≤ representations m := by
  by_cases h1 : m ≤ 25000000
  · exact band1_ok hm h1
  · by_cases h2 : m ≤ 80000000
    · exact band2_ok (by omega) h2
    · by_cases h3 : m ≤ 300000000
      · exact band3_ok (by omega) h3
      · by_cases h4 : m ≤ 1000000000
        · exact band4_ok (by omega) h4
        · by_cases h5 : m ≤ 10000000000
          · exact band5_ok (by omega) h5
          · by_cases h6 : m ≤ 1000000000000
            · exact band6_ok (by omega) h6
            · by_cases h7 : m ≤ 100000000000000
              · exact band7_ok (by omega) h7
              · by_cases h8 : m ≤ 10000000000000000
                · exact band8_ok (by omega) h8
                · by_cases h9 : m ≤ 100000000000000000
                  · exact band9_ok (by omega) h9
                  · exact large_m_ge_1e17 (by omega)

-- ## Section 5: Final Assembly and Main Theorem

private lemma two_le_representations_of_ge_62 {m : ℕ} (hm : 62 ≤ m) :
    2 ≤ representations m := by
  by_cases h : m < 12000400
  · exact small_range_ok m hm h
  · exact large_range_ok (by omega)

private lemma termsThrough_succ_of_ge {m : ℕ} (hpos : 0 < m + 1)
    (hrep : 2 ≤ representations (m + 1)) :
    termsThrough (m + 1) = termsThrough m + 1 := by
  unfold termsThrough
  rw [Finset.range_add_one, Finset.filter_insert]
  have hcond : 0 < m + 1 ∧ 2 ≤ representations (m + 1) := ⟨hpos, hrep⟩
  simp only [hcond, and_self, ↓reduceIte]
  exact Finset.card_insert_of_notMem fun h =>
    (Finset.mem_range.mp (Finset.mem_filter.mp h).1).ne rfl

private lemma termsThrough_add_eleven (n : ℕ) (hn : 50 ≤ n) :
    termsThrough (n + 11) = n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using termsThrough_61
  | succ k ih =>
    have hge62 : 62 ≤ 50 + (k + 1) + 11 := by omega
    have hrep := two_le_representations_of_ge_62 hge62
    rw [show 50 + (k + 1) + 11 = (50 + k + 11) + 1 by omega]
    rw [termsThrough_succ_of_ge (by omega)
      (by simpa [show (50 + k + 11) + 1 = 50 + (k + 1) + 11 by omega] using hrep), ih (by omega)]
    omega

end OMA.A085267Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a085267.main := by
  intro n hn
  exact ⟨OMA.A085267Proof.two_le_representations_of_ge_62 (by omega),
    OMA.A085267Proof.termsThrough_add_eleven n (by omega)⟩
