import OMAReductions.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1

/-! Bounded prime-root divisor case. The stored integer brackets and coverage are
replayed by Lean's kernel. -/

namespace A056777Bounded


def cubic (L M C x : ℤ) : ℤ := ((2*x-L)*x+M)*x-C

def slope (L M x y : ℤ) : ℤ := 2*(x*x+x*y+y*y)-L*(x+y)+M

theorem cubic_diff (L M C x y : ℤ) :
    cubic L M C y - cubic L M C x = (y-x)*slope L M x y := by
  unfold cubic slope
  ring

theorem slope_antitone {L M P u v u' v' : ℤ}
    (hL : 6*P ≤ L) (hu : u ≤ u') (hv : v ≤ v') (hu' : u' ≤ P) (hv' : v' ≤ P) :
    slope L M u' v' ≤ slope L M u v := by
  have h₁ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu)
    (show 2*(u'+u+v)-L ≤ 0 by linarith)
  have h₂ := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hv)
    (show 2*(u'+v'+v)-L ≤ 0 by linarith)
  unfold slope
  nlinarith only [h₁,h₂]

theorem no_root_between {L M C P a b x : ℤ} (hL : 6*P ≤ L) (hab : a+1 ≤ b)
    (hb : b+1 ≤ P) (hx : x ≤ P)
    (hfa : cubic L M C a < 0) (hfa' : 0 < cubic L M C (a+1))
    (hfb : 0 < cubic L M C b) (hfb' : cubic L M C (b+1) < 0) :
    cubic L M C x ≠ 0 := by
  have ha' : a+1 ≤ P := by omega
  have hbp : b ≤ P := by omega
  have leftSlope : 0 ≤ slope L M a (a+1) := by linarith [cubic_diff L M C a (a+1)]
  have rightSlope : slope L M b (b+1) ≤ 0 := by linarith [cubic_diff L M C b (b+1)]
  by_cases hxa : x ≤ a
  · have h := slope_antitone (M:=M) hL hxa (show a ≤ a+1 by omega) (by omega) ha'
    have hmul := mul_nonneg (show 0 ≤ a-x by omega) (leftSlope.trans h)
    linarith [cubic_diff L M C x a]
  by_cases hxb : b+1 ≤ x
  · have h := slope_antitone (M:=M) hL (show b ≤ b+1 by omega) hxb hb hx
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x-(b+1) by omega) (h.trans rightSlope)
    linarith [cubic_diff L M C (b+1) x]
  have hax : a+1 ≤ x := by omega
  have hxb' : x ≤ b := by omega
  by_cases hsign : 0 ≤ slope L M (a+1) x
  · have hmul := mul_nonneg (show 0 ≤ x-(a+1) by omega) hsign
    linarith [cubic_diff L M C (a+1) x]
  · have h := slope_antitone (M:=M) hL hax hxb' hx hbp
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ b-x by omega)
      (h.trans (le_of_lt (lt_of_not_ge hsign)))
    linarith [cubic_diff L M C x b]

theorem no_root_below_peak {L M C P a x : ℤ} (hL : 6*P ≤ L)
    (ha : a+1 ≤ P) (hx : x ≤ P)
    (hfa : cubic L M C a < 0) (hleft : 0 ≤ slope L M (a-1) a)
    (hright : slope L M a (a+1) ≤ 0) : cubic L M C x ≠ 0 := by
  obtain hxa|rfl|hax := lt_trichotomy x a
  · have h := slope_antitone (M:=M) hL (show x ≤ a-1 by omega) (le_refl a)
        (by omega) (by omega)
    have hmul := mul_nonneg (show 0 ≤ a-x by omega) (hleft.trans h)
    linarith [cubic_diff L M C x a]
  · exact ne_of_lt hfa
  · have h := slope_antitone (M:=M) hL (le_refl a) (show a+1 ≤ x by omega) (by omega) hx
    have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ x-a by omega) (h.trans hright)
    linarith [cubic_diff L M C a x]

def sumCoeff (p q : ℤ) : ℤ := (p*p+p+1)*(q+1)+2*p^3

def pairCoeff (p q : ℤ) : ℤ := 2*p^3*(p+q-1)+sumCoeff p q-2

def productCoeff (p q : ℤ) : ℤ := 2*(p^4*q+12)



/-- Filtering multiples of these constants reduces the kernel replay cost.
Soundness only needs every constant to be greater than one. -/
def divisors : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61]

def possiblePrime (p : ℕ) : Bool :=
  divisors.all fun d => decide (p ≤ d ∨ p % d ≠ 0)

theorem prime_possiblePrime {p : ℕ} (hp : p.Prime) : possiblePrime p = true := by
  apply List.all_eq_true.mpr
  intro d hd
  have h1 : 1 < d := by
    change d ∈ divisors at hd
    unfold divisors at hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  apply decide_eq_true
  by_contra! h
  have hdvd : d ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h.2
  rcases hp.eq_one_or_self_of_dvd d hdvd with hbad|hbad <;> omega

def qFromIndex (i : ℕ) : ℕ := 40*i+27

theorem q_index_eq {q : ℕ} (h8 : q%8=3) (h5 : q%5=2) :
    qFromIndex (q/40)=q := by
  have hmod8 : (q%40)%8=q%8 := Nat.mod_mod_of_dvd q (by decide)
  have hmod5 : (q%40)%5=q%5 := Nat.mod_mod_of_dvd q (by decide)
  unfold qFromIndex
  omega

theorem p_mod_twenty {p : ℕ} (h4 : p%4=3) (h5 : p%5=2 ∨ p%5=3) :
    p%20=3 ∨ p%20=7 := by
  have hmod4 : (p%20)%4=p%4 := Nat.mod_mod_of_dvd p (by decide)
  have hmod5 : (p%20)%5=p%5 := Nat.mod_mod_of_dvd p (by decide)
  omega

-- Every index is less than 2^18. A zero upper field represents a negative peak.
def signCertificate (p q data : ℕ) : Bool :=
  let L := sumCoeff p q
  let M := pairCoeff p q
  let C := productCoeff p q
  let a : ℤ := (data % 262144 : ℕ)
  let high := data / 262144
  decide (6*(p:ℤ) ≤ L) &&
    if high = 0 then
      decide (a+1 ≤ p ∧ cubic L M C a < 0 ∧
        0 ≤ slope L M (a-1) a ∧ slope L M a (a+1) ≤ 0)
    else
      let b : ℤ := high
      decide (a+1 ≤ b ∧ b+1 ≤ p ∧ cubic L M C a < 0 ∧ 0 < cubic L M C (a+1) ∧
        0 < cubic L M C b ∧ cubic L M C (b+1) < 0)

theorem signCertificate_sound {p q x data : ℕ} (hc : signCertificate p q data = true)
    (hx : x ≤ p) : cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x ≠ 0 := by
  unfold signCertificate at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hL,hc⟩ := hc
  have hxp : (x:ℤ) ≤ (p:ℤ) := by exact_mod_cast hx
  split at hc
  next _ =>
    simp only [decide_eq_true_eq] at hc
    exact no_root_below_peak hL hc.1 hxp hc.2.1 hc.2.2.1 hc.2.2.2
  next _ =>
    simp only [decide_eq_true_eq] at hc
    exact no_root_between hL hc.1 hc.2.1 hxp hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2

def candidateP (q p : ℕ) : Bool :=
  decide (2*q < p ∧ p*p < q^3 ∧ p%3 ≠ q%3) && possiblePrime p

def candidateList (q low count : ℕ) : List ℕ :=
  ((List.range count).flatMap fun i =>
    [20*(low+i)+3,20*(low+i)+7]).filter (candidateP q)

theorem candidateP_mem {p q lo c : ℕ} (hp : p.Prime)
    (hpLo : 2*q < p) (hpHi : p^2 < q^3) (hmod : p%3 ≠ q%3) (hmod20 : p%20=3 ∨ p%20=7)
    (hlo : lo ≤ p/20) (hhi : p/20 < lo+c) : p ∈ candidateList q lo c := by
  unfold candidateList
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨p/20-lo, List.mem_range.mpr (by omega), ?_⟩
    obtain h3|h7 := hmod20
    · have he : 20*(lo+(p/20-lo))+3=p := by omega
      simp [he]
    · have he : 20*(lo+(p/20-lo))+7=p := by omega
      simp [he]
  · unfold candidateP
    simp only [Bool.and_eq_true]
    exact ⟨decide_eq_true ⟨hpLo,by simpa only [pow_two] using hpHi,hmod⟩,
      prime_possiblePrime hp⟩

def expandSign (p q field : ℕ) : ℕ :=
  let lower := q + field % 4096
  let upperOffset := field / 4096
  let upper := if upperOffset = 0 then 0 else p-upperOffset
  lower + 262144*upper

def natQTerm (p q : ℕ) : ℕ := (p*p+p+1)*(q+1)
def natSumCoeff (p q : ℕ) : ℕ := natQTerm p q+2*p*p*p
def natPairPlusTwo (p q : ℕ) : ℕ := 2*p*p*p*(p+q)+natQTerm p q
def natProductCoeff (p q : ℕ) : ℕ := 2*(p*p*p*p*q+12)

def cubicHigh (p q x : ℕ) : ℕ := (2*x*x+natPairPlusTwo p q)*x
def cubicLow (p q x : ℕ) : ℕ := (natSumCoeff p q*x+2)*x+natProductCoeff p q
def slopeHigh (p q x y : ℕ) : ℕ := 2*(x*x+x*y+y*y)+natPairPlusTwo p q
def slopeLow (p q x y : ℕ) : ℕ := natSumCoeff p q*(x+y)+2

theorem natSumCoeff_cast (p q : ℕ) : (natSumCoeff p q : ℤ) = sumCoeff p q := by
  unfold natSumCoeff natQTerm sumCoeff
  push_cast
  ring

theorem cubic_parts (p q x : ℕ) :
    cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x =
      (cubicHigh p q x : ℤ) - cubicLow p q x := by
  simp only [cubic,pairCoeff,sumCoeff,productCoeff,cubicHigh,cubicLow,
    natPairPlusTwo,natSumCoeff,natQTerm,natProductCoeff]
  push_cast
  ring

theorem slope_parts (p q x y : ℕ) :
    slope (sumCoeff p q) (pairCoeff p q) x y =
      (slopeHigh p q x y : ℤ) - slopeLow p q x y := by
  simp only [slope,pairCoeff,sumCoeff,slopeHigh,slopeLow,natPairPlusTwo,natSumCoeff,natQTerm]
  push_cast
  ring

/-- Evaluate the same signs using only nonnegative literal arithmetic. -/
def fastSign (p q field : ℕ) : Bool :=
  let a := q+field%4096
  let offset := field/4096
  decide (6*p ≤ natSumCoeff p q ∧ a < 262144) &&
    if offset = 0 then
      decide (1 ≤ a ∧ a+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        slopeLow p q (a-1) a ≤ slopeHigh p q (a-1) a ∧
        slopeHigh p q a (a+1) ≤ slopeLow p q a (a+1))
    else
      let b := p-offset
      decide (a+1 ≤ b ∧ b+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        cubicLow p q (a+1) < cubicHigh p q (a+1) ∧
        cubicLow p q b < cubicHigh p q b ∧
        cubicHigh p q (b+1) < cubicLow p q (b+1))

theorem fastSign_sound {p q field : ℕ} (h : fastSign p q field = true) :
    signCertificate p q (expandSign p q field) = true := by
  let a := q+field%4096
  let o := field/4096
  let b := if o=0 then 0 else p-o
  have hbase : 6*p ≤ natSumCoeff p q ∧ a<262144 := by
    have hh := (show decide (6*p ≤ natSumCoeff p q ∧ a < 262144) = true ∧ _ by
      simpa only [fastSign,a,Bool.and_eq_true] using h).1
    exact decide_eq_true_eq.mp hh
  have hL : 6*(p:ℤ) ≤ sumCoeff p q := by
    rw [← natSumCoeff_cast]
    exact_mod_cast hbase.1
  have hmod : (a+262144*b)%262144 = a := by omega
  have hdiv : (a+262144*b)/262144 = b := by omega
  change signCertificate p q (a+262144*b) = true
  simp only [signCertificate,hmod,hdiv,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨hL,?_⟩
  by_cases ho : o=0
  · have hb : b=0 := by simp [b,ho]
    simp only [hb,if_true,decide_eq_true_eq]
    have hcase : 1 ≤ a ∧ a+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        slopeLow p q (a-1) a ≤ slopeHigh p q (a-1) a ∧
        slopeHigh p q a (a+1) ≤ slopeLow p q a (a+1) := by
      have hh : field/4096=0 := ho
      simp only [fastSign,hh,if_true,Bool.and_eq_true,decide_eq_true_eq] at h
      exact h.2
    obtain ⟨ha,hap,hc,hl,hr⟩ := hcase
    refine ⟨by exact_mod_cast hap,?_,?_,?_⟩
    · rw [cubic_parts]
      exact sub_neg.mpr (by exact_mod_cast hc)
    · have hs : ((a-1 : ℕ) : ℤ) = (a:ℤ)-1 := by
        rw [Int.ofNat_sub ha]
        rfl
      rw [← hs,slope_parts]
      exact sub_nonneg.mpr (by exact_mod_cast hl)
    · rw [← Int.natCast_succ,slope_parts]
      exact sub_nonpos.mpr (by exact_mod_cast hr)
  · have hb : b=p-o := if_neg ho
    have hcase : a+1 ≤ b ∧ b+1 ≤ p ∧ cubicHigh p q a < cubicLow p q a ∧
        cubicLow p q (a+1) < cubicHigh p q (a+1) ∧
        cubicLow p q b < cubicHigh p q b ∧
        cubicHigh p q (b+1) < cubicLow p q (b+1) := by
      have hh : ¬field/4096=0 := ho
      simp only [fastSign,hh,if_false,Bool.and_eq_true,decide_eq_true_eq] at h
      simpa only [a,o,hb] using h.2
    obtain ⟨hab,hbp,hca,hca',hcb,hcb'⟩ := hcase
    have hbn : b≠0 := by omega
    simp only [hbn,if_false,decide_eq_true_eq]
    refine ⟨by exact_mod_cast hab,by exact_mod_cast hbp,?_,?_,?_,?_⟩
    · rw [cubic_parts]
      exact sub_neg.mpr (by exact_mod_cast hca)
    · rw [← Int.natCast_succ,cubic_parts]
      exact sub_pos.mpr (by exact_mod_cast hca')
    · rw [cubic_parts]
      exact sub_pos.mpr (by exact_mod_cast hcb)
    · rw [← Int.natCast_succ,cubic_parts]
      exact sub_neg.mpr (by exact_mod_cast hcb')

def fastPacked (q : ℕ) : List ℕ → ℕ → Bool
  | [], data => decide (data = 0)
  | p::ps, data =>
    fastSign p q (data % 16777216) &&
      fastPacked q ps (data / 16777216)

theorem fastPacked_sound {q p : ℕ} {ps : List ℕ} {data : ℕ}
    (h : fastPacked q ps data = true) (hp : p ∈ ps) :
    ∃ d, signCertificate p q d = true := by
  induction ps generalizing data with
  | nil => simp at hp
  | cons a as ih =>
    simp only [fastPacked,Bool.and_eq_true] at h
    rcases List.mem_cons.mp hp with rfl | hpas
    · exact ⟨_,fastSign_sound h.1⟩
    · exact ih h.2 hpas

theorem cubic_parts_congr {m p q x p' q' x' : ℕ}
    (hp : p ≡ p' [MOD m]) (hq : q ≡ q' [MOD m]) (hx : x ≡ x' [MOD m]) :
    (cubicHigh p q x ≡ cubicHigh p' q' x' [MOD m]) ∧
      (cubicLow p q x ≡ cubicLow p' q' x' [MOD m]) := by
  have h₁ : 1 ≡ 1 [MOD m] := Nat.ModEq.refl 1
  have h₂ : 2 ≡ 2 [MOD m] := Nat.ModEq.refl 2
  have h₁₂ : 12 ≡ 12 [MOD m] := Nat.ModEq.refl 12
  have hQ : natQTerm p q ≡ natQTerm p' q' [MOD m] :=
    (((hp.mul hp).add hp).add h₁).mul (hq.add h₁)
  have hp3 : 2*p*p*p ≡ 2*p'*p'*p' [MOD m] := ((h₂.mul hp).mul hp).mul hp
  have hL : natSumCoeff p q ≡ natSumCoeff p' q' [MOD m] := hQ.add hp3
  have hM : natPairPlusTwo p q ≡ natPairPlusTwo p' q' [MOD m] :=
    (hp3.mul (hp.add hq)).add hQ
  have hp4 := (((hp.mul hp).mul hp).mul hp).mul hq
  have hC : natProductCoeff p q ≡ natProductCoeff p' q' [MOD m] :=
    h₂.mul (hp4.add h₁₂)
  exact ⟨(((h₂.mul hx).mul hx).add hM).mul hx, (((hL.mul hx).add h₂).mul hx).add hC⟩

def residueRoot (m p q x : ℕ) : Bool :=
  decide (cubicHigh p q x % m = cubicLow p q x % m)

def maskPossible (m mask p q : ℕ) : Bool := mask.testBit (p*m+q)

def checkMask (m mask : ℕ) : Bool :=
  (List.range m).all fun p =>
    (List.range m).all fun q =>
      maskPossible m mask p q ||
        (List.range m).all (fun x => !(residueRoot m p q x))

theorem mask_sound {m mask p q x : ℕ} (hm : 0 < m) (hvalid : checkMask m mask = true)
    (hroot : cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x = 0) :
    maskPossible m mask (p%m) (q%m) = true := by
  have he : cubicHigh p q x = cubicLow p q x := by
    rw [cubic_parts] at hroot
    exact_mod_cast (sub_eq_zero.mp hroot)
  have hp : p%m ≡ p [MOD m] := Nat.mod_mod p m
  have hq : q%m ≡ q [MOD m] := Nat.mod_mod q m
  have hx : x%m ≡ x [MOD m] := Nat.mod_mod x m
  obtain ⟨hhi,hlo⟩ := cubic_parts_congr hp hq hx
  have hme : residueRoot m (p%m) (q%m) (x%m) = true := by
    unfold residueRoot
    apply decide_eq_true
    change _ % m = _ % m at hhi hlo
    rw [hhi,hlo,he]
  have hrp := List.mem_range.mpr (Nat.mod_lt p hm)
  have hrq := List.mem_range.mpr (Nat.mod_lt q hm)
  have hrx := List.mem_range.mpr (Nat.mod_lt x hm)
  unfold checkMask at hvalid
  have h := List.all_eq_true.mp (List.all_eq_true.mp hvalid _ hrp) _ hrq
  cases hmask : maskPossible m mask (p%m) (q%m) with
  | false =>
    simp only [hmask,Bool.false_or] at h
    have hf := List.all_eq_true.mp h _ hrx
    simp [hme] at hf
  | true => rfl

def mask7 : ℕ := 0x1fcd766efba0b
def mask11 : ℕ := 0x1f38e2dc3d1f777760ec3fc1b7ffeba
def mask13 : ℕ := 0x15bb7717ffd1d30ff756d47ae6edbf79c6bcfd84ccd
def mask17 : ℕ := 0x11bbaf9c9f0f6d9e7f17db3339bef557bc3523b7dbf1ed95d61cf9b6e274bff61bb5a74dc
def mask19 : ℕ := 0x171ff6da78dbabcbed6bbcfa7fffff7f62dba2ebd77777da79b79fa9dc51debfe3b07defcf76abecf9e7ff13ecc
def mask23 : ℕ := 0x19fcbdf7959cf7bee7f77e7755f9c7f2753cf291fc76f7d78bebe61edfd9a9bb318f7662e5fcff5e3eda7ab0becffffffe9bd4fec5cdcedbc4e24ffdfafdacad4cdb
def mask29 : ℕ := 0x1f1f83ea39f6e26ffdc3f3b2f9ab34eb5e89be7d37fb5df5773bffc9bce8e97f1d9c76f4293bff9fdeafe9b4bdaae7e6ffff0b4f72ffefff2d351b77ce17ad8fae7aa977ddef1b4f6deac74df5f1fceffbfa3e77bfe245ffece73af95a9ffdfb5fadffffffffe67eabf
def mask31 : ℕ := 0x193b8e727fffffffbbdf2ff3f77ad7bb7ddf3b3b3cbfbd7dfdf7d4ca6b5f5c61ebdeda427af5dbdb8b3e3bdb1e57ff0ff4d5dfd9acdffea9ffbb797ea6fbf27976dcf6baf9d837f7aadf2aebfdbfe76dfdc97fed6de3ead1aee55b9abf3f7fb4d1bb3e7392ffffffff2a7adff6c77b6f53bcf9b5eed6594f8
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask7 : checkMask 7 mask7=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask11 : checkMask 11 mask11=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask13 : checkMask 13 mask13=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask17 : checkMask 17 mask17=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask19 : checkMask 19 mask19=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask23 : checkMask 23 mask23=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask29 : checkMask 29 mask29=true := by decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private theorem validMask31 : checkMask 31 mask31=true := by decide +kernel

def residueMasks : List (ℕ × ℕ) := [(7,mask7), (11,mask11), (13,mask13), (17,mask17), (19,mask19), (23,mask23), (29,mask29), (31,mask31)]

private theorem mask_in_list (v : ℕ × ℕ) (h : v ∈ residueMasks) :
    0<v.1 ∧ checkMask v.1 v.2=true := by
  simp only [residueMasks,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, validMask7⟩
  · exact ⟨by decide, validMask11⟩
  · exact ⟨by decide, validMask13⟩
  · exact ⟨by decide, validMask17⟩
  · exact ⟨by decide, validMask19⟩
  · exact ⟨by decide, validMask23⟩
  · exact ⟨by decide, validMask29⟩
  · exact ⟨by decide, validMask31⟩

def sieveCubic (p q : ℕ) : Bool :=
  residueMasks.all fun v => maskPossible v.1 v.2 (p%v.1) (q%v.1)

theorem sieveCubic_sound {p q x : ℕ}
    (h : cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x=0) :
    sieveCubic p q = true := by
  apply List.all_eq_true.mpr
  intro v hv
  exact mask_sound (mask_in_list v hv).1 (mask_in_list v hv).2 h

def maskedCandidates (q lo size : ℕ) : List ℕ :=
  (candidateList q lo size).filter fun p => sieveCubic p q

theorem candidate_mem_masked {p q lo c : ℕ} (hp : p.Prime)
    (hpLo : 2*q < p) (hpHi : p^2 < q^3) (hmod : p%3 ≠ q%3) (hmod20 : p%20=3 ∨ p%20=7)
    (hpass : sieveCubic p q=true) (hlo : lo ≤ p/20) (hhi : p/20 < lo+c) :
    p ∈ maskedCandidates q lo c :=
  List.mem_filter.mpr ⟨candidateP_mem hp hpLo hpHi hmod hmod20 hlo hhi, hpass⟩


theorem G {q p : ℕ} (hp : p.Prime) (hlo : 2*q < p) (hhi : p^2 < q^3) (hmod : p%3 ≠ q%3)
    (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p q = true) ⦃lo c d : ℕ⦄
    (h : fastPacked q (maskedCandidates q lo c) d = true) (h1 : lo ≤ p/20) (h2 : p/20 < lo+c) :
    ∃ d, signCertificate p q d = true :=
  fastPacked_sound h (candidate_mem_masked hp hlo hhi hmod hres hpass h1 h2)

private def rowCap (q : ℕ) : ℕ := (q ^ 3).sqrt / 20 + 1

private def rowWidth (q j : ℕ) : ℕ := min 256 (rowCap q - 256 * j)

private def CheckedRow (q : ℕ) (data : List ℕ) : Prop :=
  rowCap q ≤ 256 * data.length ∧ ∀ j : Fin data.length,
    fastPacked q (maskedCandidates q (256 * j.val) (rowWidth q j.val)) (data.get j) = true

private instance (q : ℕ) (data : List ℕ) : Decidable (CheckedRow q data) := by
  unfold CheckedRow
  infer_instance

private theorem checkedRow_sound {p q : ℕ} {data : List ℕ}
    (hp : p.Prime) (hlo : 2*q < p) (hhi : p^2 < q^3) (hmod : p%3 ≠ q%3)
    (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p q = true) (hcheck : CheckedRow q data) :
    ∃ d, signCertificate p q d = true := by
  have hd := Nat.le_sqrt.mpr (show p * p ≤ q ^ 3 by simpa only [pow_two] using le_of_lt hhi)
  have hb : p / 20 < rowCap q := Nat.lt_succ_of_le (Nat.div_le_div_right hd)
  have hc := hcheck.1
  let j : Fin data.length := ⟨p / 20 / 256, by omega⟩
  have hj : j.val = p / 20 / 256 := rfl
  refine G hp hlo hhi hmod hres hpass (hcheck.2 j) (by omega) ?_
  unfold rowWidth
  omega


private def row01 : List ℕ := [
  0
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked01 : CheckedRow 67 row01 := by decide +kernel

private def row02 : List ℕ := [
  0x3a000040004
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked02 : CheckedRow 107 row02 := by decide +kernel

private def row05 : List ℕ := [
  0x85007
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked05 : CheckedRow 227 row05 := by decide +kernel

private def row07 : List ℕ := [
  0xb3009,
  0
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked07 : CheckedRow 307 row07 := by decide +kernel

private def row08 : List ℕ := [
  0xb60010b70010be0040c10050cc00b,
  0
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked08 : CheckedRow 347 row08 := by decide +kernel

private def row11 : List ℕ := [
  0xf7002,
  0xf30000f50010f5001
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked11 : CheckedRow 467 row11 := by decide +kernel

private def row13 : List ℕ := [
  0x12500312600412a00613300a1a806900009d,
  0x11b00011b00011b00111e00111e001124003,
  0x11900011900011a00011a00011a000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked13 : CheckedRow 547 row13 := by decide +kernel

private def row14 : List ℕ := [
  0,
  0x139003,
  0
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked14 : CheckedRow 587 row14 := by decide +kernel

private def row19 : List ℕ := [
  0x1c301400012a,
  0x19d00219e0031a6006,
  0x19500119800119800119900119900119b002,
  0x194000195001195001,
  0x192000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked19 : CheckedRow 787 row19 := by decide +kernel

private def row20 : List ℕ := [
  0x1de0181f30262a70c4,
  0x1b40031b80051b90051bb006,
  0x1ab0011ab0011ac0011ad0011ae0011af0021b1002,
  0,
  0x1a70001a7000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked20 : CheckedRow 827 row20 := by decide +kernel

private def row22 : List ℕ := [
  0x21d02623a03b,
  0x1f300c,
  0x1da002,
  0x1d20011d30011d40011d5001,
  0x1cf0001d00001d0000,
  0x1cf0001cf000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked22 : CheckedRow 907 row22 := by decide +kernel

private def row23 : List ℕ := [
  0x218014232025,
  0x212011,
  0x1ec0021ed0021ed0021ed0021ef002,
  0x1e60011e80011e9001,
  0x1e40001e40001e50001e5000,
  0x1e3000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked23 : CheckedRow 947 row23 := by decide +kernel

private def row29 : List ℕ := [
  0x2db0422df0452f805834e0a23760c600019a0000f2,
  0x27e00928300b28400c28600d28600d28700d28f01129001229c0182a001a2b1024,
  0x26d00326e00426f00427500627a008,
  0x26600226600226a00326c003,
  0x262001262001263001263001264001265001265002,
  0x25f001260001260001260001260001260001261001261001,
  0x25d00025d00025e00025e00025e00025e00025e00025e000,
  0x25c00025c00025c00025c00025c00025c00025c00025c00025d00025d00025d000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked29 : CheckedRow 1187 row29 := by decide +kernel

private def row32 : List ℕ := [
  0x332052000193,
  0x2c300c2c400d2c400d2cf0122d90172f102530102f,
  0x2b00052b10062b20062b70072b70082bb0092bf00a,
  0x2a60022a70032a8003,
  0x2a10012a4002,
  0x29e00129e00129e00129f00129f001,
  0x29c00029c00029c00129c00129c00129d001,
  0x29a00029b00029b00029b00029b000,
  0x298000298000298000298000299000299000299000299000299000,
  0x298000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked32 : CheckedRow 1307 row32 := by decide +kernel

private def row35 : List ℕ := [
  0,
  0,
  0x2f10062f90092fb00a,
  0x2e70032e80042e80042ef006,
  0,
  0x2de0012e0002,
  0x2db001,
  0x2d80002d80002d8001,
  0x2d60002d70002d8000,
  0,
  0x2d50002d5000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked35 : CheckedRow 1427 row35 := by decide +kernel

private def row40 : List ℕ := [
  0x4870de000261,
  0,
  0x36400b36800c36b00d,
  0x35d008,
  0x34e004,
  0,
  0,
  0x340001341001341001,
  0,
  0x33c00033d000,
  0x33b00033b000,
  0,
  0x33900033a000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked40 : CheckedRow 1627 row40 := by decide +kernel

private def row41 : List ℕ := [
  0x49e0de65d28b0002a7000257,
  0x3ab0233ad0243bc02c3c30313e404742f080,
  0x37900b37b00b37f00d38501038b01238c01339401739601739601839c01b,
  0x36900636a00636e007370008370008372008375009,
  0x361003361004361004362004365004366005368005368005368005,
  0x35b00235b00235c00235d00235d00235d00335e00335f00335f003360003360003360003,
  0x35800135800135800135800235800235800235900235900235900235a00235a00235a00235a00235b00235b002,
  0x355001355001356001356001356001357001,
  0x352001353001353001353001353001354001354001354001354001,
  0x351000351000351000351000351000351000351000351000351001352001352001352001352001,
  0x34f000350000350000350000350000350000350000350000350000351000351000,
  0x34f00034f00034f00034f00034f00034f00034f00034f000,
  0x34d00034d00034d00034e00034e00034e00034e00034e00034e00034e00034e000,
  0x34d00034d000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked41 : CheckedRow 1667 row41 := by decide +kernel

private def row43 : List ℕ := [
  0x5271320001eb,
  0x3d10203db0263e702d3f00334650874850a2,
  0x3ae0103b30123b40123c601a3c801c,
  0x39700739b00839b00839d0093a300b,
  0x38c00438e00538e005,
  0x38600338600338600338b004,
  0x382002382002383002,
  0x37f001380001380001,
  0x37c00137d00137d00137e001,
  0x37b00137c001,
  0x37900037a00037a00137a001,
  0x378000379000,
  0x377000377000377000377000,
  0x376000376000376000376000376000376000376000,
  0x375000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked43 : CheckedRow 1747 row43 := by decide +kernel

private def row44 : List ℕ := [
  0,
  0x41a040,
  0x3c60113d3017,
  0x3ac0073b3009,
  0x3a50053ab007,
  0x39e003,
  0x39900239a003,
  0x396002,
  0,
  0,
  0x38e00038e00038f001,
  0x38d00038d000,
  0x38b00038b000,
  0x38a00038b000,
  0x38a000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked44 : CheckedRow 1787 row44 := by decide +kernel

private def row46 : List ℕ := [
  0,
  0x42002942102a43503647e069,
  0x3f50133f50133fc01641102141302241c027,
  0x3db0093de00a3df00a3e100b3e400c3e600d3eb00f3eb00f,
  0x3cd0053cd0053d40073d40073d70083d7008,
  0x3c60033ca0043cb004,
  0x3c10023c10023c20023c30033c30033c40033c50033c6003,
  0x3be0023be0023bf0023c0002,
  0x3bb0013bc0013bd0013bd002,
  0x3b90013b90013ba0013ba0013ba001,
  0x3b70013b70013b70013b80013b80013b8001,
  0x3b50003b60003b60003b60003b60003b60013b70013b7001,
  0x3b40003b40003b50003b50003b50003b50003b5000,
  0x3b30003b30003b40003b40003b40003b4000,
  0x3b20003b20003b20003b20003b30003b30003b30003b3000,
  0x3b2000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked46 : CheckedRow 1867 row46 := by decide +kernel

private def row47 : List ℕ := [
  0,
  0,
  0,
  0x3f0009,
  0x3e40063e70063ea007,
  0,
  0x3d7002,
  0,
  0x3d00013d0001,
  0,
  0x3cc001,
  0x3cb0013cb0013cb001,
  0x3c90003ca0003ca000,
  0,
  0,
  0,
  0
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked47 : CheckedRow 1907 row47 := by decide +kernel

private def row49 : List ℕ := [
  0,
  0x4cd07350309d5470d6,
  0x43701543f01944601c44f021,
  0x42100c42700e42b010,
  0x40e006411007415008418009,
  0x40700440a00540b005,
  0x401003,
  0x3fd0023fe0023ff002,
  0x3fb0023fb0023fc002,
  0x3f80013f80013f8001,
  0x3f60013f60013f70013f7001,
  0x3f40013f40013f50013f5001,
  0x3f20003f20003f20003f20003f30013f30013f3001,
  0x3f10003f10003f10003f20003f20003f2000,
  0x3f00003f1000,
  0x3ef0003ef0003ef0003f00003f0000,
  0x3ee0003ee0003ee0003ef0003ef000,
  0x3ee000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked49 : CheckedRow 1987 row49 := by decide +kernel

private def row50 : List ℕ := [
  0,
  0x49403c4b004f4b5052,
  0x44a01444e01645401945c01d46c02547802c47e02f,
  0x43100b43500c43c00e442011446013447013447013,
  0x42500742b00942d00943100b,
  0x41c00441f00541f005,
  0x41800341900441900441a00441b00441b00441c004,
  0x412002413002413002413002414003414003414003416003,
  0x410002410002411002411002412002,
  0x40c00140c00140d00140d001,
  0x40a00140a00140b00140c001,
  0x408001409001409001,
  0x407001407001408001408001,
  0x405000406000406000406000406000406000406000406000407000,
  0x404000405000405000405000405000405000405000405000405000405000405000,
  0x404000404000404000404000,
  0x403000403000403000403000403000,
  0x402000402000402000403000403000403000403000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked50 : CheckedRow 2027 row50 := by decide +kernel

private def row56 : List ℕ := [
  0,
  0,
  0,
  0x4bb010,
  0x4ad00b4b000c,
  0x4a10074a3008,
  0x49800549a00549b006,
  0x495004495004,
  0x48d00248f003490003,
  0,
  0x488002489002,
  0x485001487001,
  0x484001,
  0x482001482001,
  0,
  0x47f000,
  0x47e00047e000,
  0,
  0x47d000,
  0x47c000,
  0x47b00047b000,
  0
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked56 : CheckedRow 2267 row56 := by decide +kernel

private def row58 : List ℕ := [
  0,
  0x5ff0ca63c0fd,
  0x51c029,
  0x50a020,
  0x4d700b4dc00d4e300f,
  0x4cb0074ce0084d1009,
  0x4c10054c30054c30054c4006,
  0x4be0044bf004,
  0x4b80034bb004,
  0,
  0x4b20024b20024b30024b3002,
  0x4ae0014af0014b0002,
  0x4ac0014ad0014ae001,
  0x4ab001,
  0x4a90014aa0014aa0014aa0014aa001,
  0,
  0x4a70004a70004a80004a8000,
  0x4a7000,
  0x4a50004a50004a6000,
  0x4a5000,
  0x4a40004a40004a40004a40004a4000,
  0x4a30004a40004a40004a4000,
  0
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked58 : CheckedRow 2347 row58 := by decide +kernel

private def row61 : List ℕ := [
  0,
  0x3e2,
  0x55902856302e568031584041,
  0x53901954401e,
  0x51f00f51f00f52201052601152801252c014,
  0,
  0,
  0x4fc0044fd0054fe005,
  0x4f70034f80044fb004,
  0x4f40034f50034f6003,
  0x4f00024f10024f10024f2002,
  0x4ed0024ee002,
  0x4eb0014ec0014ec0014ec002,
  0x4e90014ea001,
  0x4e70014e80014e8001,
  0x4e60014e70014e70014e7001,
  0x4e50014e50014e60014e6001,
  0x4e40004e40004e5000,
  0x4e3000,
  0x4e20004e2000,
  0x4e10004e10004e2000,
  0x4e10004e1000,
  0x4e00004e0000,
  0x4df0004df0004df0004e0000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked61 : CheckedRow 2467 row61 := by decide +kernel

private def row67 : List ℕ := [
  0,
  0x68709b6f20ef72d1218141f188225900033a,
  0x606043626057,
  0x5e70315ec0345ec034,
  0x5a10115a40125b701a5b901b,
  0x59000b59400d59d010,
  0x58600858c00a,
  0x57e00657f007580007580007,
  0x57b00657b006,
  0x575004,
  0x570003571003571003,
  0x56c00356d00356e003,
  0x56800256900256a00256a002,
  0x566002566002,
  0x564001564001564001,
  0x562001563001563001563001563001564001,
  0,
  0x560001560001,
  0x55f00155f00155f00155f001,
  0x55d00055d00155e00155e00155e001,
  0x55c00055d00055d00055d00055d000,
  0x55c00055c00055c000,
  0x55b00055b000,
  0x55a00055a00055a00055a000,
  0x55a000,
  0x559000559000559000559000559000,
  0x558000558000,
  0x558000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked67 : CheckedRow 2707 row67 := by decide +kernel

private def row76 : List ℕ := [
  0,
  0x9d22d50003eb0003cc,
  0,
  0x6bd03f6cd048,
  0x67a01e,
  0x66601666b018,
  0x65000e657010,
  0x64800b,
  0x63b008,
  0x635006,
  0x62d005630005631005,
  0x628004,
  0,
  0x622003,
  0x620002621002621002,
  0x61d00261f002,
  0,
  0x61a00161a00161b001,
  0x618001619001619001,
  0x617001617001,
  0x616001616001,
  0x614001614001615001,
  0x614001,
  0x613001,
  0x612000,
  0x611000611000,
  0x610000,
  0x610000610000,
  0x60f000,
  0x60e00060e00060f000,
  0x60e000,
  0x60d000,
  0x60d000,
  0
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked76 : CheckedRow 3067 row76 := by decide +kernel

private def row79 : List ℕ := [
  0,
  0x84c13485e1438731558e11b5,
  0x75207477308b,
  0x6df0306e00306e9035,
  0x6b701d6c10226c20226d00296d602b6dc02f,
  0x6a20156a30156ab018,
  0x68e00e69401069801169c013,
  0x68200a68300b68500b68700c68800c68800c,
  0x67800867a00867b00867c00967d00967f009,
  0x672006673007673007676007,
  0x66e005670006671006,
  0x66700466700466c005,
  0x664003665004665004666004666004666004667004667004,
  0x661003662003662003663003,
  0x65e00265f00365f003660003660003,
  0x65c00265c002,
  0x65a00265b002,
  0x658002658002659002659002659002659002,
  0x656001656001657001657001657001,
  0x655001656001,
  0x653001654001654001,
  0x653001,
  0x651001651001651001651001652001652001652001,
  0x650001650001650001651001,
  0x64f00164f001650001650001650001,
  0x64f00064f00064f00064f000,
  0x64e00064e00064e00064e00064e00064e000,
  0x64d00064d00064d00064d00064d000,
  0x64c00064d00064d000,
  0x64c00064c00064c000,
  0x64b00064b000,
  0x64b00064b00064b000,
  0x64a00064a00064a00064a00064a00064a00064a00064a000,
  0x64a00064a00064a000,
  0x649000649000649000649000,
  0x649000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked79 : CheckedRow 3187 row79 := by decide +kernel

private def row82 : List ℕ := [
  0,
  0x94c1d9a522cc000497,
  0x79007379c07b7a107e7ab0857ae0877be0927c909a7e20ac82d0e587511f89d140,
  0x72b03774204374e04a76f05d777063,
  0x727034,
  0x6e30166e60176ed01a6ee01b6f301c6f601e,
  0x6d00106d70126d90126e1015,
  0x6c400c6c800d6cd00f,
  0x6bc0096bd00a6bd00a,
  0x6b40076b40086b40086b50086b60086b7008,
  0x6ae0066ae0066af0066b2007,
  0x6a80056a90056ab005,
  0x6a30046a40046a40046a50046a50046a5004,
  0x6a00036a10036a20046a2004,
  0x69d00369d00369d00369e00369e00369f00369f003,
  0x69b00269c00369c003,
  0x69800269900269a00269a002,
  0x696002696002696002697002,
  0x694001695002,
  0x693001694001694001,
  0x691001,
  0x690001690001691001691001691001691001,
  0x68f001690001690001690001,
  0x68e00168e00168f001,
  0x68d00168d00168d00168d00168d00168e001,
  0x68c00168c00168c001,
  0x68b00068b00168b00168c00168c00168c001,
  0x68a00068a00068b00068b000,
  0x68a00068a00068a00068a00068a000,
  0x689000689000689000689000689000,
  0x688000689000689000689000,
  0x688000688000,
  0x687000687000687000688000688000,
  0x687000687000687000687000687000,
  0x686000686000687000687000,
  0x686000686000686000686000,
  0x685000685000685000686000686000686000686000,
  0x685000685000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked82 : CheckedRow 3307 row82 := by decide +kernel

private def row83 : List ℕ := [
  0,
  0x4fc0003ba,
  0x8080b88280d08490ea,
  0x76504b,
  0x719024720027721028725029725029738033,
  0x6fa01770801d,
  0x6ec0126ef0136f00136f1014,
  0x6dc00d6e000e6e100e6e50106e5010,
  0x6cf0096d00096d100a,
  0x6c80076c80076cd0096cd0096cd009,
  0x6c30066c5007,
  0x6be0056be0056be0056c00066c1006,
  0x6b80046b90046ba0046ba0046bb005,
  0x6b50036b7004,
  0x6b20036b30036b30036b4003,
  0,
  0x6ad0026ad0026ae0026ae002,
  0x6ac0026ac002,
  0x6a90026a90026aa0026aa0026ab0026ab002,
  0x6a8001,
  0x6a60016a70016a7001,
  0x6a50016a50016a5001,
  0x6a40016a40016a40016a40016a40016a40016a4001,
  0x6a20016a30016a30016a3001,
  0x6a10016a10016a20016a20016a20016a20016a20016a2001,
  0x6a10016a10016a10016a1001,
  0x6a00016a00016a00016a00016a00016a0001,
  0x69f00069f00069f0006a0001,
  0x69e00069e00069f000,
  0x69d00069d00069e00069e000,
  0x69d00069d00069d000,
  0x69c00069d00069d000,
  0x69c00069c00069c00069c000,
  0x69b00069b00069c000,
  0x69b00069b00069b00069b00069b000,
  0x69a00069a00069a00069a000,
  0x69a00069a00069a00069a00069a00069a000,
  0x69900069900069a00069a000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked83 : CheckedRow 3347 row83 := by decide +kernel

private def row86 : List ℕ := [
  0,
  0x9ad1e0,
  0x7f507d,
  0x79d0477b9057,
  0,
  0,
  0x72b013,
  0x727011,
  0x71200b71400b71600c,
  0x70b009,
  0x704007706008,
  0x6fc0056fc005701006,
  0x6f80046fb005,
  0x6f50046f60046f6004,
  0x6f2003,
  0x6ef003,
  0,
  0x6e90026eb0026eb002,
  0x6e9002,
  0x6e70026e7002,
  0x6e40016e5001,
  0,
  0x6e10016e20016e2001,
  0,
  0x6df0016e00016e0001,
  0x6df0016df001,
  0x6de001,
  0x6dd0016dd001,
  0x6dc0006dc001,
  0x6db0006db0006db0006db000,
  0,
  0x6da0006da0006da000,
  0x6d9000,
  0,
  0x6d8000,
  0x6d70006d70006d80006d80006d8000,
  0x6d7000,
  0x6d60006d7000,
  0x6d6000,
  0x6d6000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked86 : CheckedRow 3467 row86 := by decide +kernel

private def row88 : List ℕ := [
  0,
  0,
  0x8420958530a090d13092013f,
  0x7df055,
  0x79a030,
  0x76e01c77201e77501f77a021,
  0x75801475c01575d016762017765019,
  0x74700e74e010,
  0x74000c74100c74400d,
  0x73300973300973600973900a,
  0x72e007731008733009,
  0x72800672900672a00772b007,
  0x722005,
  0x720004722005722005,
  0x71c00471d004,
  0x71800371800371900371900371a003,
  0x717003,
  0x713002713002,
  0x711002712002712002,
  0x70f002710002,
  0x70e00270f002,
  0x70c00170d00170d00170d00170d001,
  0x70b00170b00170b001,
  0x70900170a00170a001,
  0x708001709001709001709001,
  0x708001,
  0x706001707001707001707001,
  0x705001706001,
  0x705001705001705001705001,
  0x704000704000704000,
  0x703000703000703000704000,
  0x703000703000703000,
  0x702000702000702000,
  0x701000702000702000,
  0x701000701000701000,
  0x700000700000701000,
  0x700000700000700000700000,
  0x6ff0006ff0006ff0006ff000,
  0x6ff0006ff0006ff0006ff000,
  0x6fe0006ff0006ff000,
  0x6fe0006fe000,
  0x6fe0006fe000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked88 : CheckedRow 3547 row88 := by decide +kernel

private def row97 : List ℕ := [
  0,
  0xbf43140004560003ec0003ba000312,
  0x9550cf95c0d496e0e29770e898e0fa9c31239c8127a14165a21171b6b294,
  0x8b20618bd0688bf0698c706e8d30758dc07b8e30808f00888f208a8fd0918ff09390109490309591109f9190a491d0a792b0b0,
  0x86803887503f88004588904a89204f8960518980528a505a8a705b,
  0x84102684502884702984802984802a84a02b84b02b84f02d85002d85202e85d03385d033864037,
  0x82301a82301a82601b82801c82901c82901d83002083202083302083602283602283702283702283b024,
  0x81001381101481101481201481301581601681701681a01781c01881c01881e01981f019,
  0x80200f80200f80401080501080901180901180a01180b01280c01280d01380e01380e013,
  0x7f700c7f700c7f800c7f900d7fa00d7fa00d7fa00d7fb00d7fb00d7fc00d7ff00e7ff00e80000f80100f,
  0x7ef00a7ef00a7ef00a7f000a7f100a7f300b7f500c7f600c,
  0x7e70087e80087e80087e80087e90087e90087ea0097ea0097ec0097ec0097ed0097ee0097ee00a,
  0x7e20077e30077e30077e40077e40077e60087e70087e7008,
  0x7dd0067de0067de0067df0067df0067e00067e00067e00067e1007,
  0x7d90057d90057d90057d90057da0057da0057da0057db0057db0057db0057db0057dc006,
  0x7d50047d60047d60047d60047d60047d60047d70057d70057d80057d80057d8005,
  0x7d20047d20047d20047d20047d20047d20047d20047d30047d30047d30047d40047d40047d40047d40047d4004,
  0x7cf0037cf0037cf0037cf0037d00037d00037d10037d10047d10047d10047d1004,
  0x7cc0037cd0037cd0037cd0037cd0037ce0037ce0037ce0037ce0037cf003,
  0x7ca0027ca0027cb0037cb0037cb0037cb0037cc0037cc0037cc003,
  0x7c80027c80027c80027c90027c90027c90027c90027c90027ca0027ca0027ca002,
  0x7c60027c70027c70027c70027c70027c70027c70027c70027c80027c80027c8002,
  0x7c50027c50027c50027c50027c50027c60027c60027c60027c60027c60027c60027c60027c6002,
  0x7c30027c40027c40027c40027c40027c40027c40027c40027c40027c5002,
  0x7c20017c20017c20017c20017c20017c20017c20017c30017c30017c30027c30027c30027c3002,
  0x7c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c10017c2001,
  0x7bf0017c00017c00017c00017c00017c00017c00017c00017c00017c00017c0001,
  0x7be0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf0017bf001,
  0x7bd0017bd0017be0017be0017be0017be0017be0017be0017be0017be0017be0017be001,
  0x7bc0017bc0017bc0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd0017bd001,
  0x7bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc0017bc001,
  0x7bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb0017bb001,
  0x7ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017bb0017bb0017bb001,
  0x7b90017b90017b90017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba0017ba001,
  0x7b90007b90007b90007b90007b90007b90007b90007b90007b90007b90007b90017b90017b9001,
  0x7b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b80007b8000,
  0x7b70007b70007b80007b80007b80007b80007b80007b80007b8000,
  0x7b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b70007b7000,
  0x7b60007b60007b60007b60007b60007b60007b70007b70007b70007b7000,
  0x7b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b60007b6000,
  0x7b50007b50007b50007b50007b50007b50007b50007b50007b50007b60007b60007b60007b60007b60007b60007b6000,
  0x7b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b50007b5000,
  0x7b40007b40007b40007b50007b50007b50007b50007b50007b50007b50007b50007b5000,
  0x7b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b40007b4000,
  0x7b30007b40007b40007b40007b40007b40007b4000,
  0x7b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b30007b3000,
  0x7b30007b30007b30007b30007b30007b30007b30007b3000,
  0x7b30007b30007b30007b30007b30007b3000
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked97 : CheckedRow 3907 row97 := by decide +kernel

private def row98 : List ℕ := [
  0,
  0,
  0xb7728b,
  0x8c405f8d2068,
  0,
  0x85602786402d86602e,
  0x84301f84e023,
  0x82c016,
  0x821012822013,
  0x81600f,
  0x80400a80500a80b00c,
  0,
  0,
  0x7f3006,
  0x7ef0057f1006,
  0,
  0x7e80047e9004,
  0,
  0x7e3003,
  0,
  0x7dd0027de0027de002,
  0x7db0027db0027dc0027dc0027dd0027dd002,
  0x7d9002,
  0x7d8002,
  0,
  0x7d60017d60017d6001,
  0x7d5001,
  0x7d30017d4001,
  0x7d20017d3001,
  0x7d10017d1001,
  0,
  0,
  0,
  0,
  0x7cd0017cd001,
  0x7cd000,
  0x7cc000,
  0x7cc0007cc000,
  0,
  0x7ca0007cb0007cb000,
  0x7ca000,
  0x7c90007c9000,
  0,
  0x7c8000,
  0x7c8000,
  0x7c8000,
  0x7c7000,
  0x7c7000,
  0
]
set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
private def checked98 : CheckedRow 3947 row98 := by decide +kernel

private def validIndices : List ℕ := [1, 2, 5, 7, 8, 11, 13, 14, 19, 20, 22, 23, 29, 32, 35, 40, 41, 43, 44, 46, 47, 49, 50, 56, 58, 61, 67, 76, 79, 82, 83, 86, 88, 97, 98]

private theorem checkedIndices : (List.range 100).all
    (fun i => !possiblePrime (qFromIndex i) || validIndices.contains i) = true := by
  decide +kernel

private theorem index_mem {i : ℕ} (hi : i<100) (hq : (qFromIndex i).Prime) :
    i ∈ validIndices := by
  have h := List.all_eq_true.mp checkedIndices i (List.mem_range.mpr hi)
  have hs := prime_possiblePrime hq
  simpa [hs] using h

private theorem check_for_index {p i : ℕ} (hp : p.Prime) (hi : i<100)
    (hq : (qFromIndex i).Prime) (hlo : 2*qFromIndex i<p)
    (hhi : p^2<(qFromIndex i)^3) (hmod : p%3≠qFromIndex i%3)
    (hres : p%20=3 ∨ p%20=7) (hpass : sieveCubic p (qFromIndex i) = true) :
    ∃ d, signCertificate p (qFromIndex i) d = true := by
  have hvalid := index_mem hi hq
  simp only [validIndices, List.mem_cons, List.not_mem_nil, or_false] at hvalid
  rcases hvalid with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked01
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked02
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked05
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked07
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked08
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked11
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked13
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked14
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked19
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked20
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked22
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked23
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked29
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked32
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked35
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked40
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked41
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked43
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked44
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked46
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked47
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked49
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked50
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked56
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked58
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked61
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked67
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked76
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked79
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked82
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked83
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked86
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked88
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked97
  · exact checkedRow_sound hp hlo hhi hmod hres hpass checked98


theorem bounded : OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1.H1 := by
  intro p q x hp hq _ hp4 hq8 _ hlo hmod hhi hp5 hq5 hqBound _ _ hx _
  dsimp only
  intro _ hrec _
  have hroot : cubic (sumCoeff p q) (pairCoeff p q) (productCoeff p q) x=0 := by
    simp only [cubic,pairCoeff,sumCoeff,productCoeff]
    linear_combination -hrec
  have hqValue := q_index_eq hq8 hq5
  have hi : q/40 < 100 := by omega
  have hqPrime : (qFromIndex (q/40)).Prime := by rwa [hqValue]
  have hlo' : 2*qFromIndex (q/40)<p := by rwa [hqValue]
  have hhi' : p^2<(qFromIndex (q/40))^3 := by rwa [hqValue]
  have hmod' : p%3≠qFromIndex (q/40)%3 := by rwa [hqValue]
  have hpass : sieveCubic p (qFromIndex (q/40))=true := by
    rw [hqValue]
    exact sieveCubic_sound hroot
  obtain ⟨d, hd⟩ := check_for_index hp hi hqPrime hlo' hhi' hmod'
    (p_mod_twenty hp4 hp5) hpass
  rw [hqValue] at hd
  exact signCertificate_sound hd (le_of_lt hx) hroot

end A056777Bounded

theorem OMA.solution : OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1.H1 :=
  A056777Bounded.bounded
