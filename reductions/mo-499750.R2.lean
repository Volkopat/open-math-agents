import OMAStatements.S_mo_499750
import Mathlib

/-!
The two hypotheses are Pierre Dusart's unconditional estimates for the prime
counting function, Theorem 6.9, equation (6.6), arXiv:1002.0442. Taking
the strict version of each real cutoff avoids endpoint conventions.

For x = sqrt(k) and p > x+1, a failure of the two-digit inequality puts the
integer p+floor(k/p) between F(p-1) and F(p), where F(t)=t+k/t. Distinct
odd primes give disjoint intervals. Dusart's two inequalities place more
primes above x than there are possible bad integers. The finite initial
range is covered by the explicit interval and prime certificates below.
-/
namespace OMA.R_mo_499750_R2

def H1 : Prop := ∀ x : ℝ, 5393 < x →
  x / (Real.log x - 1) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ)

def H2 : Prop := ∀ x : ℝ, 60184 < x →
  (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / (Real.log x - 11/10)


theorem log_large {x : ℝ} (hx : 65536 ≤ x) : 11 < Real.log x := by
  have ht : (65536 : ℝ) = 2 ^ (16 : ℕ) := by norm_num
  have h := Real.log_le_log (by norm_num : (0:ℝ) < 65536) hx
  rw [ht, Real.log_pow] at h
  norm_num at h
  linarith [Real.log_two_gt_d9]

/-- A uniform margin for discarding the endpoint and rounding the bad-prime bound. -/
theorem squared_log_margin {x : ℝ} (hx : 65536 ≤ x) : 40 * (Real.log x)^2 < x := by
  have hx0 : 0 < x := by linarith
  have hr0 := Real.sqrt_pos.2 hx0
  have hr := Real.sq_sqrt hx0.le
  have hu : 256 ≤ Real.sqrt x := by nlinarith [sq_nonneg (Real.sqrt x-256)]
  have hl := Real.log_le_sub_one_of_pos (show 0 < Real.sqrt x / 256 by positivity)
  rw [Real.log_div hr0.ne' (by norm_num), Real.log_sqrt hx0.le,
    (show (256:ℝ) = 2^8 by norm_num), Real.log_pow] at hl
  norm_num at hl
  have hh : Real.log x ≤ Real.sqrt x / 16 := by linarith [Real.log_two_lt_d9]
  have h2 := pow_le_pow_left₀ (Real.log_pos (by linarith : 1 < x)).le hh 2
  nlinarith [h2]

/-- Explicit lower bound for primes in the short interval above √k. -/
theorem prime_supply (hLower : H1) (hUpper : H2) {x : ℝ} (hx : 65536 ≤ x) :
    3 * x / (10 * (Real.log x)^2) <
      (Nat.primeCounting ⌊(x + x / (2 * Real.log x))⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  let L := Real.log x
  have hL : 11 < L := log_large hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < L := by linarith
  let t : ℝ := 1 / (2 * L)
  have ht : 0 < t := by dsimp [t]; positivity
  have hsmall : t < 1 := by dsimp [t]; apply (div_lt_iff₀ (by linarith : (0:ℝ)<2*L)).2; linarith
  let y := x * (1+t)
  have hy : x ≤ y := by dsimp [y]; nlinarith [mul_pos hx0 ht]
  have hlog : Real.log y ≤ L + t := by
    rw [show y = x*(1+t) from rfl,Real.log_mul hx0.ne' (by positivity : (1+t:ℝ)≠0)]
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1+t by linarith)]
  have hylog : 0 < Real.log y - 1 := by linarith [log_large (hx.trans hy)]
  have hdl : 0 < L - 11/10 := by linarith
  have hdu : 0 < L - 1 + t := by linarith
  have hmin : y / (L - 1 + t) ≤ (Nat.primeCounting ⌊y⌋₊ : ℝ) := by
    exact (div_le_div_of_nonneg_left (hx0.le.trans hy) hylog (by linarith)).trans
      (hLower y (by linarith [hx.trans hy]))
  have hmax : (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ x / (L - 11/10) := (hUpper x (by linarith))
  have hnum : 3 / 10 < (1+t)*(L-11/10)-(L-1+t) := by
    dsimp [t]; field_simp; nlinarith
  have hden : (L-1+t)*(L-11/10) ≤ L^2 := by
    calc
      (L-1+t)*(L-11/10) ≤ L*L :=
        mul_le_mul (by linarith) (by linarith) hdl.le hL0.le
      _ = _ := by ring
  have halg : 3*x/(10*L^2) < y/(L-1+t)-x/(L-11/10) := by
    dsimp [y]
    rw [div_sub_div _ _ hdu.ne' hdl.ne']
    apply (div_lt_div_iff₀ (by positivity) (mul_pos hdu hdl)).2
    nlinarith [mul_pos hx0 (sub_pos.2 hnum),
      mul_nonneg (show 0 ≤ 3*x by positivity) (sub_nonneg.2 hden),
      mul_pos (mul_pos hx0 (sq_pos_of_pos hL0)) (sub_pos.2 hnum)]
  have hy' : x + x/(2*Real.log x) = y := by dsimp [y,t,L]; ring
  rw [hy']
  linarith

theorem bad_bound {k p : ℕ} (hp : 1 < p) (hk : k < p^2)
    (hb : ¬ p ≤ k%p + k/p%p) : k ≤ (p-1)*(k/p+1) := by
  have hq : k/p<p := (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa [pow_two] using hk)
  rw [Nat.mod_eq_of_lt hq] at hb
  have hd := Nat.mod_add_div k p
  have he : p-1+1=p := by omega
  have hb' : k%p+k/p+1 ≤ p := by omega
  nlinarith [congrArg (· * (k/p+1)) he]

theorem bad_index_strict {k p v : ℕ} (hgap : p+2≤v) (hk : k<p^2)
    (hb : ¬ v≤k%v+k/v%v) : (p+k/p : ℕ) < (v+k/v : ℕ) := by
  have hp : 0<p := Nat.pos_of_ne_zero (fun h => by simpa [h] using hk)
  have hv : 1<v := by omega
  have hkv : k<v^2 := by nlinarith [Nat.mul_self_lt_mul_self (show p<v by omega)]
  have hi := bad_bound hv hkv hb
  have hlo := Nat.div_mul_le_self k p
  have hq : k/p<p := (Nat.div_lt_iff_lt_mul hp).2 (by simpa [pow_two] using hk)
  by_contra hh
  try dsimp only at hh
  let d:=v-p-1
  have hd : 0<d := by dsimp [d]; omega
  have he : v-1=p+d := by dsimp [d]; omega
  have hqr : k/v+1+d ≤ k/p := by dsimp [d]; omega
  have hlt : k/v+1<p := by omega
  rw [he] at hi
  nlinarith [Nat.mul_le_mul_right p hqr,Nat.mul_lt_mul_of_pos_right hlt hd]

theorem bad_index_bounds {k p : ℕ} {x y : ℝ} (hx : 0<x) (hk : x^2=(k:ℝ))
    (hlo : x+1 < (p:ℝ)) (hhi : (p:ℝ) ≤ y) (hb : ¬p≤k%p+k/p%p) :
    2*x ≤ ((p+k/p : ℕ):ℝ) ∧ ((p+k/p : ℕ):ℝ) ≤ 2*x+(y-x)^2/y := by
  have hp : 1<p := by exact_mod_cast (show (1:ℝ)<p by linarith)
  have hk' : k<p^2 := by exact_mod_cast (show (k:ℝ)<(p:ℝ)^2 by nlinarith [sq_nonneg ((p:ℝ)-x-1), mul_pos hx (show 0 < (p:ℝ)-x by linarith)])
  have hl:=bad_bound hp hk' hb
  have hcast : (↑(p-1):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hl' : (k:ℝ) ≤ (↑(p-1):ℝ)*((k/p:ℕ)+1:ℝ) := by exact_mod_cast hl
  rw [hcast] at hl'
  have hq : ((k/p:ℕ):ℝ)*(p:ℝ)≤(k:ℝ) := by exact_mod_cast Nat.div_mul_le_self k p
  have hpy : x^2 ≤ (p:ℝ)*y := by nlinarith [mul_nonneg (show 0≤(p:ℝ)-x by linarith) (show 0≤y-x by linarith),mul_nonneg hx.le (show 0≤(p:ℝ)-x by linarith),mul_nonneg hx.le (show 0≤y-x by linarith)]
  have hy : 0<y := by linarith
  simp only [Nat.cast_add]
  constructor
  · apply le_of_mul_le_mul_right (a:= (p:ℝ)-1) _ (by linarith)
    nlinarith [sq_nonneg ((p:ℝ)-1-x)]
  · apply (sub_le_iff_le_add').1
    apply (le_div_iff₀ hy).2
    have hp' : 0<(p:ℝ) := by positivity
    apply le_of_mul_le_mul_right (a:=(p:ℝ)) _ hp'
    rw [← hk] at hq
    nlinarith [mul_le_mul_of_nonneg_right hq hy.le, mul_nonneg (show 0≤y-(p:ℝ) by linarith) (sub_nonneg.mpr hpy)]

theorem bad_card_le {k : ℕ} {x y : ℝ} (hx : 0<x) (hxy : x≤y) (hk : x^2=(k:ℝ))
    (S : Finset ℕ) (hs : ∀ p ∈ S, p.Prime ∧ p ≠ 2 ∧ x+1<(p:ℝ) ∧ (p:ℝ)≤y ∧ ¬p≤k%p+k/p%p) :
    (S.card:ℝ) ≤ (y-x)^2/y+1 := by
  let lo := ⌈2*x⌉₊
  let hi := ⌊2*x+(y-x)^2/y⌋₊
  have hy : 0<y := hx.trans_le hxy
  have hw : 0≤(y-x)^2/y := by positivity
  have hub : 0≤2*x+(y-x)^2/y := by positivity
  have mem (p : ℕ) (hp : p∈S) : (p+k/p : ℕ) ∈ Finset.Icc lo hi := by
    obtain ⟨_,_,hpx,hpy,hb⟩ := hs p hp
    obtain ⟨h1,h2⟩ := bad_index_bounds hx hk hpx hpy hb
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr h1,(Nat.le_floor_iff hub).mpr h2⟩
  have ltidx (p v : ℕ) (hp : p∈S) (hv : v∈S) (hlt : p<v) : (p+k/p : ℕ)<(v+k/v : ℕ) := by
    obtain ⟨hpr,hne,hx1,_,_⟩ := hs p hp
    obtain ⟨hvr,hne',_,_,hb⟩ := hs v hv
    obtain ⟨a,ha⟩ := hpr.odd_of_ne_two hne
    obtain ⟨b,hb'⟩ := hvr.odd_of_ne_two hne'
    have hkp : k<p^2 := by
      exact_mod_cast (show (k:ℝ)<(p:ℝ)^2 by nlinarith [sq_nonneg ((p:ℝ)-x-1), mul_pos hx (show 0 < (p:ℝ)-x by linarith)])
    exact bad_index_strict (by omega) hkp hb
  have hc : S.card ≤ (Finset.Icc lo hi).card := Finset.card_le_card_of_injOn (fun p : ℕ => p+k/p)
    (fun p hp => mem p hp) (by
      intro p hp v hv he
      rcases lt_trichotomy p v with h|h|h
      · exact False.elim ((ltidx p v hp hv h).ne he)
      · exact h
      · exact False.elim ((ltidx v p hv hp h).ne he.symm))
  rw [Nat.card_Icc] at hc
  by_cases h : lo ≤ hi+1
  · have hcr : (S.card:ℝ) ≤ ((hi+1-lo:ℕ):ℝ) := by exact_mod_cast hc
    rw [Nat.cast_sub h,Nat.cast_add,Nat.cast_one] at hcr
    have hlo := Nat.le_ceil (2*x)
    have hhi := Nat.floor_le hub
    change (hi:ℝ)≤_ at hhi
    change _≤(lo:ℝ) at hlo
    linarith
  · have : S.card=0 := by omega
    rw [this]; simp; linarith

private theorem card_short_interval_bound (x y : ℝ) :
    (Nat.primeCounting ⌊y⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      ((Nat.primesLE ⌊y⌋₊ \ Nat.primesLE (⌊x⌋₊ + 1)).card : ℝ) + 1 := by
  let A := Nat.primesLE ⌊y⌋₊
  let B := Nat.primesLE (⌊x⌋₊ + 1)
  have hsub : A ⊆ B ∪ (A \ B) := by
    intro p h
    by_cases hp : p ∈ B
    · exact Finset.mem_union_left _ hp
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h,hp⟩)
  have hc : A.card ≤ B.card + (A \ B).card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hnext : B.card ≤ (Nat.primesLE ⌊x⌋₊).card + 1 := by
    dsimp [B]
    rw [Nat.primesLE_succ]
    split
    · exact Finset.card_insert_le _ _
    · omega
  have hn : A.card ≤ (Nat.primesLE ⌊x⌋₊).card + (A \ B).card + 1 := by omega
  try dsimp only
  rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting]
  dsimp [A,B] at hn
  exact (sub_le_iff_le_add).2 (by exact_mod_cast (by omega :
    (Nat.primesLE ⌊y⌋₊).card ≤ ((Nat.primesLE ⌊y⌋₊ \ Nat.primesLE (⌊x⌋₊+1)).card + 1) +
    (Nat.primesLE ⌊x⌋₊).card))

/-- The full analytic tail, with the sole external input isolated in DusartBounds. -/
theorem of_dusart_tail (hLower : H1) (hUpper : H2) {k : ℕ} (hk : 65536^2 ≤ k) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ (k : ℝ) < (p : ℝ)^2 ∧ p ≤ k % p + k / p % p := by
  let x := Real.sqrt (k : ℝ)
  have hx2 : x^2 = k := Real.sq_sqrt (by positivity)
  have hxc : 65536 ≤ x := by
    have hk' : (65536:ℝ)^2 ≤ k := by exact_mod_cast hk
    have hxn : 0 ≤ x := Real.sqrt_nonneg _
    nlinarith [sq_nonneg (x-65536)]
  have hx : 0 < x := by linarith
  let L := Real.log x
  have hL : 11 < L := log_large hxc
  have hL0 : 0 < L := by linarith
  let y := x+x/(2*L)
  have hxy : x ≤ y := by exact le_add_of_nonneg_right (by positivity)
  have hy0 : 0<y := hx.trans_le hxy
  let S := Nat.primesLE ⌊y⌋₊ \ Nat.primesLE (⌊x⌋₊+1)
  by_contra he
  have hpS (p : ℕ) (hp : p∈S) :
      p.Prime ∧ p≠2 ∧ x+1<(p:ℝ) ∧ (p:ℝ)≤y ∧ ¬p≤k%p+k/p%p := by
    obtain ⟨ha,hb⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpy,hprime⟩ := Nat.mem_primesLE.mp ha
    have hpn : ⌊x⌋₊+1 < p := by
      by_contra! h
      exact hb (Nat.mem_primesLE.mpr ⟨h,hprime⟩)
    have hpc : x+1 < (p:ℝ) := by
      have hc : (⌊x⌋₊ : ℝ)+2 ≤ p := by exact_mod_cast (by omega : ⌊x⌋₊+2 ≤ p)
      linarith [Nat.lt_floor_add_one x]
    have hp2 : p ≠ 2 := by intro h; subst p; norm_num at hpc; linarith
    have hxpp : (k:ℝ) < (p:ℝ)^2 := by
      nlinarith [mul_pos (sub_pos.2 (by linarith : x < (p:ℝ))) (by linarith : 0 < (p:ℝ)+x)]
    exact ⟨hprime,hp2,hpc, (by exact_mod_cast hpy : (p:ℝ)≤(⌊y⌋₊:ℕ)).trans (Nat.floor_le hy0.le),
      fun hdig => he ⟨p,hprime,hp2,hxpp,hdig⟩⟩
  have hbad := bad_card_le hx hxy hx2 S hpS
  have hshort : (Nat.primeCounting ⌊y⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ (S.card:ℝ)+1 := card_short_interval_bound x y
  have hmain : 3*x/(10*L^2) < (Nat.primeCounting ⌊y⌋₊ : ℝ) - (Nat.primeCounting ⌊x⌋₊ : ℝ) := prime_supply hLower hUpper hxc
  have hupper : (y-x)^2 / y ≤ x/(4*L^2) := calc
    (y-x)^2 / y ≤ (y-x)^2/x := div_le_div_of_nonneg_left (sq_nonneg _) hx hxy
    _ = x/(4*L^2) := by dsimp [y]; field_simp; ring
  have hgap : 40*L^2 < x := squared_log_margin hxc
  have hquot : x / (4*L^2) + 2 < 3*x/(10*L^2) := by
    field_simp
    nlinarith
  linarith

private theorem stamp_bounds {k a p H T Y : ℕ}
    (ha : a*a ≤ k) (ha' : k < (a+1)*(a+1))
    (hap : a+2 ≤ p) (hYa : Y ≤ a) (hpH : p ≤ Y+H) (hHT : H*H ≤ Y*T) :
    2*a ≤ (p+k/p : ℕ) ∧ (p+k/p : ℕ) ≤ 2*a+T+2 := by
  try dsimp only
  have hmod := Nat.mod_lt k (by omega : 0 < p)
  have hdiv := Nat.mod_add_div k p
  let b := p-a
  have hb : p = a+b := by dsimp [b]; omega
  have hbH : b ≤ H := by omega
  have hsq := Nat.mul_le_mul hbH hbH
  have hYP := Nat.mul_le_mul_right T (show Y ≤ p by omega)
  have hidentity : p*p+a*a = b*b+2*a*p := by rw [hb]; ring
  constructor
  · by_contra! h
    have he := Nat.mul_le_mul_right p (show p+k/p+1 ≤ 2*a by omega)
    nlinarith [Nat.zero_le (b*b)]
  · by_contra! h
    have he := Nat.mul_le_mul_right p (show 2*a+T+3 ≤ p+k/p by omega)
    nlinarith only [he, hidentity, hHT, hsq, hYP, ha', hdiv, Nat.zero_le (k%p), hap]

private theorem stamp_lt {k a p q : ℕ} (ha' : k < (a+1)*(a+1))
    (hap : a+2 ≤ p) (hpq : p+2 ≤ q) (hbad : k%q + k/q < q) :
    (p+k/p : ℕ) < (q+k/q : ℕ) := by
  have hq : 0 < q := by omega
  have hv : k/q < a+1 := (Nat.div_lt_iff_lt_mul hq).2
    (lt_of_lt_of_le ha' (Nat.mul_le_mul_left _ (show a+1 ≤ q by omega)))
  have hdiv := Nat.mod_add_div k q
  have hdivp := Nat.div_mul_le_self k p
  let s := q-p-2
  let t := p-k/q-2
  have hs : q = p+2+s := by dsimp [s]; omega
  have ht : p = k/q+2+t := by dsimp [t]; omega
  by_contra! he
  try dsimp only at he
  have hmul := Nat.mul_le_mul_right p he
  have hpos : 0 < (s+1)*(t+1) := by positivity
  nlinarith

theorem shell {k a Y B H T : ℕ} (ha : a*a ≤ k) (ha' : k < (a+1)*(a+1))
    (hYa : Y ≤ a) (haB : a ≤ B) (hHT : H*H ≤ Y*T) (S : Finset ℕ)
    (hP : ∀ p ∈ S, p.Prime ∧ p%2 = 1 ∧ B+2 ≤ p ∧ p ≤ Y+H)
    (hcard : T+3 < S.card) : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := by
  classical
  by_contra hn
  have hbad (p) (hp : p ∈ S) : k%p + k/p < p := by
    obtain ⟨hpp, ho, hl, _⟩ := hP p hp
    have hp' : 0 < p := hpp.pos
    have haP : a+1 ≤ p := by omega
    have hs := Nat.mul_le_mul haP haP
    have hv : k/p < p := (Nat.div_lt_iff_lt_mul hp').2 (by omega)
    by_contra! h
    exact hn ⟨p,hpp, by omega, by omega, by simpa only [Nat.mod_eq_of_lt hv] using h⟩
  have hmap : Set.MapsTo (fun p : ℕ => p+k/p) (↑S : Set ℕ) (↑(Finset.Icc (2*a) (2*a+T+2)) : Set ℕ) := by
    intro p hp
    obtain ⟨_, _, hl, hu⟩ := hP p hp
    exact Finset.mem_Icc.mpr (stamp_bounds ha ha' (by omega) hYa hu hHT)
  have hstrict {p q} (hp : p ∈ S) (hq : q ∈ S) (h : p < q) : (p+k/p : ℕ) < (q+k/q : ℕ) := by
    obtain ⟨_, ho, hl, _⟩ := hP p hp
    obtain ⟨_, ho', _, _⟩ := hP q hq
    exact stamp_lt ha' (by omega) (by omega) (hbad q hq)
  have hinj : Set.InjOn (fun p : ℕ => p+k/p) (↑S : Set ℕ) := by
    intro p hp q hq he
    rcases lt_trichotomy p q with h | h | h
    · exact ((hstrict hp hq h).ne he).elim
    · exact h
    · exact ((hstrict hq hp h).ne he.symm).elim
  have hc := Finset.card_le_card_of_injOn (fun p : ℕ => p+k/p) hmap hinj
  rw [Nat.card_Icc] at hc
  omega

private theorem prime_of_gcd {p t : ℕ} (h2 : 2 ≤ p) (hb : p ≤ t*t)
    (hg : p.gcd t.factorial = 1) : p.Prime := by
  by_contra hn
  have hm := Nat.minFac_prime (by omega : p ≠ 1)
  have hs := Nat.minFac_sq_le_self (by omega : 0 < p) hn
  have ht : p.minFac ≤ t := by
    by_contra! he
    have h := Nat.mul_self_lt_mul_self he
    nlinarith
  have h := Nat.dvd_gcd (Nat.minFac_dvd p) (Nat.dvd_factorial hm.pos ht)
  rw [hg] at h
  exact hm.not_dvd_one h

theorem primeTest_sound {p : ℕ} (ht : (fun p : ℕ => if p ≤ 17 then [3,5,7,11,13,17].contains p else if p ≤ 263 then p.gcd (Nat.factorial 17) == 1 else decide (p ≤ 263*263) && (p.gcd (Nat.factorial 263) == 1)) p = true) : p.Prime := by
  dsimp only at ht
  split at ht
  · simp only [List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with h|h|h|h|h|h <;> subst p <;> decide
  split at ht
  · exact prime_of_gcd (by omega) (t := 17) (by omega) (beq_iff_eq.mp ht)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
    exact prime_of_gcd (by omega) ht.1 ht.2

private theorem good_interval {p b k : ℕ} (hprime : p.Prime) (hodd : p ≠ 2)
    (hb : 2 ≤ b) (hbp : b ≤ p) (lo : b*(p-1) < k) (hi : k < b*p) : p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := by
  have hp : 0 < p := hprime.pos
  obtain ⟨c, hc⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
  have hpm : p-1+1=p := by omega
  have hmul := congrArg (fun x : ℕ => b*x) hpm
  have lower : c ≤ k/p := (Nat.le_div_iff_mul_le hp).2 (by nlinarith)
  have upper : k/p < b := (Nat.div_lt_iff_lt_mul hp).2 hi
  have hv : k/p = c := by omega
  have hmod := Nat.mod_add_div k p
  rw [hv] at hmod
  refine ⟨hprime,hodd,lt_of_lt_of_le hi (Nat.mul_le_mul_right p hbp),?_⟩
  rw [hv, Nat.mod_eq_of_lt (by omega : c < p)]
  nlinarith

theorem direct_range {rows : List (ℕ × ℕ)} {first last : ℕ}
    (h : (fun (first : ℕ) (rows : List (ℕ × ℕ)) (last : ℕ) =>
      rows.foldr (fun row rest first =>
        (fun p : ℕ => if p ≤ 17 then [3,5,7,11,13,17].contains p else if p ≤ 263 then p.gcd (Nat.factorial 17) == 1 else decide (p ≤ 263*263) && (p.gcd (Nat.factorial 263) == 1)) row.1 && decide (row.1 ≠ 2 ∧ 2 ≤ row.2 ∧ row.2 ≤ row.1 ∧
          row.2*(row.1-1)<first ∧ first<row.2*row.1) && rest (row.2*row.1))
        (fun first => decide (last ≤ first)) first) first rows last = true) {k : ℕ} (hlo : first ≤ k) (hhi : k < last) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := by
  induction rows generalizing first with
  | nil => simp at h; omega
  | cons row tail ih =>
    obtain ⟨p,b⟩ := row
    simp only [List.foldr_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases he : k < b*p
    · obtain ⟨⟨hp, ho, hb, hbp, hf, _⟩,_⟩ := h
      exact ⟨p, good_interval (primeTest_sound hp) ho hb hbp (by omega) he⟩
    · exact ih h.2 (by omega)

theorem good_of_band {v : (ℕ × ℕ × ℕ × ℕ × List ℕ)} (hv : (fun v : (ℕ × ℕ × ℕ × ℕ × List ℕ) => decide (v.2.2.1*v.2.2.1 ≤ v.1*v.2.2.2.1 ∧ v.2.2.2.1+3 < v.2.2.2.2.length ∧ v.2.2.2.2.IsChain (· < ·)) &&
  v.2.2.2.2.all (fun p => (fun p : ℕ => if p ≤ 17 then [3,5,7,11,13,17].contains p else if p ≤ 263 then p.gcd (Nat.factorial 17) == 1 else decide (p ≤ 263*263) && (p.gcd (Nat.factorial 263) == 1)) p && decide (p%2=1 ∧ v.2.1+2 ≤ p ∧ p ≤ v.1+v.2.2.1))) v = true) {k : ℕ}
    (hlo : v.1 ≤ k.sqrt) (hhi : k.sqrt ≤ v.2.1) : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hv
  have hnd : v.2.2.2.2.Nodup := (List.isChain_iff_pairwise.mp hv.1.2.2).imp (fun ab => ne_of_lt ab)
  have hc : v.2.2.2.1+3 < v.2.2.2.2.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd]
    exact hv.1.2.1
  apply shell (Nat.sqrt_le k) (Nat.lt_succ_sqrt k) hlo hhi hv.1.1 v.2.2.2.2.toFinset ?_ hc
  intro p hp
  have h := hv.2 p (List.mem_toFinset.mp hp)
  exact ⟨primeTest_sound h.1, h.2⟩

theorem band_range {vs : List (ℕ × ℕ × ℕ × ℕ × List ℕ)} {first last : ℕ}
    (h : (fun (first : ℕ) (rows : List (ℕ × ℕ × ℕ × ℕ × List ℕ)) (last : ℕ) =>
      rows.foldr (fun v rest first =>
        decide (v.1 ≤ first ∧ first ≤ v.2.1) && (fun v : (ℕ × ℕ × ℕ × ℕ × List ℕ) => decide (v.2.2.1*v.2.2.1 ≤ v.1*v.2.2.2.1 ∧ v.2.2.2.1+3 < v.2.2.2.2.length ∧ v.2.2.2.2.IsChain (· < ·)) &&
  v.2.2.2.2.all (fun p => (fun p : ℕ => if p ≤ 17 then [3,5,7,11,13,17].contains p else if p ≤ 263 then p.gcd (Nat.factorial 17) == 1 else decide (p ≤ 263*263) && (p.gcd (Nat.factorial 263) == 1)) p && decide (p%2=1 ∧ v.2.1+2 ≤ p ∧ p ≤ v.1+v.2.2.1))) v && rest (v.2.1+1))
        (fun first => decide (last ≤ first)) first) first vs last = true) {k : ℕ} (hlo : first ≤ k.sqrt) (hhi : k.sqrt < last) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := by
  induction vs generalizing first with
  | nil => simp at h; omega
  | cons v vs ih =>
    simp only [List.foldr_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hv : k.sqrt ≤ v.2.1
    · apply good_of_band (v := v) ?_ (le_trans h.1.1.1 hlo) hv
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using h.1.2
    · exact ih h.2 (by omega)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct0 {k : ℕ} (h1 : 193 ≤ k) (h2 : k < 1128) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(17,12),(19,11),(17,13),(23,10),(17,14),(19,13),(17,15),(19,14),(23,12),(17,17),(19,16),(31,10),(19,17),(47,7),(19,18),(29,12),(19,19),(31,12),(29,13),(23,17),(31,13),(23,18),(83,5),(47,9),(23,19),(37,12),(23,20),(31,15),(23,21),(31,16),(23,22),(29,18),(41,13),(29,19),(43,13),(47,12),(29,20),(37,16),(29,21),(31,20),(29,22),(31,21),(29,23),(31,22),(41,17),(31,23),(29,25),(31,24),(29,26),(31,25),(29,27),(31,26),(41,20),(29,29),(31,28),(37,24),(43,21),(31,30),(43,22),(37,26),(41,24),(37,27),(53,19),(41,25),(61,17),(149,7),(41,26),(47,23),(37,30),(47,24)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct1 {k : ℕ} (h1 : 1128 ≤ k) (h2 : k < 3245) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(41,28),(53,22),(41,29),(37,33),(43,29),(41,31),(37,35),(47,28),(43,31),(37,37),(41,34),(43,33),(41,35),(43,34),(53,28),(41,37),(43,36),(71,22),(41,39),(43,38),(59,28),(41,41),(43,40),(53,33),(47,38),(67,27),(43,43),(47,40),(53,36),(47,41),(53,37),(71,28),(47,43),(73,28),(61,34),(47,45),(67,32),(53,41),(47,47),(59,38),(53,43),(59,39),(53,44),(59,40),(53,45),(59,41),(79,31),(53,47),(109,23),(53,48),(83,31),(53,49),(73,36),(83,32),(53,51),(61,45),(73,38),(67,42),(73,39),(59,49),(61,48),(59,50),(61,49),(67,45),(71,43),(67,46),(59,53),(61,52),(67,48),(59,55)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct2 {k : ℕ} (h1 : 3245 ≤ k) (h2 : k < 6695) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(61,54),(71,47),(59,57),(61,56),(101,34),(67,52),(61,58),(73,49),(71,51),(61,60),(71,52),(83,45),(71,53),(67,57),(73,53),(71,55),(67,59),(83,48),(79,51),(67,61),(103,40),(73,57),(67,63),(79,54),(83,52),(89,49),(67,66),(71,63),(73,62),(79,58),(89,52),(71,66),(73,65),(149,32),(71,68),(73,67),(107,46),(83,60),(71,71),(73,70),(89,58),(79,66),(73,72),(83,64),(79,68),(89,61),(83,66),(79,70),(107,52),(79,71),(101,56),(89,64),(79,73),(97,60),(89,66),(79,75),(83,72),(97,62),(79,77),(83,74),(103,60),(79,79),(83,76),(101,63),(107,60),(83,78),(107,61),(89,74),(83,80),(103,65)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct3 {k : ℕ} (h1 : 6695 ≤ k) (h2 : k < 11690) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(89,76),(131,52),(83,83),(89,78),(103,68),(101,70),(89,80),(97,74),(113,64),(89,82),(97,76),(103,72),(89,84),(109,69),(101,75),(89,86),(103,75),(101,77),(97,81),(103,77),(131,61),(97,83),(137,59),(97,84),(139,59),(101,82),(107,78),(109,77),(107,79),(97,88),(109,79),(101,86),(103,85),(109,81),(127,70),(103,87),(113,80),(97,94),(107,86),(101,92),(109,86),(131,72),(101,94),(103,93),(127,76),(107,91),(109,90),(101,98),(103,97),(107,94),(109,93),(101,101),(103,100),(107,97),(109,96),(127,83),(113,94),(107,100),(109,99),(131,83),(113,97),(149,74),(107,104),(109,103),(127,89),(137,83),(107,107),(109,106),(113,103),(167,70)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct4 {k : ℕ} (h1 : 11690 ≤ k) (h2 : k < 18178) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(109,108),(113,105),(127,94),(179,67),(113,107),(131,93),(157,78),(137,90),(113,110),(139,90),(131,96),(113,112),(137,93),(131,98),(139,93),(137,95),(131,100),(223,59),(131,101),(127,105),(137,98),(157,86),(151,90),(173,79),(139,99),(127,109),(139,100),(137,102),(151,93),(131,108),(137,104),(127,113),(131,110),(151,96),(127,115),(179,82),(157,94),(127,117),(151,99),(149,101),(139,109),(151,101),(127,121),(131,118),(139,112),(163,96),(137,115),(127,125),(139,115),(149,108),(157,103),(139,117),(131,125),(163,101),(137,121),(149,112),(163,103),(131,129),(137,124),(139,123),(179,96),(149,116),(137,127),(139,126),(163,108),(167,106),(151,118),(137,131),(139,130),(149,122)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct5 {k : ℕ} (h1 : 18178 ≤ k) (h2 : k < 26167) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(151,121),(167,110),(137,135),(139,134),(151,124),(157,120),(149,127),(139,137),(157,122),(229,84),(179,108),(211,92),(149,131),(151,130),(181,109),(149,133),(157,127),(163,123),(149,135),(151,134),(239,85),(173,118),(163,126),(181,114),(157,132),(149,140),(151,139),(173,122),(167,127),(149,143),(151,142),(167,129),(157,138),(191,114),(149,147),(151,146),(163,136),(157,142),(193,116),(151,149),(157,144),(179,127),(173,132),(227,101),(167,138),(181,128),(163,143),(157,149),(173,136),(197,120),(193,123),(167,143),(157,153),(193,125),(181,134),(173,141),(179,137),(157,157),(163,152),(173,144),(167,150),(181,139),(193,131),(163,156),(167,153),(199,129),(191,135),(163,159),(167,156),(191,137)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct6 {k : ℕ} (h1 : 26167 ≤ k) (h2 : k < 36091) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(179,147),(193,137),(163,163),(167,160),(179,150),(173,156),(191,142),(227,120),(167,164),(181,152),(211,131),(197,141),(179,156),(199,141),(173,163),(223,127),(179,159),(181,158),(173,166),(199,145),(179,162),(193,151),(199,147),(173,170),(197,150),(179,166),(181,165),(191,157),(193,156),(179,169),(181,168),(191,160),(193,159),(211,146),(179,173),(181,172),(193,162),(251,125),(197,160),(179,177),(181,176),(293,109),(191,168),(199,162),(181,179),(229,142),(191,171),(193,170),(211,156),(191,173),(193,172),(211,158),(197,170),(199,169),(191,177),(193,176),(223,153),(197,174),(199,173),(191,181),(193,180),(197,177),(211,166),(191,184),(193,183),(197,180),(199,179),(277,129),(191,188),(193,187)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct7 {k : ℕ} (h1 : 36091 ≤ k) (h2 : k < 47802) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(197,184),(199,183),(223,164),(211,174),(229,161),(193,192),(197,189),(199,188),(211,178),(223,169),(241,157),(197,193),(199,192),(227,169),(281,137),(211,183),(197,197),(199,196),(229,171),(271,145),(223,177),(229,173),(241,165),(223,179),(211,190),(241,167),(227,178),(223,182),(229,178),(211,194),(227,181),(223,185),(251,165),(239,174),(211,198),(233,180),(263,160),(269,157),(211,201),(229,186),(283,151),(227,189),(229,188),(211,205),(251,173),(227,192),(229,191),(223,197),(241,183),(211,210),(227,196),(229,195),(241,186),(271,166),(227,199),(229,198),(263,173),(233,196),(227,202),(241,191),(251,184),(223,208),(263,177),(229,204),(271,173),(233,202),(223,212),(227,209),(229,208),(257,186)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct8 {k : ℕ} (h1 : 47802 ≤ k) (h2 : k < 61279) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(233,206),(223,216),(227,213),(229,212),(233,209),(223,219),(227,216),(229,215),(241,205),(277,179),(269,185),(239,209),(227,221),(229,220),(233,217),(317,160),(239,213),(241,212),(227,226),(229,225),(233,222),(269,193),(239,218),(241,217),(251,209),(233,226),(271,195),(239,222),(241,221),(251,213),(271,198),(233,231),(277,195),(241,225),(353,154),(317,172),(239,229),(241,228),(269,205),(359,154),(263,211),(239,233),(241,232),(271,207),(257,219),(269,210),(313,181),(239,238),(241,237),(263,218),(251,229),(337,171),(241,240),(307,189),(251,232),(263,222),(257,228),(271,217),(281,210),(251,236),(269,221),(257,232),(277,216),(311,193),(251,240),(271,223),(257,236),(283,215),(269,227),(263,233)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct9 {k : ℕ} (h1 : 61279 ≤ k) (h2 : k < 76729) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(251,245),(283,218),(311,199),(281,221),(263,237),(283,221),(251,250),(257,245),(277,228),(263,241),(293,217),(281,227),(269,238),(257,250),(293,220),(263,246),(281,231),(313,208),(271,241),(257,255),(281,234),(283,233),(269,246),(271,245),(281,237),(293,228),(277,242),(269,250),(271,249),(293,231),(283,240),(277,246),(263,260),(269,255),(271,254),(283,244),(277,250),(293,237),(281,248),(269,260),(271,259),(317,222),(293,241),(281,252),(283,251),(269,265),(271,264),(293,245),(277,260),(281,257),(307,236),(293,248),(271,269),(277,264),(281,261),(283,260),(353,209),(349,212),(277,268),(281,265),(293,255),(311,241),(337,223),(373,202),(293,258),(283,268),(317,240),(419,182),(293,261),(277,277)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct10 {k : ℕ} (h1 : 76729 ≤ k) (h2 : k < 93096) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(281,274),(283,273),(349,222),(307,253),(337,231),(281,278),(283,277),(317,248),(293,269),(397,199),(317,250),(283,281),(359,222),(311,257),(347,231),(367,219),(293,275),(359,225),(349,232),(347,234),(293,278),(313,261),(353,232),(311,264),(293,281),(307,269),(431,192),(353,235),(293,284),(331,252),(311,269),(313,268),(307,274),(293,288),(317,267),(311,273),(313,272),(347,246),(337,254),(293,293),(313,275),(337,256),(317,273),(311,279),(313,278),(349,250),(307,285),(331,265),(337,261),(347,254),(307,288),(349,254),(313,284),(389,229),(307,291),(311,288),(313,287),(349,258),(367,246),(307,295),(311,292),(313,291),(331,276),(317,289),(401,229),(307,300),(311,297),(313,296),(317,293),(431,216)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct11 {k : ℕ} (h1 : 93096 ≤ k) (h2 : k < 111734) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(337,277),(307,305),(311,302),(313,301),(317,298),(347,273),(331,287),(449,212),(311,307),(313,306),(317,303),(349,276),(359,269),(347,279),(353,275),(313,311),(317,308),(433,226),(353,278),(337,292),(401,246),(317,312),(431,230),(337,295),(379,263),(331,302),(409,245),(317,317),(337,299),(419,241),(359,282),(383,265),(337,302),(397,257),(331,309),(337,304),(353,291),(349,295),(439,235),(337,307),(347,299),(397,262),(331,315),(353,296),(409,256),(367,286),(331,318),(353,299),(347,305),(349,304),(409,260),(359,297),(331,323),(337,318),(373,288),(359,300),(347,311),(331,327),(349,311),(337,323),(359,304),(353,310),(389,282),(347,317),(379,291),(359,308),(337,329),(373,298),(379,294),(347,322)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct12 {k : ℕ} (h1 : 111734 ≤ k) (h2 : k < 132650) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(349,321),(367,306),(353,319),(337,335),(397,285),(347,327),(349,326),(353,323),(401,285),(359,319),(349,329),(401,287),(421,274),(373,310),(389,298),(347,335),(349,334),(353,331),(373,314),(367,320),(359,328),(347,340),(349,339),(373,318),(367,324),(359,332),(383,312),(379,316),(347,346),(349,345),(353,342),(383,316),(359,338),(379,321),(373,327),(397,308),(367,334),(353,348),(359,343),(373,331),(383,323),(367,338),(409,304),(421,296),(359,348),(383,327),(367,342),(379,332),(419,301),(373,339),(383,331),(359,354),(419,304),(367,348),(409,313),(401,320),(397,324),(443,291),(379,341),(367,353),(383,339),(373,349),(409,319),(433,302),(389,337),(397,331),(367,359),(373,354),(401,330),(379,350)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct13 {k : ℕ} (h1 : 132650 ≤ k) (h2 : k < 155105) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(433,307),(419,318),(367,364),(373,359),(389,345),(379,355),(383,352),(401,337),(373,363),(379,358),(421,323),(499,273),(397,344),(373,367),(379,362),(383,359),(409,337),(397,348),(389,356),(431,322),(373,373),(379,368),(383,365),(397,353),(443,317),(401,351),(421,335),(379,373),(383,370),(419,339),(389,366),(439,325),(397,360),(379,378),(383,375),(409,352),(389,371),(433,334),(463,313),(431,337),(401,363),(383,381),(389,376),(431,340),(397,370),(409,360),(401,368),(419,353),(389,381),(457,325),(409,364),(401,372),(421,355),(389,385),(409,367),(397,379),(401,376),(433,349),(439,345),(467,325),(419,363),(397,384),(401,381),(449,341),(431,356),(409,376),(467,330),(461,335),(401,386),(463,335)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct14 {k : ℕ} (h1 : 155105 ≤ k) (h2 : k < 179990) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(419,371),(409,381),(421,371),(463,338),(443,354),(397,396),(401,393),(419,377),(421,376),(431,368),(449,354),(463,344),(419,381),(401,399),(431,372),(439,366),(503,320),(419,385),(421,384),(439,369),(409,397),(457,356),(443,368),(419,390),(431,380),(461,356),(409,402),(449,367),(487,339),(421,393),(467,355),(449,370),(409,407),(439,380),(419,399),(421,398),(449,374),(461,365),(457,369),(439,385),(431,393),(433,392),(419,406),(421,405),(463,369),(439,390),(431,398),(433,397),(463,372),(419,412),(421,411),(439,395),(449,387),(431,404),(433,403),(479,365),(461,380),(419,419),(421,418),(443,398),(431,410),(433,409),(467,380),(449,396),(509,350),(443,403),(461,388),(433,414),(463,388),(439,410)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct15 {k : ℕ} (h1 : 179990 ≤ k) (h2 : k < 206711) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(443,407),(499,362),(431,420),(433,419),(439,414),(467,390),(443,412),(463,395),(457,401),(449,409),(431,427),(433,426),(439,421),(463,400),(443,419),(457,407),(449,415),(461,405),(491,381),(433,433),(439,428),(457,412),(467,404),(491,385),(463,409),(479,396),(439,433),(443,430),(461,414),(449,426),(463,414),(479,401),(467,412),(521,370),(461,419),(443,437),(463,419),(449,433),(487,400),(467,418),(457,428),(509,385),(461,426),(463,425),(449,439),(509,388),(457,433),(461,430),(463,429),(467,426),(449,444),(479,417),(457,438),(509,394),(463,434),(491,410),(503,401),(487,415),(457,443),(461,440),(463,439),(467,436),(523,390),(457,447),(461,444),(463,443),(487,422),(467,441),(521,396),(491,421)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct16 {k : ℕ} (h1 : 206711 ≤ k) (h2 : k < 235054) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(499,415),(457,454),(461,451),(463,450),(467,447),(491,426),(499,420),(521,403),(487,432),(523,403),(547,386),(461,459),(463,458),(467,455),(523,407),(503,424),(479,446),(601,356),(463,463),(467,460),(487,442),(563,383),(491,440),(571,379),(509,426),(487,446),(467,466),(541,403),(479,456),(521,420),(487,450),(499,440),(491,448),(509,433),(479,461),(523,423),(487,455),(521,426),(541,411),(479,465),(587,380),(509,439),(491,456),(503,446),(619,363),(479,470),(499,452),(487,464),(491,461),(557,407),(617,368),(479,475),(487,468),(503,454),(491,466),(521,440),(523,439),(499,461),(503,458),(487,474),(491,471),(523,443),(509,456),(499,466),(503,463),(569,410),(487,480),(491,477),(509,461),(557,422)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct17 {k : ℕ} (h1 : 235054 ≤ k) (h2 : k < 265189) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(521,452),(503,469),(547,432),(557,425),(487,487),(491,484),(521,457),(499,478),(503,475),(563,425),(509,471),(521,461),(491,490),(499,483),(503,480),(587,412),(509,476),(571,425),(587,414),(503,484),(521,468),(523,467),(569,430),(557,440),(499,492),(503,489),(521,473),(509,485),(557,444),(563,440),(577,430),(521,477),(499,499),(503,496),(541,462),(509,492),(593,423),(571,440),(563,447),(541,466),(607,416),(503,503),(509,498),(563,451),(547,465),(541,471),(521,490),(523,489),(577,444),(569,451),(509,505),(541,476),(577,447),(523,494),(599,432),(607,427),(557,466),(619,420),(523,498),(547,477),(541,483),(569,460),(593,442),(521,504),(523,503),(563,468),(593,445),(643,411),(547,484),(521,509)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct18 {k : ℕ} (h1 : 265189 ≤ k) (h2 : k < 297021) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(523,508),(541,492),(577,462),(547,488),(557,480),(571,469),(523,513),(601,447),(547,492),(557,484),(577,468),(541,500),(521,520),(523,519),(547,497),(601,453),(541,504),(569,480),(587,466),(593,462),(607,452),(541,508),(563,489),(593,465),(547,505),(673,411),(587,472),(577,481),(673,413),(547,509),(601,464),(593,471),(571,490),(541,518),(557,504),(587,479),(569,495),(571,494),(601,470),(557,508),(647,438),(547,519),(571,498),(619,460),(557,512),(541,528),(547,523),(563,509),(587,489),(599,480),(557,517),(631,457),(541,534),(563,514),(547,530),(619,469),(577,504),(557,523),(571,511),(563,519),(541,541),(547,536),(577,509),(569,517),(587,502),(601,491),(563,525),(577,513),(593,500),(547,543)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct19 {k : ℕ} (h1 : 297021 ≤ k) (h2 : k < 331846) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(601,495),(557,535),(631,473),(563,531),(577,519),(587,511),(569,528),(571,527),(557,541),(593,509),(577,524),(613,494),(619,490),(571,532),(593,513),(601,507),(557,548),(563,543),(569,538),(571,537),(613,501),(587,524),(577,534),(557,554),(563,549),(607,510),(569,545),(571,544),(587,530),(617,505),(599,521),(601,520),(563,556),(569,551),(571,550),(599,525),(601,524),(653,483),(617,512),(563,562),(569,557),(571,556),(661,481),(593,537),(643,496),(619,516),(587,545),(701,457),(569,564),(571,563),(593,543),(577,559),(613,527),(607,533),(599,541),(587,553),(601,541),(641,508),(593,550),(643,508),(607,539),(577,568),(599,548),(631,521),(587,561),(613,538),(593,557),(607,545),(617,537),(599,554)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct20 {k : ℕ} (h1 : 331846 ≤ k) (h2 : k < 368924) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(601,553),(577,577),(613,544),(587,569),(647,517),(593,565),(619,542),(599,561),(601,560),(631,534),(587,575),(593,570),(677,500),(599,566),(601,565),(659,516),(617,552),(607,562),(641,533),(587,583),(593,578),(613,560),(599,574),(601,573),(617,559),(619,558),(643,538),(631,549),(613,566),(593,586),(599,581),(601,580),(619,564),(607,576),(647,541),(701,500),(593,592),(599,587),(601,586),(631,559),(607,582),(719,492),(613,578),(727,488),(619,574),(647,550),(599,595),(601,594),(607,589),(673,532),(613,585),(653,550),(617,583),(619,582),(673,536),(601,601),(607,596),(647,560),(613,592),(631,576),(617,590),(619,589),(659,554),(677,540),(673,544),(641,572),(607,605),(613,600),(617,597),(619,596)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct21 {k : ℕ} (h1 : 368924 ≤ k) (h2 : k < 407068) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(647,571),(641,577),(631,587),(653,568),(613,606),(617,603),(619,602),(691,540),(641,583),(643,582),(631,594),(719,522),(709,530),(617,610),(619,609),(641,589),(661,572),(709,534),(647,586),(719,528),(641,593),(617,617),(619,616),(677,564),(631,606),(673,569),(701,547),(653,588),(643,598),(739,521),(647,596),(659,586),(661,585),(677,572),(641,605),(643,604),(761,511),(743,524),(653,597),(641,609),(643,608),(659,594),(677,579),(691,568),(673,584),(641,614),(643,613),(659,599),(647,611),(733,540),(673,589),(727,546),(631,630),(677,588),(643,620),(661,604),(647,618),(673,595),(701,572),(691,581),(709,567),(661,609),(643,627),(647,624),(757,534),(719,563),(733,553),(659,616),(661,615),(683,596)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct22 {k : ℕ} (h1 : 407068 ≤ k) (h2 : k < 446889) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(641,636),(643,635),(677,604),(653,627),(659,622),(683,601),(761,540),(643,640),(647,637),(719,574),(761,543),(661,626),(677,612),(733,566),(647,642),(653,637),(659,632),(661,631),(709,589),(691,605),(647,647),(653,642),(659,637),(661,636),(727,579),(691,610),(683,618),(673,628),(757,559),(653,649),(659,644),(661,643),(809,526),(709,601),(673,634),(743,575),(719,595),(691,620),(701,612),(661,650),(743,579),(757,569),(787,548),(691,625),(743,582),(683,634),(659,658),(661,657),(751,579),(673,647),(709,615),(677,645),(719,608),(809,541),(739,593),(701,626),(673,653),(677,650),(761,579),(683,646),(809,546),(701,631),(691,641),(673,659),(677,656),(787,565),(709,628),(701,636),(733,609),(823,543)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct23 {k : ℕ} (h1 : 446889 ≤ k) (h2 : k < 489298) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(673,665),(677,662),(709,633),(683,658),(701,642),(751,600),(691,653),(743,608),(709,638),(719,630),(677,670),(683,665),(743,612),(691,659),(739,617),(709,644),(809,565),(743,616),(677,677),(683,672),(733,627),(691,666),(709,650),(743,621),(787,587),(757,611),(727,637),(683,679),(709,655),(691,673),(751,620),(733,636),(769,607),(719,650),(709,660),(739,634),(691,679),(827,568),(701,671),(719,655),(773,610),(709,666),(733,645),(761,622),(691,686),(757,627),(701,678),(739,644),(809,589),(709,673),(743,643),(727,658),(809,592),(719,667),(761,631),(773,622),(709,679),(727,663),(739,653),(719,672),(733,660),(751,645),(811,598),(727,668),(739,658),(821,593),(719,678),(823,593),(809,604),(701,698)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct24 {k : ℕ} (h1 : 489298 ≤ k) (h2 : k < 533624) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(739,663),(709,692),(751,654),(719,684),(773,637),(823,599),(727,679),(787,628),(709,698),(733,676),(719,690),(821,605),(757,657),(727,685),(773,645),(761,656),(769,650),(709,706),(719,697),(739,679),(751,669),(727,692),(743,678),(733,688),(757,667),(773,654),(739,685),(719,705),(769,660),(743,684),(727,700),(757,673),(797,640),(751,680),(809,632),(719,712),(811,632),(829,619),(733,701),(769,669),(739,697),(797,647),(757,682),(719,719),(727,712),(761,681),(821,632),(739,703),(823,632),(757,688),(829,629),(761,686),(727,719),(733,714),(739,709),(757,693),(743,707),(823,639),(787,669),(751,702),(727,726),(733,721),(757,699),(743,713),(761,697),(773,687),(751,708),(809,658),(757,704),(733,728)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct25 {k : ℕ} (h1 : 533624 ≤ k) (h2 : k < 580447) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(739,723),(761,703),(743,721),(751,714),(863,622),(757,710),(761,707),(739,729),(743,726),(827,653),(751,720),(769,704),(809,670),(821,661),(761,714),(823,661),(829,657),(739,738),(743,735),(769,711),(751,729),(823,666),(757,725),(761,722),(809,680),(827,666),(823,670),(839,658),(751,736),(757,731),(787,704),(761,729),(829,670),(877,634),(821,678),(773,721),(823,678),(757,738),(761,735),(821,682),(769,729),(829,677),(787,714),(751,749),(757,744),(761,741),(823,686),(811,697),(769,736),(797,711),(773,734),(839,677),(823,691),(811,702),(757,753),(761,750),(797,717),(787,727),(829,691),(773,742),(857,670),(883,651),(821,701),(797,723),(823,701),(809,714),(761,760),(769,753),(773,750),(821,707)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct26 {k : ℕ} (h1 : 580447 ≤ k) (h2 : k < 628065) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(829,701),(797,730),(809,720),(787,741),(827,706),(821,712),(769,761),(773,758),(797,736),(883,665),(787,747),(829,710),(859,686),(887,665),(769,768),(773,765),(811,730),(829,715),(887,669),(839,708),(881,675),(797,747),(811,735),(773,772),(839,712),(787,760),(853,702),(809,741),(821,731),(823,730),(887,678),(827,728),(809,745),(821,735),(797,758),(853,709),(827,732),(877,691),(787,771),(811,749),(797,763),(881,691),(827,737),(857,712),(821,744),(787,777),(877,698),(797,769),(827,742),(829,741),(839,733),(877,702),(811,760),(863,715),(787,785),(859,720),(839,738),(883,702),(823,754),(811,766),(859,724),(829,751),(797,782),(821,760),(823,759),(809,773),(811,772),(911,688),(863,727),(821,765)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct27 {k : ℕ} (h1 : 628065 ≤ k) (h2 : k < 679027) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(797,789),(823,765),(809,779),(811,778),(829,762),(941,672),(859,737),(821,772),(823,771),(797,797),(827,769),(809,787),(811,786),(937,681),(821,778),(823,777),(857,747),(827,775),(829,774),(809,794),(811,793),(863,746),(821,785),(823,784),(859,752),(827,782),(829,781),(883,734),(809,802),(811,801),(907,717),(839,776),(823,792),(853,765),(827,790),(829,789),(857,764),(881,744),(919,714),(839,783),(811,811),(863,763),(821,803),(823,802),(827,799),(829,798),(859,771),(907,731),(839,791),(887,749),(857,776),(821,811),(823,810),(827,807),(829,806),(929,720),(853,785),(839,799),(883,760),(919,731),(821,819),(823,818),(827,815),(829,814),(853,792),(839,806),(967,700),(953,711),(863,786),(883,769)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct28 {k : ℕ} (h1 : 679027 ≤ k) (h2 : k < 731533) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(827,822),(829,821),(857,795),(839,813),(919,743),(863,792),(983,696),(853,803),(907,756),(857,801),(829,829),(839,820),(883,780),(863,799),(929,743),(887,779),(853,811),(881,786),(859,807),(907,765),(877,792),(967,719),(853,816),(929,750),(859,812),(941,742),(863,810),(839,834),(929,754),(919,763),(853,823),(937,750),(859,819),(887,794),(863,817),(919,768),(881,802),(883,801),(853,830),(911,778),(859,826),(947,750),(881,807),(883,806),(911,782),(887,804),(853,837),(877,815),(859,833),(863,830),(941,762),(937,766),(967,743),(907,793),(877,821),(853,845),(857,842),(859,841),(863,838),(997,726),(941,770),(877,827),(911,797),(881,825),(853,853),(857,850),(859,849),(863,846),(887,824),(911,803)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct29 {k : ℕ} (h1 : 731533 ≤ k) (h2 : k < 786011) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(877,835),(941,779),(883,831),(857,857),(859,856),(863,853),(967,762),(929,794),(877,842),(907,815),(881,840),(883,839),(919,807),(887,837),(929,800),(937,794),(863,863),(907,822),(877,851),(881,848),(883,847),(937,799),(967,775),(907,827),(919,817),(877,857),(881,854),(883,853),(983,767),(1031,732),(971,778),(929,814),(983,770),(877,864),(881,861),(883,860),(887,857),(907,839),(937,813),(911,837),(947,806),(941,812),(1009,758),(877,873),(881,870),(883,869),(887,866),(977,787),(1033,745),(937,822),(919,839),(907,851),(983,786),(883,876),(887,873),(1039,746),(937,828),(929,836),(919,846),(1039,749),(1009,772),(971,803),(887,880),(967,808),(1021,766),(941,832),(907,864),(983,798),(911,862),(1009,779)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct30 {k : ℕ} (h1 : 786011 ≤ k) (h2 : k < 842603) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(887,887),(919,857),(983,802),(1013,779),(907,871),(937,844),(911,869),(929,853),(941,843),(919,864),(953,834),(937,849),(907,878),(911,875),(941,848),(991,806),(953,839),(1013,790),(971,825),(907,884),(967,830),(953,843),(1009,797),(919,876),(937,860),(1021,790),(941,858),(929,870),(907,892),(911,889),(991,818),(919,883),(967,840),(941,864),(953,854),(929,877),(997,818),(947,862),(907,901),(911,898),(937,874),(919,892),(941,872),(1009,814),(929,885),(947,869),(983,838),(977,844),(1019,810),(911,907),(941,879),(919,901),(967,857),(929,893),(1009,823),(1039,800),(937,888),(953,874),(941,886),(983,849),(919,909),(947,883),(929,901),(1033,811),(953,880),(983,854),(967,869),(947,888),(919,916),(929,907)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct31 {k : ℕ} (h1 : 842603 ≤ k) (h2 : k < 901094) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(983,858),(937,901),(941,898),(1019,830),(947,894),(997,850),(991,856),(953,891),(929,915),(1019,835),(937,909),(941,906),(1087,785),(947,902),(1013,844),(967,885),(1009,849),(929,923),(937,916),(983,874),(947,908),(977,881),(967,891),(953,905),(971,889),(983,879),(937,923),(941,920),(977,887),(947,916),(1019,852),(971,895),(1021,852),(1087,801),(977,892),(937,931),(941,928),(947,923),(971,901),(1069,819),(977,897),(1091,804),(967,908),(941,934),(983,895),(947,930),(953,925),(997,885),(977,904),(991,892),(967,915),(983,901),(1019,870),(1013,876),(947,938),(953,933),(977,911),(991,899),(1049,850),(967,923),(1021,875),(971,921),(1063,842),(977,917),(947,947),(953,942),(1013,887),(983,915),(997,903),(1031,874)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct32 {k : ℕ} (h1 : 901094 ≤ k) (h2 : k < 961374) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1039,868),(977,924),(1013,892),(953,949),(997,908),(1093,829),(1033,878),(971,935),(991,917),(977,931),(1031,883),(997,914),(1033,883),(1019,896),(1109,824),(991,923),(1031,888),(977,938),(1033,888),(1009,910),(983,935),(1049,877),(1013,909),(991,930),(967,954),(971,951),(1009,916),(1087,851),(1013,914),(1033,897),(967,959),(971,956),(997,932),(977,952),(1031,903),(983,948),(1109,841),(991,942),(1019,917),(1009,927),(1021,917),(997,940),(1013,926),(971,967),(977,962),(1063,885),(1019,924),(991,951),(1093,863),(1033,914),(1063,889),(1051,900),(977,969),(983,964),(1031,920),(991,958),(1013,938),(997,954),(1093,871),(1117,853),(1031,925),(977,977),(983,972),(991,965),(997,960),(1039,922),(1019,941),(1021,940),(1051,914),(983,978)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct33 {k : ℕ} (h1 : 961374 ≤ k) (h2 : k < 1024598) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(991,971),(1039,927),(997,967),(1031,936),(1051,919),(1091,886),(1069,905),(1039,932),(991,978),(1019,952),(1033,940),(1061,916),(1009,964),(1039,937),(1129,863),(1019,957),(991,985),(997,980),(1063,920),(1039,942),(1097,893),(1013,968),(1031,952),(1069,919),(1019,965),(1021,964),(1097,898),(997,989),(1051,939),(1009,979),(1031,959),(1013,977),(1033,959),(1019,973),(1021,972),(1039,956),(1069,930),(1091,912),(1031,966),(1009,988),(1013,985),(1049,952),(1021,979),(1097,912),(1063,942),(1087,922),(1031,973),(1033,972),(1009,996),(1013,993),(1051,958),(1019,989),(1021,988),(1123,899),(1129,895),(1031,981),(1069,947),(1061,955),(1051,965),(1063,955),(1039,978),(1009,1008),(1013,1005),(1019,1000),(1021,999),(1069,955),(1087,940),(1031,992),(1033,991),(1097,934)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct34 {k : ℕ} (h1 : 1024598 ≤ k) (h2 : k < 1089764) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1039,987),(1093,939),(1087,945),(1019,1009),(1021,1008),(1049,982),(1051,981),(1031,1001),(1033,1000),(1039,995),(1109,933),(1097,944),(1091,950),(1019,1018),(1021,1017),(1031,1008),(1033,1007),(1039,1002),(1091,955),(1151,906),(1049,995),(1051,994),(1163,899),(1031,1015),(1033,1014),(1039,1009),(1061,989),(1063,988),(1103,953),(1049,1003),(1051,1002),(1069,986),(1091,967),(1093,966),(1031,1025),(1033,1024),(1063,996),(1097,966),(1193,889),(1049,1012),(1051,1011),(1093,973),(1103,965),(1163,916),(1061,1005),(1063,1004),(1151,928),(1039,1029),(1117,958),(1049,1021),(1051,1020),(1087,987),(1061,1012),(1063,1011),(1093,984),(1069,1007),(1039,1037),(1049,1028),(1051,1027),(1123,962),(1109,975),(1061,1020),(1063,1019),(1069,1014),(1097,989),(1087,999),(1117,973),(1049,1037),(1051,1036),(1103,988)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct35 {k : ℕ} (h1 : 1089764 ≤ k) (h2 : k < 1156460) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1061,1028),(1063,1027),(1097,996),(1069,1023),(1187,922),(1091,1004),(1093,1003),(1049,1046),(1051,1045),(1151,955),(1063,1035),(1087,1013),(1069,1031),(1181,934),(1093,1010),(1163,950),(1117,990),(1109,998),(1061,1044),(1063,1043),(1069,1038),(1091,1018),(1093,1017),(1117,996),(1097,1015),(1129,987),(1087,1026),(1103,1012),(1061,1053),(1063,1052),(1069,1047),(1109,1010),(1217,921),(1087,1032),(1091,1029),(1093,1028),(1061,1060),(1063,1059),(1069,1054),(1097,1028),(1123,1005),(1103,1024),(1087,1040),(1151,983),(1091,1038),(1093,1037),(1237,917),(1069,1062),(1163,977),(1103,1031),(1193,954),(1213,939),(1093,1043),(1123,1016),(1097,1041),(1151,993),(1213,943),(1129,1014),(1201,954),(1087,1055),(1109,1035),(1123,1023),(1093,1052),(1097,1049),(1237,931),(1103,1045),(1213,951),(1109,1041),(1087,1063),(1091,1060)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct36 {k : ℕ} (h1 : 1156460 ≤ k) (h2 : k < 1225211) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1093,1059),(1097,1056),(1117,1038),(1103,1052),(1151,1009),(1123,1035),(1109,1049),(1087,1071),(1091,1068),(1093,1067),(1117,1045),(1097,1065),(1187,985),(1123,1042),(1163,1007),(1217,963),(1087,1079),(1091,1076),(1093,1075),(1097,1072),(1163,1012),(1103,1068),(1109,1063),(1181,999),(1153,1024),(1163,1016),(1091,1084),(1093,1083),(1123,1055),(1103,1075),(1231,964),(1109,1071),(1153,1031),(1163,1023),(1117,1066),(1181,1009),(1123,1062),(1213,984),(1093,1093),(1097,1090),(1103,1085),(1109,1080),(1181,1015),(1117,1074),(1151,1043),(1231,976),(1187,1013),(1181,1019),(1103,1092),(1109,1087),(1231,980),(1151,1049),(1187,1018),(1213,997),(1129,1072),(1279,947),(1103,1099),(1109,1094),(1213,1001),(1117,1088),(1231,988),(1237,984),(1129,1079),(1229,992),(1171,1042),(1151,1061),(1153,1060),(1109,1103),(1117,1096),(1193,1027)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct37 {k : ℕ} (h1 : 1225211 ≤ k) (h2 : k < 1295017) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1201,1021),(1129,1087),(1181,1040),(1163,1057),(1249,985),(1213,1015),(1187,1038),(1117,1104),(1123,1099),(1229,1005),(1151,1074),(1153,1073),(1283,965),(1249,992),(1181,1050),(1117,1111),(1123,1106),(1151,1080),(1129,1102),(1187,1049),(1181,1055),(1213,1028),(1163,1073),(1151,1085),(1123,1113),(1129,1108),(1231,1017),(1171,1070),(1259,996),(1163,1079),(1187,1058),(1151,1092),(1153,1091),(1181,1066),(1123,1122),(1129,1117),(1217,1037),(1163,1086),(1249,1012),(1151,1099),(1153,1098),(1223,1036),(1231,1030),(1129,1124),(1213,1047),(1289,986),(1181,1077),(1151,1106),(1153,1105),(1301,980),(1187,1075),(1277,1000),(1223,1045),(1217,1051),(1193,1073),(1171,1094),(1153,1112),(1187,1081),(1223,1050),(1231,1044),(1181,1089),(1213,1061),(1229,1048),(1153,1118),(1231,1048),(1201,1075),(1163,1111),(1279,1011),(1249,1036),(1187,1091)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct38 {k : ℕ} (h1 : 1295017 ≤ k) (h2 : k < 1367728) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1151,1126),(1153,1125),(1259,1031),(1181,1100),(1237,1051),(1301,1000),(1289,1010),(1151,1132),(1153,1131),(1237,1055),(1231,1061),(1163,1124),(1217,1075),(1187,1103),(1171,1119),(1229,1067),(1193,1100),(1151,1141),(1153,1140),(1163,1131),(1187,1109),(1237,1065),(1231,1071),(1193,1106),(1217,1085),(1181,1119),(1303,1015),(1151,1150),(1153,1149),(1187,1117),(1163,1141),(1171,1134),(1193,1114),(1181,1126),(1259,1057),(1223,1089),(1289,1034),(1163,1147),(1217,1097),(1193,1120),(1171,1142),(1259,1063),(1231,1088),(1181,1135),(1201,1117),(1187,1131),(1217,1104),(1237,1087),(1193,1128),(1163,1158),(1171,1151),(1213,1112),(1201,1124),(1181,1144),(1217,1111),(1187,1140),(1231,1100),(1249,1085),(1277,1062),(1259,1078),(1171,1160),(1217,1117),(1181,1152),(1187,1147),(1283,1062),(1223,1115),(1279,1067),(1297,1053),(1201,1138),(1171,1168)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct39 {k : ℕ} (h1 : 1367728 ≤ k) (h2 : k < 1442846) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1181,1159),(1279,1071),(1193,1149),(1237,1109),(1283,1070),(1201,1144),(1231,1117),(1259,1093),(1223,1126),(1181,1167),(1187,1162),(1213,1138),(1193,1158),(1217,1136),(1201,1152),(1223,1132),(1237,1120),(1181,1174),(1187,1169),(1259,1103),(1217,1142),(1289,1079),(1201,1159),(1223,1139),(1237,1127),(1249,1117),(1259,1109),(1213,1152),(1231,1136),(1217,1150),(1187,1180),(1193,1175),(1223,1147),(1249,1124),(1283,1095),(1277,1101),(1213,1160),(1279,1101),(1217,1158),(1301,1084),(1237,1141),(1223,1155),(1193,1185),(1201,1178),(1279,1107),(1231,1151),(1213,1169),(1217,1166),(1249,1137),(1223,1162),(1193,1192),(1201,1185),(1231,1157),(1213,1175),(1249,1142),(1237,1154),(1307,1093),(1223,1169),(1289,1110),(1297,1104),(1229,1166),(1231,1165),(1201,1195),(1279,1123),(1213,1185),(1217,1182),(1283,1122),(1223,1178),(1277,1129),(1229,1174)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct40 {k : ℕ} (h1 : 1442846 ≤ k) (h2 : k < 1520601) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1231,1173),(1249,1157),(1297,1115),(1237,1170),(1213,1194),(1217,1191),(1223,1186),(1259,1153),(1289,1127),(1249,1164),(1291,1127),(1307,1114),(1321,1103),(1279,1140),(1213,1203),(1217,1200),(1223,1195),(1283,1140),(1229,1191),(1231,1190),(1277,1148),(1237,1186),(1297,1132),(1259,1167),(1307,1125),(1301,1131),(1249,1179),(1223,1205),(1229,1200),(1231,1199),(1237,1194),(1259,1174),(1367,1082),(1303,1136),(1277,1160),(1279,1159),(1223,1213),(1229,1208),(1231,1207),(1259,1181),(1409,1056),(1277,1166),(1321,1128),(1291,1155),(1301,1147),(1223,1221),(1229,1216),(1231,1215),(1237,1210),(1277,1173),(1279,1172),(1291,1162),(1249,1202),(1283,1171),(1327,1133),(1321,1139),(1259,1196),(1277,1180),(1229,1227),(1231,1226),(1237,1221),(1303,1160),(1283,1179),(1249,1212),(1297,1168),(1367,1109),(1289,1177),(1259,1206),(1291,1177),(1303,1167)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct41 {k : ℕ} (h1 : 1520601 ≤ k) (h2 : k < 1599649) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1283,1186),(1237,1231),(1249,1220),(1289,1183),(1277,1195),(1259,1213),(1373,1113),(1283,1192),(1307,1171),(1409,1087),(1327,1155),(1367,1122),(1277,1202),(1279,1201),(1259,1221),(1307,1177),(1327,1160),(1301,1184),(1291,1194),(1277,1208),(1249,1236),(1307,1182),(1259,1228),(1319,1173),(1423,1088),(1289,1202),(1291,1201),(1277,1215),(1307,1188),(1297,1198),(1249,1245),(1321,1178),(1301,1197),(1289,1209),(1291,1208),(1307,1194),(1277,1223),(1279,1222),(1321,1184),(1283,1220),(1301,1204),(1303,1203),(1259,1246),(1291,1216),(1307,1202),(1373,1145),(1277,1232),(1279,1231),(1283,1228),(1303,1210),(1327,1189),(1289,1225),(1291,1224),(1259,1256),(1423,1112),(1277,1240),(1279,1239),(1373,1155),(1361,1166),(1319,1204),(1291,1231),(1447,1099),(1297,1227),(1367,1165),(1327,1201),(1277,1249),(1279,1248),(1283,1245),(1307,1223),(1289,1241)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct42 {k : ℕ} (h1 : 1599649 ≤ k) (h2 : k < 1682109) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1291,1240),(1381,1160),(1297,1236),(1301,1233),(1303,1232),(1277,1258),(1279,1257),(1307,1231),(1283,1255),(1289,1250),(1291,1249),(1327,1216),(1297,1245),(1399,1155),(1303,1241),(1321,1225),(1307,1239),(1277,1269),(1279,1268),(1283,1265),(1289,1260),(1291,1259),(1423,1143),(1297,1255),(1319,1235),(1301,1253),(1303,1252),(1373,1189),(1433,1140),(1439,1136),(1409,1161),(1283,1276),(1289,1271),(1291,1270),(1373,1195),(1301,1262),(1303,1261),(1307,1258),(1427,1153),(1423,1157),(1373,1200),(1319,1250),(1321,1249),(1289,1281),(1291,1280),(1297,1275),(1301,1272),(1303,1271),(1307,1268),(1409,1177),(1367,1214),(1423,1167),(1321,1258),(1451,1146),(1291,1289),(1297,1284),(1301,1281),(1303,1280),(1307,1277),(1451,1151),(1361,1228),(1319,1268),(1321,1267),(1423,1177),(1399,1198),(1447,1159),(1297,1294),(1301,1291),(1303,1290),(1307,1287)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct43 {k : ℕ} (h1 : 1682109 ≤ k) (h2 : k < 1764520) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1373,1226),(1399,1204),(1321,1276),(1427,1182),(1327,1272),(1423,1187),(1471,1149),(1481,1142),(1301,1301),(1303,1300),(1307,1297),(1319,1286),(1321,1285),(1381,1230),(1327,1281),(1483,1147),(1409,1208),(1367,1246),(1453,1173),(1307,1305),(1319,1294),(1321,1293),(1327,1288),(1447,1182),(1367,1252),(1493,1147),(1451,1181),(1373,1249),(1319,1301),(1321,1300),(1327,1295),(1367,1258),(1399,1230),(1429,1205),(1373,1255),(1489,1158),(1481,1165),(1319,1309),(1321,1308),(1327,1303),(1409,1228),(1471,1177),(1439,1204),(1483,1169),(1429,1214),(1381,1257),(1319,1317),(1321,1316),(1327,1311),(1373,1268),(1453,1199),(1423,1225),(1409,1238),(1381,1264),(1511,1156),(1459,1198),(1429,1224),(1327,1319),(1399,1252),(1439,1218),(1381,1270),(1481,1185),(1487,1181),(1511,1163),(1399,1257),(1361,1293),(1327,1327),(1381,1276),(1367,1290),(1423,1240)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct44 {k : ℕ} (h1 : 1764520 ≤ k) (h2 : k < 1848608) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1373,1286),(1399,1263),(1427,1239),(1361,1300),(1429,1239),(1451,1221),(1439,1232),(1433,1238),(1373,1293),(1489,1193),(1451,1225),(1381,1288),(1453,1225),(1367,1303),(1409,1265),(1373,1299),(1451,1230),(1487,1201),(1447,1235),(1361,1314),(1523,1175),(1367,1310),(1451,1235),(1471,1219),(1423,1261),(1433,1253),(1381,1301),(1409,1276),(1399,1286),(1367,1317),(1423,1266),(1373,1313),(1481,1218),(1451,1244),(1381,1308),(1453,1244),(1361,1329),(1367,1324),(1493,1213),(1483,1222),(1429,1269),(1381,1314),(1399,1298),(1423,1277),(1361,1336),(1367,1331),(1453,1253),(1409,1293),(1487,1226),(1381,1321),(1489,1226),(1459,1252),(1453,1258),(1361,1344),(1367,1339),(1409,1300),(1373,1335),(1399,1311),(1381,1329),(1453,1264),(1499,1226),(1439,1278),(1471,1251),(1361,1353),(1367,1348),(1373,1343),(1427,1293),(1381,1337),(1439,1284),(1409,1312)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct45 {k : ℕ} (h1 : 1848608 ≤ k) (h2 : k < 1935667) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1423,1300),(1453,1274),(1361,1361),(1367,1356),(1373,1351),(1381,1344),(1459,1273),(1433,1297),(1409,1320),(1447,1286),(1399,1331),(1493,1248),(1367,1364),(1373,1359),(1433,1303),(1381,1353),(1409,1327),(1447,1293),(1427,1312),(1481,1265),(1451,1292),(1453,1291),(1531,1226),(1373,1368),(1381,1361),(1427,1318),(1429,1317),(1531,1230),(1399,1347),(1493,1263),(1423,1326),(1409,1340),(1427,1324),(1381,1369),(1453,1302),(1433,1321),(1399,1354),(1489,1273),(1483,1279),(1439,1319),(1427,1331),(1493,1273),(1381,1377),(1447,1315),(1399,1361),(1523,1251),(1427,1336),(1409,1354),(1481,1289),(1543,1238),(1447,1321),(1459,1311),(1493,1282),(1423,1346),(1399,1370),(1481,1295),(1429,1343),(1409,1363),(1499,1282),(1493,1288),(1487,1294),(1451,1327),(1489,1294),(1511,1276),(1427,1352),(1399,1380),(1543,1252),(1409,1372),(1471,1315),(1481,1307)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct46 {k : ℕ} (h1 : 1935667 ≤ k) (h2 : k < 2025149) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1439,1346),(1423,1362),(1493,1299),(1427,1360),(1487,1306),(1447,1343),(1399,1390),(1409,1381),(1453,1340),(1423,1369),(1427,1366),(1489,1310),(1433,1362),(1451,1346),(1399,1397),(1453,1346),(1409,1389),(1487,1317),(1543,1270),(1459,1344),(1499,1309),(1427,1376),(1429,1375),(1451,1355),(1453,1354),(1439,1368),(1409,1398),(1459,1351),(1483,1330),(1447,1364),(1531,1290),(1429,1383),(1433,1380),(1499,1320),(1471,1346),(1459,1358),(1409,1407),(1423,1394),(1451,1368),(1429,1390),(1433,1387),(1471,1352),(1439,1383),(1487,1339),(1489,1338),(1423,1401),(1453,1373),(1429,1397),(1493,1338),(1459,1370),(1439,1390),(1487,1346),(1523,1315),(1447,1385),(1451,1382),(1511,1328),(1471,1365),(1423,1412),(1427,1409),(1429,1408),(1433,1405),(1499,1344),(1439,1401),(1511,1335),(1447,1395),(1483,1362),(1471,1374),(1531,1321),(1487,1361),(1499,1351)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct47 {k : ℕ} (h1 : 2025149 ≤ k) (h2 : k < 2118087) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1427,1420),(1429,1419),(1433,1416),(1493,1360),(1439,1412),(1483,1371),(1559,1305),(1471,1384),(1451,1404),(1453,1403),(1511,1350),(1459,1399),(1493,1368),(1481,1380),(1483,1379),(1433,1428),(1439,1423),(1447,1416),(1451,1413),(1453,1412),(1493,1375),(1459,1408),(1481,1388),(1483,1387),(1499,1373),(1487,1385),(1471,1401),(1579,1306),(1439,1434),(1447,1427),(1451,1424),(1453,1423),(1481,1397),(1459,1419),(1499,1382),(1597,1298),(1489,1393),(1471,1411),(1543,1346),(1493,1392),(1579,1317),(1481,1405),(1447,1439),(1451,1436),(1453,1435),(1459,1430),(1487,1404),(1489,1403),(1567,1334),(1471,1422),(1531,1367),(1511,1386),(1481,1415),(1483,1414),(1567,1339),(1451,1447),(1453,1446),(1459,1441),(1601,1314),(1471,1431),(1511,1394),(1567,1345),(1481,1424),(1483,1423),(1607,1314),(1489,1419),(1459,1449),(1543,1371),(1471,1439),(1499,1413)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct48 {k : ℕ} (h1 : 2118087 ≤ k) (h2 : k < 2212720) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1481,1431),(1483,1430),(1531,1386),(1489,1426),(1523,1395),(1511,1407),(1459,1458),(1499,1420),(1471,1448),(1481,1439),(1483,1438),(1583,1348),(1523,1402),(1571,1360),(1493,1432),(1549,1381),(1499,1428),(1531,1399),(1471,1457),(1481,1448),(1483,1447),(1487,1444),(1511,1422),(1549,1388),(1493,1441),(1597,1348),(1531,1407),(1571,1372),(1607,1342),(1471,1467),(1567,1378),(1481,1459),(1483,1458),(1487,1455),(1489,1454),(1543,1404),(1499,1446),(1523,1424),(1549,1401),(1511,1437),(1553,1399),(1481,1468),(1483,1467),(1487,1464),(1489,1463),(1493,1460),(1499,1455),(1523,1433),(1601,1364),(1621,1348),(1543,1417),(1531,1429),(1567,1397),(1613,1358),(1481,1480),(1483,1479),(1487,1476),(1489,1475),(1493,1472),(1597,1377),(1499,1468),(1543,1427),(1567,1406),(1531,1440),(1511,1460),(1579,1398),(1571,1406),(1637,1350),(1523,1452),(1627,1360)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct49 {k : ℕ} (h1 : 2212720 ≤ k) (h2 : k < 2308748) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1489,1487),(1493,1484),(1499,1479),(1531,1449),(1571,1413),(1511,1470),(1583,1404),(1553,1432),(1609,1383),(1523,1462),(1579,1411),(1559,1430),(1531,1457),(1583,1410),(1499,1490),(1511,1479),(1567,1427),(1619,1382),(1543,1451),(1523,1471),(1583,1416),(1549,1448),(1553,1445),(1567,1433),(1499,1499),(1511,1488),(1543,1458),(1583,1422),(1549,1454),(1531,1472),(1613,1398),(1579,1429),(1571,1437),(1543,1464),(1657,1364),(1549,1460),(1597,1417),(1531,1479),(1637,1384),(1601,1416),(1583,1433),(1619,1402),(1543,1472),(1621,1402),(1511,1505),(1549,1469),(1579,1442),(1523,1496),(1601,1424),(1531,1490),(1613,1415),(1597,1430),(1543,1481),(1669,1370),(1579,1449),(1549,1478),(1627,1408),(1553,1476),(1571,1460),(1523,1507),(1531,1500),(1559,1474),(1609,1429),(1601,1437),(1567,1469),(1549,1487),(1571,1467),(1597,1444),(1523,1515),(1531,1508)]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem direct50 {k : ℕ} (h1 : 2308748 ≤ k) (h2 : k < 2360683) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := direct_range (rows := [(1579,1463),(1637,1412),(1567,1476),(1583,1462),(1549,1495),(1571,1475),(1553,1493),(1619,1433),(1601,1450),(1559,1490),(1613,1441),(1531,1519),(1583,1470),(1597,1458),(1543,1510),(1571,1484),(1549,1506),(1553,1503),(1667,1401),(1559,1499),(1669,1401),(1583,1478),(1567,1494),(1531,1530),(1601,1464),(1543,1520),(1549,1515),(1553,1512),(1579,1488),(1559,1508),(1619,1453),(1667,1412),(1567,1503),(1601,1472),(1571,1501),(1543,1529),(1607,1469)]) (by decide +kernel) h1 h2

theorem direct_coverage {k : ℕ} (h1 : 193 ≤ k) (h2 : k < 2359296) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := by
  by_cases h1 : k < 533624
  · by_cases h2 : k < 111734
    · by_cases h3 : k < 26167
      · by_cases h4 : k < 6695
        · by_cases h5 : k < 1128
          · exact direct0 (by omega) (by omega)
          · by_cases h6 : k < 3245
            · exact direct1 (by omega) (by omega)
            · exact direct2 (by omega) (by omega)
        · by_cases h5 : k < 11690
          · exact direct3 (by omega) (by omega)
          · by_cases h6 : k < 18178
            · exact direct4 (by omega) (by omega)
            · exact direct5 (by omega) (by omega)
      · by_cases h4 : k < 61279
        · by_cases h5 : k < 36091
          · exact direct6 (by omega) (by omega)
          · by_cases h6 : k < 47802
            · exact direct7 (by omega) (by omega)
            · exact direct8 (by omega) (by omega)
        · by_cases h5 : k < 76729
          · exact direct9 (by omega) (by omega)
          · by_cases h6 : k < 93096
            · exact direct10 (by omega) (by omega)
            · exact direct11 (by omega) (by omega)
    · by_cases h3 : k < 265189
      · by_cases h4 : k < 179990
        · by_cases h5 : k < 132650
          · exact direct12 (by omega) (by omega)
          · by_cases h6 : k < 155105
            · exact direct13 (by omega) (by omega)
            · exact direct14 (by omega) (by omega)
        · by_cases h5 : k < 206711
          · exact direct15 (by omega) (by omega)
          · by_cases h6 : k < 235054
            · exact direct16 (by omega) (by omega)
            · exact direct17 (by omega) (by omega)
      · by_cases h4 : k < 368924
        · by_cases h5 : k < 297021
          · exact direct18 (by omega) (by omega)
          · by_cases h6 : k < 331846
            · exact direct19 (by omega) (by omega)
            · exact direct20 (by omega) (by omega)
        · by_cases h5 : k < 446889
          · by_cases h6 : k < 407068
            · exact direct21 (by omega) (by omega)
            · exact direct22 (by omega) (by omega)
          · by_cases h6 : k < 489298
            · exact direct23 (by omega) (by omega)
            · exact direct24 (by omega) (by omega)
  · by_cases h2 : k < 1295017
    · by_cases h3 : k < 842603
      · by_cases h4 : k < 679027
        · by_cases h5 : k < 580447
          · exact direct25 (by omega) (by omega)
          · by_cases h6 : k < 628065
            · exact direct26 (by omega) (by omega)
            · exact direct27 (by omega) (by omega)
        · by_cases h5 : k < 731533
          · exact direct28 (by omega) (by omega)
          · by_cases h6 : k < 786011
            · exact direct29 (by omega) (by omega)
            · exact direct30 (by omega) (by omega)
      · by_cases h4 : k < 1024598
        · by_cases h5 : k < 901094
          · exact direct31 (by omega) (by omega)
          · by_cases h6 : k < 961374
            · exact direct32 (by omega) (by omega)
            · exact direct33 (by omega) (by omega)
        · by_cases h5 : k < 1156460
          · by_cases h6 : k < 1089764
            · exact direct34 (by omega) (by omega)
            · exact direct35 (by omega) (by omega)
          · by_cases h6 : k < 1225211
            · exact direct36 (by omega) (by omega)
            · exact direct37 (by omega) (by omega)
    · by_cases h3 : k < 1764520
      · by_cases h4 : k < 1520601
        · by_cases h5 : k < 1367728
          · exact direct38 (by omega) (by omega)
          · by_cases h6 : k < 1442846
            · exact direct39 (by omega) (by omega)
            · exact direct40 (by omega) (by omega)
        · by_cases h5 : k < 1599649
          · exact direct41 (by omega) (by omega)
          · by_cases h6 : k < 1682109
            · exact direct42 (by omega) (by omega)
            · exact direct43 (by omega) (by omega)
      · by_cases h4 : k < 2025149
        · by_cases h5 : k < 1848608
          · exact direct44 (by omega) (by omega)
          · by_cases h6 : k < 1935667
            · exact direct45 (by omega) (by omega)
            · exact direct46 (by omega) (by omega)
        · by_cases h5 : k < 2212720
          · by_cases h6 : k < 2118087
            · exact direct47 (by omega) (by omega)
            · exact direct48 (by omega) (by omega)
          · by_cases h6 : k < 2308748
            · exact direct49 (by omega) (by omega)
            · exact direct50 (by omega) (by omega)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands0 {k : ℕ} (h1 : 1536 ≤ k.sqrt) (h2 : k.sqrt < 1620) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨1536,1577,86,5,[1579,1583,1597,1601,1607,1609,1613,1619,1621]⟩,⟨1578,1607,92,6,[1609,1613,1619,1621,1627,1637,1657,1663,1667,1669]⟩,⟨1608,1619,62,3,[1621,1627,1637,1657,1663,1667,1669]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands1 {k : ℕ} (h1 : 1620 ≤ k.sqrt) (h2 : k.sqrt < 1696) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨1620,1635,80,4,[1637,1657,1663,1667,1669,1693,1697,1699]⟩,⟨1636,1661,88,5,[1663,1667,1669,1693,1697,1699,1709,1721,1723]⟩,⟨1662,1695,98,6,[1697,1699,1709,1721,1723,1733,1741,1747,1753,1759]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands2 {k : ℕ} (h1 : 1696 ≤ k.sqrt) (h2 : k.sqrt < 1776) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨1696,1721,92,5,[1723,1733,1741,1747,1753,1759,1777,1783,1787]⟩,⟨1722,1745,68,3,[1747,1753,1759,1777,1783,1787,1789]⟩,⟨1746,1775,132,10,[1777,1783,1787,1789,1801,1811,1823,1831,1847,1861,1867,1871,1873,1877]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands3 {k : ℕ} (h1 : 1776 ≤ k.sqrt) (h2 : k.sqrt < 1870) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨1776,1799,102,6,[1801,1811,1823,1831,1847,1861,1867,1871,1873,1877]⟩,⟨1800,1829,80,4,[1831,1847,1861,1867,1871,1873,1877,1879]⟩,⟨1830,1869,84,4,[1871,1873,1877,1879,1889,1901,1907,1913]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands4 {k : ℕ} (h1 : 1870 ≤ k.sqrt) (h2 : k.sqrt < 1996) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨1870,1899,134,10,[1901,1907,1913,1931,1933,1949,1951,1973,1979,1987,1993,1997,1999,2003]⟩,⟨1900,1947,130,9,[1949,1951,1973,1979,1987,1993,1997,1999,2003,2011,2017,2027,2029]⟩,⟨1948,1995,142,11,[1997,1999,2003,2011,2017,2027,2029,2039,2053,2063,2069,2081,2083,2087,2089]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands5 {k : ℕ} (h1 : 1996 ≤ k.sqrt) (h2 : k.sqrt < 2130) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨1996,2051,148,11,[2053,2063,2069,2081,2083,2087,2089,2099,2111,2113,2129,2131,2137,2141,2143]⟩,⟨2052,2097,110,6,[2099,2111,2113,2129,2131,2137,2141,2143,2153,2161]⟩,⟨2098,2129,64,2,[2131,2137,2141,2143,2153,2161]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands6 {k : ℕ} (h1 : 2130 ≤ k.sqrt) (h2 : k.sqrt < 2266) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨2130,2151,122,7,[2153,2161,2179,2203,2207,2213,2221,2237,2239,2243,2251]⟩,⟨2152,2205,146,10,[2207,2213,2221,2237,2239,2243,2251,2267,2269,2273,2281,2287,2293,2297]⟩,⟨2206,2265,146,10,[2267,2269,2273,2281,2287,2293,2297,2309,2311,2333,2339,2341,2347,2351]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands7 {k : ℕ} (h1 : 2266 ≤ k.sqrt) (h2 : k.sqrt < 2422) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨2266,2337,134,8,[2339,2341,2347,2351,2357,2371,2377,2381,2383,2389,2393,2399]⟩,⟨2338,2387,136,8,[2389,2393,2399,2411,2417,2423,2437,2441,2447,2459,2467,2473]⟩,⟨2388,2421,90,4,[2423,2437,2441,2447,2459,2467,2473,2477]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands8 {k : ℕ} (h1 : 2422 ≤ k.sqrt) (h2 : k.sqrt < 2530) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨2422,2457,130,7,[2459,2467,2473,2477,2503,2521,2531,2539,2543,2549,2551]⟩,⟨2458,2475,94,4,[2477,2503,2521,2531,2539,2543,2549,2551]⟩,⟨2476,2529,238,23,[2531,2539,2543,2549,2551,2557,2579,2591,2593,2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands9 {k : ℕ} (h1 : 2530 ≤ k.sqrt) (h2 : k.sqrt < 2748) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨2530,2607,184,14,[2609,2617,2621,2633,2647,2657,2659,2663,2671,2677,2683,2687,2689,2693,2699,2707,2711,2713]⟩,⟨2608,2687,196,15,[2689,2693,2699,2707,2711,2713,2719,2729,2731,2741,2749,2753,2767,2777,2789,2791,2797,2801,2803]⟩,⟨2688,2747,170,11,[2749,2753,2767,2777,2789,2791,2797,2801,2803,2819,2833,2837,2843,2851,2857]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands10 {k : ℕ} (h1 : 2748 ≤ k.sqrt) (h2 : k.sqrt < 2908) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨2748,2799,114,5,[2801,2803,2819,2833,2837,2843,2851,2857,2861]⟩,⟨2800,2855,172,11,[2857,2861,2879,2887,2897,2903,2909,2917,2927,2939,2953,2957,2963,2969,2971]⟩,⟨2856,2907,116,5,[2909,2917,2927,2939,2953,2957,2963,2969,2971]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands11 {k : ℕ} (h1 : 2908 ≤ k.sqrt) (h2 : k.sqrt < 3066) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨2908,2961,142,7,[2963,2969,2971,2999,3001,3011,3019,3023,3037,3041,3049]⟩,⟨2962,3017,128,6,[3019,3023,3037,3041,3049,3061,3067,3079,3083,3089]⟩,⟨3018,3065,204,14,[3067,3079,3083,3089,3109,3119,3121,3137,3163,3167,3169,3181,3187,3191,3203,3209,3217,3221]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands12 {k : ℕ} (h1 : 3066 ≤ k.sqrt) (h2 : k.sqrt < 3270) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨3066,3119,156,8,[3121,3137,3163,3167,3169,3181,3187,3191,3203,3209,3217,3221]⟩,⟨3120,3189,212,15,[3191,3203,3209,3217,3221,3229,3251,3253,3257,3259,3271,3299,3301,3307,3313,3319,3323,3329,3331]⟩,⟨3190,3269,184,11,[3271,3299,3301,3307,3313,3319,3323,3329,3331,3343,3347,3359,3361,3371,3373]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands13 {k : ℕ} (h1 : 3270 ≤ k.sqrt) (h2 : k.sqrt < 3528) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨3270,3341,198,12,[3343,3347,3359,3361,3371,3373,3389,3391,3407,3413,3433,3449,3457,3461,3463,3467]⟩,⟨3342,3431,200,12,[3433,3449,3457,3461,3463,3467,3469,3491,3499,3511,3517,3527,3529,3533,3539,3541]⟩,⟨3432,3527,192,11,[3529,3533,3539,3541,3547,3557,3559,3571,3581,3583,3593,3607,3613,3617,3623]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands14 {k : ℕ} (h1 : 3528 ≤ k.sqrt) (h2 : k.sqrt < 3792) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨3528,3615,212,13,[3617,3623,3631,3637,3643,3659,3671,3673,3677,3691,3697,3701,3709,3719,3727,3733,3739]⟩,⟨3616,3695,188,10,[3697,3701,3709,3719,3727,3733,3739,3761,3767,3769,3779,3793,3797,3803]⟩,⟨3696,3791,234,15,[3793,3797,3803,3821,3823,3833,3847,3851,3853,3863,3877,3881,3889,3907,3911,3917,3919,3923,3929]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands15 {k : ℕ} (h1 : 3792 ≤ k.sqrt) (h2 : k.sqrt < 4090) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨3792,3887,230,14,[3889,3907,3911,3917,3919,3923,3929,3931,3943,3947,3967,3989,4001,4003,4007,4013,4019,4021]⟩,⟨3888,3987,206,11,[3989,4001,4003,4007,4013,4019,4021,4027,4049,4051,4057,4073,4079,4091,4093]⟩,⟨3988,4089,274,19,[4091,4093,4099,4111,4127,4129,4133,4139,4153,4157,4159,4177,4201,4211,4217,4219,4229,4231,4241,4243,4253,4259,4261]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands16 {k : ℕ} (h1 : 4090 ≤ k.sqrt) (h2 : k.sqrt < 4390) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨4090,4209,200,10,[4211,4217,4219,4229,4231,4241,4243,4253,4259,4261,4271,4273,4283,4289]⟩,⟨4210,4281,214,11,[4283,4289,4297,4327,4337,4339,4349,4357,4363,4373,4391,4397,4409,4421,4423]⟩,⟨4282,4389,242,14,[4391,4397,4409,4421,4423,4441,4447,4451,4457,4463,4481,4483,4493,4507,4513,4517,4519,4523]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands17 {k : ℕ} (h1 : 4390 ≤ k.sqrt) (h2 : k.sqrt < 4702) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨4390,4491,262,16,[4493,4507,4513,4517,4519,4523,4547,4549,4561,4567,4583,4591,4597,4603,4621,4637,4639,4643,4649,4651]⟩,⟨4492,4595,188,8,[4597,4603,4621,4637,4639,4643,4649,4651,4657,4663,4673,4679]⟩,⟨4596,4701,222,11,[4703,4721,4723,4729,4733,4751,4759,4783,4787,4789,4793,4799,4801,4813,4817]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands18 {k : ℕ} (h1 : 4702 ≤ k.sqrt) (h2 : k.sqrt < 5058) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨4702,4811,310,21,[4813,4817,4831,4861,4871,4877,4889,4903,4909,4919,4931,4933,4937,4943,4951,4957,4967,4969,4973,4987,4993,4999,5003,5009,5011]⟩,⟨4812,4949,302,19,[4951,4957,4967,4969,4973,4987,4993,4999,5003,5009,5011,5021,5023,5039,5051,5059,5077,5081,5087,5099,5101,5107,5113]⟩,⟨4950,5057,288,17,[5059,5077,5081,5087,5099,5101,5107,5113,5119,5147,5153,5167,5171,5179,5189,5197,5209,5227,5231,5233,5237]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands19 {k : ℕ} (h1 : 5058 ≤ k.sqrt) (h2 : k.sqrt < 5440) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨5058,5165,224,10,[5167,5171,5179,5189,5197,5209,5227,5231,5233,5237,5261,5273,5279,5281]⟩,⟨5166,5301,366,26,[5303,5309,5323,5333,5347,5351,5381,5387,5393,5399,5407,5413,5417,5419,5431,5437,5441,5443,5449,5471,5477,5479,5483,5501,5503,5507,5519,5521,5527,5531]⟩,⟨5302,5439,230,10,[5441,5443,5449,5471,5477,5479,5483,5501,5503,5507,5519,5521,5527,5531]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands20 {k : ℕ} (h1 : 5440 ≤ k.sqrt) (h2 : k.sqrt < 5850) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨5440,5571,304,17,[5573,5581,5591,5623,5639,5641,5647,5651,5653,5657,5659,5669,5683,5689,5693,5701,5711,5717,5737,5741,5743]⟩,⟨5572,5735,298,16,[5737,5741,5743,5749,5779,5783,5791,5801,5807,5813,5821,5827,5839,5843,5849,5851,5857,5861,5867,5869]⟩,⟨5736,5849,168,5,[5851,5857,5861,5867,5869,5879,5881,5897,5903]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands21 {k : ℕ} (h1 : 5850 ≤ k.sqrt) (h2 : k.sqrt < 6310) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨5850,5985,284,14,[5987,6007,6011,6029,6037,6043,6047,6053,6067,6073,6079,6089,6091,6101,6113,6121,6131,6133]⟩,⟨5986,6161,394,26,[6163,6173,6197,6199,6203,6211,6217,6221,6229,6247,6257,6263,6269,6271,6277,6287,6299,6301,6311,6317,6323,6329,6337,6343,6353,6359,6361,6367,6373,6379]⟩,⟨6162,6309,218,8,[6311,6317,6323,6329,6337,6343,6353,6359,6361,6367,6373,6379]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands22 {k : ℕ} (h1 : 6310 ≤ k.sqrt) (h2 : k.sqrt < 6790) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨6310,6447,272,12,[6449,6451,6469,6473,6481,6491,6521,6529,6547,6551,6553,6563,6569,6571,6577,6581]⟩,⟨6448,6605,424,28,[6607,6619,6637,6653,6659,6661,6673,6679,6689,6691,6701,6703,6709,6719,6733,6737,6761,6763,6779,6781,6791,6793,6803,6823,6827,6829,6833,6841,6857,6863,6869,6871]⟩,⟨6606,6789,396,24,[6791,6793,6803,6823,6827,6829,6833,6841,6857,6863,6869,6871,6883,6899,6907,6911,6917,6947,6949,6959,6961,6967,6971,6977,6983,6991,6997,7001]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands23 {k : ℕ} (h1 : 6790 ≤ k.sqrt) (h2 : k.sqrt < 7296) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨6790,6957,254,10,[6959,6961,6967,6971,6977,6983,6991,6997,7001,7013,7019,7027,7039,7043]⟩,⟨6958,7119,296,13,[7121,7127,7129,7151,7159,7177,7187,7193,7207,7211,7213,7219,7229,7237,7243,7247,7253]⟩,⟨7120,7295,472,32,[7297,7307,7309,7321,7331,7333,7349,7351,7369,7393,7411,7417,7433,7451,7457,7459,7477,7481,7487,7489,7499,7507,7517,7523,7529,7537,7541,7547,7549,7559,7561,7573,7577,7583,7589,7591]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands24 {k : ℕ} (h1 : 7296 ≤ k.sqrt) (h2 : k.sqrt < 7872) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨7296,7515,408,23,[7517,7523,7529,7537,7541,7547,7549,7559,7561,7573,7577,7583,7589,7591,7603,7607,7621,7639,7643,7649,7669,7673,7681,7687,7691,7699,7703]⟩,⟨7516,7689,422,24,[7691,7699,7703,7717,7723,7727,7741,7753,7757,7759,7789,7793,7817,7823,7829,7841,7853,7867,7873,7877,7879,7883,7901,7907,7919,7927,7933,7937]⟩,⟨7690,7871,428,24,[7873,7877,7879,7883,7901,7907,7919,7927,7933,7937,7949,7951,7963,7993,8009,8011,8017,8039,8053,8059,8069,8081,8087,8089,8093,8101,8111,8117]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands25 {k : ℕ} (h1 : 7872 ≤ k.sqrt) (h2 : k.sqrt < 8500) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨7872,8079,422,23,[8081,8087,8089,8093,8101,8111,8117,8123,8147,8161,8167,8171,8179,8191,8209,8219,8221,8231,8233,8237,8243,8263,8269,8273,8287,8291,8293]⟩,⟨8080,8267,368,17,[8269,8273,8287,8291,8293,8297,8311,8317,8329,8353,8363,8369,8377,8387,8389,8419,8423,8429,8431,8443,8447]⟩,⟨8268,8499,480,28,[8501,8513,8521,8527,8537,8539,8543,8563,8573,8581,8597,8599,8609,8623,8627,8629,8641,8647,8663,8669,8677,8681,8689,8693,8699,8707,8713,8719,8731,8737,8741,8747]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands26 {k : ℕ} (h1 : 8500 ≤ k.sqrt) (h2 : k.sqrt < 9180) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨8500,8717,368,16,[8719,8731,8737,8741,8747,8753,8761,8779,8783,8803,8807,8819,8821,8831,8837,8839,8849,8861,8863,8867]⟩,⟨8718,8931,492,28,[8933,8941,8951,8963,8969,8971,8999,9001,9007,9011,9013,9029,9041,9043,9049,9059,9067,9091,9103,9109,9127,9133,9137,9151,9157,9161,9173,9181,9187,9199,9203,9209]⟩,⟨8932,9179,508,29,[9181,9187,9199,9203,9209,9221,9227,9239,9241,9257,9277,9281,9283,9293,9311,9319,9323,9337,9341,9343,9349,9371,9377,9391,9397,9403,9413,9419,9421,9431,9433,9437,9439]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands27 {k : ℕ} (h1 : 9180 ≤ k.sqrt) (h2 : k.sqrt < 9882) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨9180,9411,368,15,[9413,9419,9421,9431,9433,9437,9439,9461,9463,9467,9473,9479,9491,9497,9511,9521,9533,9539,9547]⟩,⟨9412,9659,520,29,[9661,9677,9679,9689,9697,9719,9721,9733,9739,9743,9749,9767,9769,9781,9787,9791,9803,9811,9817,9829,9833,9839,9851,9857,9859,9871,9883,9887,9901,9907,9923,9929,9931]⟩,⟨9660,9881,510,27,[9883,9887,9901,9907,9923,9929,9931,9941,9949,9967,9973,10007,10009,10037,10039,10061,10067,10069,10079,10091,10093,10099,10103,10111,10133,10139,10141,10151,10159,10163,10169]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands28 {k : ℕ} (h1 : 9882 ≤ k.sqrt) (h2 : k.sqrt < 10606) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨9882,10139,462,22,[10141,10151,10159,10163,10169,10177,10181,10193,10211,10223,10243,10247,10253,10259,10267,10271,10273,10289,10301,10303,10313,10321,10331,10333,10337,10343]⟩,⟨10140,10355,528,28,[10357,10369,10391,10399,10427,10429,10433,10453,10457,10459,10463,10477,10487,10499,10501,10513,10529,10531,10559,10567,10589,10597,10601,10607,10613,10627,10631,10639,10651,10657,10663,10667]⟩,⟨10356,10605,536,28,[10607,10613,10627,10631,10639,10651,10657,10663,10667,10687,10691,10709,10711,10723,10729,10733,10739,10753,10771,10781,10789,10799,10831,10837,10847,10853,10859,10861,10867,10883,10889,10891]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands29 {k : ℕ} (h1 : 10606 ≤ k.sqrt) (h2 : k.sqrt < 11350) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨10606,10859,572,31,[10861,10867,10883,10889,10891,10903,10909,10937,10939,10949,10957,10973,10979,10987,10993,11003,11027,11047,11057,11059,11069,11071,11083,11087,11093,11113,11117,11119,11131,11149,11159,11161,11171,11173,11177]⟩,⟨10860,11111,462,20,[11113,11117,11119,11131,11149,11159,11161,11171,11173,11177,11197,11213,11239,11243,11251,11257,11261,11273,11279,11287,11299,11311,11317,11321]⟩,⟨11112,11349,392,14,[11351,11353,11369,11383,11393,11399,11411,11423,11437,11443,11447,11467,11471,11483,11489,11491,11497,11503]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands30 {k : ℕ} (h1 : 11350 ≤ k.sqrt) (h2 : k.sqrt < 12250) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨11350,11631,638,36,[11633,11657,11677,11681,11689,11699,11701,11717,11719,11731,11743,11777,11779,11783,11789,11801,11807,11813,11821,11827,11831,11833,11839,11863,11867,11887,11897,11903,11909,11923,11927,11933,11939,11941,11953,11959,11969,11971,11981,11987]⟩,⟨11632,11925,532,25,[11927,11933,11939,11941,11953,11959,11969,11971,11981,11987,12007,12011,12037,12041,12043,12049,12071,12073,12097,12101,12107,12109,12113,12119,12143,12149,12157,12161,12163]⟩,⟨11926,12249,664,37,[12251,12253,12263,12269,12277,12281,12289,12301,12323,12329,12343,12347,12373,12377,12379,12391,12401,12409,12413,12421,12433,12437,12451,12457,12473,12479,12487,12491,12497,12503,12511,12517,12527,12539,12541,12547,12553,12569,12577,12583,12589]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands31 {k : ℕ} (h1 : 12250 ≤ k.sqrt) (h2 : k.sqrt < 13176) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨12250,12551,734,44,[12553,12569,12577,12583,12589,12601,12611,12613,12619,12637,12641,12647,12653,12659,12671,12689,12697,12703,12713,12721,12739,12743,12757,12763,12781,12791,12799,12809,12821,12823,12829,12841,12853,12889,12893,12899,12907,12911,12917,12919,12923,12941,12953,12959,12967,12973,12979,12983]⟩,⟨12552,12891,632,32,[12893,12899,12907,12911,12917,12919,12923,12941,12953,12959,12967,12973,12979,12983,13001,13003,13007,13009,13033,13037,13043,13049,13063,13093,13099,13103,13109,13121,13127,13147,13151,13159,13163,13171,13177,13183]⟩,⟨12892,13175,578,26,[13177,13183,13187,13217,13219,13229,13241,13249,13259,13267,13291,13297,13309,13313,13327,13331,13337,13339,13367,13381,13397,13399,13411,13417,13421,13441,13451,13457,13463,13469]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands32 {k : ℕ} (h1 : 13176 ≤ k.sqrt) (h2 : k.sqrt < 14148) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨13176,13511,758,44,[13513,13523,13537,13553,13567,13577,13591,13597,13613,13619,13627,13633,13649,13669,13679,13681,13687,13691,13693,13697,13709,13711,13721,13723,13729,13751,13757,13759,13763,13781,13789,13799,13807,13829,13831,13841,13859,13873,13877,13879,13883,13901,13903,13907,13913,13921,13931,13933]⟩,⟨13512,13827,576,25,[13829,13831,13841,13859,13873,13877,13879,13883,13901,13903,13907,13913,13921,13931,13933,13963,13967,13997,13999,14009,14011,14029,14033,14051,14057,14071,14081,14083,14087]⟩,⟨13828,14147,734,39,[14149,14153,14159,14173,14177,14197,14207,14221,14243,14249,14251,14281,14293,14303,14321,14323,14327,14341,14347,14369,14387,14389,14401,14407,14411,14419,14423,14431,14437,14447,14449,14461,14479,14489,14503,14519,14533,14537,14543,14549,14551,14557,14561]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands33 {k : ℕ} (h1 : 14148 ≤ k.sqrt) (h2 : k.sqrt < 15288) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨14148,14541,750,40,[14543,14549,14551,14557,14561,14563,14591,14593,14621,14627,14629,14633,14639,14653,14657,14669,14683,14699,14713,14717,14723,14731,14737,14741,14747,14753,14759,14767,14771,14779,14783,14797,14813,14821,14827,14831,14843,14851,14867,14869,14879,14887,14891,14897]⟩,⟨14542,14895,790,43,[14897,14923,14929,14939,14947,14951,14957,14969,14983,15013,15017,15031,15053,15061,15073,15077,15083,15091,15101,15107,15121,15131,15137,15139,15149,15161,15173,15187,15193,15199,15217,15227,15233,15241,15259,15263,15269,15271,15277,15287,15289,15299,15307,15313,15319,15329,15331]⟩,⟨14896,15287,788,42,[15289,15299,15307,15313,15319,15329,15331,15349,15359,15361,15373,15377,15383,15391,15401,15413,15427,15439,15443,15451,15461,15467,15473,15493,15497,15511,15527,15541,15551,15559,15569,15581,15583,15601,15607,15619,15629,15641,15643,15647,15649,15661,15667,15671,15679,15683]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands34 {k : ℕ} (h1 : 15288 ≤ k.sqrt) (h2 : k.sqrt < 16410) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨15288,15665,810,43,[15667,15671,15679,15683,15727,15731,15733,15737,15739,15749,15761,15767,15773,15787,15791,15797,15803,15809,15817,15823,15859,15877,15881,15887,15889,15901,15907,15913,15919,15923,15937,15959,15971,15973,15991,16001,16007,16033,16057,16061,16063,16067,16069,16073,16087,16091,16097]⟩,⟨15666,16031,788,40,[16033,16057,16061,16063,16067,16069,16073,16087,16091,16097,16103,16111,16127,16139,16141,16183,16187,16189,16193,16217,16223,16229,16231,16249,16253,16267,16273,16301,16319,16333,16339,16349,16361,16363,16369,16381,16411,16417,16421,16427,16433,16447,16451,16453]⟩,⟨16032,16409,668,28,[16411,16417,16421,16427,16433,16447,16451,16453,16477,16481,16487,16493,16519,16529,16547,16553,16561,16567,16573,16603,16607,16619,16631,16633,16649,16651,16657,16661,16673,16691,16693,16699]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands35 {k : ℕ} (h1 : 16410 ≤ k.sqrt) (h2 : k.sqrt < 17656) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨16410,16809,798,39,[16811,16823,16829,16831,16843,16871,16879,16883,16889,16901,16903,16921,16927,16931,16937,16943,16963,16979,16981,16987,16993,17011,17021,17027,17029,17033,17041,17047,17053,17077,17093,17099,17107,17117,17123,17137,17159,17167,17183,17189,17191,17203,17207]⟩,⟨16810,17229,818,40,[17231,17239,17257,17291,17293,17299,17317,17321,17327,17333,17341,17351,17359,17377,17383,17387,17389,17393,17401,17417,17419,17431,17443,17449,17467,17471,17477,17483,17489,17491,17497,17509,17519,17539,17551,17569,17573,17579,17581,17597,17599,17609,17623,17627]⟩,⟨17230,17655,904,48,[17657,17659,17669,17681,17683,17707,17713,17729,17737,17747,17749,17761,17783,17789,17791,17807,17827,17837,17839,17851,17863,17881,17891,17903,17909,17911,17921,17923,17929,17939,17957,17959,17971,17977,17981,17987,17989,18013,18041,18043,18047,18049,18059,18061,18077,18089,18097,18119,18121,18127,18131,18133]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands36 {k : ℕ} (h1 : 17656 ≤ k.sqrt) (h2 : k.sqrt < 18916) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨17656,18119,806,37,[18121,18127,18131,18133,18143,18149,18169,18181,18191,18199,18211,18217,18223,18229,18233,18251,18253,18257,18269,18287,18289,18301,18307,18311,18313,18329,18341,18353,18367,18371,18379,18397,18401,18413,18427,18433,18439,18443,18451,18457,18461]⟩,⟨18120,18479,684,26,[18481,18493,18503,18517,18521,18523,18539,18541,18553,18583,18587,18593,18617,18637,18661,18671,18679,18691,18701,18713,18719,18731,18743,18749,18757,18773,18787,18793,18797,18803]⟩,⟨18480,18915,998,54,[18917,18919,18947,18959,18973,18979,19001,19009,19013,19031,19037,19051,19069,19073,19079,19081,19087,19121,19139,19141,19157,19163,19181,19183,19207,19211,19213,19219,19231,19237,19249,19259,19267,19273,19289,19301,19309,19319,19333,19373,19379,19381,19387,19391,19403,19417,19421,19423,19427,19429,19433,19441,19447,19457,19463,19469,19471,19477]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands37 {k : ℕ} (h1 : 18916 ≤ k.sqrt) (h2 : k.sqrt < 20358) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨18916,19401,952,48,[19403,19417,19421,19423,19427,19429,19433,19441,19447,19457,19463,19469,19471,19477,19483,19489,19501,19507,19531,19541,19543,19553,19559,19571,19577,19583,19597,19603,19609,19661,19681,19687,19697,19699,19709,19717,19727,19739,19751,19753,19759,19763,19777,19793,19801,19813,19819,19841,19843,19853,19861,19867]⟩,⟨19402,19911,1010,53,[19913,19919,19927,19937,19949,19961,19963,19973,19979,19991,19993,19997,20011,20021,20023,20029,20047,20051,20063,20071,20089,20101,20107,20113,20117,20123,20129,20143,20147,20149,20161,20173,20177,20183,20201,20219,20231,20233,20249,20261,20269,20287,20297,20323,20327,20333,20341,20347,20353,20357,20359,20369,20389,20393,20399,20407,20411]⟩,⟨19912,20357,1120,63,[20359,20369,20389,20393,20399,20407,20411,20431,20441,20443,20477,20479,20483,20507,20509,20521,20533,20543,20549,20551,20563,20593,20599,20611,20627,20639,20641,20663,20681,20693,20707,20717,20719,20731,20743,20747,20749,20753,20759,20771,20773,20789,20807,20809,20849,20857,20873,20879,20887,20897,20899,20903,20921,20929,20939,20947,20959,20963,20981,20983,21001,21011,21013,21017,21019,21023,21031]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands38 {k : ℕ} (h1 : 20358 ≤ k.sqrt) (h2 : k.sqrt < 21928) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨20358,20877,1260,78,[20879,20887,20897,20899,20903,20921,20929,20939,20947,20959,20963,20981,20983,21001,21011,21013,21017,21019,21023,21031,21059,21061,21067,21089,21101,21107,21121,21139,21143,21149,21157,21163,21169,21179,21187,21191,21193,21211,21221,21227,21247,21269,21277,21283,21313,21317,21319,21323,21341,21347,21377,21379,21383,21391,21397,21401,21407,21419,21433,21467,21481,21487,21491,21493,21499,21503,21517,21521,21523,21529,21557,21559,21563,21569,21577,21587,21589,21599,21601,21611,21613,21617]⟩,⟨20878,21405,1282,79,[21407,21419,21433,21467,21481,21487,21491,21493,21499,21503,21517,21521,21523,21529,21557,21559,21563,21569,21577,21587,21589,21599,21601,21611,21613,21617,21647,21649,21661,21673,21683,21701,21713,21727,21737,21739,21751,21757,21767,21773,21787,21799,21803,21817,21821,21839,21841,21851,21859,21863,21871,21881,21893,21911,21929,21937,21943,21961,21977,21991,21997,22003,22013,22027,22031,22037,22039,22051,22063,22067,22073,22079,22091,22093,22109,22111,22123,22129,22133,22147,22153,22157,22159]⟩,⟨21406,21927,886,37,[21929,21937,21943,21961,21977,21991,21997,22003,22013,22027,22031,22037,22039,22051,22063,22067,22073,22079,22091,22093,22109,22111,22123,22129,22133,22147,22153,22157,22159,22171,22189,22193,22229,22247,22259,22271,22273,22277,22279,22283,22291]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands39 {k : ℕ} (h1 : 21928 ≤ k.sqrt) (h2 : k.sqrt < 23628) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨21928,22479,1136,59,[22481,22483,22501,22511,22531,22541,22543,22549,22567,22571,22573,22613,22619,22621,22637,22639,22643,22651,22669,22679,22691,22697,22699,22709,22717,22721,22727,22739,22741,22751,22769,22777,22783,22787,22807,22811,22817,22853,22859,22861,22871,22877,22901,22907,22921,22937,22943,22961,22963,22973,22993,23003,23011,23017,23021,23027,23029,23039,23041,23053,23057,23059,23063]⟩,⟨22480,23019,1150,59,[23021,23027,23029,23039,23041,23053,23057,23059,23063,23071,23081,23087,23099,23117,23131,23143,23159,23167,23173,23189,23197,23201,23203,23209,23227,23251,23269,23279,23291,23293,23297,23311,23321,23327,23333,23339,23357,23369,23371,23399,23417,23431,23447,23459,23473,23497,23509,23531,23537,23539,23549,23557,23561,23563,23567,23581,23593,23599,23603,23609,23623,23627,23629]⟩,⟨23020,23627,1094,52,[23629,23633,23663,23669,23671,23677,23687,23689,23719,23741,23743,23747,23753,23761,23767,23773,23789,23801,23813,23819,23827,23831,23833,23857,23869,23873,23879,23887,23893,23899,23909,23911,23917,23929,23957,23971,23977,23981,23993,24001,24007,24019,24023,24029,24043,24049,24061,24071,24077,24083,24091,24097,24103,24107,24109,24113]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands40 {k : ℕ} (h1 : 23628 ≤ k.sqrt) (h2 : k.sqrt < 25218) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨23628,24107,906,35,[24109,24113,24121,24133,24137,24151,24169,24179,24181,24197,24203,24223,24229,24239,24247,24251,24281,24317,24329,24337,24359,24371,24373,24379,24391,24407,24413,24419,24421,24439,24443,24469,24473,24481,24499,24509,24517,24527,24533]⟩,⟨24108,24629,1064,47,[24631,24659,24671,24677,24683,24691,24697,24709,24733,24749,24763,24767,24781,24793,24799,24809,24821,24841,24847,24851,24859,24877,24889,24907,24917,24919,24923,24943,24953,24967,24971,24977,24979,24989,25013,25031,25033,25037,25057,25073,25087,25097,25111,25117,25121,25127,25147,25153,25163,25169,25171]⟩,⟨24630,25217,1142,53,[25219,25229,25237,25243,25247,25253,25261,25301,25303,25307,25309,25321,25339,25343,25349,25357,25367,25373,25391,25409,25411,25423,25439,25447,25453,25457,25463,25469,25471,25523,25537,25541,25561,25577,25579,25583,25589,25601,25603,25609,25621,25633,25639,25643,25657,25667,25673,25679,25693,25703,25717,25733,25741,25747,25759,25763,25771]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands41 {k : ℕ} (h1 : 25218 ≤ k.sqrt) (h2 : k.sqrt < 27030) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨25218,25817,1206,58,[25819,25841,25847,25849,25867,25873,25889,25903,25913,25919,25931,25933,25939,25943,25951,25969,25981,25997,25999,26003,26017,26021,26029,26041,26053,26083,26099,26107,26111,26113,26119,26141,26153,26161,26171,26177,26183,26189,26203,26209,26227,26237,26249,26251,26261,26263,26267,26293,26297,26309,26317,26321,26339,26347,26357,26371,26387,26393,26399,26407,26417,26423]⟩,⟨25818,26447,1292,65,[26449,26459,26479,26489,26497,26501,26513,26539,26557,26561,26573,26591,26597,26627,26633,26641,26647,26669,26681,26683,26687,26693,26699,26701,26711,26713,26717,26723,26729,26731,26737,26759,26777,26783,26801,26813,26821,26833,26839,26849,26861,26863,26879,26881,26891,26893,26903,26921,26927,26947,26951,26953,26959,26981,26987,26993,27011,27017,27031,27043,27059,27061,27067,27073,27077,27091,27103,27107,27109]⟩,⟨26448,27029,1370,71,[27031,27043,27059,27061,27067,27073,27077,27091,27103,27107,27109,27127,27143,27179,27191,27197,27211,27239,27241,27253,27259,27271,27277,27281,27283,27299,27329,27337,27361,27367,27397,27407,27409,27427,27431,27437,27449,27457,27479,27481,27487,27509,27527,27529,27539,27541,27551,27581,27583,27611,27617,27631,27647,27653,27673,27689,27691,27697,27701,27733,27737,27739,27743,27749,27751,27763,27767,27773,27779,27791,27793,27799,27803,27809,27817]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands42 {k : ℕ} (h1 : 27030 ≤ k.sqrt) (h2 : k.sqrt < 29058) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨27030,27695,1082,44,[27697,27701,27733,27737,27739,27743,27749,27751,27763,27767,27773,27779,27791,27793,27799,27803,27809,27817,27823,27827,27847,27851,27883,27893,27901,27917,27919,27941,27943,27947,27953,27961,27967,27983,27997,28001,28019,28027,28031,28051,28057,28069,28081,28087,28097,28099,28109,28111]⟩,⟨27696,28407,1176,50,[28409,28411,28429,28433,28439,28447,28463,28477,28493,28499,28513,28517,28537,28541,28547,28549,28559,28571,28573,28579,28591,28597,28603,28607,28619,28621,28627,28631,28643,28649,28657,28661,28663,28669,28687,28697,28703,28711,28723,28729,28751,28753,28759,28771,28789,28793,28807,28813,28817,28837,28843,28859,28867,28871]⟩,⟨28408,29057,1226,53,[29059,29063,29077,29101,29123,29129,29131,29137,29147,29153,29167,29173,29179,29191,29201,29207,29209,29221,29231,29243,29251,29269,29287,29297,29303,29311,29327,29333,29339,29347,29363,29383,29387,29389,29399,29401,29411,29423,29429,29437,29443,29453,29473,29483,29501,29527,29531,29537,29567,29569,29573,29581,29587,29599,29611,29629,29633]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands43 {k : ℕ} (h1 : 29058 ≤ k.sqrt) (h2 : k.sqrt < 31078) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨29058,29669,1214,51,[29671,29683,29717,29723,29741,29753,29759,29761,29789,29803,29819,29833,29837,29851,29863,29867,29873,29879,29881,29917,29921,29927,29947,29959,29983,29989,30011,30013,30029,30047,30059,30071,30089,30091,30097,30103,30109,30113,30119,30133,30137,30139,30161,30169,30181,30187,30197,30203,30211,30223,30241,30253,30259,30269,30271]⟩,⟨29670,30365,1602,87,[30367,30389,30391,30403,30427,30431,30449,30467,30469,30491,30493,30497,30509,30517,30529,30539,30553,30557,30559,30577,30593,30631,30637,30643,30649,30661,30671,30677,30689,30697,30703,30707,30713,30727,30757,30763,30773,30781,30803,30809,30817,30829,30839,30841,30851,30853,30859,30869,30871,30881,30893,30911,30931,30937,30941,30949,30971,30977,30983,31013,31019,31033,31039,31051,31063,31069,31079,31081,31091,31121,31123,31139,31147,31151,31153,31159,31177,31181,31183,31189,31193,31219,31223,31231,31237,31247,31249,31253,31259,31267,31271]⟩,⟨30366,31077,1302,56,[31079,31081,31091,31121,31123,31139,31147,31151,31153,31159,31177,31181,31183,31189,31193,31219,31223,31231,31237,31247,31249,31253,31259,31267,31271,31277,31307,31319,31321,31327,31333,31337,31357,31379,31387,31391,31393,31397,31469,31477,31481,31489,31511,31513,31517,31531,31541,31543,31547,31567,31573,31583,31601,31607,31627,31643,31649,31657,31663,31667]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands44 {k : ℕ} (h1 : 31078 ≤ k.sqrt) (h2 : k.sqrt < 33408) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨31078,31847,1534,76,[31849,31859,31873,31883,31891,31907,31957,31963,31973,31981,31991,32003,32009,32027,32029,32051,32057,32059,32063,32069,32077,32083,32089,32099,32117,32119,32141,32143,32159,32173,32183,32189,32191,32203,32213,32233,32237,32251,32257,32261,32297,32299,32303,32309,32321,32323,32327,32341,32353,32359,32363,32369,32371,32377,32381,32401,32411,32413,32423,32429,32441,32443,32467,32479,32491,32497,32503,32507,32531,32533,32537,32561,32563,32569,32573,32579,32587,32603,32609,32611]⟩,⟨31848,32619,1800,102,[32621,32633,32647,32653,32687,32693,32707,32713,32717,32719,32749,32771,32779,32783,32789,32797,32801,32803,32831,32833,32839,32843,32869,32887,32909,32911,32917,32933,32939,32941,32957,32969,32971,32983,32987,32993,32999,33013,33023,33029,33037,33049,33053,33071,33073,33083,33091,33107,33113,33119,33149,33151,33161,33179,33181,33191,33199,33203,33211,33223,33247,33287,33289,33301,33311,33317,33329,33331,33343,33347,33349,33353,33359,33377,33391,33403,33409,33413,33427,33457,33461,33469,33479,33487,33493,33503,33521,33529,33533,33547,33563,33569,33577,33581,33587,33589,33599,33601,33613,33617,33619,33623,33629,33637,33641,33647]⟩,⟨32620,33407,1322,54,[33409,33413,33427,33457,33461,33469,33479,33487,33493,33503,33521,33529,33533,33547,33563,33569,33577,33581,33587,33589,33599,33601,33613,33617,33619,33623,33629,33637,33641,33647,33679,33703,33713,33721,33739,33749,33751,33757,33767,33769,33773,33791,33797,33809,33811,33827,33829,33851,33857,33863,33871,33889,33893,33911,33923,33931,33937,33941]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands45 {k : ℕ} (h1 : 33408 ≤ k.sqrt) (h2 : k.sqrt < 35830) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨33408,34211,1352,55,[34213,34217,34231,34253,34259,34261,34267,34273,34283,34297,34301,34303,34313,34319,34327,34337,34351,34361,34367,34369,34381,34403,34421,34429,34439,34457,34469,34471,34483,34487,34499,34501,34511,34513,34519,34537,34543,34549,34583,34589,34591,34603,34607,34613,34631,34649,34651,34667,34673,34679,34687,34693,34703,34721,34729,34739,34747,34757,34759]⟩,⟨34212,34979,1392,57,[34981,35023,35027,35051,35053,35059,35069,35081,35083,35089,35099,35107,35111,35117,35129,35141,35149,35153,35159,35171,35201,35221,35227,35251,35257,35267,35279,35281,35291,35311,35317,35323,35327,35339,35353,35363,35381,35393,35401,35407,35419,35423,35437,35447,35449,35461,35491,35507,35509,35521,35527,35531,35533,35537,35543,35569,35573,35591,35593,35597,35603]⟩,⟨34980,35829,1952,109,[35831,35837,35839,35851,35863,35869,35879,35897,35899,35911,35923,35933,35951,35963,35969,35977,35983,35993,35999,36007,36011,36013,36017,36037,36061,36067,36073,36083,36097,36107,36109,36131,36137,36151,36161,36187,36191,36209,36217,36229,36241,36251,36263,36269,36277,36293,36299,36307,36313,36319,36341,36343,36353,36373,36383,36389,36433,36451,36457,36467,36469,36473,36479,36493,36497,36523,36527,36529,36541,36551,36559,36563,36571,36583,36587,36599,36607,36629,36637,36643,36653,36671,36677,36683,36691,36697,36709,36713,36721,36739,36749,36761,36767,36779,36781,36787,36791,36793,36809,36821,36833,36847,36857,36871,36877,36887,36899,36901,36913,36919,36923,36929,36931]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands46 {k : ℕ} (h1 : 35830 ≤ k.sqrt) (h2 : k.sqrt < 38392) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨35830,36711,1762,87,[36713,36721,36739,36749,36761,36767,36779,36781,36787,36791,36793,36809,36821,36833,36847,36857,36871,36877,36887,36899,36901,36913,36919,36923,36929,36931,36943,36947,36973,36979,36997,37003,37013,37019,37021,37039,37049,37057,37061,37087,37097,37117,37123,37139,37159,37171,37181,37189,37199,37201,37217,37223,37243,37253,37273,37277,37307,37309,37313,37321,37337,37339,37357,37361,37363,37369,37379,37397,37409,37423,37441,37447,37463,37483,37489,37493,37501,37507,37511,37517,37529,37537,37547,37549,37561,37567,37571,37573,37579,37589,37591]⟩,⟨36712,37527,1622,72,[37529,37537,37547,37549,37561,37567,37571,37573,37579,37589,37591,37607,37619,37633,37643,37649,37657,37663,37691,37693,37699,37717,37747,37781,37783,37799,37811,37813,37831,37847,37853,37861,37871,37879,37889,37897,37907,37951,37957,37963,37967,37987,37991,37993,37997,38011,38039,38047,38053,38069,38083,38113,38119,38149,38153,38167,38177,38183,38189,38197,38201,38219,38231,38237,38239,38261,38273,38281,38287,38299,38303,38317,38321,38327,38329,38333]⟩,⟨37528,38391,1714,79,[38393,38431,38447,38449,38453,38459,38461,38501,38543,38557,38561,38567,38569,38593,38603,38609,38611,38629,38639,38651,38653,38669,38671,38677,38693,38699,38707,38711,38713,38723,38729,38737,38747,38749,38767,38783,38791,38803,38821,38833,38839,38851,38861,38867,38873,38891,38903,38917,38921,38923,38933,38953,38959,38971,38977,38993,39019,39023,39041,39043,39047,39079,39089,39097,39103,39107,39113,39119,39133,39139,39157,39161,39163,39181,39191,39199,39209,39217,39227,39229,39233,39239,39241]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands47 {k : ℕ} (h1 : 38392 ≤ k.sqrt) (h2 : k.sqrt < 41130) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨38392,39249,1802,85,[39251,39293,39301,39313,39317,39323,39341,39343,39359,39367,39371,39373,39383,39397,39409,39419,39439,39443,39451,39461,39499,39503,39509,39511,39521,39541,39551,39563,39569,39581,39607,39619,39623,39631,39659,39667,39671,39679,39703,39709,39719,39727,39733,39749,39761,39769,39779,39791,39799,39821,39827,39829,39839,39841,39847,39857,39863,39869,39877,39883,39887,39901,39929,39937,39953,39971,39979,39983,39989,40009,40013,40031,40037,40039,40063,40087,40093,40099,40111,40123,40127,40129,40151,40153,40163,40169,40177,40189,40193]⟩,⟨39250,40125,2020,104,[40127,40129,40151,40153,40163,40169,40177,40189,40193,40213,40231,40237,40241,40253,40277,40283,40289,40343,40351,40357,40361,40387,40423,40427,40429,40433,40459,40471,40483,40487,40493,40499,40507,40519,40529,40531,40543,40559,40577,40583,40591,40597,40609,40627,40637,40639,40693,40697,40699,40709,40739,40751,40759,40763,40771,40787,40801,40813,40819,40823,40829,40841,40847,40849,40853,40867,40879,40883,40897,40903,40927,40933,40939,40949,40961,40973,40993,41011,41017,41023,41039,41047,41051,41057,41077,41081,41113,41117,41131,41141,41143,41149,41161,41177,41179,41183,41189,41201,41203,41213,41221,41227,41231,41233,41243,41257,41263,41269]⟩,⟨40126,41129,1898,90,[41131,41141,41143,41149,41161,41177,41179,41183,41189,41201,41203,41213,41221,41227,41231,41233,41243,41257,41263,41269,41281,41299,41333,41341,41351,41357,41381,41387,41389,41399,41411,41413,41443,41453,41467,41479,41491,41507,41513,41519,41521,41539,41543,41549,41579,41593,41597,41603,41609,41611,41617,41621,41627,41641,41647,41651,41659,41669,41681,41687,41719,41729,41737,41759,41761,41771,41777,41801,41809,41813,41843,41849,41851,41863,41879,41887,41893,41897,41903,41911,41927,41941,41947,41953,41957,41959,41969,41981,41983,41999,42013,42017,42019,42023]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands48 {k : ℕ} (h1 : 41130 ≤ k.sqrt) (h2 : k.sqrt < 44058) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨41130,42167,1890,87,[42169,42179,42181,42187,42193,42197,42209,42221,42223,42227,42239,42257,42281,42283,42293,42299,42307,42323,42331,42337,42349,42359,42373,42379,42391,42397,42403,42407,42409,42433,42437,42443,42451,42457,42461,42463,42467,42473,42487,42491,42499,42509,42533,42557,42569,42571,42577,42589,42611,42641,42643,42649,42667,42677,42683,42689,42697,42701,42703,42709,42719,42727,42737,42743,42751,42767,42773,42787,42793,42797,42821,42829,42839,42841,42853,42859,42863,42899,42901,42923,42929,42937,42943,42953,42961,42967,42979,42989,43003,43013,43019]⟩,⟨42168,43065,2114,106,[43067,43093,43103,43117,43133,43151,43159,43177,43189,43201,43207,43223,43237,43261,43271,43283,43291,43313,43319,43321,43331,43391,43397,43399,43403,43411,43427,43441,43451,43457,43481,43487,43499,43517,43541,43543,43573,43577,43579,43591,43597,43607,43609,43613,43627,43633,43649,43651,43661,43669,43691,43711,43717,43721,43753,43759,43777,43781,43783,43787,43789,43793,43801,43853,43867,43889,43891,43913,43933,43943,43951,43961,43963,43969,43973,43987,43991,43997,44017,44021,44027,44029,44041,44053,44059,44071,44087,44089,44101,44111,44119,44123,44129,44131,44159,44171,44179,44189,44201,44203,44207,44221,44249,44257,44263,44267,44269,44273,44279,44281]⟩,⟨43066,44057,1922,86,[44059,44071,44087,44089,44101,44111,44119,44123,44129,44131,44159,44171,44179,44189,44201,44203,44207,44221,44249,44257,44263,44267,44269,44273,44279,44281,44293,44351,44357,44371,44381,44383,44389,44417,44449,44453,44483,44491,44497,44501,44507,44519,44531,44533,44537,44543,44549,44563,44579,44587,44617,44621,44623,44633,44641,44647,44651,44657,44683,44687,44699,44701,44711,44729,44741,44753,44771,44773,44777,44789,44797,44809,44819,44839,44843,44851,44867,44879,44887,44893,44909,44917,44927,44939,44953,44959,44963,44971,44983,44987]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands49 {k : ℕ} (h1 : 44058 ≤ k.sqrt) (h2 : k.sqrt < 47058) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨44058,44981,1812,75,[44983,44987,45007,45013,45053,45061,45077,45083,45119,45121,45127,45131,45137,45139,45161,45179,45181,45191,45197,45233,45247,45259,45263,45281,45289,45293,45307,45317,45319,45329,45337,45341,45343,45361,45377,45389,45403,45413,45427,45433,45439,45481,45491,45497,45503,45523,45533,45541,45553,45557,45569,45587,45589,45599,45613,45631,45641,45659,45667,45673,45677,45691,45697,45707,45737,45751,45757,45763,45767,45779,45817,45821,45823,45827,45833,45841,45853,45863,45869]⟩,⟨44982,45987,1896,80,[45989,46021,46027,46049,46051,46061,46073,46091,46093,46099,46103,46133,46141,46147,46153,46171,46181,46183,46187,46199,46219,46229,46237,46261,46271,46273,46279,46301,46307,46309,46327,46337,46349,46351,46381,46399,46411,46439,46441,46447,46451,46457,46471,46477,46489,46499,46507,46511,46523,46549,46559,46567,46573,46589,46591,46601,46619,46633,46639,46643,46649,46663,46679,46681,46687,46691,46703,46723,46727,46747,46751,46757,46769,46771,46807,46811,46817,46819,46829,46831,46853,46861,46867,46877]⟩,⟨45988,47057,1994,87,[47059,47087,47093,47111,47119,47123,47129,47137,47143,47147,47149,47161,47189,47207,47221,47237,47251,47269,47279,47287,47293,47297,47303,47309,47317,47339,47351,47353,47363,47381,47387,47389,47407,47417,47419,47431,47441,47459,47491,47497,47501,47507,47513,47521,47527,47533,47543,47563,47569,47581,47591,47599,47609,47623,47629,47639,47653,47657,47659,47681,47699,47701,47711,47713,47717,47737,47741,47743,47777,47779,47791,47797,47807,47809,47819,47837,47843,47857,47869,47881,47903,47911,47917,47933,47939,47947,47951,47963,47969,47977,47981]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands50 {k : ℕ} (h1 : 47058 ≤ k.sqrt) (h2 : k.sqrt < 50362) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨47058,48155,2154,99,[48157,48163,48179,48187,48193,48197,48221,48239,48247,48259,48271,48281,48299,48311,48313,48337,48341,48353,48371,48383,48397,48407,48409,48413,48437,48449,48463,48473,48479,48481,48487,48491,48497,48523,48527,48533,48539,48541,48563,48571,48589,48593,48611,48619,48623,48647,48649,48661,48673,48677,48679,48731,48733,48751,48757,48761,48767,48779,48781,48787,48799,48809,48817,48821,48823,48847,48857,48859,48869,48871,48883,48889,48907,48947,48953,48973,48989,48991,49003,49009,49019,49031,49033,49037,49043,49057,49069,49081,49103,49109,49117,49121,49123,49139,49157,49169,49171,49177,49193,49199,49201,49207,49211]⟩,⟨48156,49277,1998,83,[49279,49297,49307,49331,49333,49339,49363,49367,49369,49391,49393,49409,49411,49417,49429,49433,49451,49459,49463,49477,49481,49499,49523,49529,49531,49537,49547,49549,49559,49597,49603,49613,49627,49633,49639,49663,49667,49669,49681,49697,49711,49727,49739,49741,49747,49757,49783,49787,49789,49801,49807,49811,49823,49831,49843,49853,49871,49877,49891,49919,49921,49927,49937,49939,49943,49957,49991,49993,49999,50021,50023,50033,50047,50051,50053,50069,50077,50087,50093,50101,50111,50119,50123,50129,50131,50147,50153]⟩,⟨49278,50361,2336,111,[50363,50377,50383,50387,50411,50417,50423,50441,50459,50461,50497,50503,50513,50527,50539,50543,50549,50551,50581,50587,50591,50593,50599,50627,50647,50651,50671,50683,50707,50723,50741,50753,50767,50773,50777,50789,50821,50833,50839,50849,50857,50867,50873,50891,50893,50909,50923,50929,50951,50957,50969,50971,50989,50993,51001,51031,51043,51047,51059,51061,51071,51109,51131,51133,51137,51151,51157,51169,51193,51197,51199,51203,51217,51229,51239,51241,51257,51263,51283,51287,51307,51329,51341,51343,51347,51349,51361,51383,51407,51413,51419,51421,51427,51431,51437,51439,51449,51461,51473,51479,51481,51487,51503,51511,51517,51521,51539,51551,51563,51577,51581,51593,51599,51607,51613]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands51 {k : ℕ} (h1 : 50362 ≤ k.sqrt) (h2 : k.sqrt < 53848) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨50362,51485,2030,82,[51487,51503,51511,51517,51521,51539,51551,51563,51577,51581,51593,51599,51607,51613,51631,51637,51647,51659,51673,51679,51683,51691,51713,51719,51721,51749,51767,51769,51787,51797,51803,51817,51827,51829,51839,51853,51859,51869,51871,51893,51899,51907,51913,51929,51941,51949,51971,51973,51977,51991,52009,52021,52027,52051,52057,52067,52069,52081,52103,52121,52127,52147,52153,52163,52177,52181,52183,52189,52201,52223,52237,52249,52253,52259,52267,52289,52291,52301,52313,52321,52361,52363,52369,52379,52387,52391]⟩,⟨51486,52665,2442,116,[52667,52673,52691,52697,52709,52711,52721,52727,52733,52747,52757,52769,52783,52807,52813,52817,52837,52859,52861,52879,52883,52889,52901,52903,52919,52937,52951,52957,52963,52967,52973,52981,52999,53003,53017,53047,53051,53069,53077,53087,53089,53093,53101,53113,53117,53129,53147,53149,53161,53171,53173,53189,53197,53201,53231,53233,53239,53267,53269,53279,53281,53299,53309,53323,53327,53353,53359,53377,53381,53401,53407,53411,53419,53437,53441,53453,53479,53503,53507,53527,53549,53551,53569,53591,53593,53597,53609,53611,53617,53623,53629,53633,53639,53653,53657,53681,53693,53699,53717,53719,53731,53759,53773,53777,53783,53791,53813,53819,53831,53849,53857,53861,53881,53887,53891,53897,53899,53917,53923,53927]⟩,⟨52666,53847,2062,81,[53849,53857,53861,53881,53887,53891,53897,53899,53917,53923,53927,53939,53951,53959,53987,53993,54001,54011,54013,54037,54049,54059,54083,54091,54101,54121,54133,54139,54151,54163,54167,54181,54193,54217,54251,54269,54277,54287,54293,54311,54319,54323,54331,54347,54361,54367,54371,54377,54401,54403,54409,54413,54419,54421,54437,54443,54449,54469,54493,54497,54499,54503,54517,54521,54539,54541,54547,54559,54563,54577,54581,54583,54601,54617,54623,54629,54631,54647,54667,54673,54679,54709,54713,54721,54727]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands52 {k : ℕ} (h1 : 53848 ≤ k.sqrt) (h2 : k.sqrt < 57718) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨53848,55071,2686,134,[55073,55079,55103,55109,55117,55127,55147,55163,55171,55201,55207,55213,55217,55219,55229,55243,55249,55259,55291,55313,55331,55333,55337,55339,55343,55351,55373,55381,55399,55411,55439,55441,55457,55469,55487,55501,55511,55529,55541,55547,55579,55589,55603,55609,55619,55621,55631,55633,55639,55661,55663,55667,55673,55681,55691,55697,55711,55717,55721,55733,55763,55787,55793,55799,55807,55813,55817,55819,55823,55829,55837,55843,55849,55871,55889,55897,55901,55903,55921,55927,55931,55933,55949,55967,55987,55997,56003,56009,56039,56041,56053,56081,56087,56093,56099,56101,56113,56123,56131,56149,56167,56171,56179,56197,56207,56209,56237,56239,56249,56263,56267,56269,56299,56311,56333,56359,56369,56377,56383,56393,56401,56417,56431,56437,56443,56453,56467,56473,56477,56479,56489,56501,56503,56509,56519,56527,56531,56533]⟩,⟨55072,56415,2318,98,[56417,56431,56437,56443,56453,56467,56473,56477,56479,56489,56501,56503,56509,56519,56527,56531,56533,56543,56569,56591,56597,56599,56611,56629,56633,56659,56663,56671,56681,56687,56701,56711,56713,56731,56737,56747,56767,56773,56779,56783,56807,56809,56813,56821,56827,56843,56857,56873,56891,56893,56897,56909,56911,56921,56923,56929,56941,56951,56957,56963,56983,56989,56993,56999,57037,57041,57047,57059,57073,57077,57089,57097,57107,57119,57131,57139,57143,57149,57163,57173,57179,57191,57193,57203,57221,57223,57241,57251,57259,57269,57271,57283,57287,57301,57329,57331,57347,57349,57367,57373,57383,57389]⟩,⟨56416,57717,2828,142,[57719,57727,57731,57737,57751,57773,57781,57787,57791,57793,57803,57809,57829,57839,57847,57853,57859,57881,57899,57901,57917,57923,57943,57947,57973,57977,57991,58013,58027,58031,58043,58049,58057,58061,58067,58073,58099,58109,58111,58129,58147,58151,58153,58169,58171,58189,58193,58199,58207,58211,58217,58229,58231,58237,58243,58271,58309,58313,58321,58337,58363,58367,58369,58379,58391,58393,58403,58411,58417,58427,58439,58441,58451,58453,58477,58481,58511,58537,58543,58549,58567,58573,58579,58601,58603,58613,58631,58657,58661,58679,58687,58693,58699,58711,58727,58733,58741,58757,58763,58771,58787,58789,58831,58889,58897,58901,58907,58909,58913,58921,58937,58943,58963,58967,58979,58991,58997,59009,59011,59021,59023,59029,59051,59053,59063,59069,59077,59083,59093,59107,59113,59119,59123,59141,59149,59159,59167,59183,59197,59207,59209,59219,59221,59233,59239,59243]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands53 {k : ℕ} (h1 : 57718 ≤ k.sqrt) (h2 : k.sqrt < 61602) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨57718,59027,2450,104,[59029,59051,59053,59063,59069,59077,59083,59093,59107,59113,59119,59123,59141,59149,59159,59167,59183,59197,59207,59209,59219,59221,59233,59239,59243,59263,59273,59281,59333,59341,59351,59357,59359,59369,59377,59387,59393,59399,59407,59417,59419,59441,59443,59447,59453,59467,59471,59473,59497,59509,59513,59539,59557,59561,59567,59581,59611,59617,59621,59627,59629,59651,59659,59663,59669,59671,59693,59699,59707,59723,59729,59743,59747,59753,59771,59779,59791,59797,59809,59833,59863,59879,59887,59921,59929,59951,59957,59971,59981,59999,60013,60017,60029,60037,60041,60077,60083,60089,60091,60101,60103,60107,60127,60133,60139,60149,60161,60167]⟩,⟨59028,60291,2660,120,[60293,60317,60331,60337,60343,60353,60373,60383,60397,60413,60427,60443,60449,60457,60493,60497,60509,60521,60527,60539,60589,60601,60607,60611,60617,60623,60631,60637,60647,60649,60659,60661,60679,60689,60703,60719,60727,60733,60737,60757,60761,60763,60773,60779,60793,60811,60821,60859,60869,60887,60889,60899,60901,60913,60917,60919,60923,60937,60943,60953,60961,61001,61007,61027,61031,61043,61051,61057,61091,61099,61121,61129,61141,61151,61153,61169,61211,61223,61231,61253,61261,61283,61291,61297,61331,61333,61339,61343,61357,61363,61379,61381,61403,61409,61417,61441,61463,61469,61471,61483,61487,61493,61507,61511,61519,61543,61547,61553,61559,61561,61583,61603,61609,61613,61627,61631,61637,61643,61651,61657,61667,61673,61681,61687]⟩,⟨60292,61601,2698,121,[61603,61609,61613,61627,61631,61637,61643,61651,61657,61667,61673,61681,61687,61703,61717,61723,61729,61751,61757,61781,61813,61819,61837,61843,61861,61871,61879,61909,61927,61933,61949,61961,61967,61979,61981,61987,61991,62003,62011,62017,62039,62047,62053,62057,62071,62081,62099,62119,62129,62131,62137,62141,62143,62171,62189,62191,62201,62207,62213,62219,62233,62273,62297,62299,62303,62311,62323,62327,62347,62351,62383,62401,62417,62423,62459,62467,62473,62477,62483,62497,62501,62507,62533,62539,62549,62563,62581,62591,62597,62603,62617,62627,62633,62639,62653,62659,62683,62687,62701,62723,62731,62743,62753,62761,62773,62791,62801,62819,62827,62851,62861,62869,62873,62897,62903,62921,62927,62929,62939,62969,62971,62981,62983,62987,62989]⟩]) (by decide +kernel) h1 h2

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem bands54 {k : ℕ} (h1 : 61602 ≤ k.sqrt) (h2 : k.sqrt < 65826) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := band_range (vs := [⟨61602,62985,2256,83,[62987,62989,63029,63031,63059,63067,63073,63079,63097,63103,63113,63127,63131,63149,63179,63197,63199,63211,63241,63247,63277,63281,63299,63311,63313,63317,63331,63337,63347,63353,63361,63367,63377,63389,63391,63397,63409,63419,63421,63439,63443,63463,63467,63473,63487,63493,63499,63521,63527,63533,63541,63559,63577,63587,63589,63599,63601,63607,63611,63617,63629,63647,63649,63659,63667,63671,63689,63691,63697,63703,63709,63719,63727,63737,63743,63761,63773,63781,63793,63799,63803,63809,63823,63839,63841,63853,63857]⟩,⟨62986,64401,2746,120,[64403,64433,64439,64451,64453,64483,64489,64499,64513,64553,64567,64577,64579,64591,64601,64609,64613,64621,64627,64633,64661,64663,64667,64679,64693,64709,64717,64747,64763,64781,64783,64793,64811,64817,64849,64853,64871,64877,64879,64891,64901,64919,64921,64927,64937,64951,64969,64997,65003,65011,65027,65029,65033,65053,65063,65071,65089,65099,65101,65111,65119,65123,65129,65141,65147,65167,65171,65173,65179,65183,65203,65213,65239,65257,65267,65269,65287,65293,65309,65323,65327,65353,65357,65371,65381,65393,65407,65413,65419,65423,65437,65447,65449,65479,65497,65519,65521,65537,65539,65543,65551,65557,65563,65579,65581,65587,65599,65609,65617,65629,65633,65647,65651,65657,65677,65687,65699,65701,65707,65713,65717,65719,65729,65731]⟩,⟨64402,65825,3178,157,[65827,65831,65837,65839,65843,65851,65867,65881,65899,65921,65927,65929,65951,65957,65963,65981,65983,65993,66029,66037,66041,66047,66067,66071,66083,66089,66103,66107,66109,66137,66161,66169,66173,66179,66191,66221,66239,66271,66293,66301,66337,66343,66347,66359,66361,66373,66377,66383,66403,66413,66431,66449,66457,66463,66467,66491,66499,66509,66523,66529,66533,66541,66553,66569,66571,66587,66593,66601,66617,66629,66643,66653,66683,66697,66701,66713,66721,66733,66739,66749,66751,66763,66791,66797,66809,66821,66841,66851,66853,66863,66877,66883,66889,66919,66923,66931,66943,66947,66949,66959,66973,66977,67003,67021,67033,67043,67049,67057,67061,67073,67079,67103,67121,67129,67139,67141,67153,67157,67169,67181,67187,67189,67211,67213,67217,67219,67231,67247,67261,67271,67273,67289,67307,67339,67343,67349,67369,67391,67399,67409,67411,67421,67427,67429,67433,67447,67453,67477,67481,67489,67493,67499,67511,67523,67531,67537,67547,67559,67567,67577,67579]⟩]) (by decide +kernel) h1 h2

theorem bands_coverage {k : ℕ} (h1 : 1536 ≤ k.sqrt) (h2 : k.sqrt < 65536) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := by
  by_cases h1 : k.sqrt < 9180
  · by_cases h2 : k.sqrt < 3270
    · by_cases h3 : k.sqrt < 2130
      · by_cases h4 : k.sqrt < 1776
        · by_cases h5 : k.sqrt < 1620
          · exact bands0 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 1696
            · exact bands1 (by omega) (by omega)
            · exact bands2 (by omega) (by omega)
        · by_cases h5 : k.sqrt < 1870
          · exact bands3 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 1996
            · exact bands4 (by omega) (by omega)
            · exact bands5 (by omega) (by omega)
      · by_cases h4 : k.sqrt < 2530
        · by_cases h5 : k.sqrt < 2266
          · exact bands6 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 2422
            · exact bands7 (by omega) (by omega)
            · exact bands8 (by omega) (by omega)
        · by_cases h5 : k.sqrt < 2908
          · by_cases h6 : k.sqrt < 2748
            · exact bands9 (by omega) (by omega)
            · exact bands10 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 3066
            · exact bands11 (by omega) (by omega)
            · exact bands12 (by omega) (by omega)
    · by_cases h3 : k.sqrt < 5440
      · by_cases h4 : k.sqrt < 4090
        · by_cases h5 : k.sqrt < 3528
          · exact bands13 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 3792
            · exact bands14 (by omega) (by omega)
            · exact bands15 (by omega) (by omega)
        · by_cases h5 : k.sqrt < 4702
          · by_cases h6 : k.sqrt < 4390
            · exact bands16 (by omega) (by omega)
            · exact bands17 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 5058
            · exact bands18 (by omega) (by omega)
            · exact bands19 (by omega) (by omega)
      · by_cases h4 : k.sqrt < 6790
        · by_cases h5 : k.sqrt < 5850
          · exact bands20 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 6310
            · exact bands21 (by omega) (by omega)
            · exact bands22 (by omega) (by omega)
        · by_cases h5 : k.sqrt < 7872
          · by_cases h6 : k.sqrt < 7296
            · exact bands23 (by omega) (by omega)
            · exact bands24 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 8500
            · exact bands25 (by omega) (by omega)
            · exact bands26 (by omega) (by omega)
  · by_cases h2 : k.sqrt < 25218
    · by_cases h3 : k.sqrt < 15288
      · by_cases h4 : k.sqrt < 11350
        · by_cases h5 : k.sqrt < 9882
          · exact bands27 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 10606
            · exact bands28 (by omega) (by omega)
            · exact bands29 (by omega) (by omega)
        · by_cases h5 : k.sqrt < 13176
          · by_cases h6 : k.sqrt < 12250
            · exact bands30 (by omega) (by omega)
            · exact bands31 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 14148
            · exact bands32 (by omega) (by omega)
            · exact bands33 (by omega) (by omega)
      · by_cases h4 : k.sqrt < 18916
        · by_cases h5 : k.sqrt < 16410
          · exact bands34 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 17656
            · exact bands35 (by omega) (by omega)
            · exact bands36 (by omega) (by omega)
        · by_cases h5 : k.sqrt < 21928
          · by_cases h6 : k.sqrt < 20358
            · exact bands37 (by omega) (by omega)
            · exact bands38 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 23628
            · exact bands39 (by omega) (by omega)
            · exact bands40 (by omega) (by omega)
    · by_cases h3 : k.sqrt < 41130
      · by_cases h4 : k.sqrt < 31078
        · by_cases h5 : k.sqrt < 27030
          · exact bands41 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 29058
            · exact bands42 (by omega) (by omega)
            · exact bands43 (by omega) (by omega)
        · by_cases h5 : k.sqrt < 35830
          · by_cases h6 : k.sqrt < 33408
            · exact bands44 (by omega) (by omega)
            · exact bands45 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 38392
            · exact bands46 (by omega) (by omega)
            · exact bands47 (by omega) (by omega)
      · by_cases h4 : k.sqrt < 50362
        · by_cases h5 : k.sqrt < 44058
          · exact bands48 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 47058
            · exact bands49 (by omega) (by omega)
            · exact bands50 (by omega) (by omega)
        · by_cases h5 : k.sqrt < 57718
          · by_cases h6 : k.sqrt < 53848
            · exact bands51 (by omega) (by omega)
            · exact bands52 (by omega) (by omega)
          · by_cases h6 : k.sqrt < 61602
            · exact bands53 (by omega) (by omega)
            · exact bands54 (by omega) (by omega)

private theorem checked_small : ∀ i : Fin 114,
    (fun (k p : ℕ) => (fun p : ℕ => if p ≤ 17 then [3,5,7,11,13,17].contains p else if p ≤ 263 then p.gcd (Nat.factorial 17) == 1 else decide (p ≤ 263*263) && (p.gcd (Nat.factorial 263) == 1)) p && decide (p ≠ 2 ∧ p ≤ k%p + k/p%p)) (79+i.val) ((#[3,3,7,7,7,5,11,3,7,3,3,7,11,5,5,5,3,5,3,3,5,13,11,11,11,3,11,3,3,11,5,13,7,11,3,5,3,3,5,5,5,11,5,3,5,3,3,13,13,13,7,7,3,7,3,3,7,7,7,5,5,3,7,3,3,5,7,5,5,5,3,13,3,3,11,13,13,23,13,3,5,3,3,11,5,5,13,7,3,5,3,3,5,5,5,5,11,3,17,3,3,7,7,11,11,5,3,7,3,3,5,7,7,5] : Array ℕ)[i.val]!) = true := by decide +kernel

theorem small_coverage {k : ℕ} (h1 : 78 < k) (h2 : k < 193) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k%p + k/p%p := by
  let i : Fin 114 := ⟨k-79,by omega⟩
  have h := checked_small i
  have he : 79+i.val = k := by dsimp [i]; omega
  rw [he] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨_,primeTest_sound h.1,h.2⟩

theorem strong {k : ℕ} (h1 : 192 < k) (h2 : k < 2^32) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p := by
  change ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ k < p*p ∧ p ≤ k%p + k/p%p
  by_cases h : k < 2359296
  · exact direct_coverage (by omega) h
  · apply bands_coverage
    · exact Nat.le_sqrt.mpr (by omega)
    · exact Nat.sqrt_lt.mpr (by omega)

theorem weak {k : ℕ} (h1 : 78 < k) (h2 : k < 2^32) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ≤ k%p + k/p%p := by
  by_cases h : k < 193
  · exact small_coverage h1 h
  · obtain ⟨p,hp,hn,_,hd⟩ := strong (by omega) h2
    exact ⟨p,hp,hn,hd⟩

theorem main : H1 → H2 → type_of% @OMA.S_mo_499750.main := by
  intro hLower hUpper k hk
  by_cases h : k < 2^32
  · exact weak hk h
  · obtain ⟨p,hp,hodd,_,hd⟩ := of_dusart_tail hLower hUpper (k := k) (by omega)
    exact ⟨p,hp,hodd,hd⟩

end OMA.R_mo_499750_R2
