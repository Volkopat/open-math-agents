import OMAStatements.S_oeis_a083143

-- Credit: @Aryan-Poonacha
-- Shifted digit windows and the Cauchy–Davenport theorem.

namespace PalBlocks
open scoped Pointwise
open Finset

private def val (d : List ℕ) := Nat.ofDigits 10 d

private def eval {p : ℕ} (u v : ZMod p) (d : List ℕ) : ZMod p :=
  u * (val d : ℕ) + v * (val d.reverse : ℕ)

private noncomputable def block (p len : ℕ) (u v : ZMod p) : Finset (ZMod p) :=
  (List.fixedLengthDigits (by decide : 1 < 10) len).image (eval u v)

private lemma block_mem {p len : ℕ} (u v : ZMod p) {d : List ℕ}
    (hl : d.length = len) (hd : ∀ i ∈ d, i < 10) : eval u v d ∈ block p len u v :=
  Finset.mem_image.mpr ⟨d, (List.mem_fixedLengthDigits_iff (by decide : 1 < 10)).mpr ⟨hl,hd⟩, rfl⟩

/-- A complete mirrored decimal word of length len+1 has at least √p
attainable residues for arbitrary reverse coefficient. -/
theorem card_block (p len : ℕ) [Fact p.Prime] (hllen : p ≤ 10^len)
    (u v : ZMod p) (hu : (99 : ZMod p)*u ≠ 0) :
    p ≤ (block p (len+1) u v).card ^ 2 := by
  classical
  let B := block p (len+1) u v
  let w (x : ZMod p) := Nat.digitsAppend 10 len x.val
  have hw (x : ZMod p) := (Nat.bijOn_digitsAppend' (by decide : 1 < 10) len).mapsTo
    (show x.val ∈ ((Finset.range (10 ^ len) : Finset ℕ) : Set ℕ) by
      simpa using x.val_lt.trans_le hllen)
  have wprop (x : ZMod p) := (List.mem_fixedLengthDigits_iff (by decide : 1 < 10)).mp (hw x)
  let F (x : ZMod p) := (eval u v (w x ++ [0]), eval u v (0 :: w x))
  have hf (x : ZMod p) : F x ∈ B ×ˢ B := by
    obtain ⟨hl,hd⟩ := wprop x
    change (w x).length = len at hl
    change ∀ i ∈ w x, i < 10 at hd
    apply mem_product.mpr
    constructor
    · apply block_mem _ _ (by simp [hl]); intro i hi; simp at hi; rcases hi with hi | rfl; exact hd _ hi; decide
    · apply block_mem _ _ (by simp [hl]);simpa using hd
  have recover (x : ZMod p) : 10*(F x).2 - (F x).1 = (99:ZMod p)*u*x := by
    have hx : (val (w x) : ℕ) = x.val := by
      simp [val,w,Nat.digitsAppend,Nat.ofDigits_append_replicate_zero,Nat.ofDigits_digits]
    simp only [F,eval,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append,
      val,Nat.ofDigits_append_zero,Nat.ofDigits_cons,Nat.cast_mul,
      Nat.cast_ofNat, zero_add]
    change 10 * (u*(10 * (val (w x):ℕ)) + v*(val (w x).reverse:ℕ)) -
      (u*(val (w x):ℕ)+v*(10*(val (w x).reverse:ℕ))) = _
    rw [hx,ZMod.natCast_zmod_val]
    ring
  have hi : Function.Injective F := by
    intro x y h
    apply mul_left_cancel₀ hu
    rw [←recover,←recover,h]
  have H := Finset.card_le_card_of_injOn F (s:=Finset.univ) (t:=B ×ˢ B)
    (fun x _ => hf x) hi.injOn
  simpa [B,pow_two] using H


private theorem card_many (p len q k : ℕ) [Fact p.Prime] (hllen : p≤10^len)
    (hq : q^2<p) (h10 : (10:ZMod p)≠0) :
    ∀ (n : ℕ) (u v : ZMod p), k*(len+1) ≤ n → (99:ZMod p)*u≠0 →
       min p (1+k*q) ≤ (block p n u v).card := by
  induction k with
  | zero =>
    intro n u v _ _
    have hne : (block p n u v).Nonempty :=
      ⟨_,block_mem _ _ (d:=List.replicate n 0) (by simp) (by simp)⟩
    exact (min_le_right ..).trans (by simpa using hne.card_pos)
  | succ k ih =>
    intro n u v hn hu
    let s := len+1
    let j := n-s
    have he : j+s=n := Nat.sub_add_cancel (by dsimp [s];nlinarith)
    let X := block p j u (v*10^s)
    let Y := block p s (u*10^j) v
    have HX : min p (1+k*q) ≤ X.card := ih _ _ _ (by dsimp [j,s];rw [Nat.succ_mul] at hn;omega) hu
    have YY := card_block p len hllen (u*10^j) v (by rw [←mul_assoc]; exact mul_ne_zero hu (pow_ne_zero _ h10))
    have HY : q+1 ≤ Y.card := by
      change p ≤ Y.card^2 at YY
      by_contra! h
      have H := Nat.pow_le_pow_left (show Y.card≤q by omega) 2
      omega
    have HXne : X.Nonempty := by
      apply Finset.card_pos.mp
      have hp := (Fact.out (p:=p.Prime)).pos
      omega
    have HYne : Y.Nonempty := Finset.card_pos.mp (by omega)
    have sub : X+Y ⊆ block p n u v := by
      intro x hx
      obtain ⟨x,hx1,y,hy,rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hx1
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hl,hd⟩ := (List.mem_fixedLengthDigits_iff (by decide : 1<10)).mp hl
      obtain ⟨hb,hd'⟩ := (List.mem_fixedLengthDigits_iff (by decide : 1<10)).mp hb
      refine Finset.mem_image.mpr ⟨l++b,(List.mem_fixedLengthDigits_iff (by decide : 1<10)).mpr ⟨by simp_all,?_⟩,?_⟩
      · intro i hi;rcases List.mem_append.mp hi with hi | hi
        exact hd _ hi
        exact hd' _ hi
      · simp [eval,val,Nat.ofDigits_append,hl,hb]
        ring
    have CD := (ZMod.cauchy_davenport (Fact.out (p:=p.Prime)) HXne HYne).trans (Finset.card_le_card sub)
    rw [Nat.succ_mul]
    omega


theorem palindrome_of_blocks (n p len q k : ℕ) [Fact p.Prime] (hn : 2 ≤ n)
    (hllen : p≤10^len) (hq : q^2<p) (h10 : (10:ZMod p)≠0)
    (hu : (99:ZMod p)*10≠0) (hblocks : k*(len+1)≤n/2-1) (hcover : p≤1+k*q) :
    ∃ m : ℕ, 0 < m ∧ (Nat.digits 10 m).length = n ∧ (Nat.digits 10 m).Palindrome ∧ p ∣ m := by
  classical
  let h := n/2-1
  let r := n%2
  let v : ZMod p := 10^(1+h+r)
  let X := block p h 10 v
  have CX := card_many p len q k hllen hq h10 h 10 v hblocks hu
  rw [min_eq_left hcover] at CX
  have HX : X=Finset.univ := X.eq_univ_of_card (by
    rw [ZMod.card];exact le_antisymm (by simpa [X] using X.card_le_univ) CX)
  have xmem : -(1+10^(n-1) : ZMod p) ∈ X := by rw [HX];simp
  obtain ⟨l,hl,he⟩ := Finset.mem_image.mp xmem
  obtain ⟨hl,hd⟩ := (List.mem_fixedLengthDigits_iff (by decide : 1<10)).mp hl
  let parts := l ++ List.replicate r 0 ++ l.reverse
  let word := 1 :: (parts ++ [1])
  have lenh : 2*h+r+2=n := by dsimp [h,r];omega
  have plen : parts.length=2*h+r := by simp [parts,hl];omega
  have dig : Nat.digits 10 (val word)=word := by
    apply Nat.digits_ofDigits 10 (by decide)
    · intro a ha
      simp [word,parts] at ha
      grind
    · intro ha
      simp [word]
  refine ⟨val word,?_,?_,?_,?_⟩
  · by_contra! hz
    have : val word=0 := by omega
    simp [this,word] at dig
  · rw [dig];simp [word,plen];omega
  · rw [dig];apply List.Palindrome.of_reverse_eq
    simp [word,parts,List.append_assoc]
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    have wh : val word = 1 + 10*val l + 10^(1+h+r)*val l.reverse + 10^(n-1) := by
      have hn' : n-1=(2*h+r)+1 := by omega
      simp [word,val,Nat.ofDigits_cons,Nat.ofDigits_append,Nat.ofDigits_replicate_zero,
        parts,hl,hn',pow_add,pow_succ]
      ring
    rw [wh]
    push_cast
    change 10*(val l:ℕ)+(10:ZMod p)^(1+h+r)*(val l.reverse:ℕ)=_ at he
    linear_combination he


private theorem primeSizeTwo (p len : ℕ) (hp : 2 ≤ p) (hl : p < 2^len) :
    p ≤ len*(p.primeCounting+1) := by
  have hp' : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
  have h2 := Real.log_pos (show (1:ℝ)<2 by norm_num)
  have hp10 : (p:ℝ)+1≤(2:ℝ)^len := by exact_mod_cast hl
  have hb := Real.log_le_log (show (0:ℝ)<p+1 by positivity) hp10
  rw [Real.log_pow] at hb
  have hb' := (Real.log_le_log (by positivity : (0:ℝ)<p) (show (p:ℝ)≤p+1 by linarith)).trans hb
  have H := (div_le_iff₀ (Real.log_pos hp')).mp (Chebyshev.pi_ge p)
  have H' : (p:ℝ)*Real.log 2 ≤ (p.primeCounting+1:ℝ)*(len*Real.log 2) := by
    nlinarith only [H,hb,mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg p.primeCounting)]
  have hfinal' : (p:ℝ)*Real.log 2 ≤ (len*(p.primeCounting+1):ℝ)*Real.log 2 := by
    nlinarith only [H']
  exact_mod_cast (le_of_mul_le_mul_right hfinal' h2)

private theorem primeSize (p len : ℕ) (hp : 2≤p) (hl : p < 10^len) :
    p ≤ 4*len*(p.primeCounting+1) := by
  apply primeSizeTwo _ _ hp
  exact hl.trans_le (by rw [pow_mul];exact Nat.pow_le_pow_left (by decide) _)

private theorem square_ge (L : ℕ) (hL : 6≤L) :
    (16*(L+1)*(L+2))^2 < 10^L := by
  induction L,hL using Nat.le_induction with
  | base => decide
  | succ L hL ih =>
    rw [show 10^(L+1)=10^L*10 by ring]
    have h1 : 16*(L+2)*(L+3) ≤ 2*(16*(L+1)*(L+2)) := by nlinarith
    have H := Nat.pow_le_pow_left h1 2
    nlinarith

private theorem enough (n p len : ℕ) (hL : 1 ≤ len)
    (hs : p ≤ 4*len*(n+1)) (hp : (16*len*(len+1))^2<p) :
    let k := (n/2-1)/(len+1)
    p ≤ 1+k*(16*len*(len+1)) := by
  let k := (n/2-1)/(len+1)
  change p ≤ 1+k*(16*len*(len+1))
  have hr : n/2-1 < (k+1)*(len+1) := by simpa [k,Nat.mul_comm] using Nat.lt_mul_div_succ (n/2-1) (Nat.zero_lt_succ len)
  have hlower : 4*(len+1)+4 ≤ n := by
    by_contra! H
    have U := Nat.mul_le_mul_left (4*len) (show n+1 ≤ 4*(len+1)+4 by omega)
    nlinarith [Nat.zero_le (len^2),Nat.zero_le (len^3),Nat.zero_le (len^4)]
  have H : n+1 ≤ 4*(k*(len+1)) := by
    rw [Nat.add_mul] at hr
    omega
  have U := Nat.mul_le_mul_left (4*len) H
  nlinarith only [hs,U]

theorem large (p : ℕ) [Fact p.Prime] (hp : 1000000 ≤ p) :
    ∃ m : ℕ, 0 < m ∧ (Nat.digits 10 m).length = p.primeCounting ∧ (Nat.digits 10 m).Palindrome ∧ p ∣ m := by
  let L := Nat.log 10 p
  have H : 6 ≤ L := (Nat.le_log_iff_pow_le (by decide : 1<10) (by omega)).mpr (by simpa using hp)
  have hp' : p < 10^(L+1) := Nat.lt_pow_succ_log_self (by decide : 1<10) _
  have hsq := (square_ge L H).trans_le (Nat.pow_log_le_self 10 (by omega : p≠0))
  have hs := primeSize p (L+1) (by omega) hp'
  have isprime := Fact.out (p:=p.Prime)
  have hne (a : ℕ) (ha : 0<a) (hab : a<p) : (a:ZMod p) ≠ 0 :=
    fun hz => (Nat.le_of_dvd ha ((ZMod.natCast_eq_zero_iff _ _).mp hz)).not_gt hab
  apply palindrome_of_blocks (p:=p) (len:=L+1) (q:=16*(L+1)*(L+2))
    (k:=(p.primeCounting/2-1)/(L+2))
  · by_contra! H'
    have U := Nat.mul_le_mul_left (4*(L+1)) (show p.primeCounting+1 ≤ 2 by omega)
    nlinarith [Nat.zero_le (L^2),Nat.zero_le (L^3),Nat.zero_le (L^4)]
  · exact hp'.le
  · exact hsq
  · exact_mod_cast hne 10 (by decide) (by omega)
  · exact mul_ne_zero (by exact_mod_cast hne 99 (by decide) (by omega)) (by exact_mod_cast hne 10 (by decide) (by omega))
  · exact Nat.div_mul_le_self _ _
  · exact enough p.primeCounting p (L+1) (by omega) hs hsq


private abbrev HasPal (n p : ℕ) :=
  ∃ m : ℕ, 0 < m ∧ (Nat.digits 10 m).length = n ∧ (Nat.digits 10 m).Palindrome ∧ p ∣ m

-- The short certificate is a nonzero outer decimal word, padded by zeros centrally.
def tested (p n x : ℕ) : Bool :=
  let d := Nat.digits 10 x
  decide (0 < x ∧ 2*d.length ≤ n ∧
    (x*10^(n-d.length)+Nat.ofDigits 10 d.reverse)%p=0)

private theorem tested_sound {p n x : ℕ} (ok : tested p n x) : HasPal n p := by
  let d := Nat.digits 10 x
  let blanks := n-2*d.length
  let word := (d.reverse ++ List.replicate blanks 0) ++ d
  have hh : 0<x ∧ 2*d.length ≤ n ∧ (x*10^(n-d.length)+Nat.ofDigits 10 d.reverse)%p=0 :=
    of_decide_eq_true ok
  obtain ⟨hx,hn,hp⟩ := hh
  have hd : d≠[] := Nat.digits_ne_nil_iff_ne_zero.mpr hx.ne'
  have hdigit : Nat.digits 10 (Nat.ofDigits 10 word)=word := by
    apply Nat.digits_ofDigits 10 (by decide)
    · intro a ha
      simp [word] at ha
      have H : ∀ i ∈ d, i<10 := fun i hi => Nat.digits_lt_base (by decide : 1 < 10) hi
      grind
    · intro h
      exact (List.getLast_append_of_ne_nil _ hd).trans_ne (Nat.getLast_digit_ne_zero 10 hx.ne')
  refine ⟨Nat.ofDigits 10 word,?_,?_,?_,?_⟩
  · show 0 < Nat.ofDigits 10 word
    by_contra! h0
    have hz : Nat.ofDigits 10 word=0 := by omega
    rw [hz,Nat.digits_zero] at hdigit
    have := List.length_eq_zero_iff.mpr hdigit.symm
    simp [word] at this
    grind
  · rw [hdigit];simp [word,blanks];omega
  · rw [hdigit];apply List.Palindrome.of_reverse_eq
    simp [word,List.append_assoc]
  · have he : Nat.ofDigits 10 word = x*10^(n-d.length)+Nat.ofDigits 10 d.reverse := by
      have H : d.length+blanks = n-d.length := by dsimp [blanks];omega
      rw [←H]
      simp [word,Nat.ofDigits_append,Nat.ofDigits_replicate_zero,d,Nat.ofDigits_digits,pow_add]
      ring
    rw [he];exact Nat.dvd_of_mod_eq_zero hp

def fastPrime (p : ℕ) : Bool :=
  if 317 < p ∧ p ≤ 100000 then decide (p.Coprime (Nat.factorial 317)) else decide p.Prime

private theorem fastPrime_iff (p : ℕ) : fastPrime p = true ↔ p.Prime := by
  unfold fastPrime
  split_ifs with h
  · simp only [decide_eq_true_eq]
    refine ⟨fun hc => Nat.prime_def_le_sqrt.mpr ⟨by omega,?_⟩, fun hp => hp.coprime_factorial_of_lt h.1⟩
    intro t ht hu hd
    have ht' : t ≤ 317 := by
      have sq : p.sqrt < 318 := Nat.sqrt_lt.mpr (by omega)
      omega
    have bad := Nat.dvd_gcd hd (Nat.dvd_factorial (by omega : 0<t) ht')
    rw [hc.gcd_eq_one] at bad
    have := Nat.le_of_dvd (by decide : 0<1) bad
    omega
  · simp

-- Rank denotes the number of primes strictly below the current candidate.
def scan (p rank : ℕ) : List ℕ → Bool
  | [] => true
  | x :: xs => if fastPrime p then tested p (rank+1) x && scan (p+1) (rank+1) xs
               else scan (p+1) rank xs

private theorem scan_sound (xs : List ℕ) (p : ℕ) (ok : scan p p.primeCounting' xs) :
    ∀ y, p ≤ y → y < p+xs.length → y.Prime → HasPal y.primeCounting y := by
  induction xs generalizing p with
  | nil => simp;omega
  | cons x xs ih =>
    intro y h₁ h₂ hy
    simp only [List.length_cons] at h₂
    have hr : (p+1).primeCounting' = p.primeCounting' + if p.Prime then 1 else 0 := Nat.count_succ _ _
    by_cases hp : p.Prime
    · simp [scan,fastPrime_iff,hp] at ok
      simp [hp] at hr
      by_cases he : y=p
      · subst y
        change HasPal (p+1).primeCounting' p
        rw [hr]
        exact tested_sound ok.1
      · apply ih (p+1) _ y (by omega) (by omega) hy
        rw [hr]; exact ok.2
    · simp [scan,fastPrime_iff,hp] at ok
      simp [hp] at hr
      apply ih (p+1) _ y (by grind) (by omega) hy
      rwa [hr]

def countFrom (start : ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => countFrom start k + (fastPrime (start+k)).toNat

private theorem count_step (start k : ℕ) :
    (start+k).primeCounting' = start.primeCounting' + countFrom start k := by
  induction k with
  | zero => simp [countFrom]
  | succ k ih =>
    rw [Nat.add_succ,show (start+k+1).primeCounting' =
      (start+k).primeCounting' + (if (start+k).Prime then 1 else 0) by apply Nat.count_succ, ih]
    by_cases h : (start+k).Prime
    · have H := (fastPrime_iff _).mpr h
      simp [countFrom,H,h,Nat.add_assoc]
    · have H : fastPrime (start+k)=false := by cases hh : fastPrime (start+k) <;> simp_all [fastPrime_iff]
      simp [countFrom,H,h,Nat.add_assoc]

set_option maxRecDepth 8000 in
private theorem rank19 : Nat.primeCounting' 19 = 7 := by
  have hc : countFrom 0 19 = 7 := by decide +kernel
  have h := count_step 0 19
  simpa [hc,Nat.primeCounting',Nat.count_zero] using h
set_option maxRecDepth 8000 in
private theorem rank147 : Nat.primeCounting' 147 = 34 := by
  have hc : countFrom 19 128 = 27 := by decide +kernel
  have h := count_step 19 128
  rw [rank19,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank275 : Nat.primeCounting' 275 = 58 := by
  have hc : countFrom 147 128 = 24 := by decide +kernel
  have h := count_step 147 128
  rw [rank147,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank403 : Nat.primeCounting' 403 = 79 := by
  have hc : countFrom 275 128 = 21 := by decide +kernel
  have h := count_step 275 128
  rw [rank275,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank531 : Nat.primeCounting' 531 = 99 := by
  have hc : countFrom 403 128 = 20 := by decide +kernel
  have h := count_step 403 128
  rw [rank403,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank659 : Nat.primeCounting' 659 = 119 := by
  have hc : countFrom 531 128 = 20 := by decide +kernel
  have h := count_step 531 128
  rw [rank531,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank787 : Nat.primeCounting' 787 = 137 := by
  have hc : countFrom 659 128 = 18 := by decide +kernel
  have h := count_step 659 128
  rw [rank659,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank915 : Nat.primeCounting' 915 = 156 := by
  have hc : countFrom 787 128 = 19 := by decide +kernel
  have h := count_step 787 128
  rw [rank787,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank1043 : Nat.primeCounting' 1043 = 175 := by
  have hc : countFrom 915 128 = 19 := by decide +kernel
  have h := count_step 915 128
  rw [rank915,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank1171 : Nat.primeCounting' 1171 = 192 := by
  have hc : countFrom 1043 128 = 17 := by decide +kernel
  have h := count_step 1043 128
  rw [rank1043,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank1299 : Nat.primeCounting' 1299 = 211 := by
  have hc : countFrom 1171 128 = 19 := by decide +kernel
  have h := count_step 1171 128
  rw [rank1171,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank1427 : Nat.primeCounting' 1427 = 224 := by
  have hc : countFrom 1299 128 = 13 := by decide +kernel
  have h := count_step 1299 128
  rw [rank1299,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank1555 : Nat.primeCounting' 1555 = 245 := by
  have hc : countFrom 1427 128 = 21 := by decide +kernel
  have h := count_step 1427 128
  rw [rank1427,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank1683 : Nat.primeCounting' 1683 = 263 := by
  have hc : countFrom 1555 128 = 18 := by decide +kernel
  have h := count_step 1555 128
  rw [rank1555,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank1811 : Nat.primeCounting' 1811 = 279 := by
  have hc : countFrom 1683 128 = 16 := by decide +kernel
  have h := count_step 1683 128
  rw [rank1683,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank1939 : Nat.primeCounting' 1939 = 295 := by
  have hc : countFrom 1811 128 = 16 := by decide +kernel
  have h := count_step 1811 128
  rw [rank1811,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank2067 : Nat.primeCounting' 2067 = 311 := by
  have hc : countFrom 1939 128 = 16 := by decide +kernel
  have h := count_step 1939 128
  rw [rank1939,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank2195 : Nat.primeCounting' 2195 = 327 := by
  have hc : countFrom 2067 128 = 16 := by decide +kernel
  have h := count_step 2067 128
  rw [rank2067,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank2323 : Nat.primeCounting' 2323 = 344 := by
  have hc : countFrom 2195 128 = 17 := by decide +kernel
  have h := count_step 2195 128
  rw [rank2195,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank2451 : Nat.primeCounting' 2451 = 363 := by
  have hc : countFrom 2323 128 = 19 := by decide +kernel
  have h := count_step 2323 128
  rw [rank2323,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank2579 : Nat.primeCounting' 2579 = 375 := by
  have hc : countFrom 2451 128 = 12 := by decide +kernel
  have h := count_step 2451 128
  rw [rank2451,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank2707 : Nat.primeCounting' 2707 = 393 := by
  have hc : countFrom 2579 128 = 18 := by decide +kernel
  have h := count_step 2579 128
  rw [rank2579,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank2835 : Nat.primeCounting' 2835 = 411 := by
  have hc : countFrom 2707 128 = 18 := by decide +kernel
  have h := count_step 2707 128
  rw [rank2707,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank2963 : Nat.primeCounting' 2963 = 426 := by
  have hc : countFrom 2835 128 = 15 := by decide +kernel
  have h := count_step 2835 128
  rw [rank2835,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank3091 : Nat.primeCounting' 3091 = 442 := by
  have hc : countFrom 2963 128 = 16 := by decide +kernel
  have h := count_step 2963 128
  rw [rank2963,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank3219 : Nat.primeCounting' 3219 = 455 := by
  have hc : countFrom 3091 128 = 13 := by decide +kernel
  have h := count_step 3091 128
  rw [rank3091,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank3347 : Nat.primeCounting' 3347 = 471 := by
  have hc : countFrom 3219 128 = 16 := by decide +kernel
  have h := count_step 3219 128
  rw [rank3219,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank3475 : Nat.primeCounting' 3475 = 487 := by
  have hc : countFrom 3347 128 = 16 := by decide +kernel
  have h := count_step 3347 128
  rw [rank3347,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank3603 : Nat.primeCounting' 3603 = 503 := by
  have hc : countFrom 3475 128 = 16 := by decide +kernel
  have h := count_step 3475 128
  rw [rank3475,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank3731 : Nat.primeCounting' 3731 = 520 := by
  have hc : countFrom 3603 128 = 17 := by decide +kernel
  have h := count_step 3603 128
  rw [rank3603,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank3859 : Nat.primeCounting' 3859 = 535 := by
  have hc : countFrom 3731 128 = 15 := by decide +kernel
  have h := count_step 3731 128
  rw [rank3731,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank3987 : Nat.primeCounting' 3987 = 549 := by
  have hc : countFrom 3859 128 = 14 := by decide +kernel
  have h := count_step 3859 128
  rw [rank3859,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank4115 : Nat.primeCounting' 4115 = 566 := by
  have hc : countFrom 3987 128 = 17 := by decide +kernel
  have h := count_step 3987 128
  rw [rank3987,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank4243 : Nat.primeCounting' 4243 = 581 := by
  have hc : countFrom 4115 128 = 15 := by decide +kernel
  have h := count_step 4115 128
  rw [rank4115,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank4371 : Nat.primeCounting' 4371 = 596 := by
  have hc : countFrom 4243 128 = 15 := by decide +kernel
  have h := count_step 4243 128
  rw [rank4243,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank4499 : Nat.primeCounting' 4499 = 610 := by
  have hc : countFrom 4371 128 = 14 := by decide +kernel
  have h := count_step 4371 128
  rw [rank4371,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank4627 : Nat.primeCounting' 4627 = 624 := by
  have hc : countFrom 4499 128 = 14 := by decide +kernel
  have h := count_step 4499 128
  rw [rank4499,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank4755 : Nat.primeCounting' 4755 = 640 := by
  have hc : countFrom 4627 128 = 16 := by decide +kernel
  have h := count_step 4627 128
  rw [rank4627,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank4883 : Nat.primeCounting' 4883 = 653 := by
  have hc : countFrom 4755 128 = 13 := by decide +kernel
  have h := count_step 4755 128
  rw [rank4755,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank5011 : Nat.primeCounting' 5011 = 671 := by
  have hc : countFrom 4883 128 = 18 := by decide +kernel
  have h := count_step 4883 128
  rw [rank4883,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank5139 : Nat.primeCounting' 5139 = 685 := by
  have hc : countFrom 5011 128 = 14 := by decide +kernel
  have h := count_step 5011 128
  rw [rank5011,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank5267 : Nat.primeCounting' 5267 = 698 := by
  have hc : countFrom 5139 128 = 13 := by decide +kernel
  have h := count_step 5139 128
  rw [rank5139,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank5395 : Nat.primeCounting' 5395 = 711 := by
  have hc : countFrom 5267 128 = 13 := by decide +kernel
  have h := count_step 5267 128
  rw [rank5267,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank5523 : Nat.primeCounting' 5523 = 730 := by
  have hc : countFrom 5395 128 = 19 := by decide +kernel
  have h := count_step 5395 128
  rw [rank5395,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank5651 : Nat.primeCounting' 5651 = 742 := by
  have hc : countFrom 5523 128 = 12 := by decide +kernel
  have h := count_step 5523 128
  rw [rank5523,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank5779 : Nat.primeCounting' 5779 = 757 := by
  have hc : countFrom 5651 128 = 15 := by decide +kernel
  have h := count_step 5651 128
  rw [rank5651,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank5907 : Nat.primeCounting' 5907 = 777 := by
  have hc : countFrom 5779 128 = 20 := by decide +kernel
  have h := count_step 5779 128
  rw [rank5779,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank6035 : Nat.primeCounting' 6035 = 786 := by
  have hc : countFrom 5907 128 = 9 := by decide +kernel
  have h := count_step 5907 128
  rw [rank5907,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank6163 : Nat.primeCounting' 6163 = 802 := by
  have hc : countFrom 6035 128 = 16 := by decide +kernel
  have h := count_step 6035 128
  rw [rank6035,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank6291 : Nat.primeCounting' 6291 = 818 := by
  have hc : countFrom 6163 128 = 16 := by decide +kernel
  have h := count_step 6163 128
  rw [rank6163,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank6419 : Nat.primeCounting' 6419 = 834 := by
  have hc : countFrom 6291 128 = 16 := by decide +kernel
  have h := count_step 6291 128
  rw [rank6291,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank6547 : Nat.primeCounting' 6547 = 844 := by
  have hc : countFrom 6419 128 = 10 := by decide +kernel
  have h := count_step 6419 128
  rw [rank6419,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank6675 : Nat.primeCounting' 6675 = 860 := by
  have hc : countFrom 6547 128 = 16 := by decide +kernel
  have h := count_step 6547 128
  rw [rank6547,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank6803 : Nat.primeCounting' 6803 = 875 := by
  have hc : countFrom 6675 128 = 15 := by decide +kernel
  have h := count_step 6675 128
  rw [rank6675,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank6931 : Nat.primeCounting' 6931 = 890 := by
  have hc : countFrom 6803 128 = 15 := by decide +kernel
  have h := count_step 6803 128
  rw [rank6803,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank7000 : Nat.primeCounting' 7000 = 900 := by
  have hc : countFrom 6931 69 = 10 := by decide +kernel
  have h := count_step 6931 69
  rw [rank6931,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank7256 : Nat.primeCounting' 7256 = 928 := by
  have hc : countFrom 7000 256 = 28 := by decide +kernel
  have h := count_step 7000 256
  rw [rank7000,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank7389 : Nat.primeCounting' 7389 = 938 := by
  have hc : countFrom 7256 133 = 10 := by decide +kernel
  have h := count_step 7256 133
  rw [rank7256,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank7645 : Nat.primeCounting' 7645 = 970 := by
  have hc : countFrom 7389 256 = 32 := by decide +kernel
  have h := count_step 7389 256
  rw [rank7389,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank7901 : Nat.primeCounting' 7901 = 997 := by
  have hc : countFrom 7645 256 = 27 := by decide +kernel
  have h := count_step 7645 256
  rw [rank7645,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank7908 : Nat.primeCounting' 7908 = 999 := by
  have hc : countFrom 7901 7 = 2 := by decide +kernel
  have h := count_step 7901 7
  rw [rank7901,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank8164 : Nat.primeCounting' 8164 = 1024 := by
  have hc : countFrom 7908 256 = 25 := by decide +kernel
  have h := count_step 7908 256
  rw [rank7908,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank8420 : Nat.primeCounting' 8420 = 1052 := by
  have hc : countFrom 8164 256 = 28 := by decide +kernel
  have h := count_step 8164 256
  rw [rank8164,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank8676 : Nat.primeCounting' 8676 = 1079 := by
  have hc : countFrom 8420 256 = 27 := by decide +kernel
  have h := count_step 8420 256
  rw [rank8420,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank8932 : Nat.primeCounting' 8932 = 1110 := by
  have hc : countFrom 8676 256 = 31 := by decide +kernel
  have h := count_step 8676 256
  rw [rank8676,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank9188 : Nat.primeCounting' 9188 = 1139 := by
  have hc : countFrom 8932 256 = 29 := by decide +kernel
  have h := count_step 8932 256
  rw [rank8932,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank9210 : Nat.primeCounting' 9210 = 1142 := by
  have hc : countFrom 9188 22 = 3 := by decide +kernel
  have h := count_step 9188 22
  rw [rank9188,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank9466 : Nat.primeCounting' 9466 = 1172 := by
  have hc : countFrom 9210 256 = 30 := by decide +kernel
  have h := count_step 9210 256
  rw [rank9210,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank9722 : Nat.primeCounting' 9722 = 1199 := by
  have hc : countFrom 9466 256 = 27 := by decide +kernel
  have h := count_step 9466 256
  rw [rank9466,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank9978 : Nat.primeCounting' 9978 = 1229 := by
  have hc : countFrom 9722 256 = 30 := by decide +kernel
  have h := count_step 9722 256
  rw [rank9722,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank10000 : Nat.primeCounting' 10000 = 1229 := by
  have hc : countFrom 9978 22 = 0 := by decide +kernel
  have h := count_step 9978 22
  rw [rank9978,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank10100 : Nat.primeCounting' 10100 = 1240 := by
  have hc : countFrom 10000 100 = 11 := by decide +kernel
  have h := count_step 10000 100
  rw [rank10000,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank10302 : Nat.primeCounting' 10302 = 1263 := by
  have hc : countFrom 10100 202 = 23 := by decide +kernel
  have h := count_step 10100 202
  rw [rank10100,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank10558 : Nat.primeCounting' 10558 = 1288 := by
  have hc : countFrom 10302 256 = 25 := by decide +kernel
  have h := count_step 10302 256
  rw [rank10302,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank10608 : Nat.primeCounting' 10608 = 1294 := by
  have hc : countFrom 10558 50 = 6 := by decide +kernel
  have h := count_step 10558 50
  rw [rank10558,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank10864 : Nat.primeCounting' 10864 = 1321 := by
  have hc : countFrom 10608 256 = 27 := by decide +kernel
  have h := count_step 10608 256
  rw [rank10608,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank10916 : Nat.primeCounting' 10916 = 1327 := by
  have hc : countFrom 10864 52 = 6 := by decide +kernel
  have h := count_step 10864 52
  rw [rank10864,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank11172 : Nat.primeCounting' 11172 = 1353 := by
  have hc : countFrom 10916 256 = 26 := by decide +kernel
  have h := count_step 10916 256
  rw [rank10916,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank11428 : Nat.primeCounting' 11428 = 1378 := by
  have hc : countFrom 11172 256 = 25 := by decide +kernel
  have h := count_step 11172 256
  rw [rank11172,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank11442 : Nat.primeCounting' 11442 = 1379 := by
  have hc : countFrom 11428 14 = 1 := by decide +kernel
  have h := count_step 11428 14
  rw [rank11428,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank11698 : Nat.primeCounting' 11698 = 1403 := by
  have hc : countFrom 11442 256 = 24 := by decide +kernel
  have h := count_step 11442 256
  rw [rank11442,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank11954 : Nat.primeCounting' 11954 = 1433 := by
  have hc : countFrom 11698 256 = 30 := by decide +kernel
  have h := count_step 11698 256
  rw [rank11698,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank12086 : Nat.primeCounting' 12086 = 1446 := by
  have hc : countFrom 11954 132 = 13 := by decide +kernel
  have h := count_step 11954 132
  rw [rank11954,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank12342 : Nat.primeCounting' 12342 = 1473 := by
  have hc : countFrom 12086 256 = 27 := by decide +kernel
  have h := count_step 12086 256
  rw [rank12086,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank12598 : Nat.primeCounting' 12598 = 1504 := by
  have hc : countFrom 12342 256 = 31 := by decide +kernel
  have h := count_step 12342 256
  rw [rank12342,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank12854 : Nat.primeCounting' 12854 = 1532 := by
  have hc : countFrom 12598 256 = 28 := by decide +kernel
  have h := count_step 12598 256
  rw [rank12598,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank13110 : Nat.primeCounting' 13110 = 1560 := by
  have hc : countFrom 12854 256 = 28 := by decide +kernel
  have h := count_step 12854 256
  rw [rank12854,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank13366 : Nat.primeCounting' 13366 = 1585 := by
  have hc : countFrom 13110 256 = 25 := by decide +kernel
  have h := count_step 13110 256
  rw [rank13110,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank13622 : Nat.primeCounting' 13622 = 1610 := by
  have hc : countFrom 13366 256 = 25 := by decide +kernel
  have h := count_step 13366 256
  rw [rank13366,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank13682 : Nat.primeCounting' 13682 = 1616 := by
  have hc : countFrom 13622 60 = 6 := by decide +kernel
  have h := count_step 13622 60
  rw [rank13622,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank13938 : Nat.primeCounting' 13938 = 1648 := by
  have hc : countFrom 13682 256 = 32 := by decide +kernel
  have h := count_step 13682 256
  rw [rank13682,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank14194 : Nat.primeCounting' 14194 = 1669 := by
  have hc : countFrom 13938 256 = 21 := by decide +kernel
  have h := count_step 13938 256
  rw [rank13938,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank14450 : Nat.primeCounting' 14450 = 1695 := by
  have hc : countFrom 14194 256 = 26 := by decide +kernel
  have h := count_step 14194 256
  rw [rank14194,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank14706 : Nat.primeCounting' 14706 = 1720 := by
  have hc : countFrom 14450 256 = 25 := by decide +kernel
  have h := count_step 14450 256
  rw [rank14450,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank14962 : Nat.primeCounting' 14962 = 1752 := by
  have hc : countFrom 14706 256 = 32 := by decide +kernel
  have h := count_step 14706 256
  rw [rank14706,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank15218 : Nat.primeCounting' 15218 = 1776 := by
  have hc : countFrom 14962 256 = 24 := by decide +kernel
  have h := count_step 14962 256
  rw [rank14962,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank15474 : Nat.primeCounting' 15474 = 1808 := by
  have hc : countFrom 15218 256 = 32 := by decide +kernel
  have h := count_step 15218 256
  rw [rank15218,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank15730 : Nat.primeCounting' 15730 = 1832 := by
  have hc : countFrom 15474 256 = 24 := by decide +kernel
  have h := count_step 15474 256
  rw [rank15474,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank15986 : Nat.primeCounting' 15986 = 1861 := by
  have hc : countFrom 15730 256 = 29 := by decide +kernel
  have h := count_step 15730 256
  rw [rank15730,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank16242 : Nat.primeCounting' 16242 = 1887 := by
  have hc : countFrom 15986 256 = 26 := by decide +kernel
  have h := count_step 15986 256
  rw [rank15986,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank16498 : Nat.primeCounting' 16498 = 1912 := by
  have hc : countFrom 16242 256 = 25 := by decide +kernel
  have h := count_step 16242 256
  rw [rank16242,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank16618 : Nat.primeCounting' 16618 = 1921 := by
  have hc : countFrom 16498 120 = 9 := by decide +kernel
  have h := count_step 16498 120
  rw [rank16498,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank16874 : Nat.primeCounting' 16874 = 1945 := by
  have hc : countFrom 16618 256 = 24 := by decide +kernel
  have h := count_step 16618 256
  rw [rank16618,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank17130 : Nat.primeCounting' 17130 = 1974 := by
  have hc : countFrom 16874 256 = 29 := by decide +kernel
  have h := count_step 16874 256
  rw [rank16874,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank17386 : Nat.primeCounting' 17386 = 1998 := by
  have hc : countFrom 17130 256 = 24 := by decide +kernel
  have h := count_step 17130 256
  rw [rank17130,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank17642 : Nat.primeCounting' 17642 = 2027 := by
  have hc : countFrom 17386 256 = 29 := by decide +kernel
  have h := count_step 17386 256
  rw [rank17386,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank17898 : Nat.primeCounting' 17898 = 2050 := by
  have hc : countFrom 17642 256 = 23 := by decide +kernel
  have h := count_step 17642 256
  rw [rank17642,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank18154 : Nat.primeCounting' 18154 = 2081 := by
  have hc : countFrom 17898 256 = 31 := by decide +kernel
  have h := count_step 17898 256
  rw [rank17898,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank18410 : Nat.primeCounting' 18410 = 2108 := by
  have hc : countFrom 18154 256 = 27 := by decide +kernel
  have h := count_step 18154 256
  rw [rank18154,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank18666 : Nat.primeCounting' 18666 = 2131 := by
  have hc : countFrom 18410 256 = 23 := by decide +kernel
  have h := count_step 18410 256
  rw [rank18410,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank18922 : Nat.primeCounting' 18922 = 2154 := by
  have hc : countFrom 18666 256 = 23 := by decide +kernel
  have h := count_step 18666 256
  rw [rank18666,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank19178 : Nat.primeCounting' 19178 = 2174 := by
  have hc : countFrom 18922 256 = 20 := by decide +kernel
  have h := count_step 18922 256
  rw [rank18922,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank19434 : Nat.primeCounting' 19434 = 2203 := by
  have hc : countFrom 19178 256 = 29 := by decide +kernel
  have h := count_step 19178 256
  rw [rank19178,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank19690 : Nat.primeCounting' 19690 = 2228 := by
  have hc : countFrom 19434 256 = 25 := by decide +kernel
  have h := count_step 19434 256
  rw [rank19434,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank19946 : Nat.primeCounting' 19946 = 2254 := by
  have hc : countFrom 19690 256 = 26 := by decide +kernel
  have h := count_step 19690 256
  rw [rank19690,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank20202 : Nat.primeCounting' 20202 = 2285 := by
  have hc : countFrom 19946 256 = 31 := by decide +kernel
  have h := count_step 19946 256
  rw [rank19946,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank20458 : Nat.primeCounting' 20458 = 2310 := by
  have hc : countFrom 20202 256 = 25 := by decide +kernel
  have h := count_step 20202 256
  rw [rank20202,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank20714 : Nat.primeCounting' 20714 = 2331 := by
  have hc : countFrom 20458 256 = 21 := by decide +kernel
  have h := count_step 20458 256
  rw [rank20458,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank20970 : Nat.primeCounting' 20970 = 2358 := by
  have hc : countFrom 20714 256 = 27 := by decide +kernel
  have h := count_step 20714 256
  rw [rank20714,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank21226 : Nat.primeCounting' 21226 = 2386 := by
  have hc : countFrom 20970 256 = 28 := by decide +kernel
  have h := count_step 20970 256
  rw [rank20970,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank21482 : Nat.primeCounting' 21482 = 2408 := by
  have hc : countFrom 21226 256 = 22 := by decide +kernel
  have h := count_step 21226 256
  rw [rank21226,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank21738 : Nat.primeCounting' 21738 = 2438 := by
  have hc : countFrom 21482 256 = 30 := by decide +kernel
  have h := count_step 21482 256
  rw [rank21482,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank21994 : Nat.primeCounting' 21994 = 2463 := by
  have hc : countFrom 21738 256 = 25 := by decide +kernel
  have h := count_step 21738 256
  rw [rank21738,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank22250 : Nat.primeCounting' 22250 = 2491 := by
  have hc : countFrom 21994 256 = 28 := by decide +kernel
  have h := count_step 21994 256
  rw [rank21994,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank22506 : Nat.primeCounting' 22506 = 2516 := by
  have hc : countFrom 22250 256 = 25 := by decide +kernel
  have h := count_step 22250 256
  rw [rank22250,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank22762 : Nat.primeCounting' 22762 = 2543 := by
  have hc : countFrom 22506 256 = 27 := by decide +kernel
  have h := count_step 22506 256
  rw [rank22506,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank23018 : Nat.primeCounting' 23018 = 2567 := by
  have hc : countFrom 22762 256 = 24 := by decide +kernel
  have h := count_step 22762 256
  rw [rank22762,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank23274 : Nat.primeCounting' 23274 = 2594 := by
  have hc : countFrom 23018 256 = 27 := by decide +kernel
  have h := count_step 23018 256
  rw [rank23018,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank23530 : Nat.primeCounting' 23530 = 2614 := by
  have hc : countFrom 23274 256 = 20 := by decide +kernel
  have h := count_step 23274 256
  rw [rank23274,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank23786 : Nat.primeCounting' 23786 = 2645 := by
  have hc : countFrom 23530 256 = 31 := by decide +kernel
  have h := count_step 23530 256
  rw [rank23530,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem rank23852 : Nat.primeCounting' 23852 = 2652 := by
  have hc : countFrom 23786 66 = 7 := by decide +kernel
  have h := count_step 23786 66
  rw [rank23786,hc] at h; exact h
set_option maxRecDepth 8000 in
private theorem small19 (p : ℕ) (hp : p.Prime) (hl : 19 ≤ p) (hu : p < 147) : HasPal p.primeCounting p := by
  let xs : List ℕ := [23,0,0,0,58,0,0,0,0,0,35,0,56,0,0,0,0,0,21,0,0,0,289,0,115,0,0,0,87,0,0,0,0,0,41,0,0,0,0,0,87,0,53,0,0,0,0,0,54,0,0,0,47,0,1,0,0,0,0,0,21,0,0,0,32,0,0,0,0,0,11,0,0,0,0,0,0,0,56,0,0,0,101,0,184,0,0,0,34,0,154,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,589,0,0,0,126,0,0,0,0,0,95,0,104,0,0,0,0,0,0,0]
  have ok : scan 19 7 xs := by decide +kernel
  apply scan_sound xs 19 _ p hl _ hp
  · rwa [rank19]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small147 (p : ℕ) (hp : p.Prime) (hl : 147 ≤ p) (hu : p < 275) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,108,0,38,0,0,0,0,0,586,0,0,0,0,0,319,0,0,0,352,0,0,0,0,0,71,0,0,0,0,0,118,0,126,0,0,0,0,0,0,0,0,0,122,0,15,0,0,0,126,0,559,0,0,0,0,0,0,0,0,0,0,0,11,0,0,0,0,0,0,0,0,0,0,0,299,0,0,0,225,0,98,0,0,0,107,0,0,0,0,0,519,0,397,0,0,0,0,0,0,0,0,0,179,0,0,0,0,0,166,0,0,0,0,0,172,0,0,0,0,0,349,0,899,0,0,0]
  have ok : scan 147 34 xs := by decide +kernel
  apply scan_sound xs 147 _ p hl _ hp
  · rwa [rank147]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small275 (p : ℕ) (hp : p.Prime) (hl : 275 ≤ p) (hu : p < 403) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,112,0,0,0,6049,0,793,0,0,0,0,0,0,0,0,0,354,0,0,0,0,0,0,0,0,0,0,0,0,0,184,0,0,0,38,0,313,0,0,0,95,0,0,0,0,0,0,0,0,0,0,0,0,0,322,0,0,0,0,0,405,0,0,0,0,0,0,0,0,0,725,0,198,0,0,0,129,0,0,0,0,0,351,0,0,0,0,0,0,0,51,0,0,0,0,0,95,0,0,0,0,0,156,0,0,0,106,0,0,0,0,0,433,0,0,0,0,0,0,0,175,0,0,0,478,0]
  have ok : scan 275 58 xs := by decide +kernel
  apply scan_sound xs 275 _ p hl _ hp
  · rwa [rank275]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small403 (p : ℕ) (hp : p.Prime) (hl : 403 ≤ p) (hu : p < 531) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,397,0,0,0,0,0,0,0,0,0,276,0,305,0,0,0,0,0,0,0,0,0,859,0,427,0,0,0,0,0,878,0,0,0,302,0,0,0,0,0,129,0,0,0,0,0,0,0,165,0,0,0,1238,0,337,0,0,0,15,0,0,0,0,0,0,0,0,0,0,0,1184,0,0,0,0,0,0,0,127,0,0,0,102,0,0,0,0,0,0,0,155,0,0,0,192,0,0,0,0,0,583,0,0,0,0,0,0,0,0,0,0,0,1895,0,542,0,0,0,0,0,0,0]
  have ok : scan 403 79 xs := by decide +kernel
  apply scan_sound xs 403 _ p hl _ hp
  · rwa [rank403]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small531 (p : ℕ) (hp : p.Prime) (hl : 531 ≤ p) (hu : p < 659) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,0,0,901,0,0,0,0,0,809,0,0,0,0,0,0,0,0,0,124,0,0,0,0,0,601,0,0,0,0,0,275,0,744,0,0,0,0,0,1614,0,0,0,0,0,0,0,0,0,2509,0,0,0,0,0,753,0,0,0,0,0,3677,0,559,0,0,0,0,0,234,0,0,0,0,0,148,0,0,0,706,0,495,0,0,0,0,0,0,0,0,0,0,0,1106,0,0,0,0,0,0,0,0,0,1001,0,869,0,0,0,275,0,0,0,0,0,225,0,0,0,0,0]
  have ok : scan 531 99 xs := by decide +kernel
  apply scan_sound xs 531 _ p hl _ hp
  · rwa [rank531]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small659 (p : ℕ) (hp : p.Prime) (hl : 659 ≤ p) (hu : p < 787) : HasPal p.primeCounting p := by
  let xs : List ℕ := [331,0,931,0,0,0,0,0,0,0,0,0,0,0,388,0,0,0,87,0,0,0,0,0,1946,0,0,0,0,0,0,0,531,0,0,0,0,0,0,0,0,0,374,0,0,0,0,0,0,0,132,0,0,0,0,0,0,0,0,0,1269,0,0,0,0,0,0,0,357,0,0,0,0,0,728,0,0,0,0,0,795,0,0,0,13,0,0,0,0,0,0,0,2859,0,0,0,0,0,757,0,0,0,477,0,0,0,0,0,0,0,893,0,0,0,857,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 659 119 xs := by decide +kernel
  apply scan_sound xs 659 _ p hl _ hp
  · rwa [rank659]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small787 (p : ℕ) (hp : p.Prime) (hl : 787 ≤ p) (hu : p < 915) : HasPal p.primeCounting p := by
  let xs : List ℕ := [702,0,0,0,0,0,0,0,0,0,797,0,0,0,0,0,0,0,0,0,0,0,384,0,612,0,0,0,0,0,0,0,0,0,586,0,1588,0,0,0,1435,0,156,0,0,0,0,0,0,0,0,0,3357,0,0,0,0,0,0,0,0,0,0,0,0,0,1745,0,0,0,47,0,9405,0,0,0,467,0,0,0,0,0,0,0,0,0,0,0,0,0,758,0,0,0,897,0,127,0,0,0,956,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10759,0,0,0,67,0,0,0]
  have ok : scan 787 137 xs := by decide +kernel
  apply scan_sound xs 787 _ p hl _ hp
  · rwa [rank787]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small915 (p : ℕ) (hp : p.Prime) (hl : 915 ≤ p) (hu : p < 1043) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,919,0,0,0,0,0,0,0,0,0,929,0,0,0,0,0,0,0,128,0,0,0,814,0,0,0,0,0,611,0,0,0,0,0,219,0,0,0,0,0,0,0,0,0,0,0,0,0,11,0,0,0,673,0,0,0,0,0,1285,0,0,0,0,0,441,0,0,0,0,0,0,0,419,0,0,0,0,0,11145,0,0,0,0,0,0,0,0,0,0,0,1299,0,0,0,473,0,0,0,0,0,1156,0,331,0,0,0,0,0,0,0,0,0,129,0,617,0,0,0,0,0,1779,0,0,0]
  have ok : scan 915 156 xs := by decide +kernel
  apply scan_sound xs 915 _ p hl _ hp
  · rwa [rank915]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small1043 (p : ℕ) (hp : p.Prime) (hl : 1043 ≤ p) (hu : p < 1171) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,1395,0,3948,0,0,0,0,0,0,0,0,0,2443,0,2494,0,0,0,0,0,1341,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,421,0,0,0,1338,0,1062,0,0,0,1226,0,0,0,0,0,2792,0,0,0,0,0,1158,0,0,0,0,0,0,0,1618,0,0,0,0,0,15,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1195,0,708,0,0,0,0,0,0,0,0,0,872,0,0,0,0,0,0,0]
  have ok : scan 1043 175 xs := by decide +kernel
  apply scan_sound xs 1043 _ p hl _ hp
  · rwa [rank1043]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small1171 (p : ℕ) (hp : p.Prime) (hl : 1171 ≤ p) (hu : p < 1299) : HasPal p.primeCounting p := by
  let xs : List ℕ := [1066,0,0,0,0,0,0,0,0,0,45,0,0,0,0,0,27,0,0,0,0,0,2564,0,0,0,0,0,0,0,528,0,0,0,0,0,0,0,0,0,0,0,956,0,0,0,1953,0,0,0,0,0,1191,0,0,0,0,0,839,0,1253,0,0,0,0,0,1167,0,0,0,0,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,0,0,489,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,413,0,364,0,0,0,1406,0,0,0,0,0,578,0,1939,0,0,0,0,0,541,0]
  have ok : scan 1171 192 xs := by decide +kernel
  apply scan_sound xs 1171 _ p hl _ hp
  · rwa [rank1171]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small1299 (p : ℕ) (hp : p.Prime) (hl : 1299 ≤ p) (hu : p < 1427) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,1639,0,2911,0,0,0,2891,0,0,0,0,0,0,0,0,0,0,0,2454,0,437,0,0,0,0,0,1222,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8502,0,0,0,0,0,105,0,0,0,0,0,8115,0,0,0,0,0,0,0,1434,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1033,0,0,0,0,0,0,0,0,0,1803,0,0,0,0,0,0,0,0,0,0,0,0,0,1744,0,0,0]
  have ok : scan 1299 211 xs := by decide +kernel
  apply scan_sound xs 1299 _ p hl _ hp
  · rwa [rank1299]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small1427 (p : ℕ) (hp : p.Prime) (hl : 1427 ≤ p) (hu : p < 1555) : HasPal p.primeCounting p := by
  let xs : List ℕ := [1296,0,1778,0,0,0,4313,0,0,0,0,0,931,0,0,0,0,0,0,0,509,0,0,0,1783,0,499,0,0,0,0,0,722,0,0,0,0,0,0,0,0,0,0,0,1928,0,0,0,0,0,0,0,0,0,531,0,1269,0,0,0,2887,0,2333,0,0,0,118,0,0,0,0,0,156,0,0,0,0,0,0,0,0,0,0,0,76,0,0,0,0,0,0,0,0,0,0,0,1246,0,0,0,0,0,0,0,1172,0,0,0,0,0,0,0,0,0,0,0,1063,0,0,0,0,0,5886,0,0,0,3562,0]
  have ok : scan 1427 224 xs := by decide +kernel
  apply scan_sound xs 1427 _ p hl _ hp
  · rwa [rank1427]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small1555 (p : ℕ) (hp : p.Prime) (hl : 1555 ≤ p) (hu : p < 1683) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,1047,0,0,0,0,0,0,0,2551,0,0,0,726,0,0,0,0,0,0,0,3842,0,0,0,2096,0,0,0,0,0,0,0,0,0,0,0,0,0,391,0,0,0,1451,0,0,0,0,0,23,0,1327,0,0,0,194,0,0,0,0,0,841,0,2991,0,0,0,0,0,3273,0,0,0,0,0,0,0,0,0,1987,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2702,0,0,0,0,0,6053,0,0,0,944,0,2643,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 1555 245 xs := by decide +kernel
  apply scan_sound xs 1555 _ p hl _ hp
  · rwa [rank1555]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small1683 (p : ℕ) (hp : p.Prime) (hl : 1683 ≤ p) (hu : p < 1811) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,0,0,493,0,0,0,2259,0,561,0,0,0,0,0,0,0,0,0,1613,0,0,0,0,0,0,0,0,0,0,0,3991,0,4392,0,0,0,0,0,0,0,0,0,3017,0,0,0,0,0,0,0,1292,0,0,0,0,0,2561,0,0,0,0,0,1317,0,0,0,0,0,2012,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1248,0,0,0,0,0,472,0,0,0,2277,0,558,0,0,0,0,0,0,0,0,0,0,0,907,0,0,0,0,0,0,0,0,0]
  have ok : scan 1683 263 xs := by decide +kernel
  apply scan_sound xs 1683 _ p hl _ hp
  · rwa [rank1683]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small1811 (p : ℕ) (hp : p.Prime) (hl : 1811 ≤ p) (hu : p < 1939) : HasPal p.primeCounting p := by
  let xs : List ℕ := [765,0,0,0,0,0,0,0,0,0,0,0,2571,0,0,0,0,0,0,0,229,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2325,0,0,0,0,0,0,0,0,0,0,0,0,0,5026,0,0,0,0,0,6594,0,0,0,1123,0,6299,0,0,0,5685,0,3127,0,0,0,0,0,0,0,0,0,427,0,0,0,0,0,0,0,0,0,0,0,51,0,0,0,0,0,1982,0,0,0,0,0,114,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1235,0,562,0,0,0,0,0]
  have ok : scan 1811 279 xs := by decide +kernel
  apply scan_sound xs 1811 _ p hl _ hp
  · rwa [rank1811]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small1939 (p : ℕ) (hp : p.Prime) (hl : 1939 ≤ p) (hu : p < 2067) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,0,0,965,0,645,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1596,0,0,0,0,0,796,0,0,0,0,0,0,0,5519,0,0,0,0,0,3242,0,0,0,1248,0,56,0,0,0,2892,0,0,0,0,0,0,0,12894,0,0,0,0,0,695,0,0,0,0,0,0,0,0,0,1072,0,1096,0,0,0,0,0,0,0,0,0,3718,0,0,0,0,0,0,0,0,0,0,0,0,0,2579,0,0,0,0,0,0,0,0,0,4705,0,0,0]
  have ok : scan 1939 295 xs := by decide +kernel
  apply scan_sound xs 1939 _ p hl _ hp
  · rwa [rank1939]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small2067 (p : ℕ) (hp : p.Prime) (hl : 2067 ≤ p) (hu : p < 2195) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,4125,0,0,0,0,0,0,0,0,0,0,0,2117,0,927,0,0,0,3739,0,912,0,0,0,0,0,0,0,0,0,738,0,0,0,0,0,0,0,0,0,0,0,258,0,7016,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1376,0,1517,0,0,0,0,0,614,0,0,0,1857,0,3662,0,0,0,0,0,0,0,0,0,5201,0,0,0,0,0,0,0,1909,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 2067 311 xs := by decide +kernel
  apply scan_sound xs 2067 _ p hl _ hp
  · rwa [rank2067]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small2195 (p : ℕ) (hp : p.Prime) (hl : 2195 ≤ p) (hu : p < 2323) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,1593,0,0,0,1732,0,0,0,0,0,184,0,0,0,0,0,0,0,2005,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1363,0,1641,0,0,0,56,0,0,0,0,0,0,0,157,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15045,0,6769,0,0,0,12417,0,0,0,0,0,0,0,1969,0,0,0,0,0,12169,0,0,0,0,0,2689,0,0,0,8953,0,0,0,0,0,0,0,0,0,0,0,1171,0,3364,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 2195 327 xs := by decide +kernel
  apply scan_sound xs 2195 _ p hl _ hp
  · rwa [rank2195]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small2323 (p : ℕ) (hp : p.Prime) (hl : 2323 ≤ p) (hu : p < 2451) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,0,0,11538,0,0,0,0,0,1411,0,1593,0,0,0,0,0,775,0,0,0,572,0,0,0,0,0,35,0,0,0,0,0,0,0,0,0,0,0,0,0,7588,0,0,0,0,0,1515,0,0,0,2016,0,2032,0,0,0,0,0,438,0,0,0,2308,0,0,0,0,0,4795,0,0,0,0,0,0,0,0,0,0,0,4009,0,0,0,0,0,2891,0,0,0,0,0,5998,0,0,0,0,0,0,0,0,0,0,0,0,0,765,0,0,0,1146,0,0,0,0,0,188,0,0,0]
  have ok : scan 2323 344 xs := by decide +kernel
  apply scan_sound xs 2323 _ p hl _ hp
  · rwa [rank2323]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small2451 (p : ℕ) (hp : p.Prime) (hl : 2451 ≤ p) (hu : p < 2579) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,2415,0,0,0,0,0,0,0,3472,0,0,0,0,0,7779,0,0,0,827,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3329,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10789,0,0,0,0,0,0,0,0,0,11936,0,0,0,0,0,0,0,7937,0,0,0,2319,0,0,0,0,0,89,0,7477,0,0,0,0,0,1376,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 2451 363 xs := by decide +kernel
  apply scan_sound xs 2451 _ p hl _ hp
  · rwa [rank2451]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small2579 (p : ℕ) (hp : p.Prime) (hl : 2579 ≤ p) (hu : p < 2707) : HasPal p.primeCounting p := by
  let xs : List ℕ := [445,0,0,0,0,0,0,0,0,0,0,0,1067,0,1717,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,385,0,0,0,0,0,0,0,1283,0,0,0,892,0,0,0,0,0,0,0,0,0,0,0,894,0,0,0,0,0,0,0,0,0,0,0,0,0,1316,0,0,0,0,0,0,0,0,0,6498,0,1083,0,0,0,3233,0,0,0,0,0,0,0,167,0,0,0,0,0,5942,0,0,0,0,0,2989,0,0,0,9813,0,1031,0,0,0,13453,0,0,0,0,0,5211,0,0,0,0,0,0,0]
  have ok : scan 2579 375 xs := by decide +kernel
  apply scan_sound xs 2579 _ p hl _ hp
  · rwa [rank2579]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small2707 (p : ℕ) (hp : p.Prime) (hl : 2707 ≤ p) (hu : p < 2835) : HasPal p.primeCounting p := by
  let xs : List ℕ := [1266,0,0,0,823,0,1444,0,0,0,0,0,1511,0,0,0,0,0,0,0,0,0,2914,0,4019,0,0,0,0,0,0,0,0,0,3676,0,0,0,0,0,0,0,4661,0,0,0,1153,0,0,0,0,0,0,0,0,0,0,0,0,0,2736,0,0,0,0,0,0,0,0,0,6781,0,0,0,0,0,0,0,0,0,0,0,1474,0,10753,0,0,0,0,0,934,0,0,0,2753,0,3283,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7828,0,0,0,0,0,0,0,0,0,0,0,0,0,965,0]
  have ok : scan 2707 393 xs := by decide +kernel
  apply scan_sound xs 2707 _ p hl _ hp
  · rwa [rank2707]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small2835 (p : ℕ) (hp : p.Prime) (hl : 2835 ≤ p) (hu : p < 2963) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,1368,0,0,0,0,0,1905,0,0,0,0,0,0,0,1317,0,0,0,0,0,3076,0,0,0,5071,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1524,0,0,0,0,0,0,0,356,0,0,0,0,0,0,0,0,0,85,0,0,0,0,0,5988,0,0,0,0,0,1295,0,0,0,0,0,0,0,4327,0,0,0,0,0,0,0,0,0,896,0,0,0,0,0,0,0,0,0,0,0,134,0,0,0,0,0,0,0,0,0,0,0,0,0,2492,0,0,0,4395,0,0,0,0,0]
  have ok : scan 2835 411 xs := by decide +kernel
  apply scan_sound xs 2835 _ p hl _ hp
  · rwa [rank2835]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small2963 (p : ℕ) (hp : p.Prime) (hl : 2963 ≤ p) (hu : p < 3091) : HasPal p.primeCounting p := by
  let xs : List ℕ := [6978,0,0,0,0,0,2845,0,4354,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2858,0,273,0,0,0,0,0,0,0,0,0,10544,0,0,0,0,0,0,0,2322,0,0,0,6192,0,0,0,0,0,0,0,0,0,0,0,0,0,2253,0,0,0,1127,0,0,0,0,0,0,0,7695,0,0,0,0,0,0,0,0,0,0,0,1757,0,0,0,0,0,2083,0,0,0,0,0,0,0,0,0,0,0,742,0,0,0,4729,0,0,0,0,0,9983,0]
  have ok : scan 2963 426 xs := by decide +kernel
  apply scan_sound xs 2963 _ p hl _ hp
  · rwa [rank2963]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small3091 (p : ℕ) (hp : p.Prime) (hl : 3091 ≤ p) (hu : p < 3219) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4669,0,0,0,0,0,0,0,0,0,16,0,6985,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,100632,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,153,0,0,0,2201,0,15098,0,0,0,0,0,0,0,0,0,0,0,1157,0,0,0,0,0,258,0,0,0,5932,0,0,0,0,0,0,0,0,0,0,0,2069,0,0,0,0,0,3905,0,0,0,0,0,0,0,2705,0]
  have ok : scan 3091 442 xs := by decide +kernel
  apply scan_sound xs 3091 _ p hl _ hp
  · rwa [rank3091]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small3219 (p : ℕ) (hp : p.Prime) (hl : 3219 ≤ p) (hu : p < 3347) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,6378,0,0,0,0,0,0,0,771,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,118,0,2303,0,0,0,4058,0,1208,0,0,0,0,0,0,0,0,0,0,0,4951,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1327,0,263,0,0,0,0,0,807,0,0,0,0,0,2455,0,0,0,0,0,4766,0,0,0,4038,0,0,0,0,0,1732,0,4343,0,0,0,0,0,0,0,0,0,0,0,492,0,0,0]
  have ok : scan 3219 455 xs := by decide +kernel
  apply scan_sound xs 3219 _ p hl _ hp
  · rwa [rank3219]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small3347 (p : ℕ) (hp : p.Prime) (hl : 3347 ≤ p) (hu : p < 3475) : HasPal p.primeCounting p := by
  let xs : List ℕ := [7578,0,0,0,0,0,0,0,0,0,0,0,1217,0,905,0,0,0,0,0,0,0,0,0,20582,0,10118,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11861,0,4663,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1069,0,0,0,0,0,122,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3283,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16495,0,0,0,0,0,0,0,2152,0,0,0,11806,0,124,0,0,0,5434,0,2076,0,0,0,0,0]
  have ok : scan 3347 471 xs := by decide +kernel
  apply scan_sound xs 3347 _ p hl _ hp
  · rwa [rank3347]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small3475 (p : ℕ) (hp : p.Prime) (hl : 3475 ≤ p) (hu : p < 3603) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,0,0,0,0,0,0,0,1595,0,0,0,0,0,0,0,0,0,0,0,9734,0,0,0,0,0,3038,0,0,0,0,0,0,0,0,0,4597,0,4173,0,0,0,2966,0,0,0,0,0,6251,0,10207,0,0,0,0,0,2113,0,0,0,0,0,0,0,0,0,5059,0,415,0,0,0,0,0,0,0,0,0,0,0,1396,0,0,0,0,0,0,0,0,0,4313,0,4233,0,0,0,0,0,0,0,0,0,3978,0,0,0,0,0,0,0,0,0]
  have ok : scan 3475 487 xs := by decide +kernel
  apply scan_sound xs 3475 _ p hl _ hp
  · rwa [rank3475]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small3603 (p : ℕ) (hp : p.Prime) (hl : 3603 ≤ p) (hu : p < 3731) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,1024,0,0,0,0,0,1398,0,0,0,2675,0,0,0,0,0,27,0,0,0,0,0,0,0,14675,0,0,0,0,0,4953,0,0,0,0,0,3667,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3747,0,0,0,0,0,0,0,0,0,0,0,112,0,1057,0,0,0,138,0,0,0,0,0,0,0,0,0,0,0,0,0,3403,0,0,0,0,0,2915,0,0,0,41,0,0,0,0,0,0,0,6078,0,0,0,0,0,0,0,0,0,12009,0,0,0,0,0,0,0,4061,0,0,0]
  have ok : scan 3603 503 xs := by decide +kernel
  apply scan_sound xs 3603 _ p hl _ hp
  · rwa [rank3603]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small3731 (p : ℕ) (hp : p.Prime) (hl : 3731 ≤ p) (hu : p < 3859) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,1514,0,0,0,0,0,1698,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,531,0,0,0,0,0,1094,0,5579,0,0,0,0,0,0,0,0,0,997,0,0,0,0,0,0,0,0,0,0,0,0,0,783,0,0,0,4557,0,0,0,0,0,275,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2207,0,6321,0,0,0,0,0,0,0,0,0,665,0,0,0,0,0,0,0,0,0,0,0,0,0,4661,0,0,0,1698,0,3964,0,0,0,0,0]
  have ok : scan 3731 520 xs := by decide +kernel
  apply scan_sound xs 3731 _ p hl _ hp
  · rwa [rank3731]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small3859 (p : ℕ) (hp : p.Prime) (hl : 3859 ≤ p) (hu : p < 3987) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,2904,0,0,0,0,0,0,0,0,0,0,0,0,0,5386,0,0,0,582,0,0,0,0,0,0,0,3377,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2788,0,0,0,4159,0,0,0,0,0,4045,0,362,0,0,0,4394,0,0,0,0,0,5953,0,3991,0,0,0,0,0,0,0,0,0,0,0,1852,0,0,0,10635,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2568,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 3859 535 xs := by decide +kernel
  apply scan_sound xs 3859 _ p hl _ hp
  · rwa [rank3859]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small3987 (p : ℕ) (hp : p.Prime) (hl : 3987 ≤ p) (hu : p < 4115) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,1158,0,0,0,0,0,0,0,0,0,0,0,2515,0,4572,0,0,0,277,0,0,0,0,0,1412,0,0,0,0,0,1544,0,6215,0,0,0,0,0,1977,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,19086,0,7163,0,0,0,0,0,2014,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,732,0,0,0,0,0,1712,0,0,0,0,0,0,0,0,0,0,0,4946,0,101,0,0,0,0,0,7412,0,0,0,0,0,0,0,0,0,0,0,6562,0,0,0]
  have ok : scan 3987 549 xs := by decide +kernel
  apply scan_sound xs 3987 _ p hl _ hp
  · rwa [rank3987]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small4115 (p : ℕ) (hp : p.Prime) (hl : 4115 ≤ p) (hu : p < 4243) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,155,0,1862,0,0,0,5042,0,0,0,0,0,2594,0,0,0,0,0,0,0,0,0,0,0,0,0,7544,0,0,0,2815,0,5991,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5746,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3655,0,0,0,0,0,0,0,0,0,581,0,0,0,0,0,5527,0,251,0,0,0,0,0,0,0,0,0,765,0,2272,0,0,0,0,0,0,0,0,0,3891,0]
  have ok : scan 4115 566 xs := by decide +kernel
  apply scan_sound xs 4115 _ p hl _ hp
  · rwa [rank4115]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small4243 (p : ℕ) (hp : p.Prime) (hl : 4243 ≤ p) (hu : p < 4371) : HasPal p.primeCounting p := by
  let xs : List ℕ := [9588,0,0,0,0,0,0,0,0,0,694,0,0,0,0,0,1623,0,3237,0,0,0,0,0,0,0,0,0,6951,0,5386,0,0,0,0,0,0,0,0,0,5336,0,0,0,0,0,5347,0,0,0,0,0,0,0,6494,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1206,0,0,0,0,0,0,0,0,0,9237,0,3122,0,0,0,0,0,0,0,0,0,50079,0,0,0,0,0,0,0,1457,0,0,0,0,0,1319,0,0,0,0,0,0,0]
  have ok : scan 4243 581 xs := by decide +kernel
  apply scan_sound xs 4243 _ p hl _ hp
  · rwa [rank4243]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small4371 (p : ℕ) (hp : p.Prime) (hl : 4371 ≤ p) (hu : p < 4499) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,1048,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1306,0,0,0,0,0,5218,0,0,0,0,0,0,0,0,0,0,0,1004,0,0,0,0,0,0,0,0,0,0,0,3611,0,6329,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6978,0,0,0,0,0,2906,0,0,0,7594,0,0,0,0,0,1736,0,0,0,0,0,8409,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,14926,0,7416,0,0,0,0,0,0,0,0,0,2299,0,0,0,0,0]
  have ok : scan 4371 596 xs := by decide +kernel
  apply scan_sound xs 4371 _ p hl _ hp
  · rwa [rank4371]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small4499 (p : ℕ) (hp : p.Prime) (hl : 4499 ≤ p) (hu : p < 4627) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,7368,0,0,0,0,0,2481,0,0,0,22762,0,10276,0,0,0,5548,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9477,0,578,0,0,0,0,0,0,0,0,0,0,0,1493,0,0,0,0,0,5146,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3413,0,0,0,0,0,0,0,857,0,0,0,0,0,3512,0,0,0,0,0,3853,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2071,0,0,0,0,0]
  have ok : scan 4499 610 xs := by decide +kernel
  apply scan_sound xs 4499 _ p hl _ hp
  · rwa [rank4499]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small4627 (p : ℕ) (hp : p.Prime) (hl : 4627 ≤ p) (hu : p < 4755) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,0,0,4519,0,614,0,0,0,3343,0,0,0,0,0,101212,0,4491,0,0,0,0,0,4417,0,0,0,0,0,2368,0,0,0,0,0,0,0,0,0,10177,0,0,0,0,0,7392,0,0,0,0,0,0,0,0,0,0,0,125,0,0,0,0,0,0,0,0,0,0,0,11047,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9512,0,3354,0,0,0,0,0,4153,0,0,0,362,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4731,0,0,0]
  have ok : scan 4627 624 xs := by decide +kernel
  apply scan_sound xs 4627 _ p hl _ hp
  · rwa [rank4627]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small4755 (p : ℕ) (hp : p.Prime) (hl : 4755 ≤ p) (hu : p < 4883) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,3822,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4592,0,0,0,643,0,2477,0,0,0,2384,0,0,0,0,0,3985,0,375,0,0,0,0,0,0,0,0,0,0,0,728,0,0,0,4343,0,0,0,0,0,0,0,0,0,0,0,0,0,2528,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2459,0,0,0,0,0,0,0,0,0,1994,0,0,0,0,0,10642,0,0,0,0,0]
  have ok : scan 4755 640 xs := by decide +kernel
  apply scan_sound xs 4755 _ p hl _ hp
  · rwa [rank4755]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small4883 (p : ℕ) (hp : p.Prime) (hl : 4883 ≤ p) (hu : p < 5011) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,9095,0,0,0,0,0,0,0,0,0,0,0,0,0,3083,0,0,0,0,0,3679,0,0,0,0,0,0,0,0,0,5511,0,0,0,0,0,0,0,0,0,0,0,1264,0,2575,0,0,0,1616,0,0,0,0,0,14622,0,0,0,0,0,0,0,9307,0,0,0,0,0,8037,0,0,0,0,0,0,0,0,0,714,0,3998,0,0,0,5388,0,0,0,0,0,0,0,0,0,0,0,0,0,7792,0,0,0,0,0,16,0,0,0,0,0,8816,0,0,0,3119,0,0,0,0,0,5924,0]
  have ok : scan 4883 653 xs := by decide +kernel
  apply scan_sound xs 4883 _ p hl _ hp
  · rwa [rank4883]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small5011 (p : ℕ) (hp : p.Prime) (hl : 5011 ≤ p) (hu : p < 5139) : HasPal p.primeCounting p := by
  let xs : List ℕ := [5045,0,0,0,0,0,0,0,0,0,2696,0,6905,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1228,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,1236,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2196,0,0,0,5815,0,0,0,0,0,3317,0,0,0,0,0,0,0,0,0,0,0,2036,0,2581,0,0,0,0,0,6328,0,0,0,0,0,11474,0,0,0,0,0,1512,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 5011 671 xs := by decide +kernel
  apply scan_sound xs 5011 _ p hl _ hp
  · rwa [rank5011]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small5139 (p : ℕ) (hp : p.Prime) (hl : 5139 ≤ p) (hu : p < 5267) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,175,0,0,0,0,0,4861,0,0,0,0,0,0,0,0,0,0,0,0,0,8959,0,0,0,14901,0,0,0,0,0,0,0,9875,0,0,0,0,0,0,0,0,0,10605,0,0,0,0,0,0,0,5586,0,0,0,0,0,0,0,0,0,0,0,2312,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2398,0,0,0,8369,0,1174,0,0,0,50592,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6074,0,0,0,0,0]
  have ok : scan 5139 685 xs := by decide +kernel
  apply scan_sound xs 5139 _ p hl _ hp
  · rwa [rank5139]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small5267 (p : ℕ) (hp : p.Prime) (hl : 5267 ≤ p) (hu : p < 5395) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,1418,0,0,0,0,0,4572,0,8629,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,304,0,0,0,0,0,11596,0,0,0,0,0,4553,0,0,0,0,0,0,0,0,0,0,0,0,0,20023,0,0,0,0,0,0,0,0,0,4371,0,0,0,0,0,0,0,0,0,0,0,0,0,10837,0,0,0,1981,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8227,0,0,0,0,0,5497,0,0,0,0,0,6582,0]
  have ok : scan 5267 698 xs := by decide +kernel
  apply scan_sound xs 5267 _ p hl _ hp
  · rwa [rank5267]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small5395 (p : ℕ) (hp : p.Prime) (hl : 5395 ≤ p) (hu : p < 5523) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,5692,0,0,0,0,0,0,0,8102,0,0,0,0,0,19073,0,0,0,28995,0,102,0,0,0,0,0,0,0,0,0,0,0,1742,0,0,0,0,0,13119,0,0,0,3662,0,3779,0,0,0,0,0,5643,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7697,0,0,0,0,0,5061,0,45539,0,0,0,16332,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5431,0,75,0,0,0,6536,0,0,0,0,0,0,0,0,0,0,0,3085,0,781,0]
  have ok : scan 5395 711 xs := by decide +kernel
  apply scan_sound xs 5395 _ p hl _ hp
  · rwa [rank5395]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small5523 (p : ℕ) (hp : p.Prime) (hl : 5523 ≤ p) (hu : p < 5651) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,704,0,0,0,8507,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9861,0,0,0,0,0,2785,0,0,0,0,0,4203,0,0,0,1246,0,0,0,0,0,0,0,672,0,0,0,0,0,0,0,0,0,394,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6567,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,11312,0,11832,0,0,0,0,0,14788,0,0,0]
  have ok : scan 5523 730 xs := by decide +kernel
  apply scan_sound xs 5523 _ p hl _ hp
  · rwa [rank5523]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small5651 (p : ℕ) (hp : p.Prime) (hl : 5651 ≤ p) (hu : p < 5779) : HasPal p.primeCounting p := by
  let xs : List ℕ := [1081,0,8195,0,0,0,2063,0,10539,0,0,0,0,0,0,0,0,0,9518,0,0,0,0,0,0,0,0,0,0,0,0,0,24998,0,0,0,0,0,4109,0,0,0,15243,0,0,0,0,0,0,0,7022,0,0,0,0,0,0,0,0,0,568,0,0,0,0,0,9825,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1359,0,0,0,5452,0,1492,0,0,0,0,0,9322,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 5651 742 xs := by decide +kernel
  apply scan_sound xs 5651 _ p hl _ hp
  · rwa [rank5651]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small5779 (p : ℕ) (hp : p.Prime) (hl : 5779 ≤ p) (hu : p < 5907) : HasPal p.primeCounting p := by
  let xs : List ℕ := [20197,0,0,0,12469,0,0,0,0,0,0,0,3661,0,0,0,0,0,0,0,0,0,15403,0,0,0,0,0,619,0,0,0,0,0,9568,0,0,0,0,0,0,0,18785,0,0,0,0,0,4719,0,0,0,0,0,0,0,0,0,0,0,7365,0,0,0,12496,0,0,0,0,0,301,0,12048,0,0,0,0,0,12669,0,0,0,2328,0,0,0,0,0,3921,0,344,0,0,0,0,0,0,0,0,0,1504,0,7586,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2671,0,0,0,0,0,13882,0,0,0]
  have ok : scan 5779 757 xs := by decide +kernel
  apply scan_sound xs 5779 _ p hl _ hp
  · rwa [rank5779]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small5907 (p : ℕ) (hp : p.Prime) (hl : 5907 ≤ p) (hu : p < 6035) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1684,0,0,0,7134,0,0,0,0,0,0,0,0,0,0,0,32681,0,0,0,0,0,0,0,0,0,0,0,0,0,13275,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,342,0,0,0,0,0,5875,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10958,0,0,0,1112,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1385,0,0,0,0,0]
  have ok : scan 5907 777 xs := by decide +kernel
  apply scan_sound xs 5907 _ p hl _ hp
  · rwa [rank5907]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small6035 (p : ℕ) (hp : p.Prime) (hl : 6035 ≤ p) (hu : p < 6163) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,7264,0,0,0,0,0,1534,0,0,0,30486,0,0,0,0,0,8307,0,0,0,0,0,0,0,0,0,0,0,0,0,4306,0,0,0,0,0,1043,0,0,0,0,0,7526,0,0,0,0,0,0,0,0,0,716,0,11819,0,0,0,0,0,0,0,0,0,10205,0,0,0,0,0,0,0,0,0,0,0,1021,0,0,0,0,0,0,0,15456,0,0,0,0,0,0,0,0,0,4187,0,13535,0,0,0,0,0,0,0,0,0,20674,0,0,0,0,0,0,0,15249,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 6035 786 xs := by decide +kernel
  apply scan_sound xs 6035 _ p hl _ hp
  · rwa [rank6035]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small6163 (p : ℕ) (hp : p.Prime) (hl : 6163 ≤ p) (hu : p < 6291) : HasPal p.primeCounting p := by
  let xs : List ℕ := [17627,0,0,0,0,0,0,0,0,0,4703,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1389,0,1078,0,0,0,9563,0,0,0,0,0,0,0,18294,0,0,0,0,0,2711,0,0,0,5719,0,0,0,0,0,0,0,56,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2238,0,0,0,0,0,0,0,0,0,10799,0,0,0,0,0,7088,0,0,0,0,0,7028,0,469,0,0,0,0,0,12272,0,0,0,0,0,0,0,0,0,3149,0,0,0]
  have ok : scan 6163 802 xs := by decide +kernel
  apply scan_sound xs 6163 _ p hl _ hp
  · rwa [rank6163]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small6291 (p : ℕ) (hp : p.Prime) (hl : 6291 ≤ p) (hu : p < 6419) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,23795,0,3291,0,0,0,0,0,0,0,0,0,1199,0,0,0,0,0,3899,0,0,0,0,0,11806,0,0,0,0,0,943,0,0,0,0,0,0,0,17925,0,0,0,0,0,1264,0,0,0,0,0,0,0,0,0,20792,0,0,0,0,0,4343,0,10602,0,0,0,0,0,746,0,0,0,0,0,22609,0,0,0,0,0,157,0,0,0,0,0,0,0,0,0,2212,0,0,0,0,0,0,0,17017,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 6291 818 xs := by decide +kernel
  apply scan_sound xs 6291 _ p hl _ hp
  · rwa [rank6291]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small6419 (p : ℕ) (hp : p.Prime) (hl : 6419 ≤ p) (hu : p < 6547) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,10202,0,0,0,0,0,1236,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,807,0,2231,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3924,0,0,0,5998,0,0,0,0,0,0,0,7793,0,0,0,0,0,0,0,0,0,1169,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3098,0,0,0,0,0,0,0,8312,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 6419 834 xs := by decide +kernel
  apply scan_sound xs 6419 _ p hl _ hp
  · rwa [rank6419]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small6547 (p : ℕ) (hp : p.Prime) (hl : 6547 ≤ p) (hu : p < 6675) : HasPal p.primeCounting p := by
  let xs : List ℕ := [955,0,0,0,1453,0,11357,0,0,0,0,0,0,0,0,0,30177,0,0,0,0,0,6749,0,1528,0,0,0,0,0,6489,0,0,0,5563,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,21543,0,0,0,0,0,0,0,843,0,0,0,0,0,0,0,0,0,0,0,14123,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1077,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6059,0,0,0,0,0,6821,0,3015,0,0,0,0,0,0,0,0,0,0,0,2142,0]
  have ok : scan 6547 844 xs := by decide +kernel
  apply scan_sound xs 6547 _ p hl _ hp
  · rwa [rank6547]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small6675 (p : ℕ) (hp : p.Prime) (hl : 6675 ≤ p) (hu : p < 6803) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,12226,0,0,0,0,0,0,0,0,0,263,0,2178,0,0,0,0,0,0,0,0,0,14563,0,1355,0,0,0,0,0,5697,0,0,0,0,0,0,0,0,0,3945,0,0,0,0,0,0,0,0,0,0,0,0,0,16014,0,0,0,7586,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2216,0,6454,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2079,0,18747,0,0,0,0,0,0,0,0,0,5281,0,6865,0,0,0,0,0,0,0,0,0]
  have ok : scan 6675 860 xs := by decide +kernel
  apply scan_sound xs 6675 _ p hl _ hp
  · rwa [rank6675]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small6803 (p : ℕ) (hp : p.Prime) (hl : 6803 ≤ p) (hu : p < 6931) : HasPal p.primeCounting p := by
  let xs : List ℕ := [18086,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3276,0,0,0,17248,0,13544,0,0,0,23312,0,0,0,0,0,0,0,14365,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5162,0,0,0,0,0,1898,0,0,0,0,0,18824,0,4029,0,0,0,0,0,0,0,0,0,0,0,7418,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1609,0,0,0,0,0,0,0,8867,0,0,0,12735,0,0,0,0,0,4349,0,0,0,0,0,0,0,0,0,0,0,0,0]
  have ok : scan 6803 875 xs := by decide +kernel
  apply scan_sound xs 6803 _ p hl _ hp
  · rwa [rank6803]
  · exact lt_of_lt_of_le hu (by decide +kernel)
set_option maxRecDepth 8000 in
private theorem small6931 (p : ℕ) (hp : p.Prime) (hl : 6931 ≤ p) (hu : p < 7000) : HasPal p.primeCounting p := by
  let xs : List ℕ := [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,24302,0,1745,0,0,0,0,0,0,0,0,0,16746,0,24937,0,0,0,0,0,23597,0,0,0,3802,0,0,0,0,0,8225,0,0,0,0,0,15821,0,0,0,0,0,0,0,1267,0,0,0,0,0,15029,0,0]
  have ok : scan 6931 890 xs := by decide +kernel
  apply scan_sound xs 6931 _ p hl _ hp
  · rwa [rank6931]
  · exact lt_of_lt_of_le hu (by decide +kernel)
private theorem small_all (p : ℕ) (hp : p.Prime) (hu : p < 7000) : HasPal p.primeCounting p := by
  by_cases h : p<19
  · have hcases : p=2 ∨ p=3 ∨ p=5 ∨ p=7 ∨ p=11 ∨ p=13 ∨ p=17 := by interval_cases p <;> first | omega | norm_num at hp
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨2,by decide,?_,List.Palindrome.of_reverse_eq ?_,?_⟩ <;> decide +kernel
    · refine ⟨33,by decide,?_,List.Palindrome.of_reverse_eq ?_,?_⟩ <;> decide +kernel
    · refine ⟨505,by decide,?_,List.Palindrome.of_reverse_eq ?_,?_⟩ <;> decide +kernel
    · refine ⟨1001,by decide,?_,List.Palindrome.of_reverse_eq ?_,?_⟩ <;> decide +kernel
    · refine ⟨10901,by decide,?_,List.Palindrome.of_reverse_eq ?_,?_⟩ <;> decide +kernel
    · refine ⟨101101,by decide,?_,List.Palindrome.of_reverse_eq ?_,?_⟩ <;> decide +kernel
    · refine ⟨1009001,by decide,?_,List.Palindrome.of_reverse_eq ?_,?_⟩ <;> decide +kernel
  have lo : 19≤p := by omega
  by_cases h147 : p<147; exact small19 p hp (by omega) h147
  by_cases h275 : p<275; exact small147 p hp (by omega) h275
  by_cases h403 : p<403; exact small275 p hp (by omega) h403
  by_cases h531 : p<531; exact small403 p hp (by omega) h531
  by_cases h659 : p<659; exact small531 p hp (by omega) h659
  by_cases h787 : p<787; exact small659 p hp (by omega) h787
  by_cases h915 : p<915; exact small787 p hp (by omega) h915
  by_cases h1043 : p<1043; exact small915 p hp (by omega) h1043
  by_cases h1171 : p<1171; exact small1043 p hp (by omega) h1171
  by_cases h1299 : p<1299; exact small1171 p hp (by omega) h1299
  by_cases h1427 : p<1427; exact small1299 p hp (by omega) h1427
  by_cases h1555 : p<1555; exact small1427 p hp (by omega) h1555
  by_cases h1683 : p<1683; exact small1555 p hp (by omega) h1683
  by_cases h1811 : p<1811; exact small1683 p hp (by omega) h1811
  by_cases h1939 : p<1939; exact small1811 p hp (by omega) h1939
  by_cases h2067 : p<2067; exact small1939 p hp (by omega) h2067
  by_cases h2195 : p<2195; exact small2067 p hp (by omega) h2195
  by_cases h2323 : p<2323; exact small2195 p hp (by omega) h2323
  by_cases h2451 : p<2451; exact small2323 p hp (by omega) h2451
  by_cases h2579 : p<2579; exact small2451 p hp (by omega) h2579
  by_cases h2707 : p<2707; exact small2579 p hp (by omega) h2707
  by_cases h2835 : p<2835; exact small2707 p hp (by omega) h2835
  by_cases h2963 : p<2963; exact small2835 p hp (by omega) h2963
  by_cases h3091 : p<3091; exact small2963 p hp (by omega) h3091
  by_cases h3219 : p<3219; exact small3091 p hp (by omega) h3219
  by_cases h3347 : p<3347; exact small3219 p hp (by omega) h3347
  by_cases h3475 : p<3475; exact small3347 p hp (by omega) h3475
  by_cases h3603 : p<3603; exact small3475 p hp (by omega) h3603
  by_cases h3731 : p<3731; exact small3603 p hp (by omega) h3731
  by_cases h3859 : p<3859; exact small3731 p hp (by omega) h3859
  by_cases h3987 : p<3987; exact small3859 p hp (by omega) h3987
  by_cases h4115 : p<4115; exact small3987 p hp (by omega) h4115
  by_cases h4243 : p<4243; exact small4115 p hp (by omega) h4243
  by_cases h4371 : p<4371; exact small4243 p hp (by omega) h4371
  by_cases h4499 : p<4499; exact small4371 p hp (by omega) h4499
  by_cases h4627 : p<4627; exact small4499 p hp (by omega) h4627
  by_cases h4755 : p<4755; exact small4627 p hp (by omega) h4755
  by_cases h4883 : p<4883; exact small4755 p hp (by omega) h4883
  by_cases h5011 : p<5011; exact small4883 p hp (by omega) h5011
  by_cases h5139 : p<5139; exact small5011 p hp (by omega) h5139
  by_cases h5267 : p<5267; exact small5139 p hp (by omega) h5267
  by_cases h5395 : p<5395; exact small5267 p hp (by omega) h5395
  by_cases h5523 : p<5523; exact small5395 p hp (by omega) h5523
  by_cases h5651 : p<5651; exact small5523 p hp (by omega) h5651
  by_cases h5779 : p<5779; exact small5651 p hp (by omega) h5779
  by_cases h5907 : p<5907; exact small5779 p hp (by omega) h5907
  by_cases h6035 : p<6035; exact small5907 p hp (by omega) h6035
  by_cases h6163 : p<6163; exact small6035 p hp (by omega) h6163
  by_cases h6291 : p<6291; exact small6163 p hp (by omega) h6291
  by_cases h6419 : p<6419; exact small6291 p hp (by omega) h6419
  by_cases h6547 : p<6547; exact small6419 p hp (by omega) h6547
  by_cases h6675 : p<6675; exact small6547 p hp (by omega) h6675
  by_cases h6803 : p<6803; exact small6675 p hp (by omega) h6803
  by_cases h6931 : p<6931; exact small6803 p hp (by omega) h6931
  by_cases h7000 : p<7000; exact small6931 p hp (by omega) h7000
  omega
private theorem medium (p : ℕ) [Fact p.Prime] (lo : 7000 ≤ p) (hi : p < 1000000) : HasPal p.primeCounting p := by
  have smallConst (a : ℕ) (ha : 0<a) (hab : a<p) : (a:ZMod p) ≠ 0 := fun hz => (Nat.le_of_dvd ha ((ZMod.natCast_eq_zero_iff _ _).mp hz)).not_gt hab
  have h10 : (10:ZMod p) ≠ 0 := by exact_mod_cast smallConst 10 (by decide) (by omega)
  have hu : (99:ZMod p)*10≠0 := mul_ne_zero (by exact_mod_cast smallConst 99 (by decide) (by omega)) h10
  by_cases hi7388 : p≤7388
  · have hr := Nat.monotone_primeCounting' (show 7000≤p+1 by omega)
    rw [rank7000] at hr
    change 900 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 4 83 89 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi7906 : p≤7906
  · have hr := Nat.monotone_primeCounting' (show 7389≤p+1 by omega)
    rw [rank7389] at hr
    change 938 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 4 85 93 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi8713 : p≤8713
  · have hr := Nat.monotone_primeCounting' (show 7908≤p+1 by omega)
    rw [rank7908] at hr
    change 999 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 4 88 99 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi9208 : p≤9208
  · have hr := Nat.monotone_primeCounting' (show 7908≤p+1 by omega)
    rw [rank7908] at hr
    change 999 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 4 93 99 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi9999 : p≤9999
  · have hr := Nat.monotone_primeCounting' (show 9210≤p+1 by omega)
    rw [rank9210] at hr
    change 1142 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 4 95 114 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi10099 : p≤10099
  · have hr := Nat.monotone_primeCounting' (show 10000≤p+1 by omega)
    rw [rank10000] at hr
    change 1229 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 99 102 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi10301 : p≤10301
  · have hr := Nat.monotone_primeCounting' (show 10100≤p+1 by omega)
    rw [rank10100] at hr
    change 1240 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 100 103 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi10606 : p≤10606
  · have hr := Nat.monotone_primeCounting' (show 10302≤p+1 by omega)
    rw [rank10302] at hr
    change 1263 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 101 105 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi10915 : p≤10915
  · have hr := Nat.monotone_primeCounting' (show 10608≤p+1 by omega)
    rw [rank10608] at hr
    change 1294 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 102 107 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi11441 : p≤11441
  · have hr := Nat.monotone_primeCounting' (show 10916≤p+1 by omega)
    rw [rank10916] at hr
    change 1327 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 104 110 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi12085 : p≤12085
  · have hr := Nat.monotone_primeCounting' (show 11442≤p+1 by omega)
    rw [rank11442] at hr
    change 1379 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 106 114 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi13081 : p≤13081
  · have hr := Nat.monotone_primeCounting' (show 12086≤p+1 by omega)
    rw [rank12086] at hr
    change 1446 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 109 120 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi13681 : p≤13681
  · have hr := Nat.monotone_primeCounting' (show 12086≤p+1 by omega)
    rw [rank12086] at hr
    change 1446 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 114 120 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi15545 : p≤15545
  · have hr := Nat.monotone_primeCounting' (show 13682≤p+1 by omega)
    rw [rank13682] at hr
    change 1616 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 116 134 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi16617 : p≤16617
  · have hr := Nat.monotone_primeCounting' (show 13682≤p+1 by omega)
    rw [rank13682] at hr
    change 1616 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 124 134 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi20353 : p≤20353
  · have hr := Nat.monotone_primeCounting' (show 16618≤p+1 by omega)
    rw [rank16618] at hr
    change 1921 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 128 159 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi22579 : p≤22579
  · have hr := Nat.monotone_primeCounting' (show 16618≤p+1 by omega)
    rw [rank16618] at hr
    change 1921 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 142 159 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi23851 : p≤23851
  · have hr := Nat.monotone_primeCounting' (show 16618≤p+1 by omega)
    rw [rank16618] at hr
    change 1921 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 150 159 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi33881 : p≤33881
  · have hr := Nat.monotone_primeCounting' (show 23852≤p+1 by omega)
    rw [rank23852] at hr
    change 2652 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 154 220 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi40481 : p≤40481
  · have hr := Nat.monotone_primeCounting' (show 23852≤p+1 by omega)
    rw [rank23852] at hr
    change 2652 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 184 220 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi44221 : p≤44221
  · have hr := Nat.monotone_primeCounting' (show 23852≤p+1 by omega)
    rw [rank23852] at hr
    change 2652 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 201 220 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi46201 : p≤46201
  · have hr := Nat.monotone_primeCounting' (show 23852≤p+1 by omega)
    rw [rank23852] at hr
    change 2652 ≤ p.primeCounting at hr
    exact palindrome_of_blocks _ _ 5 210 220 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi48365 : p≤48365
  · have hr := primeSizeTwo p 17 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 5 214 226 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi51685 : p≤51685
  · have hr := primeSizeTwo p 17 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 5 219 236 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi57432 : p≤57432
  · have hr := primeSizeTwo p 17 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 5 227 253 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi67160 : p≤67160
  · have hr := primeSizeTwo p 17 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 5 239 281 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi80291 : p≤80291
  · have hr := primeSizeTwo p 18 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 5 259 310 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi99999 : p≤99999
  · have hr := primeSizeTwo p 18 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 5 283 371 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi125137 : p≤125137
  · have hr := primeSizeTwo p 18 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 6 316 396 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi175089 : p≤175089
  · have hr := primeSizeTwo p 18 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 6 353 496 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi275045 : p≤275045
  · have hr := primeSizeTwo p 19 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 6 418 658 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi514569 : p≤514569
  · have hr := primeSizeTwo p 20 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 6 524 982 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  by_cases hi999999 : p≤999999
  · have hr := primeSizeTwo p 20 (by omega) (by norm_num;omega)
    exact palindrome_of_blocks _ _ 6 717 1837 (by omega) (by norm_num;omega) (by norm_num;omega) h10 hu (by omega) (by omega)
  omega

theorem allPrimes (p : ℕ) (hp : p.Prime) : HasPal p.primeCounting p := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases h₁ : p < 7000
  · exact small_all p hp h₁
  by_cases h₂ : p < 1000000
  · exact medium p (by omega) h₂
  exact large p (by omega)

end PalBlocks

open OMA.S_oeis_a083143 in
theorem OMA.solution : type_of% @OMA.S_oeis_a083143.main := by
  intro n hn
  let p := nthPrime n
  have hp : p.Prime := Nat.prime_nth_prime _
  have hπ : p.primeCounting=n := by
    have H : p.primeCounting'=n-1 := Nat.primeCounting'_nth_eq _
    change Nat.count Nat.Prime (p+1)=n
    rw [Nat.count_succ,if_pos hp]
    change p.primeCounting'+1=n
    omega
  have H := PalBlocks.allPrimes p hp
  rw [hπ] at H
  let S := {m : ℕ | 0 < m ∧ (Nat.digits 10 m).length = n ∧ (Nat.digits 10 m).Palindrome ∧ p ∣ m}
  have HS : S.Nonempty := H
  exact (show sInf S ∈ S from Nat.sInf_mem HS).1

