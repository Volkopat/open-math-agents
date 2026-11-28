import OMAReductions.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R2

/-! An explicit range for the arctangent integer-value conjecture.

The index is a natural number. Every positive index representable by an
unsigned 64-bit word is covered. The products and certificates use
unbounded integer arithmetic throughout.

For each index below one million, an integer interval excludes integral
slopes of the original Gaussian product. Above one million, signed CRT
constraints force any supposed integral quotient to have at least 120
decimal digits. The long-range certificate then excludes poles nearby by
tracking the rotated factorial-normalized product. It uses 57 Newton
terms per block, exact Horner evaluation, verified rounding bounds, and
2,500 adaptively sized blocks. The final endpoint is 2^64.

For the original conjecture see Amdeberhan, Medina and Moll (2008) and
Ono, https://arxiv.org/abs/2607.05739.
-/

namespace ArctanCert

open Arxiv.«2607.05739»

private lemma eval_gauss_product {p : ℕ} (n : ℕ) (r : ZMod p) (hr : r*r = -1) :
    (A n : ZMod p)+(B n : ZMod p)*r = ∏ j ∈ Finset.Icc 1 n, (1+(j : ZMod p)*r) := by
  let φ : GaussianInt →+* ZMod p := Zsqrtd.lift ⟨r,by simpa only [Int.cast_neg,Int.cast_one] using hr⟩
  change φ (gaussProd n) = _
  rw [gaussProd,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  change ((1:ℤ):ZMod p) + ((j:ℤ):ZMod p)*r = _
  simp

/-- A prime divisor of `1+k²` larger than `n+k` determines the signed residue
of every integer quotient: the two evaluations of the Gaussian product at `k`
and `-k` have opposite vanishing behavior. -/
lemma signed_residue {n p k : ℕ} (hp : p.Prime) (hk : 1≤k) (hkn : k≤n)
    (hsize : n+k<p) (hdiv : p ∣ 1+k^2) {m : ℤ} (hm : B n = A n*m) :
    (m : ZMod p) = (k : ZMod p) := by
  let _ : Fact p.Prime := ⟨hp⟩
  let K : ZMod p := k
  have hsq : K*K = -1 := by
    have h : (1 + K^2 : ZMod p)=0 := by
      simpa only [K,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff (1+k^2) p).mpr hdiv
    linear_combination h
  have plus : (A n : ZMod p)+(B n : ZMod p)*K=0 := by
    rw [eval_gauss_product n K hsq]
    apply Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hk,hkn⟩)
    change 1+K*K=0
    rw [hsq,add_neg_cancel]
  have minus : (A n : ZMod p)+(B n : ZMod p)*(-K) ≠ 0 := by
    rw [eval_gauss_product n (-K) (by simpa only [neg_mul_neg] using hsq)]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj hz
    obtain ⟨hj₁,hjn⟩ := Finset.mem_Icc.mp hj
    have hzero : ((j+k : ℕ) : ZMod p)=0 := by
      rw [Nat.cast_add]
      change (j:ZMod p)+K=0
      calc
        _ = K*(1+(j:ZMod p)*(-K)) := by linear_combination (j:ZMod p)*hsq
        _ = 0 := by rw [hz,mul_zero]
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0<j+k) (by omega : j+k<p))
      ((ZMod.natCast_eq_zero_iff (j+k) p).mp hzero)
  have hquot : (B n : ZMod p)=(A n : ZMod p)*(m : ZMod p) := by
    simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z : ZMod p)) hm
  have hA : (A n : ZMod p)≠0 := by
    intro ha
    exact minus (by simp [hquot,ha])
  have hfactor : (A n : ZMod p)*(1+(m : ZMod p)*K)=0 := by
    calc
      _ = (A n : ZMod p)+(B n : ZMod p)*K := by rw [hquot]; ring
      _ = 0 := plus
  have hz := (mul_eq_zero.mp hfactor).resolve_left hA
  change (m : ZMod p)=K
  linear_combination (m : ZMod p)*hsq - K*hz

end ArctanCert

namespace ArctanCert

open Arxiv.«2607.05739»

private lemma norm_sq_succ (n : ℕ) : A (n+1)^2+B (n+1)^2 =
    (1+((n : ℤ)+1)^2)*(A n^2+B n^2) := by
  have h : gaussProd (n+1) = gaussProd n * (⟨1, ((n+1:ℕ):ℤ)⟩ : GaussianInt) :=
    Finset.prod_Icc_succ_top (by omega : 1≤n+1) _
  simp [A,B,h,Zsqrtd.re_mul,Zsqrtd.im_mul]
  ring

/-- A telescoping estimate bounds the squared norm by `4*n/(n+1)` times the squared factorial. -/
lemma weighted_factorial_bound {n : ℕ} (hn : 1≤n) :
    ((n:ℤ)+1)*(A n^2+B n^2) ≤ 4*(n:ℤ)*(n.factorial:ℤ)^2 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n _ ih =>
    rw [norm_sq_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ]
    have h := mul_le_mul_of_nonneg_left ih
      (by positivity : (0:ℤ)≤((n:ℤ)+2)*(1+((n:ℤ)+1)^2))
    apply le_of_mul_le_mul_left ?_ (by positivity : (0:ℤ)<(n:ℤ)+1)
    nlinarith only [h,sq_nonneg (n.factorial:ℤ)]

lemma factorial_norm_bound (n : ℕ) : A n^2+B n^2 ≤ (2*(n.factorial:ℤ))^2 := by
  cases n with
  | zero => decide
  | succ n =>
    have h := weighted_factorial_bound (n:=n+1) (by omega)
    apply le_of_mul_le_mul_left ?_ (by positivity : (0:ℤ)<((n+1:ℕ):ℤ)+1)
    nlinarith only [h,sq_nonneg (((n+1).factorial):ℤ)]

/-- The imaginary coordinate of the Gaussian product has magnitude at most twice the factorial. -/
lemma factorial_bound (n : ℕ) : |B n| ≤ 2*(n.factorial:ℤ) := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  linarith only [factorial_norm_bound n,sq_nonneg (A n)]

lemma factorial_bound_A (n : ℕ) : |A n| ≤ 2*(n.factorial:ℤ) := by
  apply abs_le_of_sq_le_sq _ (by positivity)
  linarith only [factorial_norm_bound n,sq_nonneg (B n)]

end ArctanCert

namespace ArctanCRT

/-- Binary modular powering, reducing after each square and multiply. -/
private lemma pow_bits (p a n : ℕ) :
    ((n.bits.foldr (fun b v => (if b then v*v*a else v*v)%p) 1 : ℕ) : ZMod p) = (a : ZMod p)^n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb,List.foldr_cons,ZMod.natCast_mod]
    cases b <;> simp [Nat.bit_val,Nat.cast_mul,ih,two_mul,pow_add]

/-- Lucas's criterion with the factors of the square root of `p-1` supplied explicitly. -/
private lemma from_witness (p k a : ℕ) (factors : List ℕ) (hs : p-1=k^2) (hf : factors.prod=k)
    (hp : ∀ q ∈ factors, q.Prime)
    (hc : let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
      v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true) : p.Prime := by
  let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
  change v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true at hc
  have hpow (n : ℕ) : (v n : ZMod p)=(a : ZMod p)^n := pow_bits p a n
  apply lucas_primality p (a : ZMod p)
  · rw [← hpow,hc.1,Nat.cast_one]
  · intro q hq hd
    have hmem : q ∈ factors := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hq)
      (fun b hb => Nat.prime_iff.mp (hp b hb)) (hf ▸ hq.dvd_of_dvd_pow (hs ▸ hd))
    have hv := of_decide_eq_true (List.all_eq_true.mp hc.2 q hmem)
    rwa [hpow] at hv

end ArctanCRT

namespace ArctanCRT


lemma prime_0 : Nat.Prime 999920001601 := by
  apply from_witness 999920001601 999960 17 [2, 2, 2, 3, 5, 13, 641]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_1 : Nat.Prime 999900002501 := by
  apply from_witness 999900002501 999950 3 [2, 5, 5, 7, 2857]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_2 : Nat.Prime 999892002917 := by
  apply from_witness 999892002917 999946 2 [2, 499973]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_3 : Nat.Prime 999868004357 := by
  apply from_witness 999868004357 999934 2 [2, 13, 38459]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_4 : Nat.Prime 999848005777 := by
  apply from_witness 999848005777 999924 5 [2, 2, 3, 103, 809]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_5 : Nat.Prime 999732017957 := by
  apply from_witness 999732017957 999866 2 [2, 7, 71419]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_6 : Nat.Prime 999672026897 := by
  apply from_witness 999672026897 999836 3 [2, 2, 43, 5813]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_7 : Nat.Prime 999628034597 := by
  apply from_witness 999628034597 999814 2 [2, 37, 59, 229]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_8 : Nat.Prime 999620036101 := by
  apply from_witness 999620036101 999810 13 [2, 3, 3, 3, 5, 7, 23, 23]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_9 : Nat.Prime 999568046657 := by
  apply from_witness 999568046657 999784 3 [2, 2, 2, 47, 2659]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

end ArctanCRT

namespace ArctanCRT

open Arxiv.«2607.05739»

private lemma difference_factor {p k : ℕ} {m R : ℤ}
    (hr : (R : ZMod p) = (k : ZMod p)) (hm : (m : ZMod p) = (k : ZMod p)) :
    (p : ℤ) ∣ m-R :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub R m p).mp (hr.trans hm.symm)

private lemma fixed_factor {n p k : ℕ} {m R : ℤ} (hp : p.Prime)
    (lo : 1000000 ≤ n) (hi : n ≤ 900000000000) (hk : 1 ≤ k) (hkmax : k ≤ 1000000)
    (hpmin : 900001000000 < p) (hd : p ∣ 1+k^2) (hm : B n=A n*m)
    (hr : (R : ZMod p)=(k : ZMod p)) : (p : ℤ) ∣ m-R := by
  exact difference_factor hr (ArctanCert.signed_residue hp hk (hkmax.trans lo) (by omega) hd hm)

/-- Ten signed residue classes force any integer quotient in this range to have at least 120 digits. -/
lemma quotient_large {n : ℕ} {m : ℤ} (lo : 1000000 ≤ n) (hi : n ≤ 900000000000)
    (hm : B n = A n*m) : (10 : ℤ)^119 ≤ |m| := by
  let R : ℤ := 314538918741328110436849001151332386002465540153175519696217958824997488014743286934041729987811928674511392258630103331
  have d0 : (999920001601 : ℤ) ∣ m-R := fixed_factor (k:=999960) prime_0 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have d1 : (999900002501 : ℤ) ∣ m-R := fixed_factor (k:=999950) prime_1 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h1 : (999820012101639824004101 : ℤ) ∣ m-R :=
    (show IsCoprime (999920001601 : ℤ) (999900002501 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd d0 d1
  have d2 : (999892002917 : ℤ) ∣ m-R := fixed_factor (k:=999946) prime_2 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h2 : (999712034456807822203591923711962617 : ℤ) ∣ m-R :=
    (show IsCoprime (999820012101639824004101 : ℤ) (999892002917 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h1 d2
  have d3 : (999868004357 : ℤ) ∣ m-R := fixed_factor (k:=999934) prime_3 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h3 : (999580076824004857699372730919082649547577122269 : ℤ) ∣ m-R :=
    (show IsCoprime (999712034456807822203591923711962617 : ℤ) (999868004357 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h2 d3
  have d4 : (999848005777 : ℤ) ∣ m-R := fixed_factor (k:=999924) prime_4 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h4 : (999428146426901712773278489193259215504386356982768147348013 : ℤ) ∣ m-R :=
    (show IsCoprime (999580076824004857699372730919082649547577122269 : ℤ) (999848005777 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h3 d4
  have d5 : (999732017957 : ℤ) ∣ m-R := fixed_factor (k:=999866) prime_5 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h5 : (999160317630390528502129306827917252477986914251362577824091354444269441 : ℤ) ∣ m-R :=
    (show IsCoprime (999428146426901712773278489193259215504386356982768147348013 : ℤ) (999732017957 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h4 d5
  have d6 : (999672026897 : ℤ) ∣ m-R := fixed_factor (k:=999836) prime_6 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h6 : (998832619920622823713394653537049661369664474443902163517464308214596881110867154577 : ℤ) ∣ m-R :=
    (show IsCoprime (999160317630390528502129306827917252477986914251362577824091354444269441 : ℤ) (999672026897 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h5 d6
  have d7 : (999628034597 : ℤ) ∣ m-R := fixed_factor (k:=999814) prime_7 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h7 : (998461088742624503416761102738248707316942093665690854248318962705653722371502207788168302900469 : ℤ) ∣ m-R :=
    (show IsCoprime (998832619920622823713394653537049661369664474443902163517464308214596881110867154577 : ℤ) (999628034597 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h6 d7
  have d8 : (999620036101 : ℤ) ∣ m-R := fixed_factor (k:=999810) prime_8 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h8 : (998081709574346070802949931367700742761678238519024415148810130718388446593806068282810002306030724789831369 : ℤ) ∣ m-R :=
    (show IsCoprime (998461088742624503416761102738248707316942093665690854248318962705653722371502207788168302900469 : ℤ) (999620036101 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h7 d8
  have d9 : (999568046657 : ℤ) ∣ m-R := fixed_factor (k:=999784) prime_9 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h9 : (997650584843308276910627682450584843863618748551605771183587982339952371712727296788521556256100797109197688367754183433 : ℤ) ∣ m-R :=
    (show IsCoprime (998081709574346070802949931367700742761678238519024415148810130718388446593806068282810002306030724789831369 : ℤ) (999568046657 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h8 d9
  clear d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 h1 h2 h3 h4 h5 h6 h7 h8 lo hi hm
  obtain ⟨z,hz⟩ := h9
  dsimp [R] at hz
  by_contra! h
  obtain ⟨hl,hu⟩ := abs_lt.mp h
  norm_num at hl hu
  omega

/-- An exceptional index through nine hundred billion must have an exceptionally small real part
of the Gaussian product after normalization by its factorial. -/
lemma necessary_real_bound {n : ℕ} (lo : 1000000 ≤ n) (hi : n ≤ 900000000000)
    (h : IsIntegerValue n) : (10 : ℤ)^119 * |A n| ≤ 2*(n.factorial : ℤ) := by
  obtain ⟨m,hm⟩ := h
  calc
    (10 : ℤ)^119 * |A n| ≤ |m| * |A n| := mul_le_mul_of_nonneg_right
      (quotient_large lo hi hm) (abs_nonneg _)
    _ = |B n| := by rw [hm, abs_mul, mul_comm]
    _ ≤ 2*(n.factorial : ℤ) := ArctanCert.factorial_bound n

end ArctanCRT

namespace ArctanWordCRT

/-- Binary modular powering, reducing after each square and multiply. -/
private lemma pow_bits (p a n : ℕ) :
    ((n.bits.foldr (fun b v => (if b then v*v*a else v*v)%p) 1 : ℕ) : ZMod p) = (a : ZMod p)^n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hb ih =>
    rw [Nat.bits_append_bit n b hb,List.foldr_cons,ZMod.natCast_mod]
    cases b <;> simp [Nat.bit_val,Nat.cast_mul,ih,two_mul,pow_add]

/-- Lucas's criterion with the factors of the square root of `p-1` supplied explicitly. -/
private lemma from_witness (p k a : ℕ) (factors : List ℕ) (hs : p-1=k^2) (hf : factors.prod=k)
    (hp : ∀ q ∈ factors, q.Prime)
    (hc : let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
      v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true) : p.Prime := by
  let v (n : ℕ) := n.bits.foldr (fun b t => (if b then t*t*a else t*t)%p) 1
  change v (p-1)=1 ∧ factors.all (fun q => decide ((v ((p-1)/q) : ZMod p) ≠ 1))=true at hc
  have hpow (n : ℕ) : (v n : ZMod p)=(a : ZMod p)^n := pow_bits p a n
  apply lucas_primality p (a : ZMod p)
  · rw [← hpow,hc.1,Nat.cast_one]
  · intro q hq hd
    have hmem : q ∈ factors := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hq)
      (fun b hb => Nat.prime_iff.mp (hp b hb)) (hf ▸ hq.dvd_of_dvd_pow (hs ▸ hd))
    have hv := of_decide_eq_true (List.all_eq_true.mp hc.2 q hmem)
    rwa [hpow] at hv

end ArctanWordCRT

namespace ArctanWordCRT

open Arxiv.«2607.05739»

lemma prime_0 : Nat.Prime 63999977760001932101 := by
  apply from_witness 63999977760001932101 7999998610 2 [2, 5, 53, 193, 197, 397]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_1 : Nat.Prime 63999945216011723777 := by
  apply from_witness 63999945216011723777 7999996576 3 [2, 2, 2, 2, 2, 11, 13, 43, 109, 373]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_2 : Nat.Prime 63999942880012744901 := by
  apply from_witness 63999942880012744901 7999996430 2 [2, 5, 47, 97, 379, 463]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_3 : Nat.Prime 63999940544013808657 := by
  apply from_witness 63999940544013808657 7999996284 5 [2, 2, 3, 3, 7, 19, 71, 101, 233]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_4 : Nat.Prime 63999934464016777217 := by
  apply from_witness 63999934464016777217 7999995904 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 19, 31, 829]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_5 : Nat.Prime 63999932384017859077 := by
  apply from_witness 63999932384017859077 7999995774 2 [2, 3, 37, 67, 593, 907]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

lemma prime_6 : Nat.Prime 63999923840022657601 := by
  apply from_witness 63999923840022657601 7999995240 31 [2, 2, 2, 3, 3, 3, 5, 23, 443, 727]
  · decide
  · decide
  · intro q hq
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num
  · decide +kernel

private lemma signed_factor {n p k : ℕ} {m R : ℤ} (hp : p.Prime)
    (lo : 900000000000 ≤ n) (hi : n ≤ 18446744073709551615)
    (hk : 1≤k) (hkl : k≤900000000000) (hpmin : 18446744073709551615+k<p)
    (hd : p ∣ 1+k^2) (hm : B n=A n*m) (hR : (R : ZMod p)=(k : ZMod p)) : (p : ℤ) ∣ m-R :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub R m p).mp
    (hR.trans (ArctanCert.signed_residue hp hk (hkl.trans lo) (by omega) hd hm).symm)

/-- All seven signs are fixed by the corresponding split-prime evaluations. -/
lemma joint_residue {n : ℕ} {m : ℤ} (lo : 900000000000≤n) (hi : n≤18446744073709551615)
    (hm : B n=A n*m) : (4398018823282643417813692926475385294712984070195663799519080465748185703914887245168684886935938141866859953671632117304449089521051196301:ℤ) ∣ m-(-578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488) := by
  let R : ℤ := -578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488
  have d0 : (63999977760001932101 : ℤ) ∣ m-R := signed_factor (k:=7999998610) prime_0 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have d1 : (63999945216011723777 : ℤ) ∣ m-R := signed_factor (k:=7999996576) prime_1 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h1 : (4095995070466092371985415000987521265477 : ℤ) ∣ m-R :=
    (show IsCoprime (63999977760001932101 : ℤ) (63999945216011723777 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd d0 d1
  have d2 : (63999942880012744901 : ℤ) ∣ m-R := signed_factor (k:=7999996430) prime_2 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h2 : (262143450546643689835539850627434313870944816814523899082777 : ℤ) ∣ m-R :=
    (show IsCoprime (4095995070466092371985415000987521265477 : ℤ) (63999942880012744901 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h1 d2
  have d3 : (63999940544013808657 : ℤ) ∣ m-R := signed_factor (k:=7999996284) prime_3 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h3 : (16777165248987820297220722643512590539213048240464775236206103727551424682200489 : ℤ) ∣ m-R :=
    (show IsCoprime (262143450546643689835539850627434313870944816814523899082777 : ℤ) (63999940544013808657 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h2 d3
  have d4 : (63999934464016777217 : ℤ) ∣ m-R := signed_factor (k:=7999995904) prime_4 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h4 : (1073737476427200215498362378219010105829188533897124652337242504275071346909624962439305329641459113 : ℤ) ∣ m-R :=
    (show IsCoprime (16777165248987820297220722643512590539213048240464775236206103727551424682200489 : ℤ) (63999934464016777217 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h3 d4
  have d5 : (63999932384017859077 : ℤ) ∣ m-R := signed_factor (k:=7999995774) prime_5 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h5 : (68719125889526783650594720122289082963567266847347851388477413697860086182843326283279033505229539856809192592691418701 : ℤ) ∣ m-R :=
    (show IsCoprime (1073737476427200215498362378219010105829188533897124652337242504275071346909624962439305329641459113 : ℤ) (63999932384017859077 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h4 d5
  have d6 : (63999923840022657601 : ℤ) ∣ m-R := signed_factor (k:=7999995240) prime_6 lo hi
    (by decide) (by decide) (by decide) (by decide) hm (by decide +kernel)
  have h6 : (4398018823282643417813692926475385294712984070195663799519080465748185703914887245168684886935938141866859953671632117304449089521051196301 : ℤ) ∣ m-R :=
    (show IsCoprime (68719125889526783650594720122289082963567266847347851388477413697860086182843326283279033505229539856809192592691418701 : ℤ) (63999923840022657601 : ℤ) from
      Int.isCoprime_iff_gcd_eq_one.mpr (by decide +kernel)).mul_dvd h5 d6
  exact h6

/-- The centered CRT representative minimizes the absolute value in its integer coset. -/
lemma least_absolute (z : ℤ) : |(-578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488 : ℤ)| ≤ |(-578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488)+4398018823282643417813692926475385294712984070195663799519080465748185703914887245168684886935938141866859953671632117304449089521051196301*z| := by
  by_contra! he
  obtain ⟨hl,hu⟩ := abs_lt.mp he
  norm_num at hl hu
  omega

lemma quotient_large {n : ℕ} {m : ℤ} (lo : 900000000000≤n) (hi : n≤18446744073709551615)
    (hm : B n=A n*m) : (10 : ℤ)^119 ≤ |m| := by
  obtain ⟨z,hz⟩ := joint_residue lo hi hm
  have he : m=(-578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488)+4398018823282643417813692926475385294712984070195663799519080465748185703914887245168684886935938141866859953671632117304449089521051196301*z := by omega
  rw [he]
  exact (show (10:ℤ)^119 ≤ |(-578133431320477099269313245928101671987616903527324804914741378589609916690901804829913293726783226269011797614644529496127600122667986488 : ℤ)| by decide +kernel).trans (least_absolute z)

/-- An integer value anywhere on this interval forces a small normalized real coordinate. -/
lemma necessary_real_bound {n : ℕ} (lo : 900000000000≤n) (hi : n≤18446744073709551615)
    (hint : IsIntegerValue n) : (10 : ℤ)^119 * |A n| ≤ 2*(n.factorial : ℤ) := by
  obtain ⟨m,hm⟩ := hint
  calc
    (10 : ℤ)^119 * |A n| ≤ |m| * |A n| := mul_le_mul_of_nonneg_right (quotient_large lo hi hm) (abs_nonneg _)
    _ = |B n| := by rw [hm,abs_mul,mul_comm]
    _ ≤ 2*(n.factorial : ℤ) := ArctanCert.factorial_bound n

end ArctanWordCRT

namespace ArctanWordCRT

open Arxiv.«2607.05739»

lemma whole_barrier {n : ℕ} (lo : 1000000≤n) (hi : n≤18446744073709551615)
    (hint : IsIntegerValue n) : (10:ℤ)^119 * |A n| ≤ 2*(n.factorial:ℤ) := by
  by_cases small : n≤900000000000
  · exact ArctanCRT.necessary_real_bound lo small hint
  · exact necessary_real_bound (by omega) hi hint

end ArctanWordCRT

namespace ArctanBlocks

noncomputable def ratio (n : ℕ) : ℕ → ℂ
  | 0 => 1
  | h+1 => ratio n h * (1 - Complex.I / ((n+h+1 : ℕ) : ℂ))

noncomputable def rotated (n : ℕ) : ℂ := ratio 0 n

noncomputable def coeff (n : ℕ) : ℕ → ℂ
  | 0 => 1
  | j+1 => coeff n j * (-((j : ℕ) : ℂ) - Complex.I) / ((n+j+1 : ℕ) : ℂ)

noncomputable def term (n h j : ℕ) : ℂ := (h.choose j : ℂ) * coeff n j

noncomputable def trunc (n h J : ℕ) : ℂ := ∑ j ∈ Finset.range (J+1), term n h j

/-- Exact real and imaginary numerators and positive common denominator for a Newton sum. -/
def horner (n h : ℕ) : ℕ → ℕ → ℤ × ℤ × ℕ
  | 0, _ => (1, 0, 1)
  | len+1, j =>
    let t := horner n h len (j+1)
    let den := (j+1)*(n+j+1)*t.2.2
    let mult : ℤ := (h-j : ℕ)
    ((den : ℤ) + mult*(-(j:ℤ)*t.1 + t.2.1), mult*(-(j:ℤ)*t.2.1 - t.1), den)

def jump (n h : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  let t := horner n h 56 0
  ((z.1*t.1-z.2*t.2.1)/(t.2.2:ℤ), (z.1*t.2.1+z.2*t.1)/(t.2.2:ℤ))

def scale : ℕ := 2^160
def lower : ℕ := 1000000
def upper : ℕ := 18446744073709551615

/-- Each checked integer in the block lies strictly away from both coordinate axes. -/
def clear (n h : ℕ) (z : ℤ × ℤ) : Bool := decide
  ((4*n+1)*(n+1) + 3*scale*(h-1) ≤ min z.1.natAbs z.2.natAbs * (n+1))

/-- Land exactly at the lower endpoint before using the axis exclusion. -/
def width (n : ℕ) (z : ℤ × ℤ) : ℕ :=
  if n < lower then min ((n+1)/8) (lower-n)
  else min (upper+1-n) (min ((n+1)/8)
    (1 + ((min z.1.natAbs z.2.natAbs - (4*n+1))*(n+1))/(4*scale)))

end ArctanBlocks

namespace ArctanBlocks

def lift (z : ℤ × ℤ) : ℂ := ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

def Accurate (n : ℕ) (z : ℤ × ℤ) : Prop :=
  ‖(scale : ℂ)*rotated n - lift z‖ ≤ 4*(n : ℝ)

end ArctanBlocks

namespace ArctanBlocks

/-- Consecutive terms of the Newton expansion. The natural subtraction
handles the binomial endpoint and every index beyond it. -/
theorem term_succ (n h j : ℕ) :
    term n h (j+1) = term n h j * (((h-j : ℕ) : ℂ) * (-(j:ℂ) - Complex.I)) /
      (((j+1)*(n+j+1) : ℕ) : ℂ) := by
  have hj : ((j+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero j)
  have hchoose : (h.choose (j+1) : ℂ) =
      (h.choose j : ℂ) * ((h-j : ℕ) : ℂ) / ((j+1 : ℕ) : ℂ) := by
    apply (eq_div_iff hj).mpr
    exact_mod_cast Nat.choose_succ_right_eq h j
  simp only [term, coeff, hchoose, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Moving the starting index forward by one cancels the intermediate
rising-factorial denominators. -/
private lemma coeff_shift_start (n j : ℕ) :
    coeff (n+1) j = coeff n j * ((n+1 : ℕ) : ℂ) / ((n+j+1 : ℕ) : ℂ) := by
  induction j with
  | zero =>
    have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    simp only [coeff, Nat.add_zero, one_mul, div_self hn]
  | succ j ih =>
    rw [coeff, ih, coeff, show n+1+j+1 = n+(j+1)+1 by omega]
    ring

private lemma coeff_diff (n j : ℕ) :
    (1-Complex.I/((n+1 : ℕ) : ℂ))*coeff (n+1) j - coeff n j = coeff n (j+1) := by
  rw [coeff_shift_start, coeff]
  have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hnj : (n:ℂ)+(j:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n+j)
  push_cast
  field_simp [hn, hnj]
  ring

private lemma difference_formula (n j t : ℕ) :
    ((fwdDiff (1:ℕ))^[j] (ratio n)) t = ratio n t * coeff (n+t) j := by
  induction j generalizing t with
  | zero => simp [coeff]
  | succ j ih =>
    rw [Function.iterate_succ_apply', fwdDiff, ih, ih, ratio, ← Nat.add_assoc,
      mul_assoc, ← mul_sub, coeff_diff]

/-- Exact Newton interpolation for a finite block of the rotated product. -/
theorem ratio_eq_sum (n h : ℕ) :
    ratio n h = ∑ j ∈ Finset.range (h+1), term n h j := by
  have hx := shift_eq_sum_fwdDiff_iter (1:ℕ) (ratio n) h 0
  simpa [difference_formula, ratio, term, nsmul_eq_mul] using hx

end ArctanBlocks

namespace ArctanBlocks

private lemma coeff_norm_bound (n j : ℕ) : ‖coeff n j‖ ≤ (j.factorial : ℝ)/((n : ℝ)+1)^j := by
  induction j with
  | zero => simp [coeff]
  | succ j ih =>
    have hf : ‖-(j : ℂ)-Complex.I‖ ≤ (j : ℝ)+1 := by
      simpa only [norm_neg,Complex.norm_natCast,Complex.norm_I] using (norm_sub_le (-(j : ℂ)) Complex.I)
    have hp : 0 < (n : ℝ)+1 := by positivity
    have hden : (n : ℝ)+1 ≤ ((n+j+1 : ℕ) : ℝ) := by exact_mod_cast (show n+1≤n+j+1 by omega)
    rw [coeff,norm_div,norm_mul,Complex.norm_natCast]
    calc
      _ ≤ (((j.factorial : ℝ)/((n : ℝ)+1)^j)*((j : ℝ)+1))/((n+j+1 : ℕ) : ℝ) := by gcongr
      _ ≤ (((j.factorial : ℝ)/((n : ℝ)+1)^j)*((j : ℝ)+1))/((n : ℝ)+1) := by gcongr
      _ = _ := by rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ,pow_succ]; field_simp

lemma term_norm_bound (n h j : ℕ) : ‖term n h j‖ ≤ ((h : ℝ)/((n : ℝ)+1))^j := by
  rw [term,norm_mul,Complex.norm_natCast]
  have hc := Nat.choose_le_pow_div (α:=ℝ) j h
  have hf : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  calc
    _ ≤ ((h : ℝ)^j/(j.factorial : ℝ))*((j.factorial : ℝ)/((n : ℝ)+1)^j) :=
      mul_le_mul hc (coeff_norm_bound n j) (norm_nonneg _) (by positivity)
    _ = _ := by rw [div_pow]; field_simp

private lemma quotient_bound {n h : ℕ} (hh : 8*h ≤ n+1) : (h : ℝ)/((n : ℝ)+1) ≤ 1/8 := by
  apply (div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)).mpr
  have he : 8*(h : ℝ) ≤ (n : ℝ)+1 := by exact_mod_cast hh
  linarith

private lemma geometric_bound {q : ℝ} (h0 : 0≤q) (h1 : q≤1/8) (k : ℕ) :
    (∑ j ∈ Finset.range k, q^j) ≤ 8/7 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ',pow_zero]
    simp only [pow_succ,← Finset.sum_mul]
    have h := mul_le_mul_of_nonneg_right ih h0
    linarith

/-- Any remainder of the finite expansion is bounded by a geometric series, including
when the truncation length exceeds the degree and all remaining terms vanish. -/
private lemma newton_tail {n h : ℕ} (hh : 8*h ≤ n+1)
    (hex : ratio n h = ∑ j ∈ Finset.range (h+1),term n h j) (L : ℕ) :
    ‖ratio n h-(∑ j ∈ Finset.range L,term n h j)‖ ≤
      (8/7 : ℝ)*((h : ℝ)/((n : ℝ)+1))^L := by
  let q := (h : ℝ)/((n : ℝ)+1)
  have hq : 0≤q := by dsimp only [q]; positivity
  have extended (m : ℕ) : (∑ j ∈ Finset.range (h+1+m),term n h j) = ratio n h := by
    induction m with
    | zero => simpa only [Nat.add_zero] using hex.symm
    | succ m ih =>
      rw [show h+1+(m+1)=h+1+m+1 by omega, Finset.sum_range_succ,ih]
      simp [term,Nat.choose_eq_zero_of_lt (show h<h+1+m by omega)]
  have splitSum : ratio n h = (∑ j ∈ Finset.range L, term n h j) +
      ∑ k ∈ Finset.range (h+1), term n h (L+k) := by
    rw [← extended L,Nat.add_comm (h+1) L,Finset.sum_range_add]
  rw [splitSum,add_sub_cancel_left]
  calc
    _ ≤ ∑ k ∈ Finset.range (h+1), ‖term n h (L+k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (h+1), q^(L+k) := Finset.sum_le_sum fun k _ => term_norm_bound n h (L+k)
    _ = (∑ k ∈ Finset.range (h+1),q^k)*q^L := by rw [Finset.sum_mul]; simp [pow_add,mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_right (geometric_bound hq (quotient_bound hh) _) (pow_nonneg hq L)

private lemma trunc56_error_of_sum (n h : ℕ) (hh : 8*h ≤ n+1)
    (hex : ratio n h = ∑ j ∈ Finset.range (h+1),term n h j) :
    ‖ratio n h-trunc n h 56‖ ≤ 1/(16*(scale : ℝ)) := by
  calc
    _ ≤ (8/7 : ℝ)*((h : ℝ)/((n : ℝ)+1))^57 := newton_tail hh hex 57
    _ ≤ (8/7 : ℝ)*(1/8)^57 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (quotient_bound hh) 57) (by norm_num)
    _ ≤ _ := by norm_num [scale]

private lemma ratio_variation_of_sum (n h : ℕ) (hh : 8*h ≤ n+1)
    (hex : ratio n h = ∑ j ∈ Finset.range (h+1),term n h j) :
    ‖ratio n h-1‖ ≤ (8/7 : ℝ)*((h : ℝ)/((n : ℝ)+1)) := by
  simpa [term,coeff] using newton_tail hh hex 1

/-- Fifty-seven Newton terms give the required absolute precision at scale `2^160`. -/
lemma trunc56_error (n h : ℕ) (hh : 8*h ≤ n+1) :
    ‖ratio n h-trunc n h 56‖ ≤ 1/(16*(scale : ℝ)) :=
  trunc56_error_of_sum n h hh (ratio_eq_sum n h)

lemma ratio_variation_sharp (n h : ℕ) (hh : 8*h ≤ n+1) :
    ‖ratio n h-1‖ ≤ (8/7 : ℝ)*((h : ℝ)/((n : ℝ)+1)) :=
  ratio_variation_of_sum n h hh (ratio_eq_sum n h)

lemma ratio_variation (n h : ℕ) (hh : 8*h ≤ n+1) :
    ‖ratio n h-1‖ ≤ 3*(h : ℝ)/(2*((n : ℝ)+1)) := by
  apply (ratio_variation_sharp n h hh).trans
  calc
    _ ≤ (3/2 : ℝ)*((h : ℝ)/((n : ℝ)+1)) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by field_simp

end ArctanBlocks

namespace ArctanBlocks

open Arxiv.«2607.05739»

private lemma rotated_succ (n : ℕ) : rotated (n+1) =
    rotated n*(1-Complex.I/((n+1:ℕ):ℂ)) := by simp only [rotated,ratio,Nat.zero_add]

lemma rotated_add (n h : ℕ) : rotated (n+h) = rotated n * ratio n h := by
  induction h with
  | zero => simp [ratio]
  | succ h ih =>
    change rotated ((n+h)+1) = rotated n * ratio n (h+1)
    rw [rotated_succ,ih,ratio,mul_assoc]

private lemma factor_sq (k : ℕ) : ‖1-Complex.I/(k:ℂ)‖^2 = 1+1/(k:ℝ)^2 := by
  calc
    _ = 1 + (1/(k:ℝ))^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      simp [pow_two]
    _ = _ := by rw [div_pow,one_pow]

private lemma factor_budget (k : ℕ) (hk : 0 < k) : ‖1-Complex.I/((k+1:ℕ):ℂ)‖^2 ≤
    ((k:ℝ)+1)^2 / ((k:ℝ)*((k:ℝ)+2)) := by
  rw [factor_sq,Nat.cast_succ]
  have hp : 0 < (k:ℝ) := by exact_mod_cast hk
  calc
    _ = (((k:ℝ)+1)^2+1)/((k:ℝ)+1)^2 := by field_simp
    _ ≤ _ := (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by nlinarith)

/-- Squaring the norm permits the product of one-step bounds to telescope. -/
private lemma ratio_sq_budget {n : ℕ} (hn : 1 ≤ n) (h : ℕ) : ‖ratio n h‖^2 ≤
    ((n:ℝ)+1)*((n:ℝ)+(h:ℝ)) / ((n:ℝ)*((n:ℝ)+(h:ℝ)+1)) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  induction h with
  | zero =>
    simp only [ratio,norm_one,one_pow,Nat.cast_zero,add_zero]
    apply (le_div_iff₀ (by positivity)).mpr
    ring_nf
    exact le_rfl
  | succ h ih =>
    let m := (n:ℝ)+(h:ℝ)
    have hm : 0 < m := by dsimp [m]; positivity
    have step : ‖1-Complex.I/((n+h+1:ℕ):ℂ)‖^2 ≤ (m+1)^2/(m*(m+2)) := by
      simpa only [m,Nat.cast_add] using factor_budget (n+h) (by omega)
    rw [ratio,norm_mul,mul_pow]
    calc
      _ ≤ (((n:ℝ)+1)*m/((n:ℝ)*(m+1)))*((m+1)^2/(m*(m+2))) :=
        mul_le_mul ih step (sq_nonneg _) (by dsimp [m]; positivity)
      _ = ((n:ℝ)+1)*(m+1)/((n:ℝ)*(m+2)) := by field_simp
      _ = _ := by dsimp only [m]; push_cast; ring

lemma norm_ratio_le {n : ℕ} (hn : 1 ≤ n) (h : ℕ) :
    ‖ratio n h‖ ≤ 1+(h:ℝ)/((n:ℝ)*((n+h+1:ℕ):ℝ)) := by
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  let R := 1+(h:ℝ)/((n:ℝ)*((n+h+1:ℕ):ℝ))
  have hR : 1 ≤ R := le_add_of_nonneg_right (by positivity)
  have hs : ‖ratio n h‖^2 ≤ R := by
    apply (ratio_sq_budget hn h).trans_eq
    dsimp [R]
    push_cast
    field_simp
    ring
  change ‖ratio n h‖ ≤ R
  apply (sq_le_sq₀ (norm_nonneg _) (by linarith : 0≤R)).mp
  nlinarith only [hs,hR,sq_nonneg (R-1)]

lemma norm_rotated_le (n : ℕ) : ‖rotated n‖ ≤ 2 := by
  cases n with
  | zero => norm_num [rotated,ratio]
  | succ k =>
    rw [show k+1=1+k by omega,rotated_add,norm_mul]
    have first : ‖rotated 1‖^2=2 := by
      have q : rotated 1 = 1-Complex.I/((1:ℕ):ℂ) := by simp [rotated,ratio]
      rw [q,factor_sq]
      norm_num
    have hb : ‖ratio 1 k‖^2≤2 := by
      apply (ratio_sq_budget (n:=1) (by decide) k).trans
      norm_num
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,first]
    linarith only [hb]

/-- Removing the unit power `I^n` leaves precisely the rotated factorial-normalized product. -/
lemma gauss_div_factorial (n : ℕ) : (gaussProd n : ℂ)/(n.factorial:ℂ) = Complex.I^n * rotated n := by
  induction n with
  | zero => simp [gaussProd,rotated,ratio,GaussianInt.toComplex_one]
  | succ n ih =>
    have prod : gaussProd (n+1) = gaussProd n * (⟨1,((n+1:ℕ):ℤ)⟩ : GaussianInt) :=
      Finset.prod_Icc_succ_top (by omega : 1≤n+1) _
    have hn : ((n+1:ℕ):ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n
    have factor : (1+((n+1:ℕ):ℂ)*Complex.I)/((n+1:ℕ):ℂ) =
        Complex.I*(1-Complex.I/((n+1:ℕ):ℂ)) := by
      field_simp
      linear_combination Complex.I_sq
    have val : ((⟨1,((n+1:ℕ):ℤ)⟩ : GaussianInt):ℂ) = 1+((n+1:ℕ):ℂ)*Complex.I := by
      simp [GaussianInt.toComplex_def']
    rw [prod,GaussianInt.toComplex_mul,val,Nat.factorial_succ,Nat.cast_mul]
    rw [mul_comm ((n+1:ℕ):ℂ) (n.factorial:ℂ),← div_mul_div_comm,ih,factor,pow_succ,rotated_succ]
    ring

lemma abs_A_div_factorial (n : ℕ) :
    |(A n:ℝ)/(n.factorial:ℝ)| = |(rotated n).re| ∨ |(A n:ℝ)/(n.factorial:ℝ)| = |(rotated n).im| := by
  have h : (A n:ℝ)/(n.factorial:ℝ) = (Complex.I^n*rotated n).re := by
    simpa only [Complex.div_natCast_re,A,GaussianInt.intCast_re] using congrArg Complex.re (gauss_div_factorial n)
  rw [h,Complex.I_pow_eq_pow_mod]
  have hr : n%4<4 := Nat.mod_lt _ (by decide)
  interval_cases k : n%4 <;> simp [pow_succ,Complex.I_mul_I]

end ArctanBlocks

namespace ArctanBlocks

/-- Every Horner stage uses a strictly positive common denominator. -/
lemma horner_den_pos (n h len j : ℕ) : 0 < (horner n h len j).2.2 := by
  induction len generalizing j with
  | zero => exact Nat.zero_lt_one
  | succ len ih =>
    change 0 < (j+1)*(n+j+1)*(horner n h len (j+1)).2.2
    exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (ih _)

private def numerators (a b : ℤ) : ℂ := ⟨(a:ℝ),(b:ℝ)⟩

private noncomputable def hornerValue (t : ℤ × ℤ × ℕ) : ℂ := numerators t.1 t.2.1 / (t.2.2:ℂ)

private lemma numerators_step (d u j : ℕ) (a b : ℤ) :
    numerators ((d:ℤ)+(u:ℤ)*(-(j:ℤ)*a+b)) ((u:ℤ)*(-(j:ℤ)*b-a)) =
      (d:ℂ)+(u:ℂ)*(-(j:ℂ)-Complex.I)*numerators a b := by
  apply Complex.ext <;> simp [numerators,Complex.mul_re,Complex.mul_im] <;> ring

private lemma hornerValue_succ (n h len j : ℕ) :
    hornerValue (horner n h (len+1) j) = 1 +
      (((h-j : ℕ):ℂ)*(-(j:ℂ)-Complex.I)) / (((j+1)*(n+j+1):ℕ):ℂ) *
        hornerValue (horner n h len (j+1)) := by
  let t := horner n h len (j+1)
  let b := (j+1)*(n+j+1)
  have hb : (b:ℂ)≠0 := Nat.cast_ne_zero.mpr (by dsimp [b]; positivity)
  have ht : (t.2.2:ℂ)≠0 := Nat.cast_ne_zero.mpr (horner_den_pos n h len (j+1)).ne'
  change numerators (((b*t.2.2:ℕ):ℤ)+((h-j:ℕ):ℤ)*(-(j:ℤ)*t.1+t.2.1))
    (((h-j:ℕ):ℤ)*(-(j:ℤ)*t.2.1-t.1)) / ((b*t.2.2:ℕ):ℂ) =
    1 + (((h-j:ℕ):ℂ)*(-(j:ℂ)-Complex.I))/(b:ℂ)*(numerators t.1 t.2.1/(t.2.2:ℂ))
  rw [numerators_step,Nat.cast_mul]
  field_simp [hb,ht]

private lemma weighted_horner (n h len j : ℕ) :
    term n h j * hornerValue (horner n h len j) =
      ∑ s ∈ Finset.range (len+1), term n h (j+s) := by
  induction len generalizing j with
  | zero =>
    have one : numerators 1 0 = 1 := by apply Complex.ext <;> norm_num [numerators]
    simp [hornerValue,horner,one]
  | succ len ih =>
    rw [hornerValue_succ,mul_add,mul_one,← mul_assoc,← mul_div_assoc,← term_succ,ih,
      Finset.sum_range_succ' (fun s => term n h (j+s)) (len+1)]
    simp only [Nat.add_zero,Nat.add_succ,add_comm]

/-- Dividing the two integer numerators by the common denominator gives the
truncated Newton series exactly, including indices beyond the polynomial degree. -/
lemma horner_exact (n h J : ℕ) :
    (⟨((horner n h J 0).1:ℝ),((horner n h J 0).2.1:ℝ)⟩:ℂ) / ((horner n h J 0).2.2:ℂ) =
      trunc n h J := by
  have h₀ : term n h 0 = 1 := by simp [term,coeff]
  simpa only [h₀,one_mul,Nat.zero_add,hornerValue,numerators,trunc] using
    weighted_horner n h J 0

/-- Euclidean division by a positive integer changes the real quotient by at most one. -/
private lemma division_rounding_error (a : ℤ) (k : ℕ) (hk : 0 < k) :
    |(a : ℝ)/(k : ℝ) - ((a/(k : ℤ) : ℤ) : ℝ)| ≤ 1 := by
  have hki : 0 < (k : ℤ) := by exact_mod_cast hk
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have h₀ : 0 ≤ a%(k : ℤ) := Int.emod_nonneg _ (ne_of_gt hki)
  have h₁ : a%(k : ℤ) < k := Int.emod_lt_of_pos _ hki
  have he : (k : ℝ)*((a/(k : ℤ) : ℤ) : ℝ) + ((a%(k : ℤ) : ℤ) : ℝ) = (a : ℝ) := by
    exact_mod_cast Int.mul_ediv_add_emod a (k : ℤ)
  have h : (a : ℝ)/k - ((a/(k : ℤ) : ℤ) : ℝ) = ((a%(k : ℤ) : ℤ) : ℝ)/k := by
    field_simp
    linarith [he]
  rw [h,abs_of_nonneg (div_nonneg (by exact_mod_cast h₀) hkr.le)]
  exact (div_le_one hkr).mpr (by exact_mod_cast h₁.le)

private lemma round_value (t : ℤ × ℤ × ℕ) (ht : 0<t.2.2) (z : ℤ × ℤ) :
    ‖numerators z.1 z.2*hornerValue t -
      numerators ((z.1*t.1-z.2*t.2.1)/(t.2.2:ℤ)) ((z.1*t.2.1+z.2*t.1)/(t.2.2:ℤ))‖ ≤ 2 := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  have hr := division_rounding_error (z.1*t.1-z.2*t.2.1) t.2.2 ht
  have hi := division_rounding_error (z.1*t.2.1+z.2*t.1) t.2.2 ht
  simp only [Int.cast_sub,Int.cast_mul,Int.cast_add,sub_div,add_div,mul_div_assoc] at hr hi
  simp only [hornerValue,numerators,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.div_natCast_re,Complex.div_natCast_im]
  linarith [hr,hi]

/-- One jump floors each component of the exact scaled complex product, with
total Euclidean rounding error at most two. -/
lemma jump_round (n h : ℕ) (z : ℤ × ℤ) :
    ‖(⟨(z.1:ℝ),(z.2:ℝ)⟩:ℂ) * trunc n h 56 -
      ⟨((jump n h z).1:ℝ),((jump n h z).2:ℝ)⟩‖ ≤ 2 := by
  rw [← horner_exact]
  exact round_value (horner n h 56 0) (horner_den_pos n h 56 0) z

end ArctanBlocks

namespace ArctanBlocks

/-- Scaling the current rounded vector gives a small uniform bound on its norm. -/
private lemma lifted_bound {n : ℕ} {z : ℤ × ℤ} (hn : n ≤ upper+1) (hz : Accurate n z) :
    ‖lift z‖ ≤ 3*(scale : ℝ) := by
  have four : 4*(n:ℝ) ≤ (scale:ℝ) := by
    exact_mod_cast (Nat.mul_le_mul_left 4 hn).trans (by decide : 4*(upper+1) ≤ scale)
  calc
    ‖lift z‖ = ‖(scale:ℂ)*rotated n - ((scale:ℂ)*rotated n-lift z)‖ := by
      congr 1
      abel
    _ ≤ ‖(scale:ℂ)*rotated n‖ + ‖(scale:ℂ)*rotated n-lift z‖ := norm_sub_le _ _
    _ ≤ (scale:ℝ)*2 + 4*(n:ℝ) := by
      rw [norm_mul,Complex.norm_natCast]
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_rotated_le n) (by positivity)) hz
    _ ≤ 3*(scale:ℝ) := by linarith

/-- Rounding and truncation preserve a four-units-per-index error budget
even when a single jump covers many integer indices. -/
lemma accurate_jump {n h : ℕ} {z : ℤ × ℤ} (hn : 8 ≤ n) (hpos : 0 < h)
    (small : 8*h ≤ n+1) (stop : n+h ≤ upper+1) (hz : Accurate n z) :
    Accurate (n+h) (jump n h z) := by
  have zn := lifted_bound (by omega : n ≤ upper+1) hz
  have sn : 0 < (scale:ℝ) := by norm_num [scale]
  have nn : 0 < (n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hp : 1 ≤ (h:ℝ) := by exact_mod_cast hpos
  have last : 4 ≤ ((n+h+1:ℕ):ℝ) := by exact_mod_cast (by omega : 4 ≤ n+h+1)
  have fac : 4*(n:ℝ)*‖ratio n h‖ ≤ 4*(n:ℝ)+(h:ℝ) := by
    calc
      _ ≤ 4*(n:ℝ)*(1+(h:ℝ)/((n:ℝ)*((n+h+1:ℕ):ℝ))) :=
        mul_le_mul_of_nonneg_left (norm_ratio_le (by omega : 1≤n) h) (by positivity)
      _ = 4*(n:ℝ) + 4*(h:ℝ)/((n+h+1:ℕ):ℝ) := by
        field_simp
      _ ≤ 4*(n:ℝ)+(h:ℝ) := by
        apply add_le_add le_rfl
        apply (div_le_iff₀ (by positivity : 0 < ((n+h+1:ℕ):ℝ))).mpr
        nlinarith only [mul_nonneg (by positivity : 0≤(h:ℝ)) (sub_nonneg.mpr last)]
  have tr : ‖lift z‖*‖ratio n h-trunc n h 56‖ ≤ 1 := by
    calc
      _ ≤ (3*(scale:ℝ))*(1/(16*(scale:ℝ))) :=
        mul_le_mul zn (trunc56_error n h small) (norm_nonneg _) (by positivity)
      _ ≤ 1 := by field_simp; linarith
  have iden : (scale:ℂ)*rotated (n+h) - lift (jump n h z) =
      ((scale:ℂ)*rotated n - lift z)*ratio n h +
      lift z*(ratio n h-trunc n h 56) + (lift z*trunc n h 56 - lift (jump n h z)) := by
    rw [rotated_add]
    ring
  have round : ‖lift z*trunc n h 56 - lift (jump n h z)‖ ≤ 2 := jump_round n h z
  unfold Accurate
  rw [iden]
  calc
    _ ≤ ‖((scale:ℂ)*rotated n-lift z)*ratio n h‖ + ‖lift z*(ratio n h-trunc n h 56)‖ +
          ‖lift z*trunc n h 56-lift (jump n h z)‖ :=
      (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ (4*(n:ℝ)+(h:ℝ))+1+2 := by
      simp only [norm_mul]
      exact add_le_add (add_le_add ((mul_le_mul_of_nonneg_right hz (norm_nonneg _)).trans fac) tr) round
    _ ≤ 4*((n+h:ℕ):ℝ) := by push_cast; linarith

end ArctanBlocks

namespace ArctanBlocks.Range

/-- The rotated eighth product has the same coordinates as the unrotated product. -/
def start : ℤ × ℤ :=
  ((scale : ℤ)*Arxiv.«2607.05739».A 8/(Nat.factorial 8 : ℤ),
   (scale : ℤ)*Arxiv.«2607.05739».B 8/(Nat.factorial 8 : ℤ))

structure Admissible (n h : ℕ) (z : ℤ × ℤ) : Prop where
  width_eq : h=width n z
  pos : 0<h
  small : 8*h≤n+1
  stop : n+h≤upper+1
  early : n<lower → n+h≤lower
  late : lower≤n → clear n h z=true

inductive Reach : ℕ → ℤ × ℤ → Prop
  | first : Reach 8 start
  | next {n h : ℕ} {z : ℤ × ℤ} (previous : Reach n z) (valid : Admissible n h z) :
      Reach (n+h) (jump n h z)

private def guards (n h : ℕ) (z : ℤ × ℤ) : Bool :=
  decide (0<h ∧ 8*h≤n+1 ∧ n+h≤upper+1) &&
    (if n<lower then decide (n+h≤lower) else clear n h z)

private lemma of_guards {n : ℕ} {z : ℤ × ℤ} (hg : guards n (width n z) z=true) :
    Admissible n (width n z) z := by
  obtain ⟨g,h⟩ := Bool.and_eq_true_iff.mp hg
  obtain ⟨hp,hs,hb⟩ : 0<width n z ∧ 8*(width n z)≤n+1 ∧ n+width n z≤upper+1 := of_decide_eq_true g
  refine ⟨rfl,hp,hs,hb,?_,?_⟩
  · intro he
    simpa only [if_pos he,decide_eq_true_eq] using h
  · intro he
    simpa only [if_neg (Nat.not_lt.mpr he)] using h

/-- A group of consecutive steps, including its exact ending index and integer state. -/
private def segment (N : ℕ) (x y : ℤ) : ℕ → ℕ → ℤ × ℤ → Bool
  | 0, n, z => decide (n=N ∧ z=(x,y))
  | len+1, n, z =>
    let h := width n z
    guards n h z && segment N x y len (n+h) (jump n h z)

private lemma traverse {N len n : ℕ} {x y : ℤ} {z : ℤ × ℤ}
    (prev : Reach n z) (ok : segment N x y len n z=true) : Reach N (x,y) := by
  induction len generalizing n z with
  | zero =>
    obtain ⟨hn,hz⟩ : n=N ∧ z=(x,y) := of_decide_eq_true ok
    rwa [hn,hz] at prev
  | succ len ih =>
    obtain ⟨hg,next⟩ := Bool.and_eq_true_iff.mp ok
    exact ih (.next prev (of_guards hg)) next

private structure Checkpoint (n : ℕ) (x y : ℤ) : Type where
  reached : Reach n (x,y)

private def advanceCheckpoint {N n : ℕ} {x y u v : ℤ} (prev : Checkpoint n x y) (len : ℕ)
    (certificate : segment N u v len n (x,y)=true) : Checkpoint N u v :=
  ⟨traverse prev.reached certificate⟩

private lemma path_induction (Q : ℕ → ℤ × ℤ → Prop) (P : ℕ → Prop)
    (initial : Q 8 start)
    (advance : ∀ n z h, 8≤n → Q n z → Admissible n h z → Q (n+h) (jump n h z))
    (inside : ∀ n z h k, lower≤n → Q n z → Admissible n h z → n≤k → k<n+h → P k)
    {n : ℕ} {z : ℤ × ℤ} (reached : Reach n z) :
    8≤n ∧ Q n z ∧ ∀ k, lower≤k → k<n → P k := by
  induction reached with
  | first =>
    refine ⟨le_rfl,initial,?_⟩
    intro k hk h
    change 1000000≤k at hk
    omega
  | @next n h z _ good ih =>
    obtain ⟨hn,hq,prior⟩ := ih
    refine ⟨by omega,advance n z h hn hq good,?_⟩
    intro k hk hstop
    by_cases old : k<n
    · exact prior k hk old
    · have atLower : lower≤n := by
        by_contra! he
        have := good.early he
        omega
      exact inside n z h k atLower hq good (by omega) hstop

end ArctanBlocks.Range

namespace ArctanBlocks.Range

private def c0 : Checkpoint 8 (-2026238629136842091457985668374013412667823143660) (-1696385829044798030057848466545685647814921701669) := by
  constructor
  have e : start=((-2026238629136842091457985668374013412667823143660),(-1696385829044798030057848466545685647814921701669)) := by decide +kernel
  rw [← e]
  exact Reach.first

private def c8 : Checkpoint 17 (-2722570855956747348730378967055391263729477412130) 62433413504692892474375813473939262378702613045 := advanceCheckpoint c0 8 (by decide +kernel)
private def c16 : Checkpoint 40 (-1802701027119037487577189533419950487513148087075) 2100202052941424906028740502685228184901340411414 := advanceCheckpoint c8 8 (by decide +kernel)
private def c24 : Checkpoint 101 579439589815327070058865334096122360205701298671 2727512799363865658492786335180141327267018000119 := advanceCheckpoint c16 8 (by decide +kernel)
private def c32 : Checkpoint 256 2536929983571599303734577049826623168129143841423 1177067725446357483645777882947621869617487371058 := advanceCheckpoint c24 8 (by decide +kernel)
private def c40 : Checkpoint 653 2456166724621034389163604112506631783822835238871 (-1344356199035923399303641818022533984852492815672) := advanceCheckpoint c32 8 (by decide +kernel)
private def c48 : Checkpoint 1670 367209122571343748747737957285706642377393688878 (-2777141192853186086792995255779978364528217152811) := advanceCheckpoint c40 8 (by decide +kernel)
private def c56 : Checkpoint 4281 (-2028779576523810558262034417849893235842650328620) (-1932427088963906065687484140632312835843867103600) := advanceCheckpoint c48 8 (by decide +kernel)
private def c64 : Checkpoint 10982 (-2756290821906211666540364546831473149278694244165) 504183237151902478319057992300950465706971956235 := advanceCheckpoint c56 8 (by decide +kernel)
private def c72 : Checkpoint 28172 (-1213345705751878574915881233496022078820009877832) 2525780720771908653837130723242620985028476249593 := advanceCheckpoint c64 8 (by decide +kernel)
private def c80 : Checkpoint 72276 1329425420788735192474604489043306776456447211271 2466692962611417296263453034907006918634994076872 := advanceCheckpoint c72 8 (by decide +kernel)
private def c88 : Checkpoint 185440 2776933944370070974681062879763366270740634913304 375033712615056003901724532753269770085954023398 := advanceCheckpoint c80 8 (by decide +kernel)
private def c96 : Checkpoint 475796 1936101659568743071290270224673855547371274772146 (-2025721752971013703407537142171833464621750593333) := advanceCheckpoint c88 8 (by decide +kernel)
private def c104 : Checkpoint 1009594 29330406871536821893849188410701054879831932356 (-2801996914594770927368257217290976033718585983678) := advanceCheckpoint c96 8 (by decide +kernel)
private def c112 : Checkpoint 1020160 157186245766587987565248080315899608682299120 (-2802150431010202485891329724682661505764090181806) := advanceCheckpoint c104 8 (by decide +kernel)
private def c120 : Checkpoint 1020219 (-4868739728041223051146269334326649720576208) (-2802150435494067181172377448708806929933892342379) := advanceCheckpoint c112 8 (by decide +kernel)
private def c128 : Checkpoint 1020277 (-164167895974249822371831078456478410290554702) (-2802150430767362991166526372981063168628018163137) := advanceCheckpoint c120 8 (by decide +kernel)
private def c136 : Checkpoint 1021608 (-3817321456116133539192864888409132370974472187) (-2802147837228510598281567604007095756304190839081) := advanceCheckpoint c128 8 (by decide +kernel)
private def c144 : Checkpoint 1052464 (-87184630394390858256684280191049803443932207529) (-2800793840893418619925397917531062334951864080929) := advanceCheckpoint c136 8 (by decide +kernel)
private def c152 : Checkpoint 1761197 (-1455028352909806798126602406379382163118767806830) (-2394774058959368962550100887089420111629773409821) := advanceCheckpoint c144 8 (by decide +kernel)
private def c160 : Checkpoint 4399899 (-2785451388731367787493476156756405170665240065165) (-305472643639683821878951249970457839731168447792) := advanceCheckpoint c152 8 (by decide +kernel)
private def c168 : Checkpoint 4904686 (-2802150982462822302589645291320662148531119087466) (-1740732605471042423246104342096612943101898660) := advanceCheckpoint c160 8 (by decide +kernel)
private def c176 : Checkpoint 4907718 (-2802151523307586213168792182802398572745646741768) (-9021951604253644730405902558631596540359461) := advanceCheckpoint c168 8 (by decide +kernel)
private def c184 : Checkpoint 4907738 (-2802151523322247839731835184484102691981949561694) 2397390453165738279346006595400047975932875 := advanceCheckpoint c176 8 (by decide +kernel)
private def c192 : Checkpoint 4907862 (-2802151522374489742272339288656418962566770064953) 73196272532956407639224540812914108843807271 := advanceCheckpoint c184 8 (by decide +kernel)
private def c200 : Checkpoint 4910704 (-2802151010625111845014353981758937468896726575857) 1695370739430236439953477937335206878443259321 := advanceCheckpoint c192 8 (by decide +kernel)
private def c208 : Checkpoint 4976193 (-2801882663004574231172971491555805144459904812297) 38816548362967394389859438370138901146254905994 := advanceCheckpoint c200 8 (by decide +kernel)
private def c216 : Checkpoint 6638202 (-2675312102757659317984672021473071247707502531981) 833521883081713414418904391054039354008154381739 := advanceCheckpoint c208 8 (by decide +kernel)
private def c224 : Checkpoint 17032193 (-898742947000948907524415811259564227058571150648) 2654112924085881148605933550708792876012988053667 := advanceCheckpoint c216 8 (by decide +kernel)
private def c232 : Checkpoint 23552037 (-6715018312448039714689345097127340853145665702) 2802143703440905313864851299653289755357141930925 := advanceCheckpoint c224 8 (by decide +kernel)
private def c240 : Checkpoint 23608240 (-36123935456885405334128089594594995784134789) 2802151749226511771625821987190051243551510278807 := advanceCheckpoint c232 8 (by decide +kernel)
private def c248 : Checkpoint 23608544 (-41252918301197140155583099503281098524808) 2802151749460121492171198595957607487091267972695 := advanceCheckpoint c240 8 (by decide +kernel)
private def c256 : Checkpoint 23608571 3163436552161904554315094689740894018638348 2802151749458404016062666407028982810922085877979 := advanceCheckpoint c248 8 (by decide +kernel)
private def c264 : Checkpoint 23609179 75327325236853860465814447311983123181666281 2802151748449244996940896169222691791655470922061 := advanceCheckpoint c256 8 (by decide +kernel)
private def c272 : Checkpoint 23623133 1731025366120039036498731142684352109485698271 2802151214827458919701897780763582276299861670095 := advanceCheckpoint c264 8 (by decide +kernel)
private def c280 : Checkpoint 23944699 39616252042291158052295808535911615721385013167 2801871693037666947955848561147122486449811921968 := advanceCheckpoint c272 8 (by decide +kernel)
private def c288 : Checkpoint 32121566 849265272674245220257204153071350725487038221744 2670356345467334970404708770851939111612651670912 := advanceCheckpoint c280 8 (by decide +kernel)
private def c296 : Checkpoint 82417014 2659360766542745839751434456414389938493773111070 883093980104669948651905996437944979026395554359 := advanceCheckpoint c288 8 (by decide +kernel)
private def c304 : Checkpoint 113305002 2802144244085526869433719873819467349582477813545 6505815427254747023860529227402671036913439113 := advanceCheckpoint c296 8 (by decide +kernel)
private def c312 : Checkpoint 113566946 2802151796248824221796425540082520729337600687169 35147576500829406435805752652680945140961880 := advanceCheckpoint c304 8 (by decide +kernel)
private def c320 : Checkpoint 113568364 2802151796469402885002486715771488802219147158188 160050960686900990814475694329227211469840 := advanceCheckpoint c312 8 (by decide +kernel)
private def c328 : Checkpoint 113568382 2802151796469395011696419528550114164941763948262 (-284075610663963654002007996090640755195608) := advanceCheckpoint c320 8 (by decide +kernel)
private def c336 : Checkpoint 113568656 2802151796460583973835302457166713800209953654350 (-7044660283357142323230752988830771949231132) := advanceCheckpoint c328 8 (by decide +kernel)
private def c344 : Checkpoint 113574934 2802151791790674359866206777665037795782504901042 (-161941471547401246214090850101204528268945901) := advanceCheckpoint c336 8 (by decide +kernel)
private def c352 : Checkpoint 113719001 2802149335001772605145669514053703052907031335233 (-3714148278693066551639859024480912215975447370) := advanceCheckpoint c344 8 (by decide +kernel)
private def c360 : Checkpoint 117057189 2800869180810589812534689003038261719260871214114 (-84773371425267520855363327231091313191530170818) := advanceCheckpoint c352 8 (by decide +kernel)
private def c368 : Checkpoint 194457818 2406578942485316651608471324296245095638486084395 (-1435420674507378723086042682761736751637261122152) := advanceCheckpoint c360 8 (by decide +kernel)
private def c376 : Checkpoint 487503234 318487812686991166014713523420468823883136558034 (-2783993580570789593538152454903635433687633943331) := advanceCheckpoint c368 8 (by decide +kernel)
private def c384 : Checkpoint 545963391 1819843182613071321616961348991385378243029156 (-2802151215296018844498158611952983099434549592975) := advanceCheckpoint c376 8 (by decide +kernel)
private def c392 : Checkpoint 546316163 9829149173629233953566462711026455530664390 (-2802151806224430690389853227736477245157643781494) := advanceCheckpoint c384 8 (by decide +kernel)
private def c400 : Checkpoint 546318070 47827431705343274216905363593594169710561 (-2802151806241678159965434229269788578486659754082) := advanceCheckpoint c392 8 (by decide +kernel)
private def c408 : Checkpoint 546318087 (-39368256186414263742659269149334028645397) (-2802151806241678371382263172936109380795274735539) := advanceCheckpoint c400 8 (by decide +kernel)
private def c416 : Checkpoint 546318275 (-1003649800188861551204576890712108663344350) (-2802151806241499791280353684099285399970214444768) := advanceCheckpoint c408 8 (by decide +kernel)
private def c424 : Checkpoint 546322584 (-23105096991199204495408773531315136749969846) (-2802151806146443407906610171758557822591839667933) := advanceCheckpoint c416 8 (by decide +kernel)
private def c432 : Checkpoint 546421432 (-530062072207306587232751886808042193163182781) (-2802151756108226925739858647084788196963671483803) := advanceCheckpoint c424 8 (by decide +kernel)
private def c440 : Checkpoint 548691908 (-12149328245376486495005656539554736817638918322) (-2802125468123950579256483738528965119309385386052) := advanceCheckpoint c432 8 (by decide +kernel)
private def c448 : Checkpoint 602512539 (-273912477015058018908644078538444680832973659035) (-2788732095684250580213895407452548530205154529427) := advanceCheckpoint c440 8 (by decide +kernel)
private def c456 : Checkpoint 1336054220 (-2184992175085152021151501713486059514136598197751) (-1754384207787960569445495915327924975695276018017) := advanceCheckpoint c448 8 (by decide +kernel)
private def c464 : Checkpoint 2584867250 (-2801767211358647426249922065978780029016355140906) (-46424669240270665513156626449976734956182363562) := advanceCheckpoint c456 8 (by decide +kernel)
private def c472 : Checkpoint 2627813781 (-2802151796879183182991362616128129103362556329921) (-252695252262027089389803954619824956316423975) := advanceCheckpoint c464 8 (by decide +kernel)
private def c480 : Checkpoint 2628049486 (-2802151808272801792715397167771865301339524046652) (-1364059712544656741946236345285390660522644) := advanceCheckpoint c472 8 (by decide +kernel)
private def c488 : Checkpoint 2628050759 (-2802151808273134048251773471644704058375277634847) (-6726676651251336199124622455518346936866) := advanceCheckpoint c480 8 (by decide +kernel)
private def c496 : Checkpoint 2628050777 (-2802151808273134032249173973380173547440182019092) 12465773187799942054616031037532958146244 := advanceCheckpoint c488 8 (by decide +kernel)
private def c504 : Checkpoint 2628051055 (-2802151808273117092242872085645532255948670700874) 308882481786957848651565815145807814795235 := advanceCheckpoint c496 8 (by decide +kernel)
private def c512 : Checkpoint 2628057430 (-2802151808264124821570707491450989027940315582544) 7106199479832641724433288512570348321589947 := advanceCheckpoint c504 8 (by decide +kernel)
private def c520 : Checkpoint 2628203655 (-2802151803531560793955094302646196197930669470979) 163013465623886419153361800827813790825232939 := advanceCheckpoint c512 8 (by decide +kernel)
private def c528 : Checkpoint 2631558957 (-2802149314934949283105976416124118570810264723914) 3738104061226254958848699001504423050745779385 := advanceCheckpoint c520 8 (by decide +kernel)
private def c536 : Checkpoint 2709309817 (-2800852699195393470185886194162149450750242314479) 85316552367550966059518178796836230585902823699 := advanceCheckpoint c528 8 (by decide +kernel)
private def c544 : Checkpoint 4508180729 (-2403932199466920466791243375176735390005741042270) 1439848859505948642477711899190856442998469362482 := advanceCheckpoint c536 8 (by decide +kernel)
private def c552 : Checkpoint 11293072300 (-315550057904956382714984034753826446418091283302) 2784328091273918443593451200168600664489673995052 := advanceCheckpoint c544 8 (by decide +kernel)
private def c560 : Checkpoint 12634051245 (-1802052168161391553016985434401527564084296842) 2802151229249175529997081902608883033358177695061 := advanceCheckpoint c552 8 (by decide +kernel)
private def c568 : Checkpoint 12642134838 (-9736359687152335769582222075984374343878544) 2802151808678516787225456914458054474761433187990 := advanceCheckpoint c560 8 (by decide +kernel)
private def c576 : Checkpoint 12642178528 (-52409742000749159393288044055892631596012) 2802151808695431663026224582059207347279281610679 := advanceCheckpoint c568 8 (by decide +kernel)
private def c584 : Checkpoint 12642178764 (-100100969438016489606176546252878211760) 2802151808695432155213249064615247973149945442926 := advanceCheckpoint c576 8 (by decide +kernel)
private def c592 : Checkpoint 12642178791 5884476543928379931320344157641186040560 2802151808695432149273071914959635951601833320878 := advanceCheckpoint c584 8 (by decide +kernel)
private def c600 : Checkpoint 12642179390 138653433645911223782648871883630955474060 2802151808695428730343525656882026997040344229916 := advanceCheckpoint c592 8 (by decide +kernel)
private def c608 : Checkpoint 12642193130 3184136632368188689502167417001927404241670 2802151808693623184645845101915830266434910192284 := advanceCheckpoint c600 8 (by decide +kernel)
private def c616 : Checkpoint 12642508271 73034510504328112553514804728207765895206341 2802151807743659392409037070305139294869749106135 := advanceCheckpoint c608 8 (by decide +kernel)
private def c624 : Checkpoint 12649737751 1674956279728352109164322279696832941980853657 2802151308101850868015605966918294012224448416493 := advanceCheckpoint c616 8 (by decide +kernel)
private def c632 : Checkpoint 12816318808 38333701817924448651812912163795968141701967160 2801889592094673414641996258886402880330475775957 := advanceCheckpoint c624 8 (by decide +kernel)
private def c640 : Checkpoint 17038889251 823967826465281514910407262066105242796473679779 2678270296307941724522234144229376064543994966456 := advanceCheckpoint c632 8 (by decide +kernel)
private def c648 : Checkpoint 43718118170 2650888469722428784371561054755692428278397835964 908209821852447794699852627951819081006721646820 := advanceCheckpoint c640 8 (by decide +kernel)
private def c656 : Checkpoint 60666593372 2802143454475696849772504250393797531154074195272 6842514578737639969593481391930508859745997819 := advanceCheckpoint c648 8 (by decide +kernel)
private def c664 : Checkpoint 60814111960 2802151808538923475315388035747771081513229697397 37001436408013043814632972987411836598375000 := advanceCheckpoint c656 8 (by decide +kernel)
private def c672 : Checkpoint 60814910657 2802151808783212176246759270652999146139801271652 199854104493107390835475131735612513094199 := advanceCheckpoint c664 8 (by decide +kernel)
private def c680 : Checkpoint 60814914972 2802151808783219304653718917823774514940074751000 1033050655844135659579135211302632309103 := advanceCheckpoint c672 8 (by decide +kernel)
private def c688 : Checkpoint 60814914999 2802151808783219304846425575317225733245758105066 (-211020783778264887808808725371041814649) := advanceCheckpoint c680 8 (by decide +kernel)
private def c696 : Checkpoint 60814915124 2802151808783219298540864233552717334532804965705 (-5970610774832397472161164585452377804309) := advanceCheckpoint c688 8 (by decide +kernel)
private def c704 : Checkpoint 60814917993 2802151808783215899768945622980374774359711233927 (-138164716995460062211060329128698419680226) := advanceCheckpoint c696 8 (by decide +kernel)
private def c712 : Checkpoint 60814983796 2802151808781426093527429718543071376145243208573 (-3170149331957945745127923031624255925133149) := advanceCheckpoint c704 8 (by decide +kernel)
private def c720 : Checkpoint 60816493057 2802151807839857355545601071167556990818687523356 (-72711004218942866871625033214023518976608856) := advanceCheckpoint c712 8 (by decide +kernel)
private def c728 : Checkpoint 60851116172 2802151312615655649754024486171075223382089864727 (-1667535157812524787586594223363964114954886738) := advanceCheckpoint c720 8 (by decide +kernel)
private def c736 : Checkpoint 61648882658 2801891905751403110606888605502352645750068131871 (-38164223476767485267701548326009739396417453479) := advanceCheckpoint c728 8 (by decide +kernel)
private def c744 : Checkpoint 81862604983 2679300106968326249252691217542011080491590363852 (-820613000323404363436220642331529366965677758849) := advanceCheckpoint c736 8 (by decide +kernel)
private def c752 : Checkpoint 210041804135 911528997178925938530737851246336970191393496212 (-2649748978084675088868722013325756024559150538415) := advanceCheckpoint c744 8 (by decide +kernel)
private def c760 : Checkpoint 291830607335 6887334816738424228335815605828331337221191578 (-2802143344689631959504935029672998751734118986452) := advanceCheckpoint c752 8 (by decide +kernel)
private def c768 : Checkpoint 292544884694 37244108421494628970621015846691169897576896 (-2802151808553957964187349030300421964730479273374) := advanceCheckpoint c760 8 (by decide +kernel)
private def c776 : Checkpoint 292548752006 201164741782180788561364731457445603714340 (-2802151808801461239237977027850531674956955298209) := advanceCheckpoint c768 8 (by decide +kernel)
private def c784 : Checkpoint 292548772895 1081348355220265157331798769071104631092 (-2802151808801468460117369709006279856326429440144) := advanceCheckpoint c776 8 (by decide +kernel)
private def c792 : Checkpoint 292548773009 (-10590274292409262175026357293667192110) (-2802151808801468460327861721350636856318422414752) := advanceCheckpoint c784 8 (by decide +kernel)
private def c800 : Checkpoint 292548773056 (-460775498616740662575121966341183429787) (-2802151808801468460290767041585978492500091152433) := advanceCheckpoint c792 8 (by decide +kernel)
private def c808 : Checkpoint 292548774143 (-10872506092066051953488802680112260214242) (-2802151808801468439253479468969836972177303499931) := advanceCheckpoint c800 8 (by decide +kernel)
private def c816 : Checkpoint 292548799076 (-249690967308198726053564709643240806517063) (-2802151808801457336164762016857069812879017052565) := advanceCheckpoint c808 8 (by decide +kernel)
private def c824 : Checkpoint 292549370929 (-5727127064233464087919078851764162819093765) (-2802151808795615827816988129438844324969237067643) := advanceCheckpoint c816 8 (by decide +kernel)
private def c832 : Checkpoint 292562487068 (-131355798276534567647630817217407786428319890) (-2802151805722701557335842948372271853536893509388) := advanceCheckpoint c824 8 (by decide +kernel)
private def c840 : Checkpoint 292863425866 (-3012253561757374184887167750976516000618194352) (-2802150189746768368617777024082663424064339810246) := advanceCheckpoint c832 8 (by decide +kernel)
private def c848 : Checkpoint 299823112507 (-68817509103744662050992788564252677836856194788) (-2801306643338202750813802913273393618985162612015) := advanceCheckpoint c840 8 (by decide +kernel)
private def c856 : Checkpoint 471121587095 (-1285230388577742030415574727674284159111484414207) (-2490027631946244309033883312740100751667810799543) := advanceCheckpoint c848 8 (by decide +kernel)
private def c864 : Checkpoint 1208796472353 (-2769823583848071026295207117846261180778585873768) (-424419690811717289697646647661054513242174994265) := advanceCheckpoint c856 8 (by decide +kernel)
private def c872 : Checkpoint 1406056443347 (-2802150715142820095721172328511708430683558851621) (-2475725182460165614749216095270092252061809993) := advanceCheckpoint c864 8 (by decide +kernel)
private def c880 : Checkpoint 1407292536629 (-2802151808773326956464222617817745494446949690845) (-13378121735053513354583393684688558936171987) := advanceCheckpoint c872 8 (by decide +kernel)
private def c888 : Checkpoint 1407299219095 (-2802151808805261155311759511404360571781177061856) (-72260129330197649861619590003119066179621) := advanceCheckpoint c880 8 (by decide +kernel)
private def c896 : Checkpoint 1407299255191 (-2802151808805262087009914568515627701873016903617) (-387375461632172633869583074197353611550) := advanceCheckpoint c888 8 (by decide +kernel)
private def c904 : Checkpoint 1407299255386 (-2802151808805262087036828180876391173877858493703) 899882551687203746942165218177089471 := advanceCheckpoint c896 8 (by decide +kernel)
private def c912 : Checkpoint 1407299255425 (-2802151808805262087035754818745707733917839808120) 78554951382003086667893214605602959645 := advanceCheckpoint c904 8 (by decide +kernel)
private def c920 : Checkpoint 1407299256311 (-2802151808805262086431588934193301994578158860745) 1842718822178115948408817326472893350047 := advanceCheckpoint c912 8 (by decide +kernel)
private def c928 : Checkpoint 1407299276637 (-2802151808805261767555471438609789665998765754494) 42314947453733220747860728770451213845390 := advanceCheckpoint c920 8 (by decide +kernel)
private def c936 : Checkpoint 1407299742833 (-2802151808805093996479917720075424527091732715182) 970583560936935278681413154540552200160406 := advanceCheckpoint c928 8 (by decide +kernel)
private def c944 : Checkpoint 1407310435459 (-2802151808716837187909808761046129590199797949809) 22261177560539631354199147351282494755639907 := advanceCheckpoint c936 8 (by decide +kernel)
private def c952 : Checkpoint 1407555694921 (-2802151762291702452942845117810360486854891548517) 510564500703197434373405768620122053008770393 := advanceCheckpoint c944 8 (by decide +kernel)
private def c960 : Checkpoint 1413188857374 (-2802127371932207846348185723632831811182027323214) 11702609064796565895248893309516319863557689994 := advanceCheckpoint c952 8 (by decide +kernel)
private def c968 : Checkpoint 1546561468662 (-2789685723188234589617404257561428426696892080803) 264023342587054379544036817233545596313539140968 := advanceCheckpoint c960 8 (by decide +kernel)
private def c976 : Checkpoint 3405197623421 (-1777541524531933897107249291698450788587888003305) 2166195025420971635881139854408223254096870147405 := advanceCheckpoint c968 8 (by decide +kernel)
private def c984 : Checkpoint 6652232751771 (-49080603955639904838654334675167730993319628409) 2801721944431736586292898194252277669100518539493 := advanceCheckpoint c976 8 (by decide +kernel)
private def c992 : Checkpoint 6769135560966 (-267271050477927159467547404355649718656566711) 2802151796059807893545260623017133671618904565671 := advanceCheckpoint c984 8 (by decide +kernel)
private def c1000 : Checkpoint 6769777748331 (-1443735696681440721130873174281530486207112) 2802151808805678780845981487010035725835980314027 := advanceCheckpoint c992 8 (by decide +kernel)
private def c1008 : Checkpoint 6769781217444 (-7798042807465886731605297130873318377351) 2802151808806050693698849575180769674909262603189 := advanceCheckpoint c1000 8 (by decide +kernel)
private def c1016 : Checkpoint 6769781236183 (-41584956622062812242571719080744510564) 2802151808806050704549609459945611071373896035356 := advanceCheckpoint c1008 8 (by decide +kernel)
private def c1024 : Checkpoint 6769781236285 634943035610055784261877551686159954 2802151808806050704549921074245855625607225762310 := advanceCheckpoint c1016 8 (by decide +kernel)
private def c1032 : Checkpoint 6769781236342 24228416373444297660385118629388586434 2802151808806050704549818144921824982419025586926 := advanceCheckpoint c1024 8 (by decide +kernel)
private def c1040 : Checkpoint 6769781237653 566878303088804014892521266856589017308 2802151808806050704492622924558124405802747564569 := advanceCheckpoint c1032 8 (by decide +kernel)
private def c1048 : Checkpoint 6769781267722 13013056339570235655682791317024709187749 2802151808806050674334882714713812789581284756326 := advanceCheckpoint c1040 8 (by decide +kernel)
private def c1056 : Checkpoint 6769781957379 298476269277326392499548926157315421830371 2802151808806034808202068659985237845048399482415 := advanceCheckpoint c1048 8 (by decide +kernel)
private def c1064 : Checkpoint 6769797775249 6845809924710745485722098050765696886125891 2802151808797688361270652387459235188542538840697 := advanceCheckpoint c1056 8 (by decide +kernel)
private def c1072 : Checkpoint 6770160578273 157013059052843816462914631275656834829681170 2802151804407091913306235945717761680611821888064 := advanceCheckpoint c1064 8 (by decide +kernel)
private def c1080 : Checkpoint 6778485378714 3600508580653560793484611225179062140397479878 2802149495643118586874978450587686018580484966297 := advanceCheckpoint c1072 8 (by decide +kernel)
private def c1088 : Checkpoint 6971319613438 82191467863216893708695031022646678494558307037 2800946147680377138530094276684624664381080588899 := advanceCheckpoint c1080 8 (by decide +kernel)
private def c1096 : Checkpoint 11490393417420 1414265695652208034346093081515075859407149905601 2419071578456676078839169097649962766494936080128 := advanceCheckpoint c1088 8 (by decide +kernel)
private def c1104 : Checkpoint 28913914495541 2782353815819834156801543011519768909345266736943 332508651299057828211000832497549967651128556740 := advanceCheckpoint c1096 8 (by decide +kernel)
private def c1112 : Checkpoint 32543747048173 2802151161230193219164264612620096117135911521072 1905049138479246389323236353133214398239281134 := advanceCheckpoint c1104 8 (by decide +kernel)
private def c1120 : Checkpoint 32565759884348 2802151808787308836520951914815555760939564463529 10293389786219451778190547530083262159303422 := advanceCheckpoint c1112 8 (by decide +kernel)
private def c1128 : Checkpoint 32565878865057 2802151808806214090416470738330571898605343325320 55600123970136127619224713642066195863025 := advanceCheckpoint c1120 8 (by decide +kernel)
private def c1136 : Checkpoint 32565879507738 2802151808806214642008357580172872127064792635665 300228139669006219538707397119881477031 := advanceCheckpoint c1128 8 (by decide +kernel)
private def c1144 : Checkpoint 32565879511209 2802151808806214642024445250558636021298804302543 1563737697709099245018794530477129287 := advanceCheckpoint c1136 8 (by decide +kernel)
private def c1152 : Checkpoint 32565879511232 2802151808806214642024445686487939825433494286611 (-415311926310298755131656985693341138) := advanceCheckpoint c1144 8 (by decide +kernel)
private def c1160 : Checkpoint 32565879511359 2802151808806214642024422926600658599190280257979 (-11343107676305285954699250266542532377) := advanceCheckpoint c1152 8 (by decide +kernel)
private def c1168 : Checkpoint 32565879514272 2802151808806214642012201846036961847603915697561 (-261994044827877097232687027409977839810) := advanceCheckpoint c1160 8 (by decide +kernel)
private def c1176 : Checkpoint 32565879581089 2802151808806214635576673342052687833953690361417 (-6011305287439087222626347724161882051856) := advanceCheckpoint c1168 8 (by decide +kernel)
private def c1184 : Checkpoint 32565881113580 2802151808806211250054075106343718143000846476983 (-137875464395935647423810939235422302309402) := advanceCheckpoint c1176 8 (by decide +kernel)
private def c1192 : Checkpoint 32565916262566 2802151808804430284533851101514401589391379229007 (-3162290532470280100812761820441017229550201) := advanceCheckpoint c1184 8 (by decide +kernel)
private def c1200 : Checkpoint 32566722441194 2802151807867555776531819448331424886058704174041 (-72529506278093402440512399185636452654658974) := advanceCheckpoint c1192 8 (by decide +kernel)
private def c1208 : Checkpoint 32585216529863 2802151315112898885391217028107204018078121124412 (-1663372174799124253232546340282157502554435591) := advanceCheckpoint c1200 8 (by decide +kernel)
private def c1216 : Checkpoint 33011342116346 2801893199103182974634794340613143819604081030279 (-38069153067474473020195269791754957155969364277) := advanceCheckpoint c1208 8 (by decide +kernel)
private def c1224 : Checkpoint 43805944852416 2679876160422190272122411134424539105194231123478 (-818729823810529986337793291607671510479529067172) := advanceCheckpoint c1216 8 (by decide +kernel)
private def c1232 : Checkpoint 112396614921289 913390977793003825588961923857491479286474425543 (-2649107714171406081831808843250420180364303490636) := advanceCheckpoint c1224 8 (by decide +kernel)
private def c1240 : Checkpoint 156271450962504 6912511842845921435308656659560889041640226761 (-2802143282699183082547267644690658638450665582606) := advanceCheckpoint c1232 8 (by decide +kernel)
private def c1248 : Checkpoint 156655336999668 37380422524578980144034721838199781329963741 (-2802151808556923187868265090887671406540049798395) := advanceCheckpoint c1240 8 (by decide +kernel)
private def c1256 : Checkpoint 156657415491844 201912782064978764644257926763501609249708 (-2802151808806241446729287125699389842181619463173) := advanceCheckpoint c1248 8 (by decide +kernel)
private def c1264 : Checkpoint 156657426719031 1090617766220776688255220941298023847212 (-2802151808806248721064956256972545662333995228429) := advanceCheckpoint c1256 8 (by decide +kernel)
private def c1272 : Checkpoint 156657426779675 5870634728988435251427707089321908076 (-2802151808806248721277191733815661459304690701212) := advanceCheckpoint c1264 8 (by decide +kernel)
private def c1280 : Checkpoint 156657426780003 3655983192191867813380204011807911 (-2802151808806248721277197902161369885545117765818) := advanceCheckpoint c1272 8 (by decide +kernel)
private def c1288 : Checkpoint 156657426780030 (-479296535516098032782842919341659656) (-2802151808806248721277197862714333610040186500838) := advanceCheckpoint c1280 8 (by decide +kernel)
private def c1296 : Checkpoint 156657426780638 (-11354671771591844134860278570543960838) (-2802151808806248721277174933136390397595176809649) := advanceCheckpoint c1288 8 (by decide +kernel)
private def c1304 : Checkpoint 156657426794590 (-260915914019416911341228420211827964702) (-2802151808806248721265051442633563444118797703401) := advanceCheckpoint c1296 8 (by decide +kernel)
private def c1312 : Checkpoint 156657427114583 (-5984672400938296920823212147348877755072) (-2802151808806248714886359870956186649545523440603) := advanceCheckpoint c1304 8 (by decide +kernel)
private def c1320 : Checkpoint 156657434453895 (-137263899267094896322098209089145896024122) (-2802151808806245359329510496786386805463322988820) := advanceCheckpoint c1312 8 (by decide +kernel)
private def c1328 : Checkpoint 156657602787253 (-3148262846240851284711471242072616850123889) (-2802151808804480159191881624442076276857993102845) := advanceCheckpoint c1320 8 (by decide +kernel)
private def c1336 : Checkpoint 156661463688118 (-72207771183742866259485063285438155676445877) (-2802151807875899016005705784917660023883005364588) := advanceCheckpoint c1328 8 (by decide +kernel)
private def c1344 : Checkpoint 156750034355982 (-1655994264112542397870177552546507073551914669) (-2802151319482787807548365069846496676881590119856) := advanceCheckpoint c1336 8 (by decide +kernel)
private def c1352 : Checkpoint 158790765489251 (-37900662793130863152740563641297659157614303547) (-2801895483303396445219266301887710933358821792189) := advanceCheckpoint c1344 8 (by decide +kernel)
private def c1360 : Checkpoint 210465107760449 (-815390112584370346088077187123598361389310582204) (-2680894202294412093835802200014543466964179671127) := advanceCheckpoint c1352 8 (by decide +kernel)
private def c1368 : Checkpoint 540008114218647 (-2647967589723307205892935842856883585153407955732) (-916691007576220348742689672654250221163103954892) := advanceCheckpoint c1360 8 (by decide +kernel)
private def c1376 : Checkpoint 751728293294050 (-2802143172118825248076927923130667028828098156457) (-6957193688468554023612433550568264854156921689) := advanceCheckpoint c1368 8 (by decide +kernel)
private def c1384 : Checkpoint 753586890190078 (-2802151808553692919600828399307414002166757690563) (-37622321775778077257756058740897681914120328) := advanceCheckpoint c1376 8 (by decide +kernel)
private def c1392 : Checkpoint 753596953432601 (-2802151808806248436652423824751043686571194896233) (-203219445077666569292468515141351925351360) := advanceCheckpoint c1384 8 (by decide +kernel)
private def c1400 : Checkpoint 753597007790235 (-2802151808806255805442821005223303756820251682199) (-1097692530373475005091347067039361864525) := advanceCheckpoint c1392 8 (by decide +kernel)
private def c1408 : Checkpoint 753597008083850 (-2802151808806255805657816113282358030764610190663) (-5923594619707660972960408397464664516) := advanceCheckpoint c1400 8 (by decide +kernel)
private def c1416 : Checkpoint 753597008085435 (-2802151808806255805657822378108725622652627711241) (-29979638079360507258874535334255061) := advanceCheckpoint c1408 8 (by decide +kernel)
private def c1424 : Checkpoint 753597008085448 (-2802151808806255805657822378241027776486621001441) 18359159877161052999961545084959935 := advanceCheckpoint c1416 8 (by decide +kernel)
private def c1432 : Checkpoint 753597008085575 (-2802151808806255805657822335668825501423332609311) 490592032221597046220659191998491309 := advanceCheckpoint c1424 8 (by decide +kernel)
private def c1440 : Checkpoint 753597008088488 (-2802151808806255805657799511908551303601284020662) 11322201143533151719624506269838497227 := advanceCheckpoint c1432 8 (by decide +kernel)
private def c1448 : Checkpoint 753597008155305 (-2802151808806255805645781494433255394673382372487) 259772467520814538226787413240960450376 := advanceCheckpoint c1440 8 (by decide +kernel)
private def c1456 : Checkpoint 753597009687798 (-2802151808806255799323494976972666136222599201960) 5958147037874173603604847494639222977969 := advanceCheckpoint c1448 8 (by decide +kernel)
private def c1464 : Checkpoint 753597044836817 (-2802151808806252473462430968235937569730096816428) 136655168928238604741231477602363270468353 := advanceCheckpoint c1456 8 (by decide +kernel)
private def c1472 : Checkpoint 753597851009477 (-2802151808804502895246537612160335948117617938017) 3134300906257288302697818354604682324499556 := advanceCheckpoint c1464 8 (by decide +kernel)
private def c1480 : Checkpoint 753616341418209 (-2802151807884139623263529986694159101904795089008) 71887544514111581795811717284038765755462768 := advanceCheckpoint c1472 8 (by decide +kernel)
private def c1488 : Checkpoint 754040518691864 (-2802151323812875789335225579039615861742152072440) 1648650939080539921457673341785476216054533485 := advanceCheckpoint c1480 8 (by decide +kernel)
private def c1496 : Checkpoint 763813667293085 (-2801897746777323828722920650961860308146598061485) 37732959071971114919781147239383092722460891356 := advanceCheckpoint c1488 8 (by decide +kernel)
private def c1504 : Checkpoint 1011182241637619 (-2681903830303309859610602139917552320540020129997) 812063177715015716071260377506221978708109166691 := advanceCheckpoint c1496 8 (by decide +kernel)
private def c1512 : Checkpoint 2594475736375398 (-919975755675328270095474794179542969726345030815) 2646828171333716798691858797627901556003856638801 := advanceCheckpoint c1504 8 (by decide +kernel)
private def c1520 : Checkpoint 3616114458253898 (-7001745123064342481141269680469749945980513515) 2802143061151841170292718437439684194909322096001 := advanceCheckpoint c1512 8 (by decide +kernel)
private def c1528 : Checkpoint 3625112377817855 (-37863518520135165540606984515880897578273803) 2802151808550445649893438692805955401668226906021 := advanceCheckpoint c1520 8 (by decide +kernel)
private def c1536 : Checkpoint 3625161097166423 (-204522295345822436795098682257142131405332) 2802151808806249814561555486541510696307149533378 := advanceCheckpoint c1528 8 (by decide +kernel)
private def c1544 : Checkpoint 3625161360328989 (-1104732982193655816917246070189106488100) 2802151808806257278138097689905979190625554692696 := advanceCheckpoint c1536 8 (by decide +kernel)
private def c1552 : Checkpoint 3625161361750470 (-5966566402633759694539147346003919130) 2802151808806257278355858948862986316394361185535 := advanceCheckpoint c1544 8 (by decide +kernel)
private def c1560 : Checkpoint 3625161361758148 (-31679802826567818326533570519354537) 2802151808806257278355865301748369304470163152689 := advanceCheckpoint c1552 8 (by decide +kernel)
private def c1568 : Checkpoint 3625161361758191 1558035645877803377379352482418561 2802151808806257278355865301931598917537347925792 := advanceCheckpoint c1560 8 (by decide +kernel)
private def c1576 : Checkpoint 3625161361758249 46390468934292203466888079005872627 2802151808806257278355865301554211463667655173518 := advanceCheckpoint c1568 8 (by decide +kernel)
private def c1584 : Checkpoint 3625161361759585 1079082380543087418156662034957158720 2802151808806257278355865094308397409598376310920 := advanceCheckpoint c1576 8 (by decide +kernel)
private def c1592 : Checkpoint 3625161361790242 24776115265311900566081903969793876849 2802151808806257278355755772402681188233281701640 := advanceCheckpoint c1584 8 (by decide +kernel)
private def c1600 : Checkpoint 3625161362493369 568274293152336935767020890931083127346 2802151808806257278298242579283060427115431774615 := advanceCheckpoint c1592 8 (by decide +kernel)
private def c1608 : Checkpoint 3625161378620193 13033873592793871528880037276703180578232 2802151808806257248043115966900521315099289996977 := advanceCheckpoint c1600 8 (by decide +kernel)
private def c1616 : Checkpoint 3625161748502490 298942881897996786208393293645835088333844 2802151808806241332245071883452462697496440776287 := advanceCheckpoint c1608 8 (by decide +kernel)
private def c1624 : Checkpoint 3625170232071385 6856504104732150664738301746052247466757301 2802151808797868787699285437505830897252566496470 := advanceCheckpoint c1616 8 (by decide +kernel)
private def c1632 : Checkpoint 3625364813550553 157258326925161747334354844620963627478353641 2802151804393544639281036022032341440118721281323 := advanceCheckpoint c1624 8 (by decide +kernel)
private def c1640 : Checkpoint 3629829641495635 3606131750971435444309519230562338572068859656 2802149488412417672463377288511855807892139975501 := advanceCheckpoint c1632 8 (by decide +kernel)
private def c1648 : Checkpoint 3733253731658934 82319204560803044949935546720508328694055393144 2800942396436716470561194398672927558420034129902 := advanceCheckpoint c1640 8 (by decide +kernel)
private def c1656 : Checkpoint 6155683316515354 1415316436224694579372561804233507438900925713851 2418456976038319019695384831994915853242704583991 := advanceCheckpoint c1648 8 (by decide +kernel)
private def c1664 : Checkpoint 15487032735582260 2782436888616507682609610522397866394455485054576 331812779232911890133047603543480916562993245395 := advanceCheckpoint c1656 8 (by decide +kernel)
private def c1672 : Checkpoint 17426931352919127 2802151164109606709142944957014900205545287573753 1900809132219581227794234991458751293302222118 := advanceCheckpoint c1664 8 (by decide +kernel)
private def c1680 : Checkpoint 17438692816509854 2802151808787435867428226825592688951412451438610 10270473069503222225651330493367306007420837 := advanceCheckpoint c1672 8 (by decide +kernel)
private def c1688 : Checkpoint 17438756387838636 2802151808806257035345010006101911630034147328882 55476388364914755034972821809718347432604 := advanceCheckpoint c1680 8 (by decide +kernel)
private def c1696 : Checkpoint 17438756731222451 2802151808806257584483688115320533644895413753449 299657441907573580175959738127238669357 := advanceCheckpoint c1688 8 (by decide +kernel)
private def c1704 : Checkpoint 17438756733077250 2802151808806257584499710090024687454510160899842 1618513292890251615861587290278539509 := advanceCheckpoint c1696 8 (by decide +kernel)
private def c1712 : Checkpoint 17438756733087269 2802151808806257584499710557481495761311667948637 8607300040969756902885492083595284 := advanceCheckpoint c1704 8 (by decide +kernel)
private def c1720 : Checkpoint 17438756733087325 2802151808806257584499710557494945885547315237300 (-391076603359391842220491232780130) := advanceCheckpoint c1712 8 (by decide +kernel)
private def c1728 : Checkpoint 17438756733087410 2802151808806257584499710557460144779502292416520 (-14049326867073223113854598921895726) := advanceCheckpoint c1720 8 (by decide +kernel)
private def c1736 : Checkpoint 17438756733089349 2802151808806257584499710538585416000816366041331 (-325618118176950657973818924575303190) := advanceCheckpoint c1728 8 (by decide +kernel)
private def c1744 : Checkpoint 17438756733133831 2802151808806257584499700592324853769751617938959 (-7473221509114300757971893355286743886) := advanceCheckpoint c1736 8 (by decide +kernel)
private def c1752 : Checkpoint 17438756734154058 2802151808806257584494467994461856524170261653870 (-171408700230917072798213434960531819054) := advanceCheckpoint c1744 8 (by decide +kernel)
private def c1760 : Checkpoint 17438756757553818 2802151808806257581741838348689737167654530093693 (-3931406087958771833555752807594161651766) := advanceCheckpoint c1752 8 (by decide +kernel)
private def c1768 : Checkpoint 17438757294247027 2802151808806256133713008326108685659205775424185 (-90170112444138040577191022200898593338063) := advanceCheckpoint c1760 8 (by decide +kernel)
private def c1776 : Checkpoint 17438769603760699 2802151808805494394197461863869558726810881388553 (-2068127213725228656367599900913233476719141) := advanceCheckpoint c1768 8 (by decide +kernel)
private def c1784 : Checkpoint 17439051934433028 2802151808404781259970132784082253269897436880630 (-47434114493614482767089117052148569424562396) := advanceCheckpoint c1776 8 (by decide +kernel)
private def c1792 : Checkpoint 17445528274246459 2802151597633907078541933209872378998167500139318 (-1087875876783142192091138486569198564002238059) := advanceCheckpoint c1784 8 (by decide +kernel)
private def c1800 : Checkpoint 17594514757750699 2802041028135779402544606273996418981691682942222 (-24916585640200935889009493864703850945204821173) := advanceCheckpoint c1792 8 (by decide +kernel)
private def c1808 : Checkpoint 21246049225632794 2747691792105306798977800745299791121175784710500 (-549767746592421264768398840425440667984166649369) := advanceCheckpoint c1800 8 (by decide +kernel)
private def c1816 : Checkpoint 53012669275512608 1241399331370090237305700489224765289532059444732 (-2512166885314364292482022595925660365197376465591) := advanceCheckpoint c1808 8 (by decide +kernel)
private def c1824 : Checkpoint 83473835269545814 13893633278293188421100334839219821641192299012 (-2802117364877943477243101002888578209407356778344) := advanceCheckpoint c1816 8 (by decide +kernel)
private def c1832 : Checkpoint 83886493024747427 75218046480960869663035780282969126295873119 (-2802151807796720174180006871959337074572855901198) := advanceCheckpoint c1824 8 (by decide +kernel)
private def c1840 : Checkpoint 83888732653234380 406297725757183645567119817836073586977125 (-2802151808806228192591379854698481198227941028492) := advanceCheckpoint c1832 8 (by decide +kernel)
private def c1848 : Checkpoint 83888744750972574 2194630547199683180987756830399549560852 (-2802151808806257647281351852099337363526687347557) := advanceCheckpoint c1840 8 (by decide +kernel)
private def c1856 : Checkpoint 83888744816318911 11854336926586293609324962684608220386 (-2802151808806257648140738337009567065763270343365) := advanceCheckpoint c1848 8 (by decide +kernel)
private def c1864 : Checkpoint 83888744816671882 63979015405973579016417912297179964 (-2802151808806257648140763410883874764647209234428) := advanceCheckpoint c1856 8 (by decide +kernel)
private def c1872 : Checkpoint 83888744816673788 312532384246136516032681981329653 (-2802151808806257648140763411614624502523923566345) := advanceCheckpoint c1864 8 (by decide +kernel)
private def c1880 : Checkpoint 83888744816673805 (-255321871456567637829207684051291) (-2802151808806257648140763411614633683928273409460) := advanceCheckpoint c1872 8 (by decide +kernel)
private def c1888 : Checkpoint 83888744816673993 (-6535121875698229431052730548468803) (-2802151808806257648140763411607062205613530714386) := advanceCheckpoint c1880 8 (by decide +kernel)
private def c1896 : Checkpoint 83888744816678302 (-150469474100573736757184475167146294) (-2802151808806257648140763407575598442580373171783) := advanceCheckpoint c1888 8 (by decide +kernel)
private def c1904 : Checkpoint 83888744816777139 (-3451940713562461565433409255043244910) (-2802151808806257648140761285430875543980818835370) := advanceCheckpoint c1896 8 (by decide +kernel)
private def c1912 : Checkpoint 83888744819044045 (-79173835969975146510629987210833889874) (-2802151808806257648139644897328971998132135874435) := advanceCheckpoint c1904 8 (by decide +kernel)
private def c1920 : Checkpoint 83888744871037434 (-1815918965503646434704915933966391296635) (-2802151808806257647552365306584221482592829514588) := advanceCheckpoint c1912 8 (by decide +kernel)
private def c1928 : Checkpoint 83888746063549603 (-41649631017970137101147467590915777814026) (-2802151808806257338612250878807891119119242114893) := advanceCheckpoint c1920 8 (by decide +kernel)
private def c1936 : Checkpoint 83888773414823387 (-955269304801135497096877599724014142817936) (-2802151808806094819802592091703933181769507237618) := advanceCheckpoint c1928 8 (by decide +kernel)
private def c1944 : Checkpoint 83889400740970730 (-21909879251215396087290014134750682536524116) (-2802151808720601544980894519183051371657479296317) := advanceCheckpoint c1936 8 (by decide +kernel)
private def c1952 : Checkpoint 83903789864799639 (-502507561334051475685888151982790562493862169) (-2802151763749125048391084817714599695787048109164) := advanceCheckpoint c1944 8 (by decide +kernel)
private def c1960 : Checkpoint 84234274450686020 (-11518055408691002408813073248233959781777249346) (-2802128136612561092657180970137056821124801195607) := advanceCheckpoint c1952 8 (by decide +kernel)
private def c1968 : Checkpoint 92055082199144942 (-259933519332587626974117791819488265884288706852) (-2790069770655127688761374331233858521312152883820) := advanceCheckpoint c1960 8 (by decide +kernel)
private def c1976 : Checkpoint 202089725994904431 (-2158334673261764124174190773317844047550905995873) (-1787077557855902199322719564916248561134242347306) := advanceCheckpoint c1968 8 (by decide +kernel)
private def c1984 : Checkpoint 396381023323857365 (-2801702307392103844568346420339578020534717977336) (-50189046115092189200380805449623193954169616352) := advanceCheckpoint c1976 8 (by decide +kernel)
private def c1992 : Checkpoint 403505544427871936 (-2802151795472840592638418873117060508937708711383) (-273357855814771506962459341473674145726151723) := advanceCheckpoint c1984 8 (by decide +kernel)
private def c2000 : Checkpoint 403544696806875029 (-2802151808805868603445641927600677096123648943869) (-1476617328690118559710655235828255703086444) := advanceCheckpoint c1992 8 (by decide +kernel)
private def c2008 : Checkpoint 403544908309540129 (-2802151808806257650019063186677604157756235874315) (-7975998606802527464292061758788064780346) := advanceCheckpoint c2000 8 (by decide +kernel)
private def c2016 : Checkpoint 403544909451979255 (-2802151808806257661370107323482837287512093604734) (-43082609297368883062397016464708968276) := advanceCheckpoint c2008 8 (by decide +kernel)
private def c2024 : Checkpoint 403544909458150177 (-2802151808806257661370438507782592141711060179024) (-232706252741822337506689669455182083) := advanceCheckpoint c2016 8 (by decide +kernel)
private def c2032 : Checkpoint 403544909458183510 (-2802151808806257661370438517445211351947923713888) (-1247190680176755833705319042989397) := advanceCheckpoint c2024 8 (by decide +kernel)
private def c2040 : Checkpoint 403544909458183690 (-2802151808806257661370438517445490451092640504910) 2700753870418880028552237118949 := advanceCheckpoint c2032 8 (by decide +kernel)
private def c2048 : Checkpoint 403544909458183729 (-2802151808806257661370438517445477439614410014116) 273510564580639994521264762013586 := advanceCheckpoint c2040 8 (by decide +kernel)
private def c2056 : Checkpoint 403544909458184606 (-2802151808806257661370438517438273337467898027302) 6363259384910477119167202672401275 := advanceCheckpoint c2048 8 (by decide +kernel)
private def c2064 : Checkpoint 403544909458204740 (-2802151808806257661370438513633274138218276703206) 146170560124383394714054534173154819 := advanceCheckpoint c2056 8 (by decide +kernel)
private def c2072 : Checkpoint 403544909458666522 (-2802151808806257661370436511727781799523383451515) 3352711483440005404635565916565307628 := advanceCheckpoint c2064 8 (by decide +kernel)
private def c2080 : Checkpoint 403544909469257880 (-2802151808806257661369383397458657359712945003244) 76897420588648076278069537026477663771 := advanceCheckpoint c2072 8 (by decide +kernel)
private def c2088 : Checkpoint 403544909712179594 (-2802151808806257660815389493472923814749395282501) 1763707250438307341606389830089141718701 := advanceCheckpoint c2080 8 (by decide +kernel)
private def c2096 : Checkpoint 403544915283793664 (-2802151808806257369385317192738890632956157757186) 40452110847395532918551804636552770465886 := advanceCheckpoint c2088 8 (by decide +kernel)
private def c2104 : Checkpoint 403545043073467657 (-2802151808806104061782051628343594275458418164386) 927803173559378818469677770377802278854428 := advanceCheckpoint c2096 8 (by decide +kernel)
private def c2112 : Checkpoint 403547974044741933 (-2802151808725456350916165853070339089695701502520) 21279921909638934548631719489697394638745821 := advanceCheckpoint c2104 8 (by decide +kernel)
private def c2120 : Checkpoint 403615202288658999 (-2802151766302792722168140259510371234247692224593) 488059750966310482178767423483055065011170198 := advanceCheckpoint c2112 8 (by decide +kernel)
private def c2128 : Checkpoint 405159216609647842 (-2802129477441982800253337070147648090693014055386) 11187101809762738747423896365459274547961477477 := advanceCheckpoint c2120 8 (by decide +kernel)
private def c2136 : Checkpoint 441665507927018057 (-2790743901827673089418694937049446496314389018277) 252593020504994434924120145570776493305423845838 := advanceCheckpoint c2128 8 (by decide +kernel)
private def c2144 : Checkpoint 964471787346721349 (-1804131492743266843945050894949058444839633736643) 2144099884913977905281036680652677379483299819616 := advanceCheckpoint c2136 8 (by decide +kernel)
private def c2152 : Checkpoint 1905418285919159444 (-52193425402429999471458673611365167709774877741) 2801665684185203168917122471638450927551986685417 := advanceCheckpoint c2144 8 (by decide +kernel)
private def c2160 : Checkpoint 1941046666230615044 (-284370320142394207594692000630751382904801322) 2802151794376903956024357899888658510416109090165 := advanceCheckpoint c2152 8 (by decide +kernel)
private def c2168 : Checkpoint 1941242594985465346 (-1536106935120365652614240759089652988401538) 2802151808805836626168870880389372439006427253737 := advanceCheckpoint c2160 8 (by decide +kernel)
private def c2176 : Checkpoint 1941243653404168531 (-8297333819492104455119177701909168684118) 2802151808806257651836174741798034793228874560216 := advanceCheckpoint c2168 8 (by decide +kernel)
private def c2184 : Checkpoint 1941243659121254706 (-44818317538305810106401213301811143118) 2802151808806257664120259355996881179294752993675 := advanceCheckpoint c2176 8 (by decide +kernel)
private def c2192 : Checkpoint 1941243659152135733 (-242086595546283493481303076364732056) 2802151808806257664120617763246459384856727403463 := advanceCheckpoint c2184 8 (by decide +kernel)
private def c2200 : Checkpoint 1941243659152302538 (-1306449136400763859892992221679115) 2802151808806257664120617773703523186979371450797 := advanceCheckpoint c2192 8 (by decide +kernel)
private def c2208 : Checkpoint 1941243659152303439 (-5871144642153695747583971502331) 2802151808806257664120617773703828069147467835646 := advanceCheckpoint c2200 8 (by decide +kernel)
private def c2216 : Checkpoint 1941243659152303451 11450648810791163630485769860130 2802151808806257664120617773703828056363844219744 := advanceCheckpoint c2208 8 (by decide +kernel)
private def c2224 : Checkpoint 1941243659152303639 282825412906927279907483488103149 2802151808806257664120617773703813876658844468421 := advanceCheckpoint c2216 8 (by decide +kernel)
private def c2232 : Checkpoint 1941243659152307948 6502792745301869676719334896990471 2802151808806257664120617773696284422914445720510 := advanceCheckpoint c2224 8 (by decide +kernel)
private def c2240 : Checkpoint 1941243659152406792 149182405417204712936277792373725998 2802151808806257664120617769732741522204736615277 := advanceCheckpoint c2232 8 (by decide +kernel)
private def c2248 : Checkpoint 1941243659154673851 3421643050718429638947353467863234635 2802151808806257664120615684659938546351132604269 := advanceCheckpoint c2240 8 (by decide +kernel)
private def c2256 : Checkpoint 1941243659206670761 78478287650568494158886685892516960404 2802151808806257664119518825120826958665743635681 := advanceCheckpoint c2248 8 (by decide +kernel)
private def c2264 : Checkpoint 1941243660399263671 1799965625445767215196325824474518803602 2802151808806257663542512718865923075366939613317 := advanceCheckpoint c2256 8 (by decide +kernel)
private def c2272 : Checkpoint 1941243687752386319 41283727055387073333264672708432025254457 2802151808806257360006808848738154377108854456022 := advanceCheckpoint c2264 8 (by decide +kernel)
private def c2280 : Checkpoint 1941244315119355718 946876989307001581160241640087546280920951 2802151808806097684202673981075812381631466876370 := advanceCheckpoint c2272 8 (by decide +kernel)
private def c2288 : Checkpoint 1941258704346631547 21717394892778985328786799324583128479027571 2802151808722099975116452236322103047167844318110 := advanceCheckpoint c2280 8 (by decide +kernel)
private def c2296 : Checkpoint 1941588753179943270 498093014852619537512487174095852291788287662 2802151764537304671455528360951687085029838926051 := advanceCheckpoint c2288 8 (by decide +kernel)
private def c2304 : Checkpoint 1949169112178812941 11416933429398543583137728843458899819686433570 2802128550446472698216663940878635263496354903281 := advanceCheckpoint c2296 8 (by decide +kernel)
private def c2312 : Checkpoint 2128507343479785561 257691514995576754508430312514727433439936037657 2790277735763138337292843800308073069301750101702 := advanceCheckpoint c2304 8 (by decide +kernel)
private def c2320 : Checkpoint 4665194364238819686 2154004232529264206078742770558955081239079182309 1792294765333592415698379333015729979875910099441 := advanceCheckpoint c2312 8 (by decide +kernel)
private def c2328 : Checkpoint 9170534044721805113 2801691310753782004219320637462292415532597550487 50799201203724926466612512715902942939889821063 := advanceCheckpoint c2320 8 (by decide +kernel)
private def c2336 : Checkpoint 9337386611199165222 2802151795143885442061812022688279497073712739175 276709381636756980863463340309694646391147780 := advanceCheckpoint c2328 8 (by decide +kernel)
private def c2344 : Checkpoint 9338303732060215021 2802151808805859007695475415060448571646267716549 1494722331947891600862855867925620960856698 := advanceCheckpoint c2336 8 (by decide +kernel)
private def c2352 : Checkpoint 9338308686388254845 2802151808806257653060880478572353422301821381247 8073793426114399667844561455845393337591 := advanceCheckpoint c2344 8 (by decide +kernel)
private def c2360 : Checkpoint 9338308713149233140 2802151808806257664691984506943061284418570628959 43610858192193462758748721510919384195 := advanceCheckpoint c2352 8 (by decide +kernel)
private def c2368 : Checkpoint 9338308713293783437 2802151808806257664692323862481958302359949414900 235565230573446335439533779725884793 := advanceCheckpoint c2360 8 (by decide +kernel)
private def c2376 : Checkpoint 9338308713294564231 2802151808806257664692323872383176041524948275954 1271914023487233255528423809809906 := advanceCheckpoint c2368 8 (by decide +kernel)
private def c2384 : Checkpoint 9338308713294568448 2802151808806257664692323872383464766519067120694 6516343828916201466164638418747 := advanceCheckpoint c2376 8 (by decide +kernel)
private def c2392 : Checkpoint 9338308713294568474 2802151808806257664692323872383464774218748067622 (-1285491521123218958601414680479) := advanceCheckpoint c2384 8 (by decide +kernel)
private def c2400 : Checkpoint 9338308713294568598 2802151808806257664692323872383464512100697995104 (-38494244729003531454799908718895) := advanceCheckpoint c2392 8 (by decide +kernel)
private def c2408 : Checkpoint 9338308713294571440 2802151808806257664692323872383323072792814086776 (-891294862606389267911747011610909) := advanceCheckpoint c2400 8 (by decide +kernel)
private def c2416 : Checkpoint 9338308713294636619 2802151808806257664692323872308847147778691890547 (-20449595873383983382908620216518646) := advanceCheckpoint c2408 8 (by decide +kernel)
private def c2424 : Checkpoint 9338308713296131550 2802151808806257664692323833129140809018442763015 (-469034423629874834580625578202625847) := advanceCheckpoint c2416 8 (by decide +kernel)
private def c2432 : Checkpoint 9338308713330419057 2802151808806257664692303222493265798551670859973 (-10757706891967882576632722058355143289) := advanceCheckpoint c2424 8 (by decide +kernel)
private def c2440 : Checkpoint 9338308714116831906 2802151808806257664681460937727389668711039791612 (-246737074767795323675270276773667055517) := advanceCheckpoint c2432 8 (by decide +kernel)
private def c2448 : Checkpoint 9338308732153872716 2802151808806257658977846167089255104656524025369 (-5659122553739629051935224613130881891119) := advanceCheckpoint c2440 8 (by decide +kernel)
private def c2456 : Checkpoint 9338309145848596442 2802151808806254658575106632341760520919359412698 (-129796739541425201797041648947459788976026) := advanceCheckpoint c2448 8 (by decide +kernel)
private def c2464 : Checkpoint 9338318634288795935 2802151808804676288695565917543751867091474416061 (-2976997013675794096024846053867966913162303) := advanceCheckpoint c2456 8 (by decide +kernel)
private def c2472 : Checkpoint 9338536261442478851 2802151807974376602767931733114460317137773414772 (-68279675190163332649191712473006885692333794) := advanceCheckpoint c2464 8 (by decide +kernel)
private def c2480 : Checkpoint 9343528664510204134 2802151371268657298118894415382906322520723514238 (-1565916142434432923495194281966528185549490077) := advanceCheckpoint c2472 8 (by decide +kernel)
private def c2488 : Checkpoint 9458528702854120053 2801922557732177298062856498575607708508847013874 (-35843270885274776444641518552855931902863775534) := advanceCheckpoint c2480 8 (by decide +kernel)
private def c2496 : Checkpoint 12355756314517236938 2693025637801587217417419334935893320064853050605 (-774382123850709758416548384593189899441663084398) := advanceCheckpoint c2488 8 (by decide +kernel)
private def c2500 : Checkpoint 18446744073709551616 2177532263584960038760393755571963048631937253949 (-1763634883030708748022660623644637926311502014844) := advanceCheckpoint c2496 4 (by decide +kernel)

theorem reached_18446744073709551616 : Reach 18446744073709551616 (2177532263584960038760393755571963048631937253949,(-1763634883030708748022660623644637926311502014844)) := c2500.reached

/-- Every requested integer is in one of the certified half-open blocks. -/
theorem cover (Q : ℕ → ℤ × ℤ → Prop) (P : ℕ → Prop)
    (initial : Q 8 start)
    (advance : ∀ n z h, 8≤n → Q n z → Admissible n h z → Q (n+h) (jump n h z))
    (inside : ∀ n z h k, lower≤n → Q n z → Admissible n h z → n≤k → k<n+h → P k) :
    ∀ k, lower≤k → k≤upper → P k := by
  intro k lo hi
  apply (path_induction Q P initial advance inside reached_18446744073709551616).2.2 k lo
  change k≤18446744073709551615 at hi
  omega

end ArctanBlocks.Range

namespace ArctanBlocks

open Arxiv.«2607.05739»

/-- At the eighth step the unit rotation is one. Both integer divisions in the
starting pair can therefore be checked against the exact Gaussian product. -/
lemma accurate_start : Accurate 8 Range.start := by
  have product : gaussProd 8 = (⟨-55900,-46800⟩ : GaussianInt) := by decide +kernel
  have unit : Complex.I^8=1 := by rw [show 8=4*2 by decide,pow_mul,Complex.I_pow_four,one_pow]
  have rot : rotated 8 = (gaussProd 8:ℂ)/(Nat.factorial 8:ℂ) := by
    simpa only [unit,one_mul] using (gauss_div_factorial 8).symm
  unfold Accurate
  rw [rot]
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  norm_num [Range.start,A,B,product,lift,scale,Nat.factorial,Complex.mul_re,Complex.mul_im]

end ArctanBlocks

namespace ArctanBlocks

open Arxiv.«2607.05739»

private lemma guarded_coord {n h t : ℕ} {z : ℤ × ℤ} (hok : clear n h z=true) (ht : t<h)
    (x : ℤ) (hx : min z.1.natAbs z.2.natAbs ≤ x.natAbs) :
    4*(n : ℝ)+1+3*(scale : ℝ)*(t : ℝ)/((n : ℝ)+1) ≤ |(x : ℝ)| := by
  have hg : (4*n+1)*(n+1)+3*scale*(h-1) ≤ min z.1.natAbs z.2.natAbs*(n+1) := of_decide_eq_true hok
  have hb : (4*n+1)*(n+1)+3*scale*t ≤ x.natAbs*(n+1) :=
    (Nat.add_le_add_left (Nat.mul_le_mul_left (3*scale) (show t ≤ h-1 by omega)) _).trans
      (hg.trans (Nat.mul_le_mul_right (n+1) hx))
  have hbr : (4*(n : ℝ)+1)*((n : ℝ)+1)+3*(scale : ℝ)*(t : ℝ) ≤
      (x.natAbs : ℝ)*((n : ℝ)+1) := by exact_mod_cast hb
  rw [Nat.cast_natAbs,Int.cast_abs] at hbr
  have hd : 3*(scale : ℝ)*(t : ℝ)/((n : ℝ)+1) ≤ |(x : ℝ)|-(4*(n : ℝ)+1) := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ)+1)).mpr
    nlinarith only [hbr]
  linarith

private lemma within_block {n t : ℕ} {z : ℤ × ℤ} (ht : 8*t≤n+1) (hz : Accurate n z) :
    ‖(scale : ℂ)*rotated (n+t)-lift z‖ ≤ 4*(n : ℝ)+3*(scale : ℝ)*(t : ℝ)/((n : ℝ)+1) := by
  have he : (scale : ℂ)*rotated (n+t)-(scale : ℂ)*rotated n =
      ((scale : ℂ)*rotated n)*(ratio n t-1) := by rw [rotated_add]; ring
  have drift : ‖(scale : ℂ)*rotated (n+t)-(scale : ℂ)*rotated n‖ ≤
      3*(scale : ℝ)*(t : ℝ)/((n : ℝ)+1) := by
    rw [he,norm_mul,norm_mul,Complex.norm_natCast]
    calc
      _ ≤ (scale : ℝ)*2*(3*(t : ℝ)/(2*((n : ℝ)+1))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (norm_rotated_le n) (by positivity))
          (ratio_variation n t ht) (norm_nonneg _) (by positivity)
      _ = _ := by field_simp
  calc
    _ = ‖((scale : ℂ)*rotated (n+t)-(scale : ℂ)*rotated n) + ((scale : ℂ)*rotated n-lift z)‖ := by rw [sub_add_sub_cancel]
    _ ≤ _ := (norm_add_le _ _).trans (by linarith only [drift,show ‖(scale : ℂ)*rotated n-lift z‖ ≤ 4*(n : ℝ) from hz])

/-- Every index in a checked half-open block is excluded by the signed CRT bound. -/
lemma exclude_in_block {n h k : ℕ} {z : ℤ × ℤ} (hn : lower≤n) (hd : 8*h≤n+1) (hu : n+h≤upper+1)
    (hok : clear n h z=true) (hz : Accurate n z) (hlo : n≤k) (hhi : k<n+h) : ¬IsIntegerValue k := by
  let t := k-n
  have he : n+t=k := by dsimp only [t]; omega
  have ht : t<h := by omega
  have hstep : 8*t ≤ n+1 := by omega
  let loss := 4*(n : ℝ)+3*(scale : ℝ)*(t : ℝ)/((n : ℝ)+1)
  have near : ‖(scale : ℂ)*rotated k-lift z‖ ≤ loss := he ▸ within_block hstep hz
  have lower_bound (x : ℤ) (y : ℝ) (hy : |(scale : ℝ)*y-x|≤loss)
      (hx : min z.1.natAbs z.2.natAbs ≤ x.natAbs) : 1≤(scale : ℝ)*|y| := by
    have hg := guarded_coord hok ht x hx
    have ht' : |(x : ℝ)| ≤ |(scale : ℝ)*y| + |(scale : ℝ)*y-x| := by
      calc
        |(x : ℝ)| = |(scale : ℝ)*y-((scale : ℝ)*y-x)| := by congr 1; ring
        _ ≤ _ := abs_sub _ _
    have hs : |(scale : ℝ)| = (scale : ℝ) := abs_of_nonneg (Nat.cast_nonneg scale)
    rw [abs_mul (scale : ℝ) y,hs] at ht'
    dsimp only [loss] at hy
    linarith
  have hreal : 1 ≤ (scale : ℝ)*|(rotated k).re| := by
    apply lower_bound z.1 _ _ (min_le_left _ _)
    simpa only [Complex.sub_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,lift] using
      (Complex.abs_re_le_norm ((scale : ℂ)*rotated k-lift z)).trans near
  have him : 1 ≤ (scale : ℝ)*|(rotated k).im| := by
    apply lower_bound z.2 _ _ (min_le_right _ _)
    simpa only [Complex.sub_im,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero,lift] using
      (Complex.abs_im_le_norm ((scale : ℂ)*rotated k-lift z)).trans near
  have hA : 1 ≤ (scale : ℝ)*|(A k : ℝ)/(k.factorial : ℝ)| := by
    rcases abs_A_div_factorial k with h|h
    · rwa [h]
    · rwa [h]
  have hp : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [abs_div,abs_of_nonneg hp.le,← mul_div_assoc] at hA
  have hA' : (k.factorial : ℝ) ≤ (scale : ℝ)*|(A k : ℝ)| := by simpa only [one_mul] using (le_div_iff₀ hp).mp hA
  have ha : 0 < |(A k : ℝ)| := by
    apply abs_pos.mpr
    intro h
    simp [h] at hA'
    exact Nat.factorial_ne_zero k hA'
  intro hv
  have h₁ : 1000000 ≤ k := by change 1000000≤n at hn; omega
  have h₂ : k ≤ 18446744073709551615 := by change n+h≤18446744073709551615+1 at hu; omega
  have hcrt : (10 : ℝ)^119*|(A k : ℝ)| ≤ 2*(k.factorial : ℝ) := by exact_mod_cast ArctanWordCRT.whole_barrier h₁ h₂ hv
  have hc : 2*(scale : ℝ) < (10 : ℝ)^119 := by norm_num [scale]
  nlinarith only [hcrt,hA',mul_lt_mul_of_pos_right hc ha]

end ArctanBlocks

namespace ArctanBlocks

/-- The certified jumps exclude integral values between one million and
the largest unsigned 64-bit index, including both endpoints. -/
theorem word_range (n : ℕ) (lo : 1000000 ≤ n) (hi : n ≤ 18446744073709551615) :
    ¬ Arxiv.«2607.05739».IsIntegerValue n := by
  apply Range.cover Accurate (fun k => ¬ Arxiv.«2607.05739».IsIntegerValue k)
    accurate_start _ _ n lo hi
  · intro k z h hk hz valid
    exact accurate_jump hk valid.pos valid.small valid.stop hz
  · intro k z h j hk hz valid floor ceiling
    exact exclude_in_block hk valid.small valid.stop (valid.late hk) hz floor ceiling

end ArctanBlocks

namespace ArctanCert

/-- Integer arithmetic for the scaled complex product divided by the factorial. -/
def step (k : ℕ) (z : ℤ × ℤ) : ℤ × ℤ :=
  (z.1 / (k : ℤ) - z.2, z.1 + z.2 / (k : ℤ))

def trajectory (S : ℤ) : ℕ → ℤ × ℤ
  | 0 => (S,0)
  | n+1 => step (n+1) (trajectory S n)

/-- The entire error rectangle lies strictly between two consecutive integral slopes. -/
def separated (n : ℕ) (w : ℤ × ℤ) : Bool :=
  let u := if w.1 < 0 then -w.1 else w.1
  let v := if w.1 < 0 then -w.2 else w.2
  let q := v/u
  let e : ℤ := 4*(n : ℤ)
  decide (e < u ∧ e*(1+|q|) < v-q*u ∧ e*(1+|q+1|) < (q+1)*u-v)

end ArctanCert

namespace ArctanCert

open Arxiv.«2607.05739»

/-- Euclidean division by a positive integer changes the real quotient by at most one. -/
private lemma division_error (a : ℤ) (k : ℕ) (hk : 0 < k) :
    |(a : ℝ)/(k : ℝ) - ((a/(k : ℤ) : ℤ) : ℝ)| ≤ 1 := by
  have hki : 0 < (k : ℤ) := by exact_mod_cast hk
  have hkr : 0 < (k : ℝ) := by exact_mod_cast hk
  have h₀ : 0 ≤ a%(k : ℤ) := Int.emod_nonneg _ (ne_of_gt hki)
  have h₁ : a%(k : ℤ) < k := Int.emod_lt_of_pos _ hki
  have he : (k : ℝ)*((a/(k : ℤ) : ℤ) : ℝ) + ((a%(k : ℤ) : ℤ) : ℝ) = (a : ℝ) := by
    exact_mod_cast Int.mul_ediv_add_emod a (k : ℤ)
  have h : (a : ℝ)/k - ((a/(k : ℤ) : ℤ) : ℝ) = ((a%(k : ℤ) : ℤ) : ℝ)/k := by
    field_simp
    linarith [he]
  rw [h,abs_of_nonneg (div_nonneg (by exact_mod_cast h₀) hkr.le)]
  exact (div_le_one hkr).mpr (by exact_mod_cast h₁.le)

private lemma round_step (k : ℕ) (hk : 0 < k) (z : ℤ × ℤ) :
    ‖(⟨(z.1 : ℝ),(z.2 : ℝ)⟩ : ℂ) * (⟨1/(k : ℝ),1⟩ : ℂ) -
      (⟨((step k z).1 : ℝ),((step k z).2 : ℝ)⟩ : ℂ)‖ ≤ 2 := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  have hre : ((⟨(z.1 : ℝ),(z.2 : ℝ)⟩ : ℂ) * (⟨1/(k : ℝ),1⟩ : ℂ) -
      (⟨((step k z).1 : ℝ),((step k z).2 : ℝ)⟩ : ℂ)).re =
      (z.1 : ℝ)/k - ((z.1/(k : ℤ) : ℤ) : ℝ) := by
    simp [Complex.sub_re,Complex.mul_re,step,div_eq_mul_inv]
  have him : ((⟨(z.1 : ℝ),(z.2 : ℝ)⟩ : ℂ) * (⟨1/(k : ℝ),1⟩ : ℂ) -
      (⟨((step k z).1 : ℝ),((step k z).2 : ℝ)⟩ : ℂ)).im =
      (z.2 : ℝ)/k - ((z.2/(k : ℤ) : ℤ) : ℝ) := by
    simp [Complex.sub_im,Complex.mul_im,step,div_eq_mul_inv]
  rw [hre,him]
  linarith [division_error z.1 k hk,division_error z.2 k hk]

private lemma step_norm_budget (n : ℕ) :
    4*(n : ℝ)*‖(⟨1/((n : ℝ)+1),1⟩ : ℂ)‖+2 ≤ 4*((n : ℝ)+1) := by
  let u : ℝ := 1/((n : ℝ)+1)
  have hpos : 0 < (n : ℝ)+1 := by positivity
  have hu : 0 ≤ u := div_nonneg zero_le_one hpos.le
  have hu₁ : u ≤ 1 := (div_le_one hpos).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
  have hu₂ : ((n : ℝ)+1)*u=1 := by dsimp [u]; field_simp
  have hn : ‖(⟨u,1⟩ : ℂ)‖ ≤ 1+u/2 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [Complex.sq_norm,Complex.normSq_apply]
    change u*u+1*1 ≤ (1+u/2)^2
    nlinarith [mul_le_mul_of_nonneg_left hu₁ hu,sq_nonneg u]
  have hmul := mul_le_mul_of_nonneg_left hn (show 0 ≤ 4*(n : ℝ) by positivity)
  change 4*(n : ℝ)*‖(⟨u,1⟩ : ℂ)‖+2 ≤ _
  nlinarith [hmul,hu₂]

private lemma gauss_components (n : ℕ) :
    A (n+1) = A n - B n*((n:ℤ)+1) ∧ B (n+1) = A n*((n:ℤ)+1)+B n := by
  have hg : gaussProd (n+1) = gaussProd n * (⟨1,(n:ℤ)+1⟩ : GaussianInt) := by
    unfold gaussProd
    rw [Finset.prod_Icc_succ_top (by omega)]
    push_cast
    rfl
  simp only [A,B,hg,Zsqrtd.re_mul,Zsqrtd.im_mul]
  constructor <;> ring

/-- The fixed-point recurrence stays within four times the step count in each real coordinate. -/
lemma error_bounds (S : ℤ) (n : ℕ) :
    |(S : ℝ)*(A n : ℝ)/(n.factorial : ℝ) - ((trajectory S n).1 : ℝ)| ≤ 4*(n : ℝ) ∧
    |(S : ℝ)*(B n : ℝ)/(n.factorial : ℝ) - ((trajectory S n).2 : ℝ)| ≤ 4*(n : ℝ) := by
  let p (t : ℕ) : ℂ := ⟨(S : ℝ)*(A t : ℝ)/(t.factorial : ℝ),(S : ℝ)*(B t : ℝ)/(t.factorial : ℝ)⟩
  let z (t : ℕ) : ℂ := ⟨((trajectory S t).1 : ℝ),((trajectory S t).2 : ℝ)⟩
  let f (t : ℕ) : ℂ := ⟨1/((t : ℝ)+1),1⟩
  have hp (t : ℕ) : p (t+1)=p t*f t := by
    obtain ⟨ha,hb⟩ := gauss_components t
    have hfact : (t.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero t
    have ht : (t : ℝ)+1 ≠ 0 := by positivity
    apply Complex.ext <;> simp only [p,f,Complex.mul_re,Complex.mul_im,ha,hb,Nat.factorial_succ,
      Nat.cast_mul,Nat.cast_succ,Int.cast_natCast,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_one,mul_one] <;>
      field_simp
  have err (t : ℕ) : ‖p t-z t‖ ≤ 4*(t : ℝ) := by
    induction t with
    | zero =>
      have hg : gaussProd 0=1 := by simp [gaussProd]
      simp [p,z,trajectory,A,B,hg]
    | succ t ih =>
      have local_err : ‖z t*f t-z (t+1)‖ ≤ 2 := by
        simpa only [z,f,trajectory,Nat.cast_succ] using round_step (t+1) (by omega) (trajectory S t)
      rw [hp]
      calc
        ‖p t*f t-z (t+1)‖ = ‖(p t-z t)*f t + (z t*f t-z (t+1))‖ := by ring_nf
        _ ≤ ‖(p t-z t)*f t‖ + ‖z t*f t-z (t+1)‖ := norm_add_le _ _
        _ ≤ 4*(t : ℝ)*‖f t‖+2 := by rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_right ih (norm_nonneg _)) local_err
        _ ≤ 4*((t+1 : ℕ) : ℝ) := by simpa only [Nat.cast_succ,f] using step_norm_budget t
  exact ⟨(Complex.abs_re_le_norm (p n-z n)).trans (err n),(Complex.abs_im_le_norm (p n-z n)).trans (err n)⟩

end ArctanCert

namespace ArctanCert

/-- Every point in the certified error rectangle has slope strictly between the integers `q` and `q+1`. -/
private lemma excludes_integer (u v q e : ℤ) (x y : ℝ)
    (box : e<u ∧ e*(1+|q|)<v-q*u ∧ e*(1+|q+1|)<(q+1)*u-v)
    (hx : |x-(u:ℝ)| ≤ e) (hy : |y-(v:ℝ)| ≤ e) (k : ℤ) (hxy : y=(k:ℝ)*x) : False := by
  have hden : (e : ℝ) < u := by exact_mod_cast box.1
  have lower : (e : ℝ)*(1+|(q:ℝ)|) < (v:ℝ)-(q:ℝ)*u := by exact_mod_cast box.2.1
  have upper : (e : ℝ)*(1+|(q:ℝ)+1|) < ((q:ℝ)+1)*u-(v:ℝ) := by exact_mod_cast box.2.2
  have positive : 0 < x := by linarith only [(abs_le.mp hx).1,hden]
  have error (p : ℝ) : |(y-p*x)-((v:ℝ)-p*u)| ≤ (e:ℝ)*(1+|p|) := by
    calc
      _ = |(y-v)-p*(x-u)| := by congr 1; ring
      _ ≤ |y-v|+|p*(x-u)| := abs_sub _ _
      _ ≤ (e:ℝ) + |p| * e := by rw [abs_mul]; exact add_le_add hy (mul_le_mul_of_nonneg_left hx (abs_nonneg p))
      _ = _ := by ring
  have lo : (q:ℝ)*x < y := by linarith only [(abs_le.mp (error (q:ℝ))).1,lower]
  have hi : y < ((q:ℝ)+1)*x := by linarith only [(abs_le.mp (error ((q:ℝ)+1))).2,upper]
  by_cases hk : k≤q
  · have hle : (k:ℝ)≤q := by exact_mod_cast hk
    linarith only [mul_le_mul_of_nonneg_right hle positive.le,lo,hxy]
  · have hle : (q:ℝ)+1 ≤ k := by exact_mod_cast (show q+1≤k by omega)
    linarith only [mul_le_mul_of_nonneg_right hle positive.le,hi,hxy]

open Arxiv.«2607.05739»

/-- A separated trajectory rules out divisibility for the exact integer coordinates. -/
lemma not_integer_of_separated {S : ℤ} {n : ℕ} (hs : 0 < S)
    (ok : separated n (trajectory S n) = true)
    (hx : |(S:ℝ)*(A n:ℝ)/(n.factorial:ℝ)-((trajectory S n).1:ℝ)| ≤ 4*(n:ℝ))
    (hy : |(S:ℝ)*(B n:ℝ)/(n.factorial:ℝ)-((trajectory S n).2:ℝ)| ≤ 4*(n:ℝ)) :
    ¬ IsIntegerValue n := by
  let w := trajectory S n
  let x := (S:ℝ)*(A n:ℝ)/(n.factorial:ℝ)
  let y := (S:ℝ)*(B n:ℝ)/(n.factorial:ℝ)
  let e : ℤ := 4*(n:ℤ)
  have hxe : |x-(w.1:ℝ)| ≤ (e:ℝ) := by simpa only [e,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using hx
  have hye : |y-(w.2:ℝ)| ≤ (e:ℝ) := by simpa only [e,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using hy
  rintro ⟨k,hk⟩
  have hB : (B n : ℝ)=(A n:ℝ)*(k:ℝ) := by exact_mod_cast hk
  have hxy : y=(k:ℝ)*x := by
    have scaled : (S:ℝ)*(B n:ℝ)=(S:ℝ)*((A n:ℝ)*(k:ℝ)) :=
      (mul_right_inj' (show (S:ℝ)≠0 by exact_mod_cast hs.ne')).mpr hB
    dsimp only [x,y]
    rw [scaled]
    ring
  change separated n w=true at ok
  by_cases neg : w.1<0
  · simp only [separated,if_pos neg,decide_eq_true_eq] at ok
    have flip (a b : ℝ) : |-a- -b| = |a-b| := by rw [show -a- -b = -(a-b) by ring,abs_neg]
    refine excludes_integer (-w.1) (-w.2) ((-w.2)/(-w.1)) e (-x) (-y) ok ?_ ?_ k ?_
    · simpa only [Int.cast_neg,flip] using hxe
    · simpa only [Int.cast_neg,flip] using hye
    · rw [hxy]; ring
  · simp only [separated,if_neg neg,decide_eq_true_eq] at ok
    exact excludes_integer w.1 w.2 (w.2/w.1) e x y ok hxe hye k hxy

end ArctanCert

namespace ArctanCert.NaturalRange

def center : ℕ := 316912650057057350374175801344
def margin : ℕ := 36893488147419103232

def magnitude (x : ℕ) := if x<center then center-x else x-center

def safe (x y : ℕ) : Bool :=
  let u := magnitude x
  let w := magnitude y
  let d := w%u
  decide (w≤center ∧ margin<d ∧ d+margin<u)

def block (u v : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, x, y => (x == u) && (y == v)
  | n+1, k, x, y =>
    let b := k <<< 98
    let xt := center+(x+b)/(k+1)
    let yt := x+(y+b)/(k+1)
    let xx := xt-y
    let yy := yt-center
    decide (y≤xt ∧ center≤yt) && safe xx yy && block u v n (k+1) xx yy

end ArctanCert.NaturalRange

namespace ArctanCert.NaturalRange

def decode (x : ℕ) : ℤ := x-(center : ℤ)

private lemma cast_magnitude (x : ℕ) : ((magnitude x : ℕ) : ℤ)=(abs (decode x)) := by
  unfold magnitude decode
  split
  · rename_i h
    rw [Nat.cast_sub h.le,abs_of_nonpos (by omega)]
    omega
  · rename_i h
    rw [Nat.cast_sub (Nat.le_of_not_gt h),abs_of_nonneg (by omega)]

private lemma signed_gaps {u w : ℤ} (hu : 0<u)
    (h : (margin : ℤ)<w%u ∧ w%u+margin<u) :
    (margin : ℤ)<(-w)%u ∧ (-w)%u+margin<u := by
  have hn : ¬u ∣ w := by
    intro hd
    rw [Int.emod_eq_zero_of_dvd hd] at h
    have hpos : (0 : ℤ)≤ margin := by positivity
    omega
  rw [Int.neg_emod,if_neg hn,Int.natAbs_of_nonneg hu.le]
  omega

private lemma slope_bounds {n : ℕ} (hn : n≤1000000) {u v : ℤ}
    (hu : (margin : ℤ)<u) (hv : (abs v)≤(center : ℤ))
    (hl : (margin : ℤ)<v%u) (hh : v%u+margin<u) :
    let q := v/u
    let e := 4*(n : ℤ)
    e<u ∧ e*(1+|q|)<v-q*u ∧ e*(1+|q+1|)<(q+1)*u-v := by
  let q := v/u
  let e := 4*(n : ℤ)
  change e<u ∧ e*(1+|q|)<v-q*u ∧ e*(1+|q+1|)<(q+1)*u-v
  have up : 0<u := lt_of_le_of_lt (by positivity) hu
  obtain ⟨vmin,vmax⟩ := abs_le.mp hv
  have qmin : -8589934592≤q := by
    apply (Int.le_ediv_iff_mul_le up).mpr
    norm_num [center,margin] at vmin hu
    omega
  have qmax : q<8589934592 := by
    apply (Int.ediv_lt_iff_lt_mul up).mpr
    norm_num [center,margin] at vmax hu
    omega
  have emax : e≤4000000 := by dsimp [e]; omega
  have small (z : ℤ) (hz : -8589934592≤z ∧ z≤8589934592) : e*(1+(abs z))≤ margin := by
    have bound := abs_le.mpr hz
    have high : (1:ℤ)+(abs z)≤8589934593 := by omega
    have hprod := mul_le_mul emax high (by positivity) (by decide)
    norm_num [margin] at hprod ⊢
    omega
  have rem : v-q*u = v%u := by rw [Int.emod_def]; dsimp [q]; ring
  have rem' : (q+1)*u-v = u-v%u := by rw [Int.emod_def]; dsimp [q]; ring
  rw [rem,rem']
  refine ⟨?_,lt_of_le_of_lt (small _ ⟨qmin,le_of_lt qmax⟩) hl,?_⟩
  · norm_num [margin] at hu; omega
  · exact lt_of_le_of_lt (small _ (by omega)) (by omega)

private lemma safe_sound {n x y : ℕ} (hn : n≤1000000) (hs : safe x y=true) :
    separated n (decode x,decode y)=true := by
  obtain ⟨hy,hl,hh⟩ : magnitude y≤center ∧ margin< magnitude y%magnitude x ∧
      magnitude y%magnitude x+margin< magnitude x := of_decide_eq_true hs
  have vlim : (abs (decode y))≤(center : ℤ) := by rw [← cast_magnitude]; exact_mod_cast hy
  have hr : (margin : ℤ)<(abs (decode y))%(abs (decode x)) ∧ (abs (decode y))%(abs (decode x))+margin<(abs (decode x)) := by
    rw [← cast_magnitude,← cast_magnitude,← Int.natCast_emod]
    exact ⟨by exact_mod_cast hl,by exact_mod_cast hh⟩
  have hu : (margin : ℤ)<(abs (decode x)) := by
    have hn' : (0 : ℤ)≤ margin := by positivity
    omega
  have good (v : ℤ) (hv : (abs v)=(abs (decode y))) :
      let u := (abs (decode x))
      let q := v/u
      let e := 4*(n : ℤ)
      e<u ∧ e*(1+|q|)<v-q*u ∧ e*(1+|q+1|)<(q+1)*u-v := by
    have hgap : (margin : ℤ)<v%(abs (decode x)) ∧ v%(abs (decode x))+margin<(abs (decode x)) := by
      by_cases vh : 0≤v
      · rwa [← hv,abs_of_nonneg vh] at hr
      · have hv' : v = -(abs (decode y)) := by rw [← hv,abs_of_neg (lt_of_not_ge vh),neg_neg]
        rw [hv']
        exact signed_gaps (lt_of_le_of_lt (by positivity) hu) hr
    exact slope_bounds hn hu (hv ▸ vlim) hgap.1 hgap.2
  by_cases hx : decode x<0
  · simp only [separated,if_pos hx,decide_eq_true_eq]
    simpa only [abs_of_neg hx] using good (-decode y) (abs_neg _)
  · simp only [separated,if_neg hx,decide_eq_true_eq]
    simpa only [abs_of_nonneg (le_of_not_gt hx)] using good (decode y) rfl

private lemma quotient (k x : ℕ) :
    decode ((x+(k <<< 98))/(k+1)) = decode x / ((k+1 : ℕ) : ℤ) := by
  unfold decode
  rw [Int.natCast_ediv]
  have h : ((x+(k <<< 98) : ℕ) : ℤ) = ((x:ℤ)-(center : ℤ)) + center*((k+1 : ℕ):ℤ) := by
    rw [Nat.shiftLeft_eq,show (2:ℕ)^98=center by decide]
    push_cast
    ring
  rw [h,Int.add_mul_ediv_right _ _ (by exact_mod_cast (Nat.succ_ne_zero k))]
  ring

private lemma step_decode (k x y : ℕ)
    (hx : y≤center+(x+(k <<< 98))/(k+1)) (hy : center≤x+(y+(k <<< 98))/(k+1)) :
    step (k+1) (decode x,decode y) =
      (decode (center+(x+(k <<< 98))/(k+1)-y),decode (x+(y+(k <<< 98))/(k+1)-center)) := by
  unfold step
  simp only
  rw [← quotient k x,← quotient k y]
  unfold decode
  rw [Nat.cast_sub hx,Nat.cast_sub hy,Nat.cast_add,Nat.cast_add]
  apply Prod.ext <;> dsimp only <;> ring

private lemma block_sound {u v : ℕ} {len k x y : ℕ}
    (hs : trajectory (2^96) k=(decode x,decode y)) (cap : k+len≤1000000)
    (h : block u v len k x y=true) :
    trajectory (2^96) (k+len)=(decode u,decode v) ∧
    ∀ n, k<n → n≤k+len → separated n (trajectory (2^96) n)=true := by
  induction len generalizing k x y with
  | zero =>
    obtain ⟨hx,hy⟩ := Bool.and_eq_true_iff.mp h
    rw [beq_iff_eq.mp hx,beq_iff_eq.mp hy] at hs
    exact ⟨hs,fun n hn hu => by omega⟩
  | succ len ih =>
    obtain ⟨hh,hr⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨guards,sep⟩ := Bool.and_eq_true_iff.mp hh
    let u' := center+(x+(k <<< 98))/(k+1)-y
    let v' := x+(y+(k <<< 98))/(k+1)-center
    have hs' : trajectory (2^96) (k+1)=(decode u',decode v') := by
      rw [trajectory,hs]
      exact step_decode k x y (of_decide_eq_true guards).1 (of_decide_eq_true guards).2
    obtain ⟨hend,sub⟩ := ih hs' (by omega) hr
    rw [show k+(len+1)=(k+1)+len by omega]
    refine ⟨hend,?_⟩
    intro n hn hu
    by_cases eq : n=k+1
    · rw [eq,hs']
      exact safe_sound (by omega) sep
    · exact sub n (by omega) hu

structure Checkpoint (k x y : ℕ) : Type where
  state : trajectory (2^96) k=(decode x,decode y)
  valid : ∀ n, 5≤n → n≤k → separated n (trajectory (2^96) n)=true

def advance {k x y u v : ℕ} (prev : Checkpoint k x y) (len : ℕ) (cap : k+len≤1000000)
    (test : block u v len k x y=true) : Checkpoint (k+len) u v := by
  obtain ⟨state,sub⟩ := block_sound prev.state cap test
  refine ⟨state,?_⟩
  intro n hn hu
  by_cases h : n≤k
  · exact prev.valid n hn h
  · exact sub n (by omega) hu

end ArctanCert.NaturalRange

namespace ArctanCert.NaturalRange

private def c4 : Checkpoint 4 283900915676113876376865822037 184865712533283454384935884117 := ⟨by decide +kernel,fun _ h h' => by omega⟩

private def c1004 : Checkpoint 1004 407596133262801944967080959122 195139662090009507357873597285 := advance c4 1000 (by decide) (by decide +kernel)
private def c2004 : Checkpoint 2004 309199805744758094319814365020 165241564221131663273515442766 := advance c1004 1000 (by decide) (by decide +kernel)
private def c3004 : Checkpoint 3004 250095619815636431243436650422 180520126091116289361181847015 := advance c2004 1000 (by decide) (by decide +kernel)
private def c4004 : Checkpoint 4004 214180450479481158043128523110 205040184168807870266550815103 := advance c3004 1000 (by decide) (by decide +kernel)
private def c5004 : Checkpoint 5004 191986863433872047207104648742 230517902215087150440960404978 := advance c4004 1000 (by decide) (by decide +kernel)
private def c6004 : Checkpoint 6004 178399989829384650935623410905 254578748069264926245449696904 := advance c5004 1000 (by decide) (by decide +kernel)
private def c7004 : Checkpoint 7004 170474206482326753615920216366 276569085737791051956034722559 := advance c6004 1000 (by decide) (by decide +kernel)
private def c8004 : Checkpoint 8004 166406979261692476062281679847 296412028083024801787594738319 := advance c7004 1000 (by decide) (by decide +kernel)
private def c9004 : Checkpoint 9004 165039811010311696627818300888 314230614924532650902050179684 := advance c8004 1000 (by decide) (by decide +kernel)
private def c10004 : Checkpoint 10004 165598426765529719732999785343 330209811483351017252824051202 := advance c9004 1000 (by decide) (by decide +kernel)
private def c11004 : Checkpoint 11004 167548806756068292896718668358 344543440135313273467305643327 := advance c10004 1000 (by decide) (by decide +kernel)
private def c12004 : Checkpoint 12004 170513091602111489588635216635 357414035088507429104284272036 := advance c11004 1000 (by decide) (by decide +kernel)
private def c13004 : Checkpoint 13004 174218241485551862718930417415 368986121869947842683881219554 := advance c12004 1000 (by decide) (by decide +kernel)
private def c14004 : Checkpoint 14004 178463503702552282098131502080 379405059758409083427771411344 := advance c13004 1000 (by decide) (by decide +kernel)
private def c15004 : Checkpoint 15004 183099135860933663583213009676 388798118830133590438451721457 := advance c14004 1000 (by decide) (by decide +kernel)
private def c16004 : Checkpoint 16004 188012107599097418020917065482 397276344848502768182730963161 := advance c15004 1000 (by decide) (by decide +kernel)
private def c17004 : Checkpoint 17004 193116263440664502682931293571 404936582772858823661910275144 := advance c16004 1000 (by decide) (by decide +kernel)
private def c18004 : Checkpoint 18004 198345414575681330213324968321 411863395741860645377935344920 := advance c17004 1000 (by decide) (by decide +kernel)
private def c19004 : Checkpoint 19004 203648399171845549349729397100 418130782532527020198525897870 := advance c18004 1000 (by decide) (by decide +kernel)
private def c20004 : Checkpoint 20004 208985493421319463102886414931 423803671306611283424893386613 := advance c19004 1000 (by decide) (by decide +kernel)
private def c21004 : Checkpoint 21004 214325766657380915423128787758 428939199729589538577843842980 := advance c20004 1000 (by decide) (by decide +kernel)
private def c22004 : Checkpoint 22004 219645107287310038468725556885 433587803897228519369961608428 := advance c21004 1000 (by decide) (by decide +kernel)
private def c23004 : Checkpoint 23004 224924732507258999246892679849 437794141641445587976254127479 := advance c22004 1000 (by decide) (by decide +kernel)
private def c24004 : Checkpoint 24004 230150051625134414170540355077 441597874847766516702940520378 := advance c23004 1000 (by decide) (by decide +kernel)
private def c25004 : Checkpoint 25004 235309791009839421225416218453 445034332866465426399699615554 := advance c24004 1000 (by decide) (by decide +kernel)
private def c26004 : Checkpoint 26004 240395314769829759805728882985 448135076103029788093088302961 := advance c25004 1000 (by decide) (by decide +kernel)
private def c27004 : Checkpoint 27004 245400093352523196181062162318 450928375957262070807299341764 := advance c26004 1000 (by decide) (by decide +kernel)
private def c28004 : Checkpoint 28004 250319284976031828269044355703 453439624658058348655397619846 := advance c27004 1000 (by decide) (by decide +kernel)
private def c29004 : Checkpoint 29004 255149403864882596851358892311 455691686276436328427770540801 := advance c28004 1000 (by decide) (by decide +kernel)
private def c30004 : Checkpoint 30004 259888055791662441217541837440 457705198287322330957975601868 := advance c29004 1000 (by decide) (by decide +kernel)
private def c31004 : Checkpoint 31004 264533726185141573476395876112 459498831456731630613082975228 := advance c30004 1000 (by decide) (by decide +kernel)
private def c32004 : Checkpoint 32004 269085609568441509110884194247 461089514511938259316946784216 := advance c31004 1000 (by decide) (by decide +kernel)
private def c33004 : Checkpoint 33004 273543471693997394127492805634 462492628964752630552502598450 := advance c32004 1000 (by decide) (by decide +kernel)
private def c34004 : Checkpoint 34004 277907537693661266094859903781 463722178562831800656742406695 := advance c33004 1000 (by decide) (by decide +kernel)
private def c35004 : Checkpoint 35004 282178401037473566533366408399 464790937107073428397906792380 := advance c34004 1000 (by decide) (by decide +kernel)
private def c36004 : Checkpoint 36004 286356949218303077133594315702 465710577766009719334505118864 := advance c35004 1000 (by decide) (by decide +kernel)
private def c37004 : Checkpoint 37004 290444302941669002605751387974 466491786517056923108372231033 := advance c36004 1000 (by decide) (by decide +kernel)
private def c38004 : Checkpoint 38004 294441766265986635905547442260 467144361930083663168934005497 := advance c37004 1000 (by decide) (by decide +kernel)
private def c39004 : Checkpoint 39004 298350785656146436407525431594 467677303165214391951029150902 := advance c38004 1000 (by decide) (by decide +kernel)
private def c40004 : Checkpoint 40004 302172916318169502986655635518 468098887771219624844441642588 := advance c39004 1000 (by decide) (by decide +kernel)
private def c41004 : Checkpoint 41004 305909794501066043508132006846 468416740632818897643734610762 := advance c40004 1000 (by decide) (by decide +kernel)
private def c42004 : Checkpoint 42004 309563114703754661085373328400 468637895216256923607975057528 := advance c41004 1000 (by decide) (by decide +kernel)
private def c43004 : Checkpoint 43004 313134610924935552252212811413 468768848095718950443188254494 := advance c42004 1000 (by decide) (by decide +kernel)
private def c44004 : Checkpoint 44004 316626041253523458541450880446 468815607602922068994579532485 := advance c43004 1000 (by decide) (by decide +kernel)
private def c45004 : Checkpoint 45004 320039175225338913541922679726 468783737323985319807579570277 := advance c44004 1000 (by decide) (by decide +kernel)
private def c46004 : Checkpoint 46004 323375783474927061101559994672 468678395067709392092486061452 := advance c45004 1000 (by decide) (by decide +kernel)
private def c47004 : Checkpoint 47004 326637629294806342099647706450 468504367844629083965042581605 := advance c46004 1000 (by decide) (by decide +kernel)
private def c48004 : Checkpoint 48004 329826461782178642048340944469 468266103324128385361311338393 := advance c47004 1000 (by decide) (by decide +kernel)
private def c49004 : Checkpoint 49004 332944010308312951562474433841 467967738175462893611059948182 := advance c48004 1000 (by decide) (by decide +kernel)
private def c50004 : Checkpoint 50004 335991980090925547777771907372 467613123646011990798940617085 := advance c49004 1000 (by decide) (by decide +kernel)
private def c51004 : Checkpoint 51004 338972048686878597510869683534 467205848685072555223294879444 := advance c50004 1000 (by decide) (by decide +kernel)
private def c52004 : Checkpoint 52004 341885863252958143204731005990 466749260882835871206239120451 := advance c51004 1000 (by decide) (by decide +kernel)
private def c53004 : Checkpoint 53004 344735038447607759110153740553 466246485460885438681419306462 := advance c52004 1000 (by decide) (by decide +kernel)
private def c54004 : Checkpoint 54004 347521154867274081285616318355 465700442521802631757843134887 := advance c53004 1000 (by decide) (by decide +kernel)
private def c55004 : Checkpoint 55004 350245757928258187326237295414 465113862740589593773894501073 := advance c54004 1000 (by decide) (by decide +kernel)
private def c56004 : Checkpoint 56004 352910357119301490506005256131 464489301659044062426351601886 := advance c55004 1000 (by decide) (by decide +kernel)
private def c57004 : Checkpoint 57004 355516425562083072376174642094 463829152725469442263692156473 := advance c56004 1000 (by decide) (by decide +kernel)
private def c58004 : Checkpoint 58004 358065399826786319316512031460 463135659205771141262800620649 := advance c57004 1000 (by decide) (by decide +kernel)
private def c59004 : Checkpoint 59004 360558679958247443045353058165 462410925077735360597296348681 := advance c58004 1000 (by decide) (by decide +kernel)
private def c60004 : Checkpoint 60004 362997629675205413508752354930 461656925007819803013841061047 := advance c59004 1000 (by decide) (by decide +kernel)
private def c61004 : Checkpoint 61004 365383576711060026254545737309 460875513498861442219975982440 := advance c60004 1000 (by decide) (by decide +kernel)
private def c62004 : Checkpoint 62004 367717813269499503748059622198 460068433287515463197515650412 := advance c61004 1000 (by decide) (by decide +kernel)
private def c63004 : Checkpoint 63004 370001596572535371567449035453 459237323061803371289049948690 := advance c62004 1000 (by decide) (by decide +kernel)
private def c64004 : Checkpoint 64004 372236149482007651206592069140 458383724561714590581428709516 := advance c63004 1000 (by decide) (by decide +kernel)
private def c65004 : Checkpoint 65004 374422661178603036423115421685 457509089119243990255849072127 := advance c64004 1000 (by decide) (by decide +kernel)
private def c66004 : Checkpoint 66004 376562287884950095559180234952 456614783688445532204534918788 := advance c65004 1000 (by decide) (by decide +kernel)
private def c67004 : Checkpoint 67004 378656153621491378819006476490 455702096410943132995166012613 := advance c66004 1000 (by decide) (by decide +kernel)
private def c68004 : Checkpoint 68004 380705350985643215501634501783 454772241757780698905798456947 := advance c67004 1000 (by decide) (by decide +kernel)
private def c69004 : Checkpoint 69004 382710941946290590999857289098 453826365284442279681795653807 := advance c68004 1000 (by decide) (by decide +kernel)
private def c70004 : Checkpoint 70004 384673958646969177793284845651 452865548032268221532466188840 := advance c69004 1000 (by decide) (by decide +kernel)
private def c71004 : Checkpoint 71004 386595404212194905171002287231 451890810606280178031379310801 := advance c70004 1000 (by decide) (by decide +kernel)
private def c72004 : Checkpoint 72004 388476253552343259946682271428 450903116956560038005453459228 := advance c71004 1000 (by decide) (by decide +kernel)
private def c73004 : Checkpoint 73004 390317454163280962224778021457 449903377887764511463142315609 := advance c72004 1000 (by decide) (by decide +kernel)
private def c74004 : Checkpoint 74004 392119926917632963758754255725 448892454319062766356003857511 := advance c73004 1000 (by decide) (by decide +kernel)
private def c75004 : Checkpoint 75004 393884566845145786222298373998 447871160314728123949431214042 := advance c74004 1000 (by decide) (by decide +kernel)
private def c76004 : Checkpoint 76004 395612243900099209906862849375 446840265903769280978916936822 := advance c75004 1000 (by decide) (by decide +kernel)
private def c77004 : Checkpoint 77004 397303803714135083455986382275 445800499705328077327713884607 := advance c76004 1000 (by decide) (by decide +kernel)
private def c78004 : Checkpoint 78004 398960068333225450967900067620 444752551375078626065651894735 := advance c77004 1000 (by decide) (by decide +kernel)
private def c79004 : Checkpoint 79004 400581836937801545235307693321 443697073886518352946612721125 := advance c78004 1000 (by decide) (by decide +kernel)
private def c80004 : Checkpoint 80004 402169886545318354792156192425 442634685659829035934911172017 := advance c79004 1000 (by decide) (by decide +kernel)
private def c81004 : Checkpoint 81004 403724972694743150462873131686 441565972549891085157477142432 := advance c80004 1000 (by decide) (by decide +kernel)
private def c82004 : Checkpoint 82004 405247830112636279301228780130 440491489704044520168249577423 := advance c81004 1000 (by decide) (by decide +kernel)
private def c83004 : Checkpoint 83004 406739173360643588183635128614 439411763299294300766286426075 := advance c82004 1000 (by decide) (by decide +kernel)
private def c84004 : Checkpoint 84004 408199697464346203482503809742 438327292167846039360292996373 := advance c83004 1000 (by decide) (by decide +kernel)
private def c85004 : Checkpoint 85004 409630078523518640969562220649 437238549319121971864540478844 := advance c84004 1000 (by decide) (by decide +kernel)
private def c86004 : Checkpoint 86004 411030974303933411269766612332 436145983365738673523421699814 := advance c85004 1000 (by decide) (by decide +kernel)
private def c87004 : Checkpoint 87004 412403024810922042756100063866 435050019860320518474815938916 := advance c86004 1000 (by decide) (by decide +kernel)
private def c88004 : Checkpoint 88004 413746852844961014044668103890 433951062549470195838727389429 := advance c87004 1000 (by decide) (by decide +kernel)
private def c89004 : Checkpoint 89004 415063064539598401337256606306 432849494550714275137333118034 := advance c88004 1000 (by decide) (by decide +kernel)
private def c90004 : Checkpoint 90004 416352249882074757928422089191 431745679457783011763602741992 := advance c89004 1000 (by decide) (by decide +kernel)
private def c91004 : Checkpoint 91004 417614983217021276738076387383 430639962379164969629496752379 := advance c90004 1000 (by decide) (by decide +kernel)
private def c92004 : Checkpoint 92004 418851823733640863998179285964 429532670914494742413430271110 := advance c91004 1000 (by decide) (by decide +kernel)
private def c93004 : Checkpoint 93004 420063315936794423706100383063 428424116072982612570650540553 := advance c92004 1000 (by decide) (by decide +kernel)
private def c94004 : Checkpoint 94004 421249990102426321194640127094 427314593137775294169649428779 := advance c93004 1000 (by decide) (by decide +kernel)
private def c95004 : Checkpoint 95004 422412362717770436499690138020 426204382479844177019119189412 := advance c94004 1000 (by decide) (by decide +kernel)
private def c96004 : Checkpoint 96004 423550936906782101525966466974 425093750324729224857064562841 := advance c95004 1000 (by decide) (by decide +kernel)
private def c97004 : Checkpoint 97004 424666202841242112966818932084 423982949475220631714413634020 := advance c96004 1000 (by decide) (by decide +kernel)
private def c98004 : Checkpoint 98004 425758638137977418451506405593 422872219992834485170753183976 := advance c97004 1000 (by decide) (by decide +kernel)
private def c99004 : Checkpoint 99004 426828708242639409850971825107 421761789840731201045147964546 := advance c98004 1000 (by decide) (by decide +kernel)
private def c100004 : Checkpoint 100004 427876866800475388498625250808 420651875490534738248122344572 := advance c99004 1000 (by decide) (by decide +kernel)
private def c101004 : Checkpoint 101004 428903556014522004001361923510 419542682495335092323198760943 := advance c100004 1000 (by decide) (by decide +kernel)
private def c102004 : Checkpoint 102004 429909206991641578447834215263 418434406030994962132342480524 := advance c101004 1000 (by decide) (by decide +kernel)
private def c103004 : Checkpoint 103004 430894240076813439790612871497 417327231407732574968165587592 := advance c102004 1000 (by decide) (by decide +kernel)
private def c104004 : Checkpoint 104004 431859065176082897381622311369 416221334553815344872337500210 := advance c103004 1000 (by decide) (by decide +kernel)
private def c105004 : Checkpoint 105004 432804082068560465782957657317 415116882473072334047802215905 := advance c104004 1000 (by decide) (by decide +kernel)
private def c106004 : Checkpoint 106004 433729680707853521995047916810 414014033677816487588020590056 := advance c105004 1000 (by decide) (by decide +kernel)
private def c107004 : Checkpoint 107004 434636241513301886692654315063 412912938598659500241954843074 := advance c106004 1000 (by decide) (by decide +kernel)
private def c108004 : Checkpoint 108004 435524135651377954026340115301 411813739972602208497035506417 := advance c107004 1000 (by decide) (by decide +kernel)
private def c109004 : Checkpoint 109004 436393725307601043189158253060 410716573210690907334437185705 := advance c108004 1000 (by decide) (by decide +kernel)
private def c110004 : Checkpoint 110004 437245363949304680674723913386 409621566746444354915499146521 := advance c109004 1000 (by decide) (by decide +kernel)
private def c111004 : Checkpoint 111004 438079396579584605518140683384 408528842366176891456848832525 := advance c110004 1000 (by decide) (by decide +kernel)
private def c112004 : Checkpoint 112004 438896159982744471153301924631 407438515522269551523135397897 := advance c111004 1000 (by decide) (by decide +kernel)
private def c113004 : Checkpoint 113004 439695982961545538378609270445 406350695630372827638062513276 := advance c112004 1000 (by decide) (by decide +kernel)
private def c114004 : Checkpoint 114004 440479186566556148268458836107 405265486351461423788994825296 := advance c113004 1000 (by decide) (by decide +kernel)
private def c115004 : Checkpoint 115004 441246084317886459165454032557 404182985859602533117943940903 := advance c114004 1000 (by decide) (by decide +kernel)
private def c116004 : Checkpoint 116004 441996982419583850021382616013 403103287096244531183402058636 := advance c115004 1000 (by decide) (by decide +kernel)
private def c117004 : Checkpoint 117004 442732179966954550423752055486 402026478011782171166442520954 := advance c116004 1000 (by decide) (by decide +kernel)
private def c118004 : Checkpoint 118004 443451969147067468659055326763 400952641795107104206985978942 := advance c117004 1000 (by decide) (by decide +kernel)
private def c119004 : Checkpoint 119004 444156635432686862643821406092 399881857091808555509551111339 := advance c118004 1000 (by decide) (by decide +kernel)
private def c120004 : Checkpoint 120004 444846457769871441049672100810 398814198211648016396420195262 := advance c119004 1000 (by decide) (by decide +kernel)
private def c121004 : Checkpoint 121004 445521708759468697489058264864 397749735325893636138187930104 := advance c120004 1000 (by decide) (by decide +kernel)
private def c122004 : Checkpoint 122004 446182654832724771114156914843 396688534655064405924814360437 := advance c121004 1000 (by decide) (by decide +kernel)
private def c123004 : Checkpoint 123004 446829556421221892520067198861 395630658647601028594907942836 := advance c122004 1000 (by decide) (by decide +kernel)
private def c124004 : Checkpoint 124004 447462668121347513041579213777 394576166149949385122630408457 := advance c123004 1000 (by decide) (by decide +kernel)
private def c125004 : Checkpoint 125004 448082238853491525748257316554 393525112568513579976950924657 := advance c124004 1000 (by decide) (by decide +kernel)
private def c126004 : Checkpoint 126004 448688512016160564002075875536 392477550023908522888912193179 := advance c125004 1000 (by decide) (by decide +kernel)
private def c127004 : Checkpoint 127004 449281725635191203828587545122 391433527497916746706294358028 := advance c126004 1000 (by decide) (by decide +kernel)
private def c128004 : Checkpoint 128004 449862112508236994367969556969 390393090973530543128016347786 := advance c127004 1000 (by decide) (by decide +kernel)
private def c129004 : Checkpoint 129004 450429900344697590574827896034 389356283568438403346203513446 := advance c128004 1000 (by decide) (by decide +kernel)
private def c130004 : Checkpoint 130004 450985311901251857960391881427 388323145662294071204621808311 := advance c129004 1000 (by decide) (by decide +kernel)
private def c131004 : Checkpoint 131004 451528565113150654031493138225 387293715018087152938195686043 := advance c130004 1000 (by decide) (by decide +kernel)
private def c132004 : Checkpoint 132004 452059873221419058457406023859 386268026897916088034328800241 := advance c131004 1000 (by decide) (by decide +kernel)
private def c133004 : Checkpoint 133004 452579444896112117008742094855 385246114173447285381448250633 := advance c132004 1000 (by decide) (by decide +kernel)
private def c134004 : Checkpoint 134004 453087484355762675986518143692 384228007431328289181762830512 := advance c133004 1000 (by decide) (by decide +kernel)
private def c135004 : Checkpoint 135004 453584191483154607176047821319 383213735073807887527589925675 := advance c134004 1000 (by decide) (by decide +kernel)
private def c136004 : Checkpoint 136004 454069761937549651303756242033 382203323414802045905770486991 := advance c135004 1000 (by decide) (by decide +kernel)
private def c137004 : Checkpoint 137004 454544387263491233570023384148 381196796771631376006755832252 := advance c136004 1000 (by decide) (by decide +kernel)
private def c138004 : Checkpoint 138004 455008254996303921174155547658 380194177552643479451918475838 := advance c137004 1000 (by decide) (by decide +kernel)
private def c139004 : Checkpoint 139004 455461548764402693032779364843 379195486340921883002528381405 := advance c138004 1000 (by decide) (by decide +kernel)
private def c140004 : Checkpoint 140004 455904448388521869433610793445 378200741974272356941915743880 := advance c139004 1000 (by decide) (by decide +kernel)
private def c141004 : Checkpoint 141004 456337129977969397612158243868 377209961621667135666660478153 := advance c140004 1000 (by decide) (by decide +kernel)
private def c142004 : Checkpoint 142004 456759766024008201788848170688 376223160856317896415273959820 := advance c141004 1000 (by decide) (by decide +kernel)
private def c143004 : Checkpoint 143004 457172525490462476818213096556 375240353725539258874484439176 := advance c142004 1000 (by decide) (by decide +kernel)
private def c144004 : Checkpoint 144004 457575573901643127208627116937 374261552817556008309185247214 := advance c143004 1000 (by decide) (by decide +kernel)
private def c145004 : Checkpoint 145004 457969073427683021973479000089 373286769325399183627514515248 := advance c144004 1000 (by decide) (by decide +kernel)
private def c146004 : Checkpoint 146004 458353182967369344853830331680 372316013108028577575430440949 := advance c145004 1000 (by decide) (by decide +kernel)
private def c147004 : Checkpoint 147004 458728058228557063370352911276 371349292748812039425516539690 := advance c146004 1000 (by decide) (by decide +kernel)
private def c148004 : Checkpoint 148004 459093851806244413562112313279 370386615611485223498360133264 := advance c147004 1000 (by decide) (by decide +kernel)
private def c149004 : Checkpoint 149004 459450713258388294976403082516 369427987893709063940467584477 := advance c148004 1000 (by decide) (by decide +kernel)
private def c150004 : Checkpoint 150004 459798789179534587492428161813 368473414678336253441596930520 := advance c149004 1000 (by decide) (by decide +kernel)
private def c151004 : Checkpoint 151004 460138223272335633075512529694 367522899982492338691116266735 := advance c150004 1000 (by decide) (by decide +kernel)
private def c152004 : Checkpoint 152004 460469156417024466926761914477 366576446804571697536247930187 := advance c151004 1000 (by decide) (by decide +kernel)
private def c153004 : Checkpoint 153004 460791726738912829247116652009 365634057169243612598104435094 := advance c152004 1000 (by decide) (by decide +kernel)
private def c154004 : Checkpoint 154004 461106069673977536674976483115 364695732170558885401039889281 := advance c153004 1000 (by decide) (by decide +kernel)
private def c155004 : Checkpoint 155004 461412318032597437248269808280 363761472013242926954139266112 := advance c154004 1000 (by decide) (by decide +kernel)
private def c156004 : Checkpoint 156004 461710602061500910510986774275 362831276052256999382128519962 := advance c155004 1000 (by decide) (by decide +kernel)
private def c157004 : Checkpoint 157004 462001049503981701313026034163 361905142830705253863124017836 := advance c156004 1000 (by decide) (by decide +kernel)
private def c158004 : Checkpoint 158004 462283785658438788274639870258 360983070116161398980728231417 := advance c157004 1000 (by decide) (by decide +kernel)
private def c159004 : Checkpoint 159004 462558933435293982283729714849 360065054935485227720373116516 := advance c158004 1000 (by decide) (by decide +kernel)
private def c160004 : Checkpoint 160004 462826613412339023388949032802 359151093608195818648373014141 := advance c159004 1000 (by decide) (by decide +kernel)
private def c161004 : Checkpoint 161004 463086943888562092804742480762 358241181778464995994381636250 := advance c160004 1000 (by decide) (by decide +kernel)
private def c162004 : Checkpoint 162004 463340040936501877349598832276 357335314445791573821473932846 := advance c161004 1000 (by decide) (by decide +kernel)
private def c163004 : Checkpoint 163004 463586018453175613517499238352 356433485994414011291079923419 := advance c162004 1000 (by decide) (by decide +kernel)
private def c164004 : Checkpoint 164004 463824988209625894679793309737 355535690221516359915351767067 := advance c163004 1000 (by decide) (by decide +kernel)
private def c165004 : Checkpoint 165004 464057059899129444894351355345 354641920364279780922287857874 := advance c164004 1000 (by decide) (by decide +kernel)
private def c166004 : Checkpoint 166004 464282341184109543838966216593 353752169125829443266882506370 := advance c165004 1000 (by decide) (by decide +kernel)
private def c167004 : Checkpoint 167004 464500937741792326974678975716 352866428700124272738771586838 := advance c166004 1000 (by decide) (by decide +kernel)
private def c168004 : Checkpoint 168004 464712953308645780775669306128 351984690795834802849709623806 := advance c167004 1000 (by decide) (by decide +kernel)
private def c169004 : Checkpoint 169004 464918489723638902430710380266 351106946659252271980049135401 := advance c168004 1000 (by decide) (by decide +kernel)
private def c170004 : Checkpoint 170004 465117646970357194619435330795 350233187096270112281206659632 := advance c169004 1000 (by decide) (by decide +kernel)
private def c171004 : Checkpoint 171004 465310523218009416680713276853 349363402493477078114479739599 := advance c170004 1000 (by decide) (by decide +kernel)
private def c172004 : Checkpoint 172004 465497214861359311695800804016 348497582838399459758492476732 := advance c171004 1000 (by decide) (by decide +kernel)
private def c173004 : Checkpoint 173004 465677816559614872767030681597 347635717738928116476914802521 := advance c172004 1000 (by decide) (by decide +kernel)
private def c174004 : Checkpoint 174004 465852421274306599227359794231 346777796441964436858011992593 := advance c173004 1000 (by decide) (by decide +kernel)
private def c175004 : Checkpoint 175004 466021120306185122889736326740 345923807851317788965028310276 := advance c174004 1000 (by decide) (by decide +kernel)
private def c176004 : Checkpoint 176004 466184003331167554036129515147 345073740544885553893425389585 := advance c175004 1000 (by decide) (by decide +kernel)
private def c177004 : Checkpoint 177004 466341158435360905024714191844 344227582791145439697096153471 := advance c176004 1000 (by decide) (by decide +kernel)
private def c178004 : Checkpoint 178004 466492672149189994599910615436 343385322564988444441497972979 := advance c177004 1000 (by decide) (by decide +kernel)
private def c179004 : Checkpoint 179004 466638629480656316729853445792 342546947562919573713719704972 := advance c178004 1000 (by decide) (by decide +kernel)
private def c180004 : Checkpoint 180004 466779113947753472638974769752 341712445217652215826023378137 := advance c179004 1000 (by decide) (by decide +kernel)
private def c181004 : Checkpoint 181004 466914207610063912280042087601 340881802712120933947027305351 := advance c180004 1000 (by decide) (by decide +kernel)
private def c182004 : Checkpoint 182004 467043991099560910488613184724 340055006992936345426151492355 := advance c181004 1000 (by decide) (by decide +kernel)
private def c183004 : Checkpoint 183004 467168543650638912227473706258 339232044783304721759512564721 := advance c182004 1000 (by decide) (by decide +kernel)
private def c184004 : Checkpoint 184004 467287943129394619456414506907 338412902595433955260213894994 := advance c183004 1000 (by decide) (by decide +kernel)
private def c185004 : Checkpoint 185004 467402266062180458101764841048 337597566742446597977755067625 := advance c184004 1000 (by decide) (by decide +kernel)
private def c186004 : Checkpoint 186004 467511587663451356247166823133 336786023349819782339273743513 := advance c185004 1000 (by decide) (by decide +kernel)
private def c187004 : Checkpoint 187004 467615981862925082965441393172 335978258366370979074315495572 := advance c186004 1000 (by decide) (by decide +kernel)
private def c188004 : Checkpoint 188004 467715521332075740148854352130 335174257574807734076981443307 := advance c187004 1000 (by decide) (by decide +kernel)
private def c189004 : Checkpoint 189004 467810277509979366302011726483 334374006601858749916537532711 := advance c188004 1000 (by decide) (by decide +kernel)
private def c190004 : Checkpoint 190004 467900320628530000609077964426 333577490928002937804351176456 := advance c189004 1000 (by decide) (by decide +kernel)
private def c191004 : Checkpoint 191004 467985719737043966785034030612 332784695896812360141670276528 := advance c190004 1000 (by decide) (by decide +kernel)
private def c192004 : Checkpoint 192004 468066542726269568416525465013 331995606723924310589168353741 := advance c191004 1000 (by decide) (by decide +kernel)
private def c193004 : Checkpoint 193004 468142856351818839874351514281 331210208505657136288932882227 := advance c192004 1000 (by decide) (by decide +kernel)
private def c194004 : Checkpoint 194004 468214726257037468653728235599 330428486227283793894444324937 := advance c193004 1000 (by decide) (by decide +kernel)
private def c195004 : Checkpoint 195004 468282216995328495419601880083 329650424770976545968881505901 := advance c194004 1000 (by decide) (by decide +kernel)
private def c196004 : Checkpoint 196004 468345392051944906383122658008 328876008923435645719789295008 := advance c195004 1000 (by decide) (by decide +kernel)
private def c197004 : Checkpoint 197004 468404313865265758222332494972 328105223383214324645413003272 := advance c196004 1000 (by decide) (by decide +kernel)
private def c198004 : Checkpoint 198004 468459043847570017924086362535 327338052767751888240907484587 := advance c197004 1000 (by decide) (by decide +kernel)
private def c199004 : Checkpoint 199004 468509642405321858031381970487 326574481620126238282659135997 := advance c198004 1000 (by decide) (by decide +kernel)
private def c200004 : Checkpoint 200004 468556168958980721222853550900 325814494415536675269290540743 := advance c199004 1000 (by decide) (by decide +kernel)
private def c201004 : Checkpoint 201004 468598681962349056346366964028 325058075567527390299897174968 := advance c200004 1000 (by decide) (by decide +kernel)
private def c202004 : Checkpoint 202004 468637238921470230417467574861 324305209433961631019915466934 := advance c201004 1000 (by decide) (by decide +kernel)
private def c203004 : Checkpoint 203004 468671896413088737139736122874 323555880322756120320742777199 := advance c202004 1000 (by decide) (by decide +kernel)
private def c204004 : Checkpoint 204004 468702710102684451693596102784 322810072497384918347694334846 := advance c203004 1000 (by decide) (by decide +kernel)
private def c205004 : Checkpoint 205004 468729734762092323379379664509 322067770182161547205098932122 := advance c204004 1000 (by decide) (by decide +kernel)
private def c206004 : Checkpoint 206004 468753024286718551716083802843 321328957567307842743881582382 := advance c205004 1000 (by decide) (by decide +kernel)
private def c207004 : Checkpoint 207004 468772631712363957334956073104 320593618813817658213587364813 := advance c206004 1000 (by decide) (by decide +kernel)
private def c208004 : Checkpoint 208004 468788609231664936030874433972 319861738058123219634077133147 := advance c207004 1000 (by decide) (by decide +kernel)
private def c209004 : Checkpoint 209004 468801008210162072225993143775 319133299416571621805427085299 := advance c208004 1000 (by decide) (by decide +kernel)
private def c210004 : Checkpoint 210004 468809879202006186457659039913 318408286989718656275977298161 := advance c209004 1000 (by decide) (by decide +kernel)
private def c211004 : Checkpoint 211004 468815271965311299940565822860 317686684866446877708925629065 := advance c210004 1000 (by decide) (by decide +kernel)
private def c212004 : Checkpoint 212004 468817235477163717401292269222 316968477127914542339336472596 := advance c211004 1000 (by decide) (by decide +kernel)
private def c213004 : Checkpoint 213004 468815817948296156886272154622 316253647851341791037291046570 := advance c212004 1000 (by decide) (by decide +kernel)
private def c214004 : Checkpoint 214004 468811066837435591760477278744 315542181113640199358307025419 := advance c213004 1000 (by decide) (by decide +kernel)
private def c215004 : Checkpoint 215004 468803028865333215315771242112 314834060994891577364568003380 := advance c214004 1000 (by decide) (by decide +kernel)
private def c216004 : Checkpoint 216004 468791750028484691980053668850 314129271581681672460298539804 := advance c215004 1000 (by decide) (by decide +kernel)
private def c217004 : Checkpoint 217004 468777275612548620758392670253 313427796970294208545749244626 := advance c216004 1000 (by decide) (by decide +kernel)
private def c218004 : Checkpoint 218004 468759650205470905954633946486 312729621269770484023000793356 := advance c217004 1000 (by decide) (by decide +kernel)
private def c219004 : Checkpoint 219004 468738917710322507137142748477 312034728604839549170592267009 := advance c218004 1000 (by decide) (by decide +kernel)
private def c220004 : Checkpoint 220004 468715121357857824456937086718 311343103118723789750307384484 := advance c219004 1000 (by decide) (by decide +kernel)
private def c221004 : Checkpoint 221004 468688303718800766542501706170 310654728975824558044786617331 := advance c220004 1000 (by decide) (by decide +kernel)
private def c222004 : Checkpoint 222004 468658506715865346035029749965 309969590364292314493453972080 := advance c221004 1000 (by decide) (by decide +kernel)
private def c223004 : Checkpoint 223004 468625771635517452152306981545 309287671498485572358105877426 := advance c222004 1000 (by decide) (by decide +kernel)
private def c224004 : Checkpoint 224004 468590139139484260249705717542 308608956621322774086146763325 := advance c223004 1000 (by decide) (by decide +kernel)
private def c225004 : Checkpoint 225004 468551649276017554962375530461 307933430006531070941968052837 := advance c224004 1000 (by decide) (by decide +kernel)
private def c226004 : Checkpoint 226004 468510341490917065951734699940 307261075960795826753019411565 := advance c225004 1000 (by decide) (by decide +kernel)
private def c227004 : Checkpoint 227004 468466254638319743337908296191 306591878825814521988202703118 := advance c226004 1000 (by decide) (by decide +kernel)
private def c228004 : Checkpoint 228004 468419426991260733381719848101 305925822980258595586940850410 := advance c227004 1000 (by decide) (by decide +kernel)
private def c229004 : Checkpoint 229004 468369896252011653696566267779 305262892841646628734702612806 := advance c228004 1000 (by decide) (by decide +kernel)
private def c230004 : Checkpoint 230004 468317699562201611040476751714 304603072868132146893794484039 := advance c229004 1000 (by decide) (by decide +kernel)
private def c231004 : Checkpoint 231004 468262873512726253387215711337 303946347560209193616989454821 := advance c230004 1000 (by decide) (by decide +kernel)
private def c232004 : Checkpoint 232004 468205454153450001334352284448 303292701462338711776846119070 := advance c231004 1000 (by decide) (by decide +kernel)
private def c233004 : Checkpoint 233004 468145477002706461814008117911 302642119164498654626314769950 := advance c232004 1000 (by decide) (by decide +kernel)
private def c234004 : Checkpoint 234004 468082977056601889372788096723 301994585303660640366997317267 := advance c233004 1000 (by decide) (by decide +kernel)
private def c235004 : Checkpoint 235004 468017988798126426831282544464 301350084565195859449948817385 := advance c234004 1000 (by decide) (by decide +kernel)
private def c236004 : Checkpoint 236004 467950546206077727776167509113 300708601684212843488608225669 := advance c235004 1000 (by decide) (by decide +kernel)
private def c237004 : Checkpoint 237004 467880682763801437940338338310 300070121446829608251029108379 := advance c236004 1000 (by decide) (by decide +kernel)
private def c238004 : Checkpoint 238004 467808431467752890954846047805 299434628691382590553622896822 := advance c237004 1000 (by decide) (by decide +kernel)
private def c239004 : Checkpoint 239004 467733824835884256081755330936 298802108309574709843190060710 := advance c238004 1000 (by decide) (by decide +kernel)
private def c240004 : Checkpoint 240004 467656894915861261235234779326 298172545247564799677283318583 := advance c239004 1000 (by decide) (by decide +kernel)
private def c241004 : Checkpoint 241004 467577673293113503749601505699 297545924507000572050884371710 := advance c240004 1000 (by decide) (by decide +kernel)
private def c242004 : Checkpoint 242004 467496191098722253842421715279 296922231145997198432394820665 := advance c241004 1000 (by decide) (by decide +kernel)
private def c243004 : Checkpoint 243004 467412479017149551437061727299 296301450280063515332596315743 := advance c242004 1000 (by decide) (by decide +kernel)
private def c244004 : Checkpoint 244004 467326567293812295845269361827 295683567082977789110923968717 := advance c243004 1000 (by decide) (by decide +kernel)
private def c245004 : Checkpoint 245004 467238485742504929663297224258 295068566787614904404086758210 := advance c244004 1000 (by decide) (by decide +kernel)
private def c246004 : Checkpoint 246004 467148263752674223005334382855 294456434686726772928027110032 := advance c245004 1000 (by decide) (by decide +kernel)
private def c247004 : Checkpoint 247004 467055930296549571789746622227 293847156133677694345757516434 := advance c246004 1000 (by decide) (by decide +kernel)
private def c248004 : Checkpoint 248004 466961513936132134114432371866 293240716543136338305875295310 := advance c247004 1000 (by decide) (by decide +kernel)
private def c249004 : Checkpoint 249004 466865042830046041718381854140 292637101391725956539252963264 := advance c248004 1000 (by decide) (by decide +kernel)
private def c250004 : Checkpoint 250004 466766544740254839041359260056 292036296218634375958616906656 := advance c249004 1000 (by decide) (by decide +kernel)
private def c251004 : Checkpoint 251004 466666047038646220379645611085 291438286626185267945712552994 := advance c250004 1000 (by decide) (by decide +kernel)
private def c252004 : Checkpoint 252004 466563576713488056013055178159 290843058280372135345733204522 := advance c251004 1000 (by decide) (by decide +kernel)
private def c253004 : Checkpoint 253004 466459160375758620869868061727 290250596911356407034672453612 := advance c252004 1000 (by decide) (by decide +kernel)
private def c254004 : Checkpoint 254004 466352824265353864227520319317 289660888313930980201868969380 := advance c253004 1000 (by decide) (by decide +kernel)
private def c255004 : Checkpoint 255004 466244594257174486046089173925 289073918347950502620315111180 := advance c254004 1000 (by decide) (by decide +kernel)
private def c256004 : Checkpoint 256004 466134495867095514729547087284 288489672938729641087651969163 := advance c255004 1000 (by decide) (by decide +kernel)
private def c257004 : Checkpoint 257004 466022554257821012339596694489 287908138077410537840664165223 := advance c256004 1000 (by decide) (by decide +kernel)
private def c258004 : Checkpoint 258004 465908794244626466484128300433 287329299821300614008002396794 := advance c257004 1000 (by decide) (by decide +kernel)
private def c259004 : Checkpoint 259004 465793240300991363204692304468 286753144294181838005141623427 := advance c258004 1000 (by decide) (by decide +kernel)
private def c260004 : Checkpoint 260004 465675916564124372134735766527 286179657686592537130296772931 := advance c259004 1000 (by decide) (by decide +kernel)
private def c261004 : Checkpoint 261004 465556846840383513934675524329 285608826256082792430838829078 := advance c260004 1000 (by decide) (by decide +kernel)
private def c262004 : Checkpoint 262004 465436054610593620475127387432 285040636327444420119841926474 := advance c261004 1000 (by decide) (by decide +kernel)
private def c263004 : Checkpoint 263004 465313563035263340381662499830 284475074292916507377281542897 := advance c262004 1000 (by decide) (by decide +kernel)
private def c264004 : Checkpoint 264004 465189394959703886321050003416 283912126612367436217898798636 := advance c263004 1000 (by decide) (by decide +kernel)
private def c265004 : Checkpoint 265004 465063572919051665749584557288 283351779813454296197817613130 := advance c264004 1000 (by decide) (by decide +kernel)
private def c266004 : Checkpoint 266004 464936119143196883710019972621 282794020491760555016692607923 := advance c265004 1000 (by decide) (by decide +kernel)
private def c267004 : Checkpoint 267004 464807055561620154607721838439 282238835310912825505498159011 := advance c266004 1000 (by decide) (by decide +kernel)
private def c268004 : Checkpoint 268004 464676403808139109673391119451 281686211002677538027956801052 := advance c267004 1000 (by decide) (by decide +kernel)
private def c269004 : Checkpoint 269004 464544185225566937985110471850 281136134367038298923770784637 := advance c268004 1000 (by decide) (by decide +kernel)
private def c270004 : Checkpoint 270004 464410420870284751434017124614 280588592272254688243715690285 := advance c269004 1000 (by decide) (by decide +kernel)
private def c271004 : Checkpoint 271004 464275131516729617834526931055 280043571654903223631384823740 := advance c270004 1000 (by decide) (by decide +kernel)
private def c272004 : Checkpoint 272004 464138337661800061462012802878 279501059519901191756624231901 := advance c271004 1000 (by decide) (by decide +kernel)
private def c273004 : Checkpoint 273004 464000059529180786609789524351 278961042940514024165669750566 := advance c272004 1000 (by decide) (by decide +kernel)
private def c274004 : Checkpoint 274004 463860317073588337256063563122 278423509058346870748335679995 := advance c273004 1000 (by decide) (by decide +kernel)
private def c275004 : Checkpoint 275004 463719129984939364584287981728 277888445083321001200340092514 := advance c274004 1000 (by decide) (by decide +kernel)
private def c276004 : Checkpoint 276004 463576517692443133872421152909 277355838293635642847339809964 := advance c275004 1000 (by decide) (by decide +kernel)
private def c277004 : Checkpoint 277004 463432499368619863124368681900 276825676035715841966112025953 := advance c276004 1000 (by decide) (by decide +kernel)
private def c278004 : Checkpoint 278004 463287093933246447727937648569 276297945724146915258396245629 := advance c277004 1000 (by decide) (by decide +kernel)
private def c279004 : Checkpoint 279004 463140320057231088356560568526 275772634841596038376198287801 := advance c278004 1000 (by decide) (by decide +kernel)
private def c280004 : Checkpoint 280004 462992196166418303256487807328 275249730938721499336968455218 := advance c279004 1000 (by decide) (by decide +kernel)
private def c281004 : Checkpoint 281004 462842740445325770947724634898 274729221634070126277174637721 := advance c280004 1000 (by decide) (by decide +kernel)
private def c282004 : Checkpoint 282004 462691970840814415187279407540 274211094613963381248594102651 := advance c281004 1000 (by decide) (by decide +kernel)
private def c283004 : Checkpoint 283004 462539905065693110769789315338 273695337632372594639318068726 := advance c282004 1000 (by decide) (by decide +kernel)
private def c284004 : Checkpoint 284004 462386560602259356346684272193 273181938510783798278109771554 := advance c283004 1000 (by decide) (by decide +kernel)
private def c285004 : Checkpoint 285004 462231954705777228904979031386 272670885138052599334385170618 := advance c284004 1000 (by decide) (by decide +kernel)
private def c286004 : Checkpoint 286004 462076104407893903835616366760 272162165470249521735560428767 := advance c285004 1000 (by decide) (by decide +kernel)
private def c287004 : Checkpoint 287004 461919026519995994614885952684 271655767530496226968519851687 := advance c286004 1000 (by decide) (by decide +kernel)
private def c288004 : Checkpoint 288004 461760737636506936997450368712 271151679408793011792979243356 := advance c287004 1000 (by decide) (by decide +kernel)
private def c289004 : Checkpoint 289004 461601254138126614253300898376 270649889261837966552786139794 := advance c288004 1000 (by decide) (by decide +kernel)
private def c290004 : Checkpoint 290004 461440592195014392351638739567 270150385312838164408668779009 := advance c289004 1000 (by decide) (by decide +kernel)
private def c291004 : Checkpoint 291004 461278767769916707081022206154 269653155851313238915273841625 := advance c290004 1000 (by decide) (by decide +kernel)
private def c292004 : Checkpoint 292004 461115796621240318876597040513 269158189232891694909839514443 := advance c291004 1000 (by decide) (by decide +kernel)
private def c293004 : Checkpoint 293004 460951694306072325581940939237 268665473879100285653495198790 := advance c292004 1000 (by decide) (by decide +kernel)
private def c294004 : Checkpoint 294004 460786476183147998485734911036 268174998277146777553535336149 := advance c293004 1000 (by decide) (by decide +kernel)
private def c295004 : Checkpoint 295004 460620157415767482723456168092 267686750979696412581243723226 := advance c294004 1000 (by decide) (by decide +kernel)
private def c296004 : Checkpoint 296004 460452752974662379503485384484 267200720604642367670672034350 := advance c295004 1000 (by decide) (by decide +kernel)
private def c297004 : Checkpoint 297004 460284277640813204587913525735 266716895834870499925469224672 := advance c296004 1000 (by decide) (by decide +kernel)
private def c298004 : Checkpoint 298004 460114746008218695013941934041 266235265418018656360203799616 := advance c297004 1000 (by decide) (by decide +kernel)
private def c299004 : Checkpoint 299004 459944172486617914165641170349 265755818166230817146903999904 := advance c298004 1000 (by decide) (by decide +kernel)
private def c300004 : Checkpoint 300004 459772571304166083982024180450 265278542955906331914525771186 := advance c299004 1000 (by decide) (by decide +kernel)
private def c301004 : Checkpoint 301004 459599956510065052300443249598 264803428727444499546968392916 := advance c300004 1000 (by decide) (by decide +kernel)
private def c302004 : Checkpoint 302004 459426341977149283069257775655 264330464484984733132757331906 := advance c301004 1000 (by decide) (by decide +kernel)
private def c303004 : Checkpoint 303004 459251741404428237406019404493 263859639296142543225691241908 := advance c302004 1000 (by decide) (by decide +kernel)
private def c304004 : Checkpoint 304004 459076168319585994213004003072 263390942291741564370099690490 := advance c303004 1000 (by decide) (by decide +kernel)
private def c305004 : Checkpoint 305004 458899636081438940277136258974 262924362665541841916765319344 := advance c304004 1000 (by decide) (by decide +kernel)
private def c306004 : Checkpoint 306004 458722157882352341462966669008 262459889673964588496288992067 := advance c305004 1000 (by decide) (by decide +kernel)
private def c307004 : Checkpoint 307004 458543746750616588742537235338 261997512635813612116339605162 := advance c306004 1000 (by decide) (by decide +kernel)
private def c308004 : Checkpoint 308004 458364415552783895382263715694 261537220931993610698798317519 := advance c307004 1000 (by decide) (by decide +kernel)
private def c309004 : Checkpoint 309004 458184176995966204612295904659 261079004005225520963579222181 := advance c308004 1000 (by decide) (by decide +kernel)
private def c310004 : Checkpoint 310004 458003043630095050526482772664 260622851359759102889503718794 := advance c309004 1000 (by decide) (by decide +kernel)
private def c311004 : Checkpoint 311004 457821027850144098789706620195 260168752561082934530949892000 := advance c310004 1000 (by decide) (by decide +kernel)
private def c312004 : Checkpoint 312004 457638141898315077952939213521 259716697235631985734312031343 := advance c311004 1000 (by decide) (by decide +kernel)
private def c313004 : Checkpoint 313004 457454397866187796784220868416 259266675070492933273093677381 := advance c312004 1000 (by decide) (by decide +kernel)
private def c314004 : Checkpoint 314004 457269807696834928005495943055 258818675813107374097497565160 := advance c313004 1000 (by decide) (by decide +kernel)
private def c315004 : Checkpoint 315004 457084383186902224170787823554 258372689270973087766707031974 := advance c314004 1000 (by decide) (by decide +kernel)
private def c316004 : Checkpoint 316004 456898135988654817120793298365 257928705311343493692967384971 := advance c315004 1000 (by decide) (by decide +kernel)
private def c317004 : Checkpoint 317004 456711077611990238493138161709 257486713860925443569606280360 := advance c316004 1000 (by decide) (by decide +kernel)
private def c318004 : Checkpoint 318004 456523219426418785147059546312 257046704905575484274046323258 := advance c317004 1000 (by decide) (by decide +kernel)
private def c319004 : Checkpoint 319004 456334572663011840067232194896 256608668489994721625651998063 := advance c318004 1000 (by decide) (by decide +kernel)
private def c320004 : Checkpoint 320004 456145148416318746335163113706 256172594717422410631123448704 := advance c319004 1000 (by decide) (by decide +kernel)
private def c321004 : Checkpoint 321004 455954957646252819089622127300 255738473749328393261515727439 := advance c320004 1000 (by decide) (by decide +kernel)
private def c322004 : Checkpoint 322004 455764011179947068031779913666 255306295805104500369437650948 := advance c321004 1000 (by decide) (by decide +kernel)
private def c323004 : Checkpoint 323004 455572319713580190958152366405 254876051161755030067375068174 := advance c322004 1000 (by decide) (by decide +kernel)
private def c324004 : Checkpoint 324004 455379893814173387017392424915 254447730153586410743379624766 := advance c323004 1000 (by decide) (by decide +kernel)
private def c325004 : Checkpoint 325004 455186743921358526877942039538 254021323171896152883734261673 := advance c324004 1000 (by decide) (by decide +kernel)
private def c326004 : Checkpoint 326004 454992880349118205755287289387 253596820664661189998990069626 := advance c325004 1000 (by decide) (by decide +kernel)
private def c327004 : Checkpoint 327004 454798313287498194272987099631 253174213136225705205469791607 := advance c326004 1000 (by decide) (by decide +kernel)
private def c328004 : Checkpoint 328004 454603052804292791413910905367 252753491146988536394613807568 := advance c327004 1000 (by decide) (by decide +kernel)
private def c329004 : Checkpoint 329004 454407108846703573350559214527 252334645313090249423220052876 := advance c328004 1000 (by decide) (by decide +kernel)
private def c330004 : Checkpoint 330004 454210491242972021719479335475 251917666306099965374662158764 := advance c329004 1000 (by decide) (by decide +kernel)
private def c331004 : Checkpoint 331004 454013209703986504918336429740 251502544852702024670663783963 := advance c330004 1000 (by decide) (by decide +kernel)
private def c332004 : Checkpoint 332004 453815273824864076249045611830 251089271734382567651401499933 := advance c331004 1000 (by decide) (by decide +kernel)
private def c333004 : Checkpoint 333004 453616693086507543200574825947 250677837787116108184974772046 := advance c332004 1000 (by decide) (by decide +kernel)
private def c334004 : Checkpoint 334004 453417476857138252854818867027 250268233901052173912116990019 := advance c333004 1000 (by decide) (by decide +kernel)
private def c335004 : Checkpoint 335004 453217634393805029302712621774 249860451020202083875045308882 := advance c334004 1000 (by decide) (by decide +kernel)
private def c336004 : Checkpoint 336004 453017174843869690070044123145 249454480142125931517295684550 := advance c335004 1000 (by decide) (by decide +kernel)
private def c337004 : Checkpoint 337004 452816107246469559867945578457 249050312317619838371112309253 := advance c336004 1000 (by decide) (by decide +kernel)
private def c338004 : Checkpoint 338004 452614440533957391496631237795 248647938650403541167415882626 := advance c337004 1000 (by decide) (by decide +kernel)
private def c339004 : Checkpoint 339004 452412183533319095437606278546 248247350296808372607625879913 := advance c338004 1000 (by decide) (by decide +kernel)
private def c340004 : Checkpoint 340004 452209344967569671564421277361 247848538465465693623822332732 := advance c339004 1000 (by decide) (by decide +kernel)
private def c341004 : Checkpoint 341004 452005933457127728480357634363 247451494416995832621164145248 := advance c340004 1000 (by decide) (by decide +kernel)
private def c342004 : Checkpoint 342004 451801957521168968248596577756 247056209463697584941489013282 := advance c341004 1000 (by decide) (by decide +kernel)
private def c343004 : Checkpoint 343004 451597425578959006711971016503 246662674969238323607050450776 := advance c342004 1000 (by decide) (by decide +kernel)
private def c344004 : Checkpoint 344004 451392345951165892200971455587 246270882348344770295933324114 := advance c343004 1000 (by decide) (by decide +kernel)
private def c345004 : Checkpoint 345004 451186726861152678196039727323 245880823066494473463447787728 := advance c344004 1000 (by decide) (by decide +kernel)
private def c346004 : Checkpoint 346004 450980576436250398439218492535 245492488639608038554430801133 := advance c345004 1000 (by decide) (by decide +kernel)
private def c347004 : Checkpoint 347004 450773902709011786076923740281 245105870633742153347660837494 := advance c346004 1000 (by decide) (by decide +kernel)
private def c348004 : Checkpoint 348004 450566713618446071656074284134 244720960664783449633366679234 := advance c347004 1000 (by decide) (by decide +kernel)
private def c349004 : Checkpoint 349004 450359017011235188186254714689 244337750398143240646009724618 := advance c348004 1000 (by decide) (by decide +kernel)
private def c350004 : Checkpoint 350004 450150820642931705017317273880 243956231548453171955135476313 := advance c349004 1000 (by decide) (by decide +kernel)
private def c351004 : Checkpoint 351004 449942132179138805961254146752 243576395879261821855185927259 := advance c350004 1000 (by decide) (by decide +kernel)
private def c352004 : Checkpoint 352004 449732959196672620905801900624 243198235202732285688867685351 := advance c351004 1000 (by decide) (by decide +kernel)
private def c353004 : Checkpoint 353004 449523309184707214121675282113 242821741379340776986171071611 := advance c352004 1000 (by decide) (by decide +kernel)
private def c354004 : Checkpoint 354004 449313189545902526552260471207 242446906317576276800683956049 := advance c353004 1000 (by decide) (by decide +kernel)
private def c355004 : Checkpoint 355004 449102607597515563590808806559 242073721973641261174750175696 := advance c354004 1000 (by decide) (by decide +kernel)
private def c356004 : Checkpoint 356004 448891570572495114192527439764 241702180351153535263651914004 := advance c355004 1000 (by decide) (by decide +kernel)
private def c357004 : Checkpoint 357004 448680085620560281634413239952 241332273500849201294768824959 := advance c356004 1000 (by decide) (by decide +kernel)
private def c358004 : Checkpoint 358004 448468159809263100821251416939 240963993520286786229056972386 := advance c357004 1000 (by decide) (by decide +kernel)
private def c359004 : Checkpoint 359004 448255800125035511739010256623 240597332553552553727721608014 := advance c358004 1000 (by decide) (by decide +kernel)
private def c360004 : Checkpoint 360004 448043013474220953474093930279 240232282790967023805202207273 := advance c359004 1000 (by decide) (by decide +kernel)
private def c361004 : Checkpoint 361004 447829806684090838145826575915 239868836468792722369166090500 := advance c360004 1000 (by decide) (by decide +kernel)
private def c362004 : Checkpoint 362004 447616186503846159137464828510 239506985868943181707784101763 := advance c361004 1000 (by decide) (by decide +kernel)
private def c363004 : Checkpoint 363004 447402159605604483155374743323 239146723318693211882847988969 := advance c362004 1000 (by decide) (by decide +kernel)
private def c364004 : Checkpoint 364004 447187732585372570894232639424 238788041190390461923036668753 := advance c363004 1000 (by decide) (by decide +kernel)
private def c365004 : Checkpoint 365004 446972911964004866435753861558 238430931901168288683640884341 := advance c364004 1000 (by decide) (by decide +kernel)
private def c366004 : Checkpoint 366004 446757704188148090957119051425 238075387912659950246145959430 := advance c365004 1000 (by decide) (by decide +kernel)
private def c367004 : Checkpoint 367004 446542115631172171870616816776 237721401730714139772121800167 := advance c366004 1000 (by decide) (by decide +kernel)
private def c368004 : Checkpoint 368004 446326152594087734155777854084 237368965905111874799786373848 := advance c367004 1000 (by decide) (by decide +kernel)
private def c369004 : Checkpoint 369004 446109821306450376377220652304 237018073029284756077337692747 := advance c368004 1000 (by decide) (by decide +kernel)
private def c370004 : Checkpoint 370004 445893127927251949703402136158 236668715740034609163668449898 := advance c369004 1000 (by decide) (by decide +kernel)
private def c371004 : Checkpoint 371004 445676078545799054151362854504 236320886717254521193398812261 := advance c370004 1000 (by decide) (by decide +kernel)
private def c372004 : Checkpoint 372004 445458679182578962278324494335 235974578683651284398330587668 := advance c371004 1000 (by decide) (by decide +kernel)
private def c373004 : Checkpoint 373004 445240935790113176620639049116 235629784404469257200515252153 := advance c372004 1000 (by decide) (by decide +kernel)
private def c374004 : Checkpoint 374004 445022854253798823342156413810 235286496687215652942244405701 := advance c373004 1000 (by decide) (by decide +kernel)
private def c375004 : Checkpoint 375004 444804440392738080795672688509 234944708381387265594548393183 := advance c374004 1000 (by decide) (by decide +kernel)
private def c376004 : Checkpoint 376004 444585699960555838020895494651 234604412378198641087389402180 := advance c375004 1000 (by decide) (by decide +kernel)
private def c377004 : Checkpoint 377004 444366638646205774598512521370 234265601610311702230848753029 := advance c376004 1000 (by decide) (by decide +kernel)
private def c378004 : Checkpoint 378004 444147262074765049750718347434 233928269051566834546449932569 := advance c377004 1000 (by decide) (by decide +kernel)
private def c379004 : Checkpoint 379004 443927575808217785122229723260 233592407716715439700570106801 := advance c378004 1000 (by decide) (by decide +kernel)
private def c380004 : Checkpoint 380004 443707585346227522290731510667 233258010661153962626938748386 := advance c379004 1000 (by decide) (by decide +kernel)
private def c381004 : Checkpoint 381004 443487296126898832740216899437 232925070980659397841791643609 := advance c380004 1000 (by decide) (by decide +kernel)
private def c382004 : Checkpoint 382004 443266713527528254783229709953 232593581811126279892653759711 := advance c381004 1000 (by decide) (by decide +kernel)
private def c383004 : Checkpoint 383004 443045842865344728737036622488 232263536328305162339299199508 := advance c382004 1000 (by decide) (by decide +kernel)
private def c384004 : Checkpoint 384004 442824689398239698542744745858 231934927747542589142536046607 := advance c383004 1000 (by decide) (by decide +kernel)
private def c385004 : Checkpoint 385004 442603258325487044963864326957 231607749323522561832464245100 := advance c384004 1000 (by decide) (by decide +kernel)
private def c386004 : Checkpoint 386004 442381554788453012510363445568 231281994350009505342151656128 := advance c385004 1000 (by decide) (by decide +kernel)
private def c387004 : Checkpoint 387004 442159583871296289304472636967 230957656159592734924682279265 := advance c386004 1000 (by decide) (by decide +kernel)
private def c388004 : Checkpoint 388004 441937350601658396234008551185 230634728123432426120685160710 := advance c387004 1000 (by decide) (by decide +kernel)
private def c389004 : Checkpoint 389004 441714859951344538926466677182 230313203651007089309204619051 := advance c388004 1000 (by decide) (by decide +kernel)
private def c390004 : Checkpoint 390004 441492116836995073321286289142 229993076189862549956591430868 := advance c389004 1000 (by decide) (by decide +kernel)
private def c391004 : Checkpoint 391004 441269126120747732917250455700 229674339225362435275466734809 := advance c390004 1000 (by decide) (by decide +kernel)
private def c392004 : Checkpoint 392004 441045892610890763125715573744 229356986280440167618238150118 := advance c391004 1000 (by decide) (by decide +kernel)
private def c393004 : Checkpoint 393004 440822421062507105567064038744 229041010915352464556649264836 := advance c392004 1000 (by decide) (by decide +kernel)
private def c394004 : Checkpoint 394004 440598716178109772606265332355 228726406727434345239952791814 := advance c393004 1000 (by decide) (by decide +kernel)
private def c395004 : Checkpoint 395004 440374782608268549932568614804 228413167350855642279062649043 := advance c394004 1000 (by decide) (by decide +kernel)
private def c396004 : Checkpoint 396004 440150624952228162547015325704 228101286456379018072023604591 := advance c395004 1000 (by decide) (by decide +kernel)
private def c397004 : Checkpoint 397004 439926247758518037128561924350 227790757751119484166915368722 := advance c396004 1000 (by decide) (by decide +kernel)
private def c398004 : Checkpoint 398004 439701655525553791404075747463 227481574978305421951470913345 := advance c397004 1000 (by decide) (by decide +kernel)
private def c399004 : Checkpoint 399004 439476852702230578848271747209 227173731917041102663839085059 := advance c398004 1000 (by decide) (by decide +kernel)
private def c400004 : Checkpoint 400004 439251843688508414785780350725 226867222382070704435674499104 := advance c399004 1000 (by decide) (by decide +kernel)
private def c401004 : Checkpoint 401004 439026632835989607757986989272 226562040223543823806720611990 := advance c400004 1000 (by decide) (by decide +kernel)
private def c402004 : Checkpoint 402004 438801224448488417851095853802 226258179326782478888903843556 := advance c401004 1000 (by decide) (by decide +kernel)
private def c403004 : Checkpoint 403004 438575622782593061558101140630 225955633612049601107328064548 := advance c402004 1000 (by decide) (by decide +kernel)
private def c404004 : Checkpoint 404004 438349832048220180665077967757 225654397034319012205111067468 := advance c403004 1000 (by decide) (by decide +kernel)
private def c405004 : Checkpoint 405004 438123856409161890610533715557 225354463583046882968409800105 := advance c404004 1000 (by decide) (by decide +kernel)
private def c406004 : Checkpoint 406004 437897699983625521764611581110 225055827281944669906921443567 := advance c405004 1000 (by decide) (by decide +kernel)
private def c407004 : Checkpoint 407004 437671366844766165111855252846 224758482188753525913315089603 := advance c406004 1000 (by decide) (by decide +kernel)
private def c408004 : Checkpoint 408004 437444861021212131896190699945 224462422395020180722145674336 := advance c407004 1000 (by decide) (by decide +kernel)
private def c409004 : Checkpoint 409004 437218186497583434898941768317 224167642025874286794539137201 := advance c408004 1000 (by decide) (by decide +kernel)
private def c410004 : Checkpoint 410004 436991347215003397169273462047 223874135239807226069035696779 := advance c409004 1000 (by decide) (by decide +kernel)
private def c411004 : Checkpoint 411004 436764347071603492210672093968 223581896228452372841165607153 := advance c410004 1000 (by decide) (by decide +kernel)
private def c412004 : Checkpoint 412004 436537189923021517846164804620 223290919216366807864346173925 := advance c411004 1000 (by decide) (by decide +kernel)
private def c413004 : Checkpoint 413004 436309879582893204238209971169 223001198460814478602275748631 := advance c412004 1000 (by decide) (by decide +kernel)
private def c414004 : Checkpoint 414004 436082419823337354825829796278 222712728251550800407913391502 := advance c413004 1000 (by decide) (by decide +kernel)
private def c415004 : Checkpoint 415004 435854814375434617260898827481 222425502910608693256133080316 := advance c414004 1000 (by decide) (by decide +kernel)
private def c416004 : Checkpoint 416004 435627066929699979776855728437 222139516792086048515997360818 := advance c415004 1000 (by decide) (by decide +kernel)
private def c417004 : Checkpoint 417004 435399181136549086805794785495 221854764281934620114082994611 := advance c416004 1000 (by decide) (by decide +kernel)
private def c418004 : Checkpoint 418004 435171160606758466073258511808 221571239797750334312193244060 := advance c417004 1000 (by decide) (by decide +kernel)
private def c419004 : Checkpoint 419004 434943008911919757843448695832 221288937788565012200897469747 := advance c418004 1000 (by decide) (by decide +kernel)
private def c420004 : Checkpoint 420004 434714729584888035460370586403 221007852734639498894444770295 := advance c419004 1000 (by decide) (by decide +kernel)
private def c421004 : Checkpoint 421004 434486326120224304832008372287 220727979147258193302506862304 := advance c420004 1000 (by decide) (by decide +kernel)
private def c422004 : Checkpoint 422004 434257801974632269034398588575 220449311568524972249724806759 := advance c421004 1000 (by decide) (by decide +kernel)
private def c423004 : Checkpoint 423004 434029160567389442769834240608 220171844571160502614979000744 := advance c422004 1000 (by decide) (by decide +kernel)
private def c424004 : Checkpoint 424004 433800405280772699997822386543 219895572758300935068492289570 := advance c423004 1000 (by decide) (by decide +kernel)
private def c425004 : Checkpoint 425004 433571539460478336668270874572 219620490763297972896137898405 := advance c424004 1000 (by decide) (by decide +kernel)
private def c426004 : Checkpoint 426004 433342566416036729123147878597 219346593249520309316488324101 := advance c425004 1000 (by decide) (by decide +kernel)
private def c427004 : Checkpoint 427004 433113489421221667395005264597 219073874910156426617044777210 := advance c426004 1000 (by decide) (by decide +kernel)
private def c428004 : Checkpoint 428004 432884311714454441317760246377 218802330468018750361570702610 := advance c427004 1000 (by decide) (by decide +kernel)
private def c429004 : Checkpoint 429004 432655036499202756076477704290 218531954675349151850363719523 := advance c428004 1000 (by decide) (by decide +kernel)
private def c430004 : Checkpoint 430004 432425666944374552558087949542 218262742313625791949489147600 := advance c429004 1000 (by decide) (by decide +kernel)
private def c431004 : Checkpoint 431004 432196206184706806623522901270 217994688193371299343320872200 := advance c430004 1000 (by decide) (by decide +kernel)
private def c432004 : Checkpoint 432004 431966657321149380203179882171 217727787153962276207051857761 := advance c431004 1000 (by decide) (by decide +kernel)
private def c433004 : Checkpoint 433004 431737023421243995921459533655 217462034063440124242011675715 := advance c432004 1000 (by decide) (by decide +kernel)
private def c434004 : Checkpoint 434004 431507307519498405781916177262 217197423818323183966530696842 := advance c433004 1000 (by decide) (by decide +kernel)
private def c435004 : Checkpoint 435004 431277512617755823291858980544 216933951343420180108592891081 := advance c434004 1000 (by decide) (by decide +kernel)
private def c436004 : Checkpoint 436004 431047641685559687273614166657 216671611591644965903498197651 := advance c435004 1000 (by decide) (by decide +kernel)
private def c437004 : Checkpoint 437004 430817697660513824498675595206 216410399543832559060091706618 := advance c436004 1000 (by decide) (by decide +kernel)
private def c438004 : Checkpoint 438004 430587683448638077190216178235 216150310208556462122694655848 := advance c437004 1000 (by decide) (by decide +kernel)
private def c439004 : Checkpoint 439004 430357601924719460368497877619 215891338621947259922579300171 := advance c438004 1000 (by decide) (by decide +kernel)
private def c440004 : Checkpoint 440004 430127455932658912962204581097 215633479847512486782557332250 := advance c439004 1000 (by decide) (by decide +kernel)
private def c441004 : Checkpoint 441004 429897248285813705576239912052 215376728975957756110894365218 := advance c440004 1000 (by decide) (by decide +kernel)
private def c442004 : Checkpoint 442004 429666981767335566792699529536 215121081125009144996218929659 := advance c441004 1000 (by decide) (by decide +kernel)
private def c443004 : Checkpoint 443004 429436659130504588886171650528 214866531439236826393264550833 := advance c442004 1000 (by decide) (by decide +kernel)
private def c444004 : Checkpoint 444004 429206283099058972856875498996 214613075089879941470071880893 := advance c443004 1000 (by decide) (by decide +kernel)
private def c445004 : Checkpoint 445004 428975856367520671725058273962 214360707274672704670591657574 := advance c444004 1000 (by decide) (by decide +kernel)
private def c446004 : Checkpoint 446004 428745381601516990087187957807 214109423217671734032378416011 := advance c445004 1000 (by decide) (by decide +kernel)
private def c447004 : Checkpoint 447004 428514861438098197008460398606 213859218169084599287162153059 := advance c446004 1000 (by decide) (by decide +kernel)
private def c448004 : Checkpoint 448004 428284298486051208416650580203 213610087405099580262445998956 := advance c447004 1000 (by decide) (by decide +kernel)
private def c449004 : Checkpoint 449004 428053695326209394269053083816 213362026227716628094820473733 := advance c448004 1000 (by decide) (by decide +kernel)
private def c450004 : Checkpoint 450004 427823054511758564886855780932 213115029964579521760329723436 := advance c449004 1000 (by decide) (by decide +kernel)
private def c451004 : Checkpoint 451004 427592378568539189989461033867 212869093968809212423895333522 := advance c450004 1000 (by decide) (by decide +kernel)
private def c452004 : Checkpoint 452004 427361669995344903114704134245 212624213618838348108424383827 := advance c451004 1000 (by decide) (by decide +kernel)
private def c453004 : Checkpoint 453004 427130931264217343279319995563 212380384318246971184728136060 := advance c452004 1000 (by decide) (by decide +kernel)
private def c454004 : Checkpoint 454004 426900164820737384917083294692 212137601495599381185686170249 := advance c453004 1000 (by decide) (by decide +kernel)
private def c455004 : Checkpoint 455004 426669373084312806329507681719 211895860604282155452140129472 := advance c454004 1000 (by decide) (by decide +kernel)
private def c456004 : Checkpoint 456004 426438558448462446095555849792 211655157122343320123725818501 := advance c455004 1000 (by decide) (by decide +kernel)
private def c457004 : Checkpoint 457004 426207723281096896112209679248 211415486552332663995188607433 := advance c456004 1000 (by decide) (by decide +kernel)
private def c458004 : Checkpoint 458004 425976869924795779176709708866 211176844421143187767613272420 := advance c457004 1000 (by decide) (by decide +kernel)
private def c459004 : Checkpoint 459004 425746000697081658273532936957 210939226279853681234375847207 := advance c458004 1000 (by decide) (by decide +kernel)
private def c460004 : Checkpoint 460004 425515117890690623994480100244 210702627703572420953433906837 := advance c459004 1000 (by decide) (by decide +kernel)
private def c461004 : Checkpoint 461004 425284223773839605798336271211 210467044291281980970756917488 := advance c460004 1000 (by decide) (by decide +kernel)
private def c462004 : Checkpoint 462004 425053320590490452107205343423 210232471665685149174205575122 := advance c461004 1000 (by decide) (by decide +kernel)
private def c463004 : Checkpoint 463004 424822410560610823539558440060 209998905473051941872945832296 := advance c462004 1000 (by decide) (by decide +kernel)
private def c464004 : Checkpoint 464004 424591495880431942895042283452 209766341383067709214478640839 := advance c463004 1000 (by decide) (by decide +kernel)
private def c465004 : Checkpoint 465004 424360578722703244832934873775 209534775088682324069530978327 := advance c464004 1000 (by decide) (by decide +kernel)
private def c466004 : Checkpoint 466004 424129661236943967524586082816 209304202305960447034339693228 := advance c465004 1000 (by decide) (by decide +kernel)
private def c467004 : Checkpoint 467004 423898745549691727910018361140 209074618773932860220220814936 := advance c466004 1000 (by decide) (by decide +kernel)
private def c468004 : Checkpoint 468004 423667833764748121549870715632 208846020254448862521708406532 := advance c467004 1000 (by decide) (by decide +kernel)
private def c469004 : Checkpoint 469004 423436927963421387435835008500 208618402532029719076925383154 := advance c468004 1000 (by decide) (by decide +kernel)
private def c470004 : Checkpoint 470004 423206030204766177505449459097 208391761413723157657171940790 := advance c469004 1000 (by decide) (by decide +kernel)
private def c471004 : Checkpoint 471004 422975142525820470000376332613 208166092728958904746944634668 := advance c470004 1000 (by decide) (by decide +kernel)
private def c472004 : Checkpoint 472004 422744266941839665210899743331 207941392329405254100691298338 := advance c471004 1000 (by decide) (by decide +kernel)
private def c473004 : Checkpoint 473004 422513405446527901563139993165 207717656088826660588525742449 := advance c472004 1000 (by decide) (by decide +kernel)
private def c474004 : Checkpoint 474004 422282560012266629429201661478 207494879902942352169834567524 := advance c473004 1000 (by decide) (by decide +kernel)
private def c475004 : Checkpoint 475004 422051732590340479473966467307 207273059689285952861170696903 := advance c474004 1000 (by decide) (by decide +kernel)
private def c476004 : Checkpoint 476004 421820925111160461795325311053 207052191387066109593009756363 := advance c475004 1000 (by decide) (by decide +kernel)
private def c477004 : Checkpoint 477004 421590139484484531567137220257 206832270957028115878812674062 := advance c476004 1000 (by decide) (by decide +kernel)
private def c478004 : Checkpoint 478004 421359377599635556355930215526 206613294381316525249358402832 := advance c477004 1000 (by decide) (by decide +kernel)
private def c479004 : Checkpoint 479004 421128641325716719753148031288 206395257663338747435453071097 := advance c478004 1000 (by decide) (by decide +kernel)
private def c480004 : Checkpoint 480004 420897932511824395444428356844 206178156827629620312855755184 := advance c479004 1000 (by decide) (by decide +kernel)
private def c481004 : Checkpoint 481004 420667252987258525325807438500 205961987919716950654557021840 := advance c480004 1000 (by decide) (by decide +kernel)
private def c482004 : Checkpoint 482004 420436604561730534773720513320 205746747005988016767375950394 := advance c481004 1000 (by decide) (by decide +kernel)
private def c483004 : Checkpoint 483004 420205989025568817681048937646 205532430173557026122176972138 := advance c482004 1000 (by decide) (by decide +kernel)
private def c484004 : Checkpoint 484004 419975408149921823385097562070 205319033530133521119822909810 := advance c483004 1000 (by decide) (by decide +kernel)
private def c485004 : Checkpoint 485004 419744863686958777135117578438 205106553203891726168249288174 := advance c484004 1000 (by decide) (by decide +kernel)
private def c486004 : Checkpoint 486004 419514357370068065276671497605 204894985343340829279742377279 := advance c485004 1000 (by decide) (by decide +kernel)
private def c487004 : Checkpoint 487004 419283890914053315867621899250 204684326117196191431605404560 := advance c486004 1000 (by decide) (by decide +kernel)
private def c488004 : Checkpoint 488004 419053466015327204985670868771 204474571714251476967880599643 := advance c487004 1000 (by decide) (by decide +kernel)
private def c489004 : Checkpoint 489004 418823084352103018540042227530 204265718343251698354636657252 := advance c488004 1000 (by decide) (by decide +kernel)
private def c490004 : Checkpoint 490004 418592747584583998959946220891 204057762232767168636509999430 := advance c489004 1000 (by decide) (by decide +kernel)
private def c491004 : Checkpoint 491004 418362457355150505699761463036 203850699631068354977682798264 := advance c490004 1000 (by decide) (by decide +kernel)
private def c492004 : Checkpoint 492004 418132215288545018075279559051 203644526806001626706270687578 := advance c491004 1000 (by decide) (by decide +kernel)
private def c493004 : Checkpoint 493004 417902022992055008526754483267 203439240044865891317158733713 := advance c492004 1000 (by decide) (by decide +kernel)
private def c494004 : Checkpoint 494004 417671882055693713992754624519 203234835654290111924646498933 := advance c493004 1000 (by decide) (by decide +kernel)
private def c495004 : Checkpoint 495004 417441794052378832673806075676 203031309960111699692823497018 := advance c494004 1000 (by decide) (by decide +kernel)
private def c496004 : Checkpoint 496004 417211760538109173066419382573 202828659307255774808377217548 := advance c495004 1000 (by decide) (by decide +kernel)
private def c497004 : Checkpoint 497004 416981783052139281756189129871 202626880059615289597519986830 := advance c496004 1000 (by decide) (by decide +kernel)
private def c498004 : Checkpoint 498004 416751863117152076073129351382 202425968599932007425891630129 := advance c497004 1000 (by decide) (by decide +kernel)
private def c499004 : Checkpoint 499004 416522002239429507333143046479 202225921329678331057636156736 := advance c498004 1000 (by decide) (by decide +kernel)
private def c500004 : Checkpoint 500004 416292201909021280016408565253 202026734668939974187347009793 := advance c499004 1000 (by decide) (by decide +kernel)
private def c501004 : Checkpoint 501004 416062463599911651866389016167 201828405056299469896211843662 := advance c500004 1000 (by decide) (by decide +kernel)
private def c502004 : Checkpoint 502004 415832788770184339532025037047 201630928948720509821449863706 := advance c501004 1000 (by decide) (by decide +kernel)
private def c503004 : Checkpoint 503004 415603178862185554020350272057 201434302821433107866008541525 := advance c502004 1000 (by decide) (by decide +kernel)
private def c504004 : Checkpoint 504004 415373635302685189877168800142 201238523167819582313458537761 := advance c503004 1000 (by decide) (by decide +kernel)
private def c505004 : Checkpoint 505004 415144159503036191669452692506 201043586499301350251082937861 := advance c504004 1000 (by decide) (by decide +kernel)
private def c506004 : Checkpoint 506004 414914752859332121004655950899 200849489345226528242286894000 := advance c505004 1000 (by decide) (by decide +kernel)
private def c507004 : Checkpoint 507004 414685416752562946989100357257 200656228252758333227644382026 := advance c506004 1000 (by decide) (by decide +kernel)
private def c508004 : Checkpoint 508004 414456152548769082699873219094 200463799786764277672138358755 := advance c507004 1000 (by decide) (by decide +kernel)
private def c509004 : Checkpoint 509004 414226961599193689922192456139 200272200529706153014427900106 := advance c508004 1000 (by decide) (by decide +kernel)
private def c510004 : Checkpoint 510004 413997845240433274086848606272 200081427081530795512280068725 := advance c509004 1000 (by decide) (by decide +kernel)
private def c511004 : Checkpoint 511004 413768804794586591030035579871 199891476059561628616624852433 := advance c510004 1000 (by decide) (by decide +kernel)
private def c512004 : Checkpoint 512004 413539841569401886890543561688 199702344098390976045018460312 := advance c511004 1000 (by decide) (by decide +kernel)
private def c513004 : Checkpoint 513004 413310956858422492156821261383 199514027849773139763623856547 := advance c512004 1000 (by decide) (by decide +kernel)
private def c514004 : Checkpoint 514004 413082151941130790578735338087 199326523982518237125128310806 := advance c513004 1000 (by decide) (by decide +kernel)
private def c515004 : Checkpoint 515004 412853428083090583365878501867 199139829182386791448306944031 := advance c514004 1000 (by decide) (by decide +kernel)
private def c516004 : Checkpoint 516004 412624786536087868805922369624 198953940151985070363200087807 := advance c515004 1000 (by decide) (by decide +kernel)
private def c517004 : Checkpoint 517004 412396228538270057152696034200 198768853610661166284092413685 := advance c516004 1000 (by decide) (by decide +kernel)
private def c518004 : Checkpoint 518004 412167755314283640354317454705 198584566294401813410655202922 := advance c517004 1000 (by decide) (by decide +kernel)
private def c519004 : Checkpoint 519004 411939368075410335916734654533 198401074955729935695732097132 := advance c518004 1000 (by decide) (by decide +kernel)
private def c520004 : Checkpoint 520004 411711068019701723927371265675 198218376363602920256305777038 := advance c519004 1000 (by decide) (by decide +kernel)
private def c521004 : Checkpoint 521004 411482856332112395997141575328 198036467303311610742171122566 := advance c520004 1000 (by decide) (by decide +kernel)
private def c522004 : Checkpoint 522004 411254734184631634616830719029 197855344576380015214752660076 := advance c521004 1000 (by decide) (by decide +kernel)
private def c523004 : Checkpoint 523004 411026702736413641165654220583 197675005000465723126333911953 := advance c522004 1000 (by decide) (by decide +kernel)
private def c524004 : Checkpoint 524004 410798763133906330555647257482 197495445409261026027707309538 := advance c523004 1000 (by decide) (by decide +kernel)
private def c525004 : Checkpoint 525004 410570916510978710245318717318 197316662652394736669899538968 := advance c524004 1000 (by decide) (by decide +kernel)
private def c526004 : Checkpoint 526004 410343163989046861109670495682 197138653595334701203172736564 := advance c525004 1000 (by decide) (by decide +kernel)
private def c527004 : Checkpoint 527004 410115506677198537411162037292 196961415119290999213941250925 := advance c526004 1000 (by decide) (by decide +kernel)
private def c528004 : Checkpoint 528004 409887945672316402877428556036 196784944121119826377571384255 := advance c527004 1000 (by decide) (by decide +kernel)
private def c529004 : Checkpoint 529004 409660482059199919656474631351 196609237513228054542242485918 := advance c528004 1000 (by decide) (by decide +kernel)
private def c530004 : Checkpoint 530004 409433116910685906688600110084 196434292223478464096137079917 := advance c529004 1000 (by decide) (by decide +kernel)
private def c531004 : Checkpoint 531004 409205851287767783806410764819 196260105195095643507190659925 := advance c530004 1000 (by decide) (by decide +kernel)
private def c532004 : Checkpoint 532004 408978686239713517649861442446 196086673386572550961463879817 := advance c531004 1000 (by decide) (by decide +kernel)
private def c533004 : Checkpoint 533004 408751622804182285262315080718 195913993771577733062896797146 := advance c532004 1000 (by decide) (by decide +kernel)
private def c534004 : Checkpoint 534004 408524662007339871016018679481 195742063338863195593762480965 := advance c533004 1000 (by decide) (by decide +kernel)
private def c535004 : Checkpoint 535004 408297804863972812301139877411 195570879092172921371551743018 := advance c534004 1000 (by decide) (by decide +kernel)
private def c536004 : Checkpoint 536004 408071052377601309201519052032 195400438050152030274288243239 := advance c535004 1000 (by decide) (by decide +kernel)
private def c537004 : Checkpoint 537004 407844405540590913172516720919 195230737246256576542390182455 := advance c536004 1000 (by decide) (by decide +kernel)
private def c538004 : Checkpoint 538004 407617865334263009531720382491 195061773728663978501157816736 := advance c537004 1000 (by decide) (by decide +kernel)
private def c539004 : Checkpoint 539004 407391432729004108371765703758 194893544560184075883771866515 := advance c538004 1000 (by decide) (by decide +kernel)
private def c540004 : Checkpoint 540004 407165108684373958306072021062 194726046818170809970333460074 := advance c539004 1000 (by decide) (by decide +kernel)
private def c541004 : Checkpoint 541004 406938894149212497262840316182 194559277594434521793958611657 := advance c540004 1000 (by decide) (by decide +kernel)
private def c542004 : Checkpoint 542004 406712790061745654350162942018 194393233995154863700256602525 := advance c541004 1000 (by decide) (by decide +kernel)
private def c543004 : Checkpoint 543004 406486797349690016625499106392 194227913140794319581669363152 := advance c542004 1000 (by decide) (by decide +kernel)
private def c544004 : Checkpoint 544004 406260916930356374416030083016 194063312166012329143125544278 := advance c543004 1000 (by decide) (by decide +kernel)
private def c545004 : Checkpoint 545004 406035149710752158652475795918 193899428219580011590266038602 := advance c544004 1000 (by decide) (by decide +kernel)
private def c546004 : Checkpoint 546004 405809496587682783497783174341 193736258464295484166125036073 := advance c545004 1000 (by decide) (by decide +kernel)
private def c547004 : Checkpoint 547004 405583958447851907373640704801 193573800076899770996600143950 := advance c546004 1000 (by decide) (by decide +kernel)
private def c548004 : Checkpoint 548004 405358536167960625311987955291 193412050247993297739314688094 := advance c547004 1000 (by decide) (by decide +kernel)
private def c549004 : Checkpoint 549004 405133230614805605385529368282 193251006181952967564563153002 := advance c548004 1000 (by decide) (by decide +kernel)
private def c550004 : Checkpoint 550004 404908042645376181800684968266 193090665096849814030935056317 := advance c549004 1000 (by decide) (by decide +kernel)
private def c551004 : Checkpoint 551004 404682973106950417068374247095 192931024224367226451931731766 := advance c550004 1000 (by decide) (by decide +kernel)
private def c552004 : Checkpoint 552004 404458022837190145502491582966 192772080809719743383422970098 := advance c551004 1000 (by decide) (by decide +kernel)
private def c553004 : Checkpoint 553004 404233192664235010132851079209 192613832111572409895134793557 := advance c552004 1000 (by decide) (by decide +kernel)
private def c554004 : Checkpoint 554004 404008483406795504958715377480 192456275401960694322514474320 := advance c553004 1000 (by decide) (by decide +kernel)
private def c555004 : Checkpoint 555004 403783895874245034310737231527 192299407966210960228283002273 := advance c554004 1000 (by decide) (by decide +kernel)
private def c556004 : Checkpoint 556004 403559430866711000933195558593 192143227102861489335757406914 := advance c555004 1000 (by decide) (by decide +kernel)
private def c557004 : Checkpoint 557004 403335089175164934244761146360 191987730123584051228604579872 := advance c556004 1000 (by decide) (by decide +kernel)
private def c558004 : Checkpoint 558004 403110871581511670084643699736 191832914353106015644073547924 := advance c557004 1000 (by decide) (by decide +kernel)
private def c559004 : Checkpoint 559004 402886778858677593101814647290 191678777129133003218943619217 := advance c558004 1000 (by decide) (by decide +kernel)
private def c560004 : Checkpoint 560004 402662811770697952798032932368 191525315802272070579420655233 := advance c559004 1000 (by decide) (by decide +kernel)
private def c561004 : Checkpoint 561004 402438971072803264090588373341 191372527735955425698012172727 := advance c560004 1000 (by decide) (by decide +kernel)
private def c562004 : Checkpoint 562004 402215257511504803117984206970 191220410306364669472013395870 := advance c561004 1000 (by decide) (by decide +kernel)
private def c563004 : Checkpoint 563004 401991671824679208871172861829 191068960902355559509640173694 := advance c562004 1000 (by decide) (by decide +kernel)
private def c564004 : Checkpoint 564004 401768214741652201094403188928 190918176925383292141050337091 := advance c563004 1000 (by decide) (by decide +kernel)
private def c565004 : Checkpoint 565004 401544886983281424763200239314 190768055789428298702502146007 := advance c564004 1000 (by decide) (by decide +kernel)
private def c566004 : Checkpoint 566004 401321689262038431312447746083 190618594920922552172706592913 := advance c565004 1000 (by decide) (by decide +kernel)
private def c567004 : Checkpoint 567004 401098622282089806654946833139 190469791758676380271039162200 := advance c566004 1000 (by decide) (by decide +kernel)
private def c568004 : Checkpoint 568004 400875686739377455900150792913 190321643753805781157685945937 := advance c567004 1000 (by decide) (by decide +kernel)
private def c569004 : Checkpoint 569004 400652883321698054553994253818 190174148369660237906008583302 := advance c568004 1000 (by decide) (by decide +kernel)
private def c570004 : Checkpoint 570004 400430212708781675853815444691 190027303081751027947422188545 := advance c569004 1000 (by decide) (by decide +kernel)
private def c571004 : Checkpoint 571004 400207675572369603767282833866 189881105377680023718890172863 := advance c570004 1000 (by decide) (by decide +kernel)
private def c572004 : Checkpoint 572004 399985272576291341060952971183 189735552757068980772749619793 := advance c571004 1000 (by decide) (by decide +kernel)
private def c573004 : Checkpoint 573004 399763004376540821722576200465 189590642731489309637990660665 := advance c572004 1000 (by decide) (by decide +kernel)
private def c574004 : Checkpoint 574004 399540871621351836901502844420 189446372824392327751323184341 := advance c573004 1000 (by decide) (by decide +kernel)
private def c575004 : Checkpoint 575004 399318874951272683413496791730 189302740571039987805374322252 := advance c574004 1000 (by decide) (by decide +kernel)
private def c576004 : Checkpoint 576004 399097014999240043739908918034 189159743518436078890170635683 := advance c575004 1000 (by decide) (by decide +kernel)
private def c577004 : Checkpoint 577004 398875292390652106336472699790 189017379225257896832670004735 := advance c576004 1000 (by decide) (by decide +kernel)
private def c578004 : Checkpoint 578004 398653707743440934953932449613 188875645261788380167520125362 := advance c577004 1000 (by decide) (by decide +kernel)
private def c579004 : Checkpoint 579004 398432261668144095561274983847 188734539209848708200433551278 := advance c578004 1000 (by decide) (by decide +kernel)
private def c580004 : Checkpoint 580004 398210954767975549352482844886 188594058662731357653583700672 := advance c579004 1000 (by decide) (by decide +kernel)
private def c581004 : Checkpoint 581004 397989787638895820209436496862 188454201225133614410242547828 := advance c580004 1000 (by decide) (by decide +kernel)
private def c582004 : Checkpoint 582004 397768760869681444886839678708 188314964513091536903499241495 := advance c581004 1000 (by decide) (by decide +kernel)
private def c583004 : Checkpoint 583004 397547875041993714079802238844 188176346153914367721320070188 := advance c582004 1000 (by decide) (by decide +kernel)
private def c584004 : Checkpoint 584004 397327130730446712430964610865 188038343786119390027434501586 := advance c583004 1000 (by decide) (by decide +kernel)
private def c585004 : Checkpoint 585004 397106528502674665431764345267 187900955059367225424559960421 := advance c584004 1000 (by decide) (by decide +kernel)
private def c586004 : Checkpoint 586004 396886068919398601071604912561 187764177634397569913310111104 := advance c585004 1000 (by decide) (by decide +kernel)
private def c587004 : Checkpoint 587004 396665752534492333989267853399 187628009182965364626768239948 := advance c586004 1000 (by decide) (by decide +kernel)
private def c588004 : Checkpoint 588004 396445579895047779782889170078 187492447387777398047149480029 := advance c587004 1000 (by decide) (by decide +kernel)
private def c589004 : Checkpoint 589004 396225551541439607038177906633 187357489942429336437223705943 := advance c588004 1000 (by decide) (by decide +kernel)
private def c590004 : Checkpoint 590004 396005668007389234539267796334 187223134551343179245225592942 := advance c589004 1000 (by decide) (by decide +kernel)
private def c591004 : Checkpoint 591004 395785929820028181032640674129 187089378929705136267840253292 := advance c590004 1000 (by decide) (by decide +kernel)
private def c592004 : Checkpoint 592004 395566337499960774821922420342 186956220803403923381522726052 := advance c591004 1000 (by decide) (by decide +kernel)
private def c593004 : Checkpoint 593004 395346891561326230380008234757 186823657908969473677888121061 := advance c592004 1000 (by decide) (by decide +kernel)
private def c594004 : Checkpoint 594004 395127592511860099074904093100 186691687993512060864197142102 := advance c593004 1000 (by decide) (by decide +kernel)
private def c595004 : Checkpoint 595004 394908440852955101016855703817 186560308814661831815059796578 := advance c594004 1000 (by decide) (by decide +kernel)
private def c596004 : Checkpoint 596004 394689437079721344946755885444 186429518140508745186389118564 := advance c595004 1000 (by decide) (by decide +kernel)
private def c597004 : Checkpoint 597004 394470581681045942999457072426 186299313749542913027357487354 := advance c596004 1000 (by decide) (by decide +kernel)
private def c598004 : Checkpoint 598004 394251875139652027090448995847 186169693430595342350641428493 := advance c597004 1000 (by decide) (by decide +kernel)
private def c599004 : Checkpoint 599004 394033317932157173590374154485 186040654982779073645587475081 := advance c598004 1000 (by decide) (by decide +kernel)
private def c600004 : Checkpoint 600004 393814910529131242869027478020 185912196215430713343092590301 := advance c599004 1000 (by decide) (by decide +kernel)
private def c601004 : Checkpoint 601004 393596653395153640208803874852 185784314948052357264968675208 := advance c600004 1000 (by decide) (by decide +kernel)
private def c602004 : Checkpoint 602004 393378546988870004507000736073 185657009010253902114352687249 := advance c601004 1000 (by decide) (by decide +kernel)
private def c603004 : Checkpoint 603004 393160591763048331106934808201 185530276241695742087332769960 := advance c602004 1000 (by decide) (by decide +kernel)
private def c604004 : Checkpoint 604004 392942788164634535019477311057 185404114492031847709387449276 := advance c603004 1000 (by decide) (by decide +kernel)
private def c605004 : Checkpoint 605004 392725136634807460719331201350 185278521620853224023480307882 := advance c604004 1000 (by decide) (by decide +kernel)
private def c606004 : Checkpoint 606004 392507637609033344624153782896 185153495497631745279717536733 := advance c605004 1000 (by decide) (by decide +kernel)
private def c607004 : Checkpoint 607004 392290291517119736289450426080 185029034001664363299361326635 := advance c606004 1000 (by decide) (by decide +kernel)
private def c608004 : Checkpoint 608004 392073098783268884278015229821 184905135022017686708699155907 := advance c607004 1000 (by decide) (by decide +kernel)
private def c609004 : Checkpoint 609004 391856059826130592589556551458 184781796457472928260798616208 := advance c608004 1000 (by decide) (by decide +kernel)
private def c610004 : Checkpoint 610004 391639175058854553464004208627 184659016216471217485530471310 := advance c609004 1000 (by decide) (by decide +kernel)
private def c611004 : Checkpoint 611004 391422444889142162300835838740 184536792217059275930420144806 := advance c610004 1000 (by decide) (by decide +kernel)
private def c612004 : Checkpoint 612004 391205869719297820366567651271 184415122386835452276890772222 := advance c611004 1000 (by decide) (by decide +kernel)
private def c613004 : Checkpoint 613004 390989449946279730893315130090 184294004662896114638290329609 := advance c612004 1000 (by decide) (by decide +kernel)
private def c614004 : Checkpoint 614004 390773185961750194103027882931 184173436991782397367752168507 := advance c613004 1000 (by decide) (by decide +kernel)
private def c615004 : Checkpoint 615004 390557078152125406624625768602 184053417329427299725423558880 := advance c614004 1000 (by decide) (by decide +kernel)
private def c616004 : Checkpoint 616004 390341126898624770704796867724 183933943641103133775911584404 := advance c615004 1000 (by decide) (by decide +kernel)
private def c617004 : Checkpoint 617004 390125332577319718547648232069 183815013901369318907940972458 := advance c616004 1000 (by decide) (by decide +kernel)
private def c618004 : Checkpoint 618004 389909695559182057053714303029 183696626094020520389195202979 := advance c617004 1000 (by decide) (by decide +kernel)
private def c619004 : Checkpoint 619004 389694216210131838165012305054 183578778212035129390121559095 := advance c618004 1000 (by decide) (by decide +kernel)
private def c620004 : Checkpoint 620004 389478894891084759959875877189 183461468257524081931123697315 := advance c619004 1000 (by decide) (by decide +kernel)
private def c621004 : Checkpoint 621004 389263731957999103579185001939 183344694241680014228042865958 := advance c620004 1000 (by decide) (by decide +kernel)
private def c622004 : Checkpoint 622004 389048727761922211004329423775 183228454184726751931142135125 := advance c621004 1000 (by decide) (by decide +kernel)
private def c623004 : Checkpoint 623004 388833882649036508646781926203 183112746115869130772957965798 := advance c622004 1000 (by decide) (by decide +kernel)
private def c624004 : Checkpoint 624004 388619196960705081649504954270 182997568073243146160371193470 := advance c623004 1000 (by decide) (by decide +kernel)
private def c625004 : Checkpoint 625004 388404671033516803741557230012 182882918103866429266076083609 := advance c624004 1000 (by decide) (by decide +kernel)
private def c626004 : Checkpoint 626004 388190305199331027429194498820 182768794263589047194292591574 := advance c625004 1000 (by decide) (by decide +kernel)
private def c627004 : Checkpoint 627004 387976099785321839249458843148 182655194617044624815074381654 := advance c626004 1000 (by decide) (by decide +kernel)
private def c628004 : Checkpoint 628004 387762055114021884755712771162 182542117237601785880914591026 := advance c627004 1000 (by decide) (by decide +kernel)
private def c629004 : Checkpoint 629004 387548171503365767848786375439 182429560207315911058543821181 := advance c628004 1000 (by decide) (by decide +kernel)
private def c630004 : Checkpoint 630004 387334449266733029012357286154 182317521616881210527851465299 := advance c629004 1000 (by decide) (by decide +kernel)
private def c631004 : Checkpoint 631004 387120888712990706956863114058 182205999565583108818743293115 := advance c630004 1000 (by decide) (by decide +kernel)
private def c632004 : Checkpoint 632004 386907490146535488122643963116 182094992161250939575476278530 := advance c631004 1000 (by decide) (by decide +kernel)
private def c633004 : Checkpoint 633004 386694253867335448440117934496 181984497520210947956587028831 := advance c632004 1000 (by decide) (by decide +kernel)
private def c634004 : Checkpoint 634004 386481180170971391692595050950 181874513767239598396953920009 := advance c633004 1000 (by decide) (by decide +kernel)
private def c635004 : Checkpoint 635004 386268269348677788775824576125 181765039035517185476806218522 := advance c634004 1000 (by decide) (by decide +kernel)
private def c636004 : Checkpoint 636004 386055521687383322097537323459 181656071466581745660617137039 := advance c635004 1000 (by decide) (by decide +kernel)
private def c637004 : Checkpoint 637004 385842937469751039310078432269 181547609210283267686792986635 := advance c636004 1000 (by decide) (by decide +kernel)
private def c638004 : Checkpoint 638004 385630516974218120519717586894 181439650424738199406898407567 := advance c637004 1000 (by decide) (by decide +kernel)
private def c639004 : Checkpoint 639004 385418260475035263067363264559 181332193276284248890839141882 := advance c638004 1000 (by decide) (by decide +kernel)
private def c640004 : Checkpoint 640004 385206168242305687927185973532 181225235939435477631960003674 := advance c639004 1000 (by decide) (by decide +kernel)
private def c641004 : Checkpoint 641004 384994240542023771722063380630 181118776596837683703407662507 := advance c640004 1000 (by decide) (by decide +kernel)
private def c642004 : Checkpoint 642004 384782477636113308307788671534 181012813439224072734356627263 := advance c641004 1000 (by decide) (by decide +kernel)
private def c643004 : Checkpoint 643004 384570879782465403831623524279 180907344665371214591803452234 := advance c642004 1000 (by decide) (by decide +kernel)
private def c644004 : Checkpoint 644004 384359447234976009125019931159 180802368482055283670599725478 := advance c643004 1000 (by decide) (by decide +kernel)
private def c645004 : Checkpoint 645004 384148180243583093245172142683 180697883104008580711219886665 := advance c644004 1000 (by decide) (by decide +kernel)
private def c646004 : Checkpoint 646004 383937079054303461935482726801 180593886753876334081446392444 := advance c645004 1000 (by decide) (by decide +kernel)
private def c647004 : Checkpoint 647004 383726143909269224731026771220 180490377662173778474703242025 := advance c646004 1000 (by decide) (by decide +kernel)
private def c648004 : Checkpoint 648004 383515375046763914391667368563 180387354067243508994180422658 := advance c647004 1000 (by decide) (by decide +kernel)
private def c649004 : Checkpoint 649004 383304772701258262302605606129 180284814215213108608167466626 := advance c648004 1000 (by decide) (by decide +kernel)
private def c650004 : Checkpoint 650004 383094337103445633439831351553 180182756359953046978155051629 := advance c649004 1000 (by decide) (by decide +kernel)
private def c651004 : Checkpoint 651004 382884068480277124456169326313 180081178763034848677270448892 := advance c650004 1000 (by decide) (by decide +kernel)
private def c652004 : Checkpoint 652004 382673967054996328402380554330 179980079693689528832486645551 := advance c651004 1000 (by decide) (by decide +kernel)
private def c653004 : Checkpoint 653004 382464033047173769557074648747 179879457428766294239787154856 := advance c652004 1000 (by decide) (by decide +kernel)
private def c654004 : Checkpoint 654004 382254266672741011799006059243 179779310252691508017079890265 := advance c653004 1000 (by decide) (by decide +kernel)
private def c655004 : Checkpoint 655004 382044668144024443915659962991 179679636457427915875135023678 := advance c654004 1000 (by decide) (by decide +kernel)
private def c656004 : Checkpoint 656004 381835237669778745202873678679 179580434342434132102174477393 := advance c655004 1000 (by decide) (by decide +kernel)
private def c657004 : Checkpoint 657004 381625975455220034671580160657 179481702214624383372965610617 := advance c656004 1000 (by decide) (by decide +kernel)
private def c658004 : Checkpoint 658004 381416881702058707139594242901 179383438388328508508369749149 := advance c657004 1000 (by decide) (by decide +kernel)
private def c659004 : Checkpoint 659004 381207956608531959448682917460 179285641185252212326268460811 := advance c658004 1000 (by decide) (by decide +kernel)
private def c660004 : Checkpoint 660004 380999200369436010009961216516 179188308934437571739637882719 := advance c659004 1000 (by decide) (by decide +kernel)
private def c661004 : Checkpoint 661004 380790613176158014843928500714 179091439972223792272264941208 := advance c660004 1000 (by decide) (by decide +kernel)
private def c662004 : Checkpoint 662004 380582195216707683245199514448 178995032642208213177199945110 := advance c661004 1000 (by decide) (by decide +kernel)
private def c663004 : Checkpoint 663004 380373946675748596166183934013 178899085295207559357518750006 := advance c662004 1000 (by decide) (by decide +kernel)
private def c664004 : Checkpoint 664004 380165867734629230378620885396 178803596289219438303325449184 := advance c663004 1000 (by decide) (by decide +kernel)
private def c665004 : Checkpoint 665004 379957958571413691436974724331 178708563989384080273164308582 := advance c664004 1000 (by decide) (by decide +kernel)
private def c666004 : Checkpoint 666004 379750219360912158433239025316 178613986767946319962128382742 := advance c665004 1000 (by decide) (by decide +kernel)
private def c667004 : Checkpoint 667004 379542650274711043498671088770 178519863004217817912952877178 := advance c666004 1000 (by decide) (by decide +kernel)
private def c668004 : Checkpoint 668004 379335251481202868974383308630 178426191084539519940264806296 := advance c667004 1000 (by decide) (by decide +kernel)
private def c669004 : Checkpoint 669004 379128023145615865139544501032 178332969402244352851927774310 := advance c668004 1000 (by decide) (by decide +kernel)
private def c670004 : Checkpoint 670004 378920965430043291353187922240 178240196357620154765072714364 := advance c669004 1000 (by decide) (by decide +kernel)
private def c671004 : Checkpoint 671004 378714078493472483433277434736 178147870357872838327943089921 := advance c670004 1000 (by decide) (by decide +kernel)
private def c672004 : Checkpoint 672004 378507362491813630064743434065 178055989817089785172107314259 := advance c671004 1000 (by decide) (by decide +kernel)
private def c673004 : Checkpoint 673004 378300817577928280996660132629 177964553156203469932902900345 := advance c672004 1000 (by decide) (by decide +kernel)
private def c674004 : Checkpoint 674004 378094443901657589757590100048 177873558802955312189177026160 := advance c673004 1000 (by decide) (by decide +kernel)
private def c675004 : Checkpoint 675004 377888241609850293587365158341 177783005191859754686477699167 := advance c674004 1000 (by decide) (by decide +kernel)
private def c676004 : Checkpoint 676004 377682210846390433253199476860 177692890764168566220829430667 := advance c675004 1000 (by decide) (by decide +kernel)
private def c677004 : Checkpoint 677004 377476351752224815388035745188 177603213967835367573098183046 := advance c676004 1000 (by decide) (by decide +kernel)
private def c678004 : Checkpoint 678004 377270664465390219959403435082 177513973257480378896713222813 := advance c677004 1000 (by decide) (by decide +kernel)
private def c679004 : Checkpoint 679004 377065149121040355447814287968 177425167094355386974169285717 := advance c678004 1000 (by decide) (by decide +kernel)
private def c680004 : Checkpoint 680004 376859805851472564284829251673 177336793946308930770282018025 := advance c679004 1000 (by decide) (by decide +kernel)
private def c681004 : Checkpoint 681004 376654634786154281072398183356 177248852287751703722613874638 := advance c680004 1000 (by decide) (by decide +kernel)
private def c682004 : Checkpoint 682004 376449636051749246076893852290 177161340599622171221827400448 := advance c681004 1000 (by decide) (by decide +kernel)
private def c683004 : Checkpoint 683004 376244809772143476463430308267 177074257369352401746958959459 := advance c682004 1000 (by decide) (by decide +kernel)
private def c684004 : Checkpoint 684004 376040156068470997708567791767 176987601090834110132739364141 := advance c683004 1000 (by decide) (by decide +kernel)
private def c685004 : Checkpoint 685004 375835675059139337602357381509 176901370264384911458119349836 := advance c684004 1000 (by decide) (by decide +kernel)
private def c686004 : Checkpoint 686004 375631366859854785223863909511 176815563396714784057088279376 := advance c685004 1000 (by decide) (by decide +kernel)
private def c687004 : Checkpoint 687004 375427231583647417247820790609 176730179000892740164704696152 := advance c686004 1000 (by decide) (by decide +kernel)
private def c688004 : Checkpoint 688004 375223269340895893913910852735 176645215596313702722988201105 := advance c687004 1000 (by decide) (by decide +kernel)
private def c689004 : Checkpoint 689004 375019480239352026964328617551 176560671708665586882954444587 := advance c688004 1000 (by decide) (by decide +kernel)
private def c690004 : Checkpoint 690004 374815864384165121829757439621 176476545869896584750609617126 := advance c689004 1000 (by decide) (by decide +kernel)
private def c691004 : Checkpoint 691004 374612421877906096318685195886 176392836618182651936158516387 := advance c690004 1000 (by decide) (by decide +kernel)
private def c692004 : Checkpoint 692004 374409152820591378040080623993 176309542497895194477021869973 := advance c691004 1000 (by decide) (by decide +kernel)
private def c693004 : Checkpoint 693004 374206057309706582764854793139 176226662059568954716504915070 := advance c692004 1000 (by decide) (by decide +kernel)
private def c694004 : Checkpoint 694004 374003135440229975907234474233 176144193859870094731111075031 := advance c693004 1000 (by decide) (by decide +kernel)
private def c695004 : Checkpoint 695004 373800387304655719283172335358 176062136461564475910552727057 := advance c694004 1000 (by decide) (by decide +kernel)
private def c696004 : Checkpoint 696004 373597812993016905279208959718 175980488433486133305476312398 := advance c695004 1000 (by decide) (by decide +kernel)
private def c697004 : Checkpoint 697004 373395412592908380541779763481 175899248350505943368792186966 := advance c696004 1000 (by decide) (by decide +kernel)
private def c698004 : Checkpoint 698004 373193186189509361273822131019 175818414793500483727281421754 := advance c697004 1000 (by decide) (by decide +kernel)
private def c699004 : Checkpoint 699004 372991133865605842202680694320 175737986349321083630843014564 := advance c698004 1000 (by decide) (by decide +kernel)
private def c700004 : Checkpoint 700004 372789255701612801260727924386 175657961610763063737346431297 := advance c699004 1000 (by decide) (by decide +kernel)
private def c701004 : Checkpoint 701004 372587551775596201997809396002 175578339176535163901566821173 := advance c700004 1000 (by decide) (by decide +kernel)
private def c702004 : Checkpoint 702004 372386022163294795722584601374 175499117651229157647104397826 := advance c701004 1000 (by decide) (by decide +kernel)
private def c703004 : Checkpoint 703004 372184666938141725348061451280 175420295645289652010526100927 := advance c702004 1000 (by decide) (by decide +kernel)
private def c704004 : Checkpoint 704004 371983486171285932895112087488 175341871774984071457217492129 := advance c703004 1000 (by decide) (by decide +kernel)
private def c705004 : Checkpoint 705004 371782479931613372586505867282 175263844662372824578596636563 := advance c704004 1000 (by decide) (by decide +kernel)
private def c706004 : Checkpoint 706004 371581648285768031442998946146 175186212935279652290420207319 := advance c705004 1000 (by decide) (by decide +kernel)
private def c707004 : Checkpoint 707004 371380991298172759272275405764 175108975227262156261905955372 := advance c706004 1000 (by decide) (by decide +kernel)
private def c708004 : Checkpoint 708004 371180509031049909921039027809 175032130177582506315305732345 := advance c707004 1000 (by decide) (by decide +kernel)
private def c709004 : Checkpoint 709004 370980201544441795640304321740 174955676431178325545390154469 := advance c708004 1000 (by decide) (by decide +kernel)
private def c710004 : Checkpoint 710004 370780068896230956393927050570 174879612638633751918050465872 := advance c709004 1000 (by decide) (by decide +kernel)
private def c711004 : Checkpoint 711004 370580111142160245920645076956 174803937456150675116885902113 := advance c710004 1000 (by decide) (by decide +kernel)
private def c712004 : Checkpoint 712004 370380328335852736340366738507 174728649545520147416226570767 := advance c711004 1000 (by decide) (by decide +kernel)
private def c713004 : Checkpoint 713004 370180720528831443076143062202 174653747574093967368543251638 := advance c712004 1000 (by decide) (by decide +kernel)
private def c714004 : Checkpoint 714004 369981287770538871844188897360 174579230214756435103617260327 := advance c713004 1000 (by decide) (by decide +kernel)
private def c715004 : Checkpoint 715004 369782030108356389445473479356 174505096145896278046186303700 := advance c714004 1000 (by decide) (by decide +kernel)
private def c716004 : Checkpoint 716004 369582947587623420073780072203 174431344051378745868046759088 := advance c715004 1000 (by decide) (by decide +kernel)
private def c717004 : Checkpoint 717004 369384040251656468836734258551 174357972620517873499779705931 := advance c716004 1000 (by decide) (by decide +kernel)
private def c718004 : Checkpoint 718004 369185308141767974168118271983 174284980548048911036377996038 := advance c717004 1000 (by decide) (by decide +kernel)
private def c719004 : Checkpoint 719004 368986751297284990791821665288 174212366534100919380085329662 := advance c718004 1000 (by decide) (by decide +kernel)
private def c720004 : Checkpoint 720004 368788369755567704880023781135 174140129284169530472716365632 := advance c719004 1000 (by decide) (by decide +kernel)
private def c721004 : Checkpoint 721004 368590163552027783030658183441 174068267509089870978609987128 := advance c720004 1000 (by decide) (by decide +kernel)
private def c722004 : Checkpoint 722004 368392132720146556671870702714 173996779925009648288176616983 := advance c721004 1000 (by decide) (by decide +kernel)
private def c723004 : Checkpoint 723004 368194277291493043484048365449 173925665253362397720735569425 := advance c722004 1000 (by decide) (by decide +kernel)
private def c724004 : Checkpoint 724004 367996597295741807413063579315 173854922220840889814000473589 := advance c723004 1000 (by decide) (by decide +kernel)
private def c725004 : Checkpoint 725004 367799092760690658831643925285 173784549559370696596160441628 := advance c724004 1000 (by decide) (by decide +kernel)
private def c726004 : Checkpoint 726004 367601763712278196389240202490 173714546006083915745022504176 := advance c725004 1000 (by decide) (by decide +kernel)
private def c727004 : Checkpoint 727004 367404610174601192074421447091 173644910303293051547127520649 := advance c726004 1000 (by decide) (by decide +kernel)
private def c728004 : Checkpoint 728004 367207632169931820997673011599 173575641198465051578127906731 := advance c727004 1000 (by decide) (by decide +kernel)
private def c729004 : Checkpoint 729004 367010829718734737386509984135 173506737444195498034021717004 := advance c728004 1000 (by decide) (by decide +kernel)
private def c730004 : Checkpoint 730004 366814202839683998269040823512 173438197798182952651074482639 := advance c729004 1000 (by decide) (by decide +kernel)
private def c731004 : Checkpoint 731004 366617751549679836306522695259 173370021023203454160428333660 := advance c730004 1000 (by decide) (by decide +kernel)
private def c732004 : Checkpoint 732004 366421475863865283220038257322 173302205887085167231497926621 := advance c731004 1000 (by decide) (by decide +kernel)
private def c733004 : Checkpoint 733004 366225375795642645241191238744 173234751162683181866285145325 := advance c732004 1000 (by decide) (by decide +kernel)
private def c734004 : Checkpoint 734004 366029451356689832001662787225 173167655627854462214710026333 := advance c733004 1000 (by decide) (by decide +kernel)
private def c735004 : Checkpoint 735004 365833702556976540261589971544 173100918065432943788954467851 := advance c734004 1000 (by decide) (by decide +kernel)
private def c736004 : Checkpoint 736004 365638129404780293862019786389 173034537263204778062648581756 := advance c735004 1000 (by decide) (by decide +kernel)
private def c737004 : Checkpoint 737004 365442731906702341272154318948 172968512013883723448497619816 := advance c736004 1000 (by decide) (by decide +kernel)
private def c738004 : Checkpoint 738004 365247510067683412087733235154 172902841115086681655650809201 := advance c737004 1000 (by decide) (by decide +kernel)
private def c739004 : Checkpoint 739004 365052463891019333822696289522 172837523369309378435752733963 := advance c738004 1000 (by decide) (by decide +kernel)
private def c740004 : Checkpoint 740004 364857593378376510322229050596 172772557583902187734193653085 := advance c739004 1000 (by decide) (by decide +kernel)
private def c741004 : Checkpoint 741004 364662898529807263111417384975 172707942571046098270587905918 := advance c740004 1000 (by decide) (by decide +kernel)
private def c742004 : Checkpoint 742004 364468379343765036980018407672 172643677147728821579959869120 := advance c741004 1000 (by decide) (by decide +kernel)
private def c743004 : Checkpoint 743004 364274035817119471090295565506 172579760135721040553505338984 := advance c742004 1000 (by decide) (by decide +kernel)
private def c744004 : Checkpoint 744004 364079867945171336881461278589 172516190361552797525123257557 := advance c743004 1000 (by decide) (by decide +kernel)
private def c745004 : Checkpoint 745004 363885875721667344031020158521 172452966656490020957178914445 := advance c744004 1000 (by decide) (by decide +kernel)
private def c746004 : Checkpoint 746004 363692059138814815720207311718 172390087856511189786165667123 := advance c745004 1000 (by decide) (by decide +kernel)
private def c747004 : Checkpoint 747004 363498418187296234437767711156 172327552802284134496078357639 := advance c746004 1000 (by decide) (by decide +kernel)
private def c748004 : Checkpoint 748004 363304952856283659543522193294 172265360339142973994398479981 := advance c747004 1000 (by decide) (by decide +kernel)
private def c749004 : Checkpoint 749004 363111663133453017800511450846 172203509317065187372619289638 := advance c748004 1000 (by decide) (by decide +kernel)
private def c750004 : Checkpoint 750004 362918549004998268071999610758 172141998590648819640208953794 := advance c749004 1000 (by decide) (by decide +kernel)
private def c751004 : Checkpoint 751004 362725610455645441367251803022 172080827019089820527822025049 := advance c750004 1000 (by decide) (by decide +kernel)
private def c752004 : Checkpoint 752004 362532847468666557407773753615 172019993466159515462424487031 := advance c751004 1000 (by decide) (by decide +kernel)
private def c753004 : Checkpoint 753004 362340260025893418873614116339 171959496800182207823795863664 := advance c752004 1000 (by decide) (by decide +kernel)
private def c754004 : Checkpoint 754004 362147848107731284477380255225 171899335894012911598613900854 := advance c753004 1000 (by decide) (by decide +kernel)
private def c755004 : Checkpoint 755004 361955611693172422001803792000 171839509625015213555013608597 := advance c754004 1000 (by decide) (by decide +kernel)
private def c756004 : Checkpoint 756004 361763550759809542425011750729 171780016875039264067143479130 := advance c755004 1000 (by decide) (by decide +kernel)
private def c757004 : Checkpoint 757004 361571665283849116246110899769 171720856530399895725817954300 := advance c756004 1000 (by decide) (by decide +kernel)
private def c758004 : Checkpoint 758004 361379955240124573112275265642 171662027481854868877887179337 := advance c757004 1000 (by decide) (by decide +kernel)
private def c759004 : Checkpoint 759004 361188420602109385837238153482 171603528624583243243413224992 := advance c758004 1000 (by decide) (by decide +kernel)
private def c760004 : Checkpoint 760004 360997061341930039889928755348 171545358858163874766156752705 := advance c759004 1000 (by decide) (by decide +kernel)
private def c761004 : Checkpoint 761004 360805877430378889420957983959 171487517086554036859240005692 := advance c760004 1000 (by decide) (by decide +kernel)
private def c762004 : Checkpoint 762004 360614868836926900883746978143 171430002218068165214161489649 := advance c761004 1000 (by decide) (by decide +kernel)
private def c763004 : Checkpoint 763004 360424035529736285296303254034 171372813165356725347595221646 := advance c762004 1000 (by decide) (by decide +kernel)
private def c764004 : Checkpoint 764004 360233377475673020178982206525 171315948845385202066613422980 := advance c763004 1000 (by decide) (by decide +kernel)
private def c765004 : Checkpoint 765004 360042894640319262193024107283 171259408179413210039126463874 := advance c764004 1000 (by decide) (by decide +kernel)
private def c766004 : Checkpoint 766004 359852586987985651494227421923 171203190092973724662438177200 := advance c765004 1000 (by decide) (by decide +kernel)
private def c767004 : Checkpoint 767004 359662454481723508805806728158 171147293515852432428868788172 := advance c766004 1000 (by decide) (by decide +kernel)
private def c768004 : Checkpoint 768004 359472497083336926204286323213 171091717382067199993402092343 := advance c767004 1000 (by decide) (by decide +kernel)
private def c769004 : Checkpoint 769004 359282714753394752602197347173 171036460629847661154268590430 := advance c768004 1000 (by decide) (by decide +kernel)
private def c770004 : Checkpoint 770004 359093107451242474901375523803 170981522201614920963282483882 := advance c769004 1000 (by decide) (by decide +kernel)
private def c771004 : Checkpoint 771004 358903675135013995780797052340 170926901043961376188608175599 := advance c770004 1000 (by decide) (by decide +kernel)
private def c772004 : Checkpoint 772004 358714417761643309073140415733 170872596107630651358441629052 := advance c771004 1000 (by decide) (by decide +kernel)
private def c773004 : Checkpoint 773004 358525335286876073674620560214 170818606347497649619854032300 := advance c772004 1000 (by decide) (by decide +kernel)
private def c774004 : Checkpoint 774004 358336427665281086923107724431 170764930722548717652760108459 := advance c773004 1000 (by decide) (by decide +kernel)
private def c775004 : Checkpoint 775004 358147694850261658370114850123 170711568195861923884641519456 := advance c774004 1000 (by decide) (by decide +kernel)
private def c776004 : Checkpoint 776004 357959136794066884862913698970 170658517734587449257277534925 := advance c775004 1000 (by decide) (by decide +kernel)
private def c777004 : Checkpoint 777004 357770753447802827843819264142 170605778309928089802310884553 := advance c776004 1000 (by decide) (by decide +kernel)
private def c778004 : Checkpoint 778004 357582544761443593764563543096 170553348897119870288006882764 := advance c777004 1000 (by decide) (by decide +kernel)
private def c779004 : Checkpoint 779004 357394510683842318504661994395 170501228475412768205048903157 := advance c778004 1000 (by decide) (by decide +kernel)
private def c780004 : Checkpoint 780004 357206651162742056673757813747 170449416028051547364653482230 := advance c779004 1000 (by decide) (by decide +kernel)
private def c781004 : Checkpoint 781004 357018966144786576669109328132 170397910542256700387684135717 := advance c780004 1000 (by decide) (by decide +kernel)
private def c782004 : Checkpoint 782004 356831455575531062350663132672 170346711009205499368794763238 := advance c781004 1000 (by decide) (by decide +kernel)
private def c783004 : Checkpoint 783004 356644119399452722187528909127 170295816424013154004941680429 := advance c782004 1000 (by decide) (by decide +kernel)
private def c784004 : Checkpoint 784004 356456957559961306721140009643 170245225785714076482868231911 := advance c783004 1000 (by decide) (by decide +kernel)
private def c785004 : Checkpoint 785004 356269969999409535181945721981 170194938097243252425387979067 := advance c784004 1000 (by decide) (by decide +kernel)
private def c786004 : Checkpoint 786004 356083156659103432088135524507 170144952365417717201471996545 := advance c785004 1000 (by decide) (by decide +kernel)
private def c787004 : Checkpoint 787004 355896517479312574646641478719 170095267600918136910283220353 := advance c786004 1000 (by decide) (by decide +kernel)
private def c788004 : Checkpoint 788004 355710052399280251768501094694 170045882818270493354396432891 := advance c787004 1000 (by decide) (by decide +kernel)
private def c789004 : Checkpoint 789004 355523761357233535502588457635 169996797035827872322496712094 := advance c788004 1000 (by decide) (by decide +kernel)
private def c790004 : Checkpoint 790004 355337644290393265683735050159 169948009275752354506862368913 := advance c789004 1000 (by decide) (by decide +kernel)
private def c791004 : Checkpoint 791004 355151701134983948583362491859 169899518563997008385910909486 := advance c790004 1000 (by decide) (by decide +kernel)
private def c792004 : Checkpoint 792004 354965931826243570342936300309 169851323930287984407018735785 := advance c791004 1000 (by decide) (by decide +kernel)
private def c793004 : Checkpoint 793004 354780336298433325962821729555 169803424408106709809717493954 := advance c792004 1000 (by decide) (by decide +kernel)
private def c794004 : Checkpoint 794004 354594914484847264611478747113 169755819034672183434222537531 := advance c793004 1000 (by decide) (by decide +kernel)
private def c795004 : Checkpoint 795004 354409666317821852012372267741 169708506850923369865062239217 := advance c794004 1000 (by decide) (by decide +kernel)
private def c796004 : Checkpoint 796004 354224591728745450658494881213 169661486901501692264351198759 := advance c795004 1000 (by decide) (by decide +kernel)
private def c797004 : Checkpoint 797004 354039690648067718597001519174 169614758234733623253986094862 := advance c796004 1000 (by decide) (by decide +kernel)
private def c798004 : Checkpoint 798004 353854963005308927519137835436 169568319902613373210740350127 := advance c797004 1000 (by decide) (by decide +kernel)
private def c799004 : Checkpoint 799004 353670408729069200883405577800 169522170960785675342893251016 := advance c798004 1000 (by decide) (by decide +kernel)
private def c800004 : Checkpoint 800004 353486027747037672792747967297 169476310468528666921651019304 := advance c799004 1000 (by decide) (by decide +kernel)
private def c801004 : Checkpoint 801004 353301819986001568339455145558 169430737488736866045201892914 := advance c800004 1000 (by decide) (by decide +kernel)
private def c802004 : Checkpoint 802004 353117785371855206124483190665 169385451087904243317794864993 := advance c801004 1000 (by decide) (by decide +kernel)
private def c803004 : Checkpoint 803004 352933923829608923650949131872 169340450336107387830742670855 := advance c802004 1000 (by decide) (by decide +kernel)
private def c804004 : Checkpoint 804004 352750235283397926284707922893 169295734306988766836724220252 := advance c803004 1000 (by decide) (by decide +kernel)
private def c805004 : Checkpoint 805004 352566719656491060468134584891 169251302077740078513200261409 := advance c804004 1000 (by decide) (by decide +kernel)
private def c806004 : Checkpoint 806004 352383376871299511866524832006 169207152729085697215158944382 := advance c805004 1000 (by decide) (by decide +kernel)
private def c807004 : Checkpoint 807004 352200206849385429119889590513 169163285345266210621775434733 := advance c806004 1000 (by decide) (by decide +kernel)
private def c808004 : Checkpoint 808004 352017209511470473866352069737 169119699014022048185902117860 := advance c807004 1000 (by decide) (by decide +kernel)
private def c809004 : Checkpoint 809004 351834384777444297696859603069 169076392826577200299603535493 := advance c808004 1000 (by decide) (by decide +kernel)
private def c810004 : Checkpoint 810004 351651732566372946694495528196 169033365877623027593213305845 := advance c809004 1000 (by decide) (by decide +kernel)
private def c811004 : Checkpoint 811004 351469252796507194205318100647 168990617265302159789619200124 := advance c810004 1000 (by decide) (by decide +kernel)
private def c812004 : Checkpoint 812004 351286945385290802481363031993 168948146091192483539677570136 := advance c811004 1000 (by decide) (by decide +kernel)
private def c813004 : Checkpoint 813004 351104810249368713830222919994 168905951460291218668819741525 := advance c812004 1000 (by decide) (by decide +kernel)
private def c814004 : Checkpoint 814004 350922847304595171899459808163 168864032480999082269041092707 := advance c813004 1000 (by decide) (by decide +kernel)
private def c815004 : Checkpoint 815004 350741056466041773718015605537 168822388265104540074558617227 := advance c814004 1000 (by decide) (by decide +kernel)
private def c816004 : Checkpoint 816004 350559437648005453110758347842 168781017927768144563485102967 := advance c815004 1000 (by decide) (by decide +kernel)
private def c817004 : Checkpoint 817004 350377990764016396096339537972 168739920587506959231897937876 := advance c816004 1000 (by decide) (by decide +kernel)
private def c818004 : Checkpoint 818004 350196715726845888872638319027 168699095366179068490678245723 := advance c817004 1000 (by decide) (by decide +kernel)
private def c819004 : Checkpoint 819004 350015612448514098988231276671 168658541388968172639461846838 := advance c818004 1000 (by decide) (by decide +kernel)
private def c820004 : Checkpoint 820004 349834680840297790292551508967 168618257784368267375977700227 := advance c819004 1000 (by decide) (by decide +kernel)
private def c821004 : Checkpoint 821004 349653920812737972251686529394 168578243684168407302952287938 := advance c820004 1000 (by decide) (by decide +kernel)
private def c822004 : Checkpoint 822004 349473332275647484211110872145 168538498223437552898630119391 := advance c821004 1000 (by decide) (by decide +kernel)
private def c823004 : Checkpoint 823004 349292915138118515181055251116 168499020540509500420801429986 := advance c822004 1000 (by decide) (by decide +kernel)
private def c824004 : Checkpoint 824004 349112669308530059714679095058 168459809776967894218038488595 := advance c823004 1000 (by decide) (by decide +kernel)
private def c825004 : Checkpoint 825004 348932594694555310443736561745 168420865077631320925621976937 := advance c824004 1000 (by decide) (by decide +kernel)
private def c826004 : Checkpoint 826004 348752691203168987831007048970 168382185590538485027388917412 := advance c825004 1000 (by decide) (by decide +kernel)
private def c827004 : Checkpoint 827004 348572958740654607693399109053 168343770466933465268453865408 := advance c826004 1000 (by decide) (by decide +kernel)
private def c828004 : Checkpoint 828004 348393397212611687044330877757 168305618861251051407445800862 := advance c827004 1000 (by decide) (by decide +kernel)
private def c829004 : Checkpoint 829004 348214006523962888798740003418 168267729931102160800564605330 := advance c828004 1000 (by decide) (by decide +kernel)
private def c830004 : Checkpoint 830004 348034786578961105878880966830 168230102837259334313393447074 := advance c829004 1000 (by decide) (by decide +kernel)
private def c831004 : Checkpoint 831004 347855737281196485253926986634 168192736743642311060007064161 := advance c830004 1000 (by decide) (by decide +kernel)
private def c832004 : Checkpoint 832004 347676858533603392441306785063 168155630817303681472491082736 := advance c831004 1000 (by decide) (by decide +kernel)
private def c833004 : Checkpoint 833004 347498150238467316992672730065 168118784228414618207534376879 := advance c832004 1000 (by decide) (by decide +kernel)
private def c834004 : Checkpoint 834004 347319612297431719482415662983 168082196150250684400275311014 := advance c833004 1000 (by decide) (by decide +kernel)
private def c835004 : Checkpoint 835004 347141244611504820511712467243 168045865759177718779073744473 := advance c834004 1000 (by decide) (by decide +kernel)
private def c836004 : Checkpoint 836004 346963047081066332236214539613 168009792234637797158344158718 := advance c835004 1000 (by decide) (by decide +kernel)
private def c837004 : Checkpoint 837004 346785019605874132920658205530 167973974759135269830021426223 := advance c836004 1000 (by decide) (by decide +kernel)
private def c838004 : Checkpoint 838004 346607162085070885018901196746 167938412518222874377639808760 := advance c837004 1000 (by decide) (by decide +kernel)
private def c839004 : Checkpoint 839004 346429474417190597273162011707 167903104700487923440387984982 := advance c838004 1000 (by decide) (by decide +kernel)
private def c840004 : Checkpoint 840004 346251956500165131321560741922 167868050497538566957858488705 := advance c839004 1000 (by decide) (by decide +kernel)
private def c841004 : Checkpoint 841004 346074608231330653298430216130 167833249103990128429539121001 := advance c840004 1000 (by decide) (by decide +kernel)
private def c842004 : Checkpoint 842004 345897429507434030907284536316 167798699717451514726396903088 := advance c841004 1000 (by decide) (by decide +kernel)
private def c843004 : Checkpoint 843004 345720420224639176441797713419 167764401538511698995182187602 := advance c842004 1000 (by decide) (by decide +kernel)
private def c844004 : Checkpoint 844004 345543580278533336225657619667 167730353770726276199331864416 := advance c843004 1000 (by decide) (by decide +kernel)
private def c845004 : Checkpoint 845004 345366909564133326937719327883 167696555620604090843576401239 := advance c844004 1000 (by decide) (by decide +kernel)
private def c846004 : Checkpoint 846004 345190407975891719284486583807 167663006297593936432555968058 := advance c845004 1000 (by decide) (by decide +kernel)
private def c847004 : Checkpoint 847004 345014075407702969477600136851 167629705014071326216926320867 := advance c846004 1000 (by decide) (by decide +kernel)
private def c848004 : Checkpoint 848004 344837911752909498969706429430 167596650985325334783585679338 := advance c847004 1000 (by decide) (by decide +kernel)
private def c849004 : Checkpoint 849004 344661916904307722897819208539 167563843429545510049779734856 := advance c848004 1000 (by decide) (by decide +kernel)
private def c850004 : Checkpoint 850004 344486090754154027679069478589 167531281567808855223943380172 := advance c849004 1000 (by decide) (by decide +kernel)
private def c851004 : Checkpoint 851004 344310433194170698199565370022 167498964624066880299214966053 := advance c850004 1000 (by decide) (by decide +kernel)
private def c852004 : Checkpoint 852004 344134944115551795032952466788 167466891825132722648612071189 := advance c851004 1000 (by decide) (by decide +kernel)
private def c853004 : Checkpoint 853004 343959623408968982121176437781 167435062400668336293887121014 := advance c852004 1000 (by decide) (by decide +kernel)
private def c854004 : Checkpoint 854004 343784470964577305345902979578 167403475583171749423086912685 := advance c853004 1000 (by decide) (by decide +kernel)
private def c855004 : Checkpoint 855004 343609486672020922415044630039 167372130607964389734822395968 := advance c854004 1000 (by decide) (by decide +kernel)
private def c856004 : Checkpoint 856004 343434670420438784484879492987 167341026713178477190214122943 := advance c855004 1000 (by decide) (by decide +kernel)
private def c857004 : Checkpoint 857004 343260022098470269934322866843 167310163139744483756414808852 := advance c856004 1000 (by decide) (by decide +kernel)
private def c858004 : Checkpoint 858004 343085541594260770704028741131 167279539131378659728523636882 := advance c857004 1000 (by decide) (by decide +kernel)
private def c859004 : Checkpoint 859004 342911228795467231609153670253 167249153934570626219597485211 := advance c858004 1000 (by decide) (by decide +kernel)
private def c860004 : Checkpoint 860004 342737083589263643030810212205 167219006798571033411332345431 := advance c859004 1000 (by decide) (by decide +kernel)
private def c861004 : Checkpoint 861004 342563105862346487387470496046 167189096975379284160834028072 := advance c860004 1000 (by decide) (by decide +kernel)
private def c862004 : Checkpoint 862004 342389295500940139783852125206 167159423719731322561721000237 := advance c861004 1000 (by decide) (by decide +kernel)
private def c863004 : Checkpoint 863004 342215652390802223231128110797 167129986289087487060604060106 := advance c862004 1000 (by decide) (by decide +kernel)
private def c864004 : Checkpoint 864004 342042176417228918828649438782 167100783943620427732767706306 := advance c863004 1000 (by decide) (by decide +kernel)
private def c865004 : Checkpoint 865004 341868867465060231293752793227 167071815946203087323636690508 := advance c864004 1000 (by decide) (by decide +kernel)
private def c866004 : Checkpoint 866004 341695725418685210222646475677 167043081562396745665348530666 := advance c865004 1000 (by decide) (by decide +kernel)
private def c867004 : Checkpoint 867004 341522750162047127461824272544 167014580060439127080468889099 := advance c866004 1000 (by decide) (by decide +kernel)
private def c868004 : Checkpoint 868004 341349941578648610965949528780 166986310711232570387581862540 := advance c867004 1000 (by decide) (by decide +kernel)
private def c869004 : Checkpoint 869004 341177299551556735514679592656 166958272788332261126161566545 := advance c868004 1000 (by decide) (by decide +kernel)
private def c870004 : Checkpoint 870004 341004823963408070657463711450 166930465567934525620785100062 := advance c869004 1000 (by decide) (by decide +kernel)
private def c871004 : Checkpoint 871004 340832514696413686251944997576 166902888328865186507380218929 := advance c870004 1000 (by decide) (by decide +kernel)
private def c872004 : Checkpoint 872004 340660371632364115958228866716 166875540352567979346814003642 := advance c871004 1000 (by decide) (by decide +kernel)
private def c873004 : Checkpoint 873004 340488394652634279047945998056 166848420923093029953721645547 := advance c872004 1000 (by decide) (by decide +kernel)
private def c874004 : Checkpoint 874004 340316583638188360883737010314 166821529327085392071047365614 := advance c873004 1000 (by decide) (by decide +kernel)
private def c875004 : Checkpoint 875004 340144938469584652421518317468 166794864853773645023322589580 := advance c874004 1000 (by decide) (by decide +kernel)
private def c876004 : Checkpoint 876004 339973459026980349084653662827 166768426794958550984239995938 := advance c875004 1000 (by decide) (by decide +kernel)
private def c877004 : Checkpoint 877004 339802145190136309355953270147 166742214445001771496596096009 := advance c876004 1000 (by decide) (by decide +kernel)
private def c878004 : Checkpoint 878004 339630996838421773430252041662 166716227100814642885169758097 := advance c877004 1000 (by decide) (by decide +kernel)
private def c879004 : Checkpoint 879004 339460013850819042267179424763 166690464061847010205579714531 := advance c878004 1000 (by decide) (by decide +kernel)
private def c880004 : Checkpoint 880004 339289196105928117380626115329 166664924630076119374620748619 := advance c879004 1000 (by decide) (by decide +kernel)
private def c881004 : Checkpoint 881004 339118543481971301698336325919 166639608109995567130016108828 := advance c880004 1000 (by decide) (by decide +kernel)
private def c882004 : Checkpoint 882004 338948055856797761822008580285 166614513808604308469942895315 := advance c881004 1000 (by decide) (by decide +kernel)
private def c883004 : Checkpoint 883004 338777733107888052015272572100 166589641035395721225087865333 := advance c882004 1000 (by decide) (by decide +kernel)
private def c884004 : Checkpoint 884004 338607575112358600243924211383 166564989102346727418373464521 := advance c883004 1000 (by decide) (by decide +kernel)
private def c885004 : Checkpoint 885004 338437581746966156589845254216 166540557323906971069858060977 := advance c884004 1000 (by decide) (by decide +kernel)
private def c886004 : Checkpoint 886004 338267752888112204357107545620 166516345016988052106660492672 := advance c885004 1000 (by decide) (by decide +kernel)
private def c887004 : Checkpoint 887004 338098088411847334185864584486 166492351500952816040087283990 := advance c886004 1000 (by decide) (by decide +kernel)
private def c888004 : Checkpoint 888004 337928588193875581486764528507 166468576097604699074451394872 := advance c887004 1000 (by decide) (by decide +kernel)
private def c889004 : Checkpoint 889004 337759252109558727505778585160 166445018131177128314364281829 := advance c888004 1000 (by decide) (by decide +kernel)
private def c890004 : Checkpoint 890004 337590080033920564326526674557 166421676928322976739558521469 := advance c889004 1000 (by decide) (by decide +kernel)
private def c891004 : Checkpoint 891004 337421071841651124114397998279 166398551818104072618556418759 := advance c890004 1000 (by decide) (by decide +kernel)
private def c892004 : Checkpoint 892004 337252227407110872904007404139 166375642131980763034741037385 := advance c891004 1000 (by decide) (by decide +kernel)
private def c893004 : Checkpoint 893004 337083546604334869228798905214 166352947203801531200610090737 := advance c892004 1000 (by decide) (by decide +kernel)
private def c894004 : Checkpoint 894004 336915029307036887888905097169 166330466369792667238200260442 := advance c893004 1000 (by decide) (by decide +kernel)
private def c895004 : Checkpoint 895004 336746675388613509150695233949 166308198968547992105859904935 := advance c894004 1000 (by decide) (by decide +kernel)
private def c896004 : Checkpoint 896004 336578484722148173668795079138 166286144341018634353721921272 := advance c895004 1000 (by decide) (by decide +kernel)
private def c897004 : Checkpoint 897004 336410457180415203418738068700 166264301830502859392385867547 := advance c896004 1000 (by decide) (by decide +kernel)
private def c898004 : Checkpoint 898004 336242592635883788925809518448 166242670782635950961459476256 := advance c897004 1000 (by decide) (by decide +kernel)
private def c899004 : Checkpoint 899004 336074890960721943073073311716 166221250545380144486734525945 := advance c898004 1000 (by decide) (by decide +kernel)
private def c900004 : Checkpoint 900004 335907352026800421769023434961 166200040469014612016880823313 := advance c899004 1000 (by decide) (by decide +kernel)
private def c901004 : Checkpoint 901004 335739975705696611752780623496 166179039906125498432634913475 := advance c900004 1000 (by decide) (by decide +kernel)
private def c902004 : Checkpoint 902004 335572761868698385812256966039 166158248211596008623537212559 := advance c901004 1000 (by decide) (by decide +kernel)
private def c903004 : Checkpoint 903004 335405710386807925688238335958 166137664742596545329332676171 := advance c902004 1000 (by decide) (by decide +kernel)
private def c904004 : Checkpoint 904004 335238821130745512934885704144 166117288858574897345196007111 := advance c903004 1000 (by decide) (by decide +kernel)
private def c905004 : Checkpoint 905004 335072093970953288004731489310 166097119921246477791972894613 := advance c904004 1000 (by decide) (by decide +kernel)
private def c906004 : Checkpoint 906004 334905528777598977823845858324 166077157294584612154643992232 := advance c905004 1000 (by decide) (by decide +kernel)
private def c907004 : Checkpoint 907004 334739125420579592120470054182 166057400344810875794218407800 := advance c906004 1000 (by decide) (by decide +kernel)
private def c908004 : Checkpoint 908004 334572883769525088768059148258 166037848440385480640248521096 := advance c907004 1000 (by decide) (by decide +kernel)
private def c909004 : Checkpoint 909004 334406803693802008401344847612 166018500951997710773128086913 := advance c908004 1000 (by decide) (by decide +kernel)
private def c910004 : Checkpoint 910004 334240885062517078561719887287 165999357252556406607290944709 := advance c909004 1000 (by decide) (by decide +kernel)
private def c911004 : Checkpoint 911004 334075127744520787625958866454 165980416717180497388368363324 := advance c910004 1000 (by decide) (by decide +kernel)
private def c912004 : Checkpoint 912004 333909531608410928770025906606 165961678723189581719289219705 := advance c911004 1000 (by decide) (by decide +kernel)
private def c913004 : Checkpoint 913004 333744096522536114217476984702 165943142650094555832218963604 := advance c912004 1000 (by decide) (by decide +kernel)
private def c914004 : Checkpoint 914004 333578822354999260019743993280 165924807879588289325130774478 := advance c913004 1000 (by decide) (by decide +kernel)
private def c915004 : Checkpoint 915004 333413708973661041613388272625 165906673795536348083685588475 := advance c914004 1000 (by decide) (by decide +kernel)
private def c916004 : Checkpoint 916004 333248756246143320397233321142 165888739783967764110966879390 := advance c915004 1000 (by decide) (by decide +kernel)
private def c917004 : Checkpoint 917004 333083964039832541570129395115 165871005233065851989471332210 := advance c916004 1000 (by decide) (by decide +kernel)
private def c918004 : Checkpoint 918004 332919332221883103467966534984 165853469533159071701597965922 := advance c917004 1000 (by decide) (by decide +kernel)
private def c919004 : Checkpoint 919004 332754860659220698636436985816 165836132076711937536705956152 := advance c918004 1000 (by decide) (by decide +kernel)
private def c920004 : Checkpoint 920004 332590549218545626873952795062 165818992258315972814625490104 := advance c919004 1000 (by decide) (by decide +kernel)
private def c921004 : Checkpoint 921004 332426397766336080477049359975 165802049474680710157306568049 := advance c920004 1000 (by decide) (by decide +kernel)
private def c922004 : Checkpoint 922004 332262406168851401918550646001 165785303124624737042077855434 := advance c921004 1000 (by decide) (by decide +kernel)
private def c923004 : Checkpoint 923004 332098574292135314186736498794 165768752609066786371761599126 := advance c922004 1000 (by decide) (by decide +kernel)
private def c924004 : Checkpoint 924004 331934902002019124011736718352 165752397331016871798651356435 := advance c923004 1000 (by decide) (by decide +kernel)
private def c925004 : Checkpoint 925004 331771389164124898203380150039 165736236695567467541106954599 := advance c924004 1000 (by decide) (by decide +kernel)
private def c926004 : Checkpoint 926004 331608035643868613322749771668 165720270109884732433255808044 := advance c925004 1000 (by decide) (by decide +kernel)
private def c927004 : Checkpoint 927004 331444841306463278907736418841 165704496983199777950011574556 := advance c926004 1000 (by decide) (by decide +kernel)
private def c928004 : Checkpoint 928004 331281806016922034470944194138 165688916726799979951330236485 := advance c927004 1000 (by decide) (by decide +kernel)
private def c929004 : Checkpoint 929004 331118929640061220486379555451 165673528754020333891320150179 := advance c928004 1000 (by decide) (by decide +kernel)
private def c930004 : Checkpoint 930004 330956212040503423579453379464 165658332480234853239506520611 := advance c929004 1000 (by decide) (by decide +kernel)
private def c931004 : Checkpoint 931004 330793653082680496132940760314 165643327322848010863222229132 := advance c930004 1000 (by decide) (by decide +kernel)
private def c932004 : Checkpoint 932004 330631252630836550519676737892 165628512701286223121756071959 := advance c931004 1000 (by decide) (by decide +kernel)
private def c933004 : Checkpoint 933004 330469010549030928170917372969 165613888036989376424536354519 := advance c932004 1000 (by decide) (by decide +kernel)
private def c934004 : Checkpoint 934004 330306926701141143687464408749 165599452753402396007262532550 := advance c933004 1000 (by decide) (by decide +kernel)
private def c935004 : Checkpoint 935004 330145000950865804198838000834 165585206275966856681520291411 := advance c934004 1000 (by decide) (by decide +kernel)
private def c936004 : Checkpoint 936004 329983233161727504173985478129 165571148032112635315026209416 := advance c935004 1000 (by decide) (by decide +kernel)
private def c937004 : Checkpoint 937004 329821623197075695885234638825 165557277451249604801247053880 := advance c936004 1000 (by decide) (by decide +kernel)
private def c938004 : Checkpoint 938004 329660170920089535725437509358 165543593964759369278725907615 := advance c937004 1000 (by decide) (by decide +kernel)
private def c939004 : Checkpoint 939004 329498876193780706576504629799 165530097005987040362022812048 := advance c938004 1000 (by decide) (by decide +kernel)
private def c940004 : Checkpoint 940004 329337738880996216425800599628 165516786010233054147741535491 := advance c939004 1000 (by decide) (by decide +kernel)
private def c941004 : Checkpoint 941004 329176758844421173425158656397 165503660414745028760666525065 := advance c940004 1000 (by decide) (by decide +kernel)
private def c942004 : Checkpoint 942004 329015935946581537585575295487 165490719658709662206575169894 := advance c941004 1000 (by decide) (by decide +kernel)
private def c943004 : Checkpoint 943004 328855270049846849298965206257 165477963183244670299820283545 := advance c942004 1000 (by decide) (by decide +kernel)
private def c944004 : Checkpoint 944004 328694761016432934876691934091 165465390431390764435296296027 := advance c943004 1000 (by decide) (by decide +kernel)
private def c945004 : Checkpoint 945004 328534408708404589292940514307 165453000848103668975910119821 := advance c944004 1000 (by decide) (by decide +kernel)
private def c946004 : Checkpoint 946004 328374212987678236319364703659 165440793880246178028174109695 := advance c945004 1000 (by decide) (by decide +kernel)
private def c947004 : Checkpoint 947004 328214173716024566235823197449 165428768976580251380024060887 := advance c946004 1000 (by decide) (by decide +kernel)
private def c948004 : Checkpoint 948004 328054290755071151300416207373 165416925587759149376439872195 := advance c947004 1000 (by decide) (by decide +kernel)
private def c949004 : Checkpoint 949004 327894563966305039160445832841 165405263166319606509910426843 := advance c948004 1000 (by decide) (by decide +kernel)
private def c950004 : Checkpoint 950004 327734993211075324384350630154 165393781166674043504237500220 := advance c949004 1000 (by decide) (by decide +kernel)
private def c951004 : Checkpoint 951004 327575578350595698293106519326 165382479045102817671616176099 := advance c950004 1000 (by decide) (by decide +kernel)
private def c952004 : Checkpoint 952004 327416319245946977268042515765 165371356259746511324361425023 := advance c951004 1000 (by decide) (by decide +kernel)
private def c953004 : Checkpoint 953004 327257215758079609710490584289 165360412270598258024072256029 := advance c952004 1000 (by decide) (by decide +kernel)
private def c954004 : Checkpoint 954004 327098267747816161827174039267 165349646539496106452436276483 := advance c953004 1000 (by decide) (by decide +kernel)
private def c955004 : Checkpoint 955004 326939475075853782413738210699 165339058530115421689278670401 := advance c954004 1000 (by decide) (by decide +kernel)
private def c956004 : Checkpoint 956004 326780837602766646807340418268 165328647707961323684850610813 := advance c955004 1000 (by decide) (by decide +kernel)
private def c957004 : Checkpoint 957004 326622355189008380177743500386 165318413540361162714733041895 := advance c956004 1000 (by decide) (by decide +kernel)
private def c958004 : Checkpoint 958004 326464027694914460324898092798 165308355496457031607102678618 := advance c957004 1000 (by decide) (by decide +kernel)
private def c959004 : Checkpoint 959004 326305854980704600149553401809 165298473047198314533468057503 := advance c958004 1000 (by decide) (by decide +kernel)
private def c960004 : Checkpoint 960004 326147836906485109962004232354 165288765665334272155334609845 := advance c959004 1000 (by decide) (by decide +kernel)
private def c961004 : Checkpoint 961004 325989973332251239792663374878 165279232825406662920599096259 := advance c960004 1000 (by decide) (by decide +kernel)
private def c962004 : Checkpoint 962004 325832264117889501866742992808 165269874003742400304805417833 := advance c961004 1000 (by decide) (by decide +kernel)
private def c963004 : Checkpoint 963004 325674709123179973403936249721 165260688678446245793715880145 := advance c962004 1000 (by decide) (by decide +kernel)
private def c964004 : Checkpoint 964004 325517308207798579902610941863 165251676329393537404964508277 := advance c963004 1000 (by decide) (by decide +kernel)
private def c965004 : Checkpoint 965004 325360061231319359066660225575 165242836438222953547862070675 := advance c964004 1000 (by decide) (by decide +kernel)
private def c966004 : Checkpoint 966004 325202968053216705531801521813 165234168488329312021716140871 := advance c965004 1000 (by decide) (by decide +kernel)
private def c967004 : Checkpoint 967004 325046028532867596546773214067 165225671964856403954313883642 := advance c966004 1000 (by decide) (by decide +kernel)
private def c968004 : Checkpoint 968004 324889242529553798763549704696 165217346354689862483490370282 := advance c967004 1000 (by decide) (by decide +kernel)
private def c969004 : Checkpoint 969004 324732609902464056289378633739 165209191146450065985971178381 := advance c968004 1000 (by decide) (by decide +kernel)
private def c970004 : Checkpoint 970004 324576130510696260152139469530 165201205830485075658934888589 := advance c969004 1000 (by decide) (by decide +kernel)
private def c971004 : Checkpoint 971004 324419804213259599329230130367 165193389898863607260988925260 := advance c970004 1000 (by decide) (by decide +kernel)
private def c972004 : Checkpoint 972004 324263630869076693488907669539 165185742845368036820491070552 := advance c971004 1000 (by decide) (by decide +kernel)
private def c973004 : Checkpoint 973004 324107610336985707591740233680 165178264165487440120378985064 := advance c972004 1000 (by decide) (by decide +kernel)
private def c974004 : Checkpoint 974004 323951742475742448498570367301 165170953356410665769891259622 := advance c973004 1000 (by decide) (by decide +kernel)
private def c975004 : Checkpoint 975004 323796027144022443730144168515 165163809917019441674775974316 := advance c974004 1000 (by decide) (by decide +kernel)
private def c976004 : Checkpoint 976004 323640464200423002522326686175 165156833347881514718786519586 := advance c975004 1000 (by decide) (by decide +kernel)
private def c977004 : Checkpoint 977004 323485053503465259319601172556 165150023151243823470459609521 := advance c976004 1000 (by decide) (by decide +kernel)
private def c978004 : Checkpoint 978004 323329794911596199848338255794 165143378831025703730357055893 := advance c977004 1000 (by decide) (by decide +kernel)
private def c979004 : Checkpoint 979004 323174688283190669910120659231 165136899892812126735131041050 := advance c978004 1000 (by decide) (by decide +kernel)
private def c980004 : Checkpoint 980004 323019733476553367034219661557 165130585843846969835942394885 := advance c979004 1000 (by decide) (by decide +kernel)
private def c981004 : Checkpoint 981004 322864930349920815127140951452 165124436193026319469922811136 := advance c980004 1000 (by decide) (by decide +kernel)
private def c982004 : Checkpoint 982004 322710278761463322255989775005 165118450450891806244525097141 := advance c981004 1000 (by decide) (by decide +kernel)
private def c983004 : Checkpoint 983004 322555778569286921701248197606 165112628129623971955750503947 := advance c982004 1000 (by decide) (by decide +kernel)
private def c984004 : Checkpoint 984004 322401429631435296413410796364 165106968743035668362378993676 := advance c983004 1000 (by decide) (by decide +kernel)
private def c985004 : Checkpoint 985004 322247231805891687006789061109 165101471806565487539457033023 := advance c984004 1000 (by decide) (by decide +kernel)
private def c986004 : Checkpoint 986004 322093184950580783422669106714 165096136837271223635418218980 := advance c985004 1000 (by decide) (by decide +kernel)
private def c987004 : Checkpoint 987004 321939288923370600392891885607 165090963353823365858324806313 := advance c986004 1000 (by decide) (by decide +kernel)
private def c988004 : Checkpoint 988004 321785543582074336833819833667 165085950876498622517823081007 := advance c987004 1000 (by decide) (by decide +kernel)
private def c989004 : Checkpoint 989004 321631948784452219299558686198 165081098927173475950502568075 := advance c988004 1000 (by decide) (by decide +kernel)
private def c990004 : Checkpoint 990004 321478504388213329622217963557 165076407029317768157438340553 := advance c989004 1000 (by decide) (by decide +kernel)
private def c991004 : Checkpoint 991004 321325210251017416865918248956 165071874707988316983777265858 := advance c990004 1000 (by decide) (by decide +kernel)
private def c992004 : Checkpoint 992004 321172066230476693720187769204 165067501489822562671302949509 := advance c991004 1000 (by decide) (by decide +kernel)
private def c993004 : Checkpoint 993004 321019072184157617457334843068 165063286903032244615980471659 := advance c992004 1000 (by decide) (by decide +kernel)
private def c994004 : Checkpoint 994004 320866227969582655577336389696 165059230477397108163540819647 := advance c993004 1000 (by decide) (by decide +kernel)
private def c995004 : Checkpoint 995004 320713533444232036262745794397 165055331744258641277216256615 := advance c994004 1000 (by decide) (by decide +kernel)
private def c996004 : Checkpoint 996004 320560988465545483765095919690 165051590236513840912781792383 := advance c995004 1000 (by decide) (by decide +kernel)
private def c997004 : Checkpoint 997004 320408592890923938843254832486 165048005488609008937094493955 := advance c996004 1000 (by decide) (by decide +kernel)
private def c998004 : Checkpoint 998004 320256346577731264373182802666 165044577036533577427351646929 := advance c997004 1000 (by decide) (by decide +kernel)
private def c999004 : Checkpoint 999004 320104249383295936247539225071 165041304417813963189310813537 := advance c998004 1000 (by decide) (by decide +kernel)
private def c1000000 : Checkpoint 1000000 319952908661215122412993574428 165038199331600223309684716121 := advance c999004 996 (by decide) (by decide +kernel)

theorem separated_1000000 (n : ℕ) (h₁ : 5≤n) (h₂ : n≤1000000) :
    separated n (trajectory (2^96) n)=true := c1000000.valid n h₁ h₂

end ArctanCert.NaturalRange

namespace ArctanCert

/-- None of the indices from five through one million has an integral tangent. -/
theorem nonintegral_through_million (n : ℕ) (hn : 5 ≤ n) (hb : n ≤ 1000000) :
    ¬ Arxiv.«2607.05739».IsIntegerValue n := by
  obtain ⟨hx,hy⟩ := error_bounds (2^96) n
  exact not_integer_of_separated (S:=2^96) (by decide)
    (NaturalRange.separated_1000000 n hn hb) hx hy

end ArctanCert

namespace ArctanCert

open Arxiv.«2607.05739»

/-- A split prime of this size distinguishes the two Gaussian evaluations, forcing
both coordinates of the product to be nonzero before any quotient is formed. -/
lemma coordinates_ne_zero_of_split {n p k : ℕ} (hp : p.Prime) (hk : 1≤k) (hkn : k≤n)
    (hsize : n+k<p) (hdiv : p ∣ 1+k^2) : A n≠0 ∧ B n≠0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let K : ZMod p := k
  have evaluate (r : ZMod p) (hr : r*r = -1) :
      (A n : ZMod p)+(B n : ZMod p)*r = ∏ j ∈ Finset.Icc 1 n, (1+(j : ZMod p)*r) := by
    let φ : GaussianInt →+* ZMod p := Zsqrtd.lift ⟨r,by simpa only [Int.cast_neg,Int.cast_one] using hr⟩
    change φ (gaussProd n) = _
    rw [gaussProd,map_prod]
    apply Finset.prod_congr rfl
    intro j _
    change ((1:ℤ):ZMod p) + ((j:ℤ):ZMod p)*r = _
    simp
  have hsq : K*K = -1 := by
    have h : (1 + K^2 : ZMod p)=0 := by
      simpa only [K,Nat.cast_add,Nat.cast_one,Nat.cast_pow] using (ZMod.natCast_eq_zero_iff (1+k^2) p).mpr hdiv
    linear_combination h
  have plus : (A n : ZMod p)+(B n : ZMod p)*K=0 := by
    rw [evaluate K hsq]
    apply Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨hk,hkn⟩)
    change 1+K*K=0
    rw [hsq,add_neg_cancel]
  have minus : (A n : ZMod p)+(B n : ZMod p)*(-K) ≠ 0 := by
    rw [evaluate (-K) (by simpa only [neg_mul_neg] using hsq)]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj hz
    obtain ⟨hj₁,hjn⟩ := Finset.mem_Icc.mp hj
    have hzero : ((j+k : ℕ) : ZMod p)=0 := by
      rw [Nat.cast_add]
      change (j:ZMod p)+K=0
      calc
        _ = K*(1+(j:ZMod p)*(-K)) := by linear_combination (j:ZMod p)*hsq
        _ = 0 := by rw [hz,mul_zero]
    exact (Nat.not_dvd_of_pos_of_lt (by omega : 0<j+k) (by omega : j+k<p))
      ((ZMod.natCast_eq_zero_iff (j+k) p).mp hzero)
  constructor
  · intro ha
    have hz : (B n : ZMod p)*K=0 := by simpa only [ha,Int.cast_zero,zero_add] using plus
    exact minus (by simp only [ha,Int.cast_zero,zero_add,mul_neg,hz,neg_zero])
  · intro hb
    apply minus
    simpa only [hb,Int.cast_zero,zero_mul,add_zero] using plus

/-- The real-coordinate guard and the certified rounding error put the exact
scaled real coordinate strictly on the same side of zero as its integer approximation. -/
lemma A_ne_zero_of_separated {S : ℤ} {n : ℕ} (hs : 0 < S)
    (ok : separated n (trajectory S n)=true) : A n≠0 := by
  let w := trajectory S n
  let c := (S:ℝ)/(n.factorial:ℝ)
  have hc : 0 < c := div_pos (by exact_mod_cast hs) (by exact_mod_cast Nat.factorial_pos n)
  have err : |c*(A n:ℝ)-(w.1:ℝ)| ≤ 4*(n:ℝ) := by
    rw [show c*(A n:ℝ)=(S:ℝ)*(A n:ℝ)/(n.factorial:ℝ) by dsimp [c]; ring]
    exact (error_bounds S n).1
  change separated n w=true at ok
  by_cases neg : w.1<0
  · simp only [separated,if_pos neg,decide_eq_true_eq] at ok
    have bound : 4*(n:ℝ) < -(w.1:ℝ) := by exact_mod_cast ok.1
    have h : c*(A n:ℝ)<0 := by linarith only [bound,(abs_le.mp err).2]
    have ha : (A n:ℝ)<0 := lt_of_not_ge (fun hn => h.not_ge (mul_nonneg hc.le hn))
    exact_mod_cast ha.ne
  · simp only [separated,if_neg neg,decide_eq_true_eq] at ok
    have bound : 4*(n:ℝ) < (w.1:ℝ) := by exact_mod_cast ok.1
    have h : 0<c*(A n:ℝ) := by linarith only [bound,(abs_le.mp err).1]
    exact_mod_cast ((mul_pos_iff_of_pos_left hc).mp h).ne'

end ArctanCert

/- The scaled-coordinate proof was contributed by HudZah in Left to Solve PR #327.
   https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/327 -/


namespace ArctanWordConclusion

open Arxiv.«2607.05739» Finset

/-- The denominator is nonzero at every unsigned-word index: use the initial
separation certificate followed by one split prime on each subsequent interval. -/
lemma nonzero_of_initial (initial : ∀ n : ℕ, 5≤n → n≤1000000 →
    ArctanCert.separated n (ArctanCert.trajectory (2^96) n)=true)
    (n : ℕ) (hi : n<2^64) : A n ≠ 0 := by
  by_cases first : n≤4
  · interval_cases n <;> decide
  by_cases low : n≤1000000
  · exact ArctanCert.A_ne_zero_of_separated (by decide : (0:ℤ)<2^96) (initial n (by omega) low)
  by_cases middle : n≤900000000000
  · exact (ArctanCert.coordinates_ne_zero_of_split (k:=999960) ArctanCRT.prime_0 (by decide)
      (by omega) (by omega) (by decide)).1
  · have hn : n≤18446744073709551615 := by norm_num at hi; omega
    exact (ArctanCert.coordinates_ne_zero_of_split (k:=7999998610) ArctanWordCRT.prime_0 (by decide)
      (by omega) (by omega) (by decide)).1

/-- With a nonzero real coordinate, the divisibility formulation is equivalent
to integrality of the literal real tangent of the arctangent sum. -/
lemma literal_iff {n : ℕ} (ha : A n ≠ 0) :
    (∃ m : ℤ, Real.tan (∑ j ∈ Icc 1 n, Real.arctan j) = (m:ℝ)) ↔ IsIntegerValue n := by
  obtain ⟨c,hc,hcos,hsin⟩ := ArctanTrigBridge.scaled_coordinates n
  have den : (A n : ℝ) ≠ 0 := by exact_mod_cast ha
  have equal : Real.tan (∑ j ∈ Icc 1 n, Real.arctan j) = (B n : ℝ)/(A n : ℝ) := by
    rw [Real.tan_eq_sin_div_cos,hsin,hcos,mul_div_mul_left _ _ hc.ne']
  constructor
  · rintro ⟨m,hm⟩
    rw [equal] at hm
    have h := (div_eq_iff den).mp hm
    refine ⟨m,?_⟩
    rw [mul_comm] at h
    exact_mod_cast h
  · rintro ⟨m,hm⟩
    refine ⟨m,?_⟩
    rw [equal]
    apply (div_eq_iff den).mpr
    rw [hm,Int.cast_mul,mul_comm]

end ArctanWordConclusion

namespace ArctanBlocks

open Arxiv.«2607.05739»

/-- The original Gaussian divisibility conjecture over every unsigned 64-bit index it covers. -/
theorem nonintegral_word64 (n : ℕ) (h5 : 5≤n) (hi : n<2^64) : ¬IsIntegerValue n := by
  by_cases early : n≤1000000
  · exact ArctanCert.nonintegral_through_million n h5 early
  · exact word_range n (by omega) (by norm_num at hi; omega)

/-- Complete classification, including the empty arctangent sum. -/
theorem integer_indices_word64 (n : ℕ) (hi : n<2^64) : IsIntegerValue n ↔ n≤4 := by
  constructor
  · intro h
    by_contra! fail
    exact nonintegral_word64 n (by omega) hi h
  · intro h
    interval_cases n <;> decide

theorem no_poles_word64 (n : ℕ) (hi : n<2^64) : A n ≠ 0 :=
  ArctanWordConclusion.nonzero_of_initial ArctanCert.NaturalRange.separated_1000000 n hi

/-- The literal trigonometric sum takes an integer value exactly at the first five
nonnegative indices, including the empty sum at zero. -/
theorem integer_tangent_word64 (n : ℕ) (hi : n<2^64) :
    (∃ m : ℤ, Real.tan (∑ j ∈ Finset.Icc 1 n, Real.arctan j) = (m:ℝ)) ↔ n≤4 :=
  (ArctanWordConclusion.literal_iff (no_poles_word64 n hi)).trans (integer_indices_word64 n hi)

end ArctanBlocks

namespace ArctanEffective

open Arxiv.«2607.05739» Finset

/-- No pole exception is needed at any index. -/
lemma tangent_eq_iff (n : ℕ) (m : ℤ) :
    Real.tan (∑ j ∈ Icc 1 n,Real.arctan j)=(m:ℝ) ↔ B n=A n*m := by
  obtain ⟨c,hc,cosine,sine⟩ := ArctanTrigBridge.scaled_coordinates n
  have ha : (A n:ℝ) ≠ 0 := by exact_mod_cast ArctanGlobal.real_ne_zero n
  rw [Real.tan_eq_sin_div_cos,sine,cosine,mul_div_mul_left _ _ hc.ne',div_eq_iff ha]
  constructor
  · intro h
    rw [mul_comm] at h
    exact_mod_cast h
  · intro h
    rw [h,Int.cast_mul,mul_comm]

/-- The certified initial interval and the global exponential growth theorem
give both an index lower bound and an effective upper bound for any given quotient. -/
lemma effective_of_word (finite : ∀ n : ℕ, 5≤n → n<2^64 → ¬IsIntegerValue n)
    {n : ℕ} {m : ℤ} (hn : 5≤n) (hm : B n=A n*m) :
    2^64 ≤ n ∧ 2^(n/8) ≤ m.natAbs ∧ 2^61 ≤ m.natAbs.log2 ∧ n<8*(m.natAbs.log2+1) := by
  have big : 2^64≤n := by
    by_contra! small
    exact finite n hn small ⟨m,hm⟩
  have idx := ArctanGlobal.index_lt_bit_bound big hm
  exact ⟨big,ArctanGlobal.quotient_exponential big hm,by omega,idx⟩

lemma small_values_of_word (finite : ∀ n : ℕ, 5≤n → n<2^64 → ¬IsIntegerValue n)
    (n : ℕ) (m : ℤ) (hn : 1≤n) (hbits : m.natAbs.log2<2^61) :
    Real.tan (∑ j ∈ Icc 1 n,Real.arctan j)=(m:ℝ) ↔
      (n=1 ∧ m=1) ∨ (n=2 ∧ m= -3) ∨ (n=3 ∧ m=0) ∨ (n=4 ∧ m=4) := by
  rw [tangent_eq_iff]
  by_cases h1 : n=1
  · subst n
    rw [show B 1=1 by decide,show A 1=1 by decide]
    omega
  by_cases h2 : n=2
  · subst n
    rw [show B 2=3 by decide,show A 2= -1 by decide]
    omega
  by_cases h3 : n=3
  · subst n
    rw [show B 3=0 by decide,show A 3= -10 by decide]
    omega
  by_cases h4 : n=4
  · subst n
    rw [show B 4= -40 by decide,show A 4= -10 by decide]
    omega
  constructor
  · intro h
    have := (effective_of_word finite (by omega) h).2.2.1
    omega
  · omega

end ArctanEffective

namespace ArctanEffective

open Arxiv.«2607.05739» Finset

/-- Any further integer value must have more than 2^61 binary digits, and a
given prospective quotient can only occur below eight times its bit length. -/
theorem new_integer_requires_huge_bits {n : ℕ} {m : ℤ} (hn : 5≤n)
    (h : Real.tan (∑ j ∈ Icc 1 n,Real.arctan j)=(m:ℝ)) :
    2^64 ≤ n ∧ 2^(n/8) ≤ m.natAbs ∧ 2^61 ≤ m.natAbs.log2 ∧ n<8*(m.natAbs.log2+1) :=
  effective_of_word ArctanBlocks.nonintegral_word64 hn ((tangent_eq_iff n m).mp h)

/-- An all-index classification of integer values having at most 2^61 binary digits. -/
theorem small_integer_values_all_indices (n : ℕ) (m : ℤ)
    (hn : 1≤n) (hbits : m.natAbs.log2<2^61) :
    Real.tan (∑ j ∈ Icc 1 n,Real.arctan j)=(m:ℝ) ↔
      (n=1 ∧ m=1) ∨ (n=2 ∧ m= -3) ∨ (n=3 ∧ m=0) ∨ (n=4 ∧ m=4) :=
  small_values_of_word ArctanBlocks.nonintegral_word64 n m hn hbits

end ArctanEffective

theorem OMA.solution : OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R2.H1 :=
  OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R2.bounded_of_word ArctanBlocks.nonintegral_word64
