import FormalConjectures.Arxiv.«2607.05739».TanArctanSum

/-! Finite exclusion and effective arithmetic restrictions on the arctangent conjecture.

Modulo an inert prime, every complete block of the Gaussian product has
real multiplier 2. At a split prime p dividing 1+k² with k at most n and
n+k below p, evaluation of the product at the two square roots of minus
one fixes the sign of the quotient residue. An integer quotient must be
congruent to positive k. Ten such primes force at least 120 decimal digits
for any integral value between index one million and nine hundred billion.

The factorial-normalized product has both coordinates at most 2 in absolute
value. A rounded recurrence tracks the scaled product with coordinate error
at most 4n. The residual hypothesis only tests denominators and integer
slopes satisfying all these explicit bounds and congruences.

See Amdeberhan, Medina and Moll (2008), Moll (2013), and
Ono, Integer values of an arctangent sum are rare, https://arxiv.org/abs/2607.05739.
-/

namespace ArctanCert.Periodic

open Arxiv.«2607.05739»

private lemma coordinate_succ (n : ℕ) :
    A (n+1) = A n - B n * ((n:ℤ)+1) ∧
      B (n+1) = A n * ((n:ℤ)+1) + B n := by
  have h : gaussProd (n+1) = gaussProd n * (⟨1, ((n+1:ℕ):ℤ)⟩ : GaussianInt) := by
    exact Finset.prod_Icc_succ_top (by omega : 1≤n+1) _
  constructor <;> simp [A, B, h, Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

private lemma coordinate_mod_succ (p n : ℕ) :
    (A (n+1) : ZMod p) = (A n : ZMod p) - (B n : ZMod p)*((n:ZMod p)+1) ∧
      (B (n+1) : ZMod p) = (A n : ZMod p)*((n:ZMod p)+1) + (B n : ZMod p) := by
  obtain ⟨ha,hb⟩ := coordinate_succ n
  simp [ha,hb]

/-- A purely real block multiplier propagates over any following prefix. -/
theorem shift {p : ℕ} (hb : (B p : ZMod p) = 0) (n : ℕ) :
    (A (p+n) : ZMod p) = (A p : ZMod p) * (A n : ZMod p) ∧
      (B (p+n) : ZMod p) = (A p : ZMod p) * (B n : ZMod p) := by
  induction n with
  | zero =>
    have hA : A 0 = 1 := by decide
    have hB : B 0 = 0 := by decide
    simp [hb,hA,hB]
  | succ n ih =>
    obtain ⟨aa,bb⟩ := coordinate_mod_succ p (p+n)
    obtain ⟨a,b⟩ := coordinate_mod_succ p n
    rw [Nat.add_succ, aa, bb, a, b, ih.1, ih.2]
    simp only [Nat.cast_add, ZMod.natCast_self, zero_add]
    constructor <;> ring

/-- Complete p-blocks scale both original coordinates by the same residue. -/
theorem coordinates_mod {p : ℕ} (hb : (B p : ZMod p) = 0) (n : ℕ) :
    (A n : ZMod p) = (A p : ZMod p)^(n/p) * (A (n%p) : ZMod p) ∧
      (B n : ZMod p) = (A p : ZMod p)^(n/p) * (B (n%p) : ZMod p) := by
  have blocks (r k : ℕ) :
      (A (p*k+r) : ZMod p) = (A p : ZMod p)^k * (A r : ZMod p) ∧
        (B (p*k+r) : ZMod p) = (A p : ZMod p)^k * (B r : ZMod p) := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h := shift hb (p*k+r)
      rw [show p*(k+1)+r = p+(p*k+r) by ring, h.1, h.2, ih.1, ih.2, pow_succ]
      constructor <;> ring
  simpa only [Nat.div_add_mod] using blocks (n%p) (n/p)

/-- A good prime excludes every index in a residue class where it divides
the real coordinate and does not divide the imaginary coordinate. -/
theorem not_integer_of_residue {p n : ℕ} (hp : Nat.Prime p)
    (hpb : (p:ℤ) ∣ B p) (hpa : ¬(p:ℤ) ∣ A p)
    (hra : (p:ℤ) ∣ A (n%p)) (hrb : ¬(p:ℤ) ∣ B (n%p)) : ¬ IsIntegerValue n := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  have hα : (A p : ZMod p) ≠ 0 := fun h => hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  have hβ : (B (n%p) : ZMod p) ≠ 0 := fun h => hrb ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)
  obtain ⟨ha,hb⟩ := coordinates_mod ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpb) n
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hra, mul_zero] at ha
  have hB : (B n : ZMod p) ≠ 0 := hb ▸ mul_ne_zero (pow_ne_zero _ hα) hβ
  intro hab
  exact hB ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
    (((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ha).trans hab))

theorem not_integer_mod_nineteen {n : ℕ} (h : n%19=5 ∨ n%19=13) : ¬ IsIntegerValue n := by
  apply not_integer_of_residue (p:=19) (by decide) (by decide) (by decide)
  · rcases h with h | h <;> rw [h] <;> decide
  · rcases h with h | h <;> rw [h] <;> decide

end ArctanCert.Periodic

namespace ArctanCert.Periodic

open Arxiv.«2607.05739»
open Polynomial
open scoped QuadraticAlgebra

/-- Evaluate the splitting of X^q-X at an arbitrary point of a commutative algebra. -/
private lemma finite_product {K S : Type*} [Field K] [Fintype K] [CommRing S] [Algebra K S] (z : S) :
    (∏ k : K, (z - algebraMap K S k)) = z^(Fintype.card K) - z := by
  classical
  let f : K[X] := X ^ (Fintype.card K) - X
  have hr : f.roots = Finset.univ.val := FiniteField.roots_X_pow_card_sub_X K
  have hm : f.Monic := Polynomial.monic_X_pow_sub (by simpa using (Fintype.one_lt_card (α:=K)))
  have hd : f.natDegree = Fintype.card K :=
    FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
  have hp := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hm (by rw [hr,hd]; rfl)
  rw [hr] at hp
  change (∏ k : K, (X-C k)) = f at hp
  simpa [f] using congrArg (Polynomial.aeval z) hp

/-- The integers from 1 through p represent all residues, including zero exactly once. -/
private lemma full_residues {p : ℕ} [NeZero p] {S : Type*} [CommMonoid S] (f : ZMod p → S) :
    (∏ k ∈ Finset.Icc 1 p, f (k : ZMod p)) = ∏ k : ZMod p, f k := by
  let e : ZMod p ≃ Fin p := {
    toFun := fun k => ⟨k.val,k.val_lt⟩
    invFun := fun i => (i.val : ZMod p)
    left_inv := fun k => ZMod.natCast_zmod_val k
    right_inv := fun i => Fin.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]) }
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel_right, Nat.cast_add, Nat.cast_one]
  rw [← Fin.prod_univ_eq_prod_range (fun k : ℕ => f (1+(k:ZMod p)))]
  exact (e.symm.trans (Equiv.addLeft 1)).prod_comp f

private lemma fourth_root_power {R : Type*} [CommRing R] (z : R) (hz : z^2 = -1)
    {p : ℕ} (h : p%4=3) : z^p = -z := by
  have h₄ : z^4 = 1 := by rw [show 4 = 2*2 by decide, pow_mul, hz]; ring
  have h₃ : z^3 = -z := by rw [pow_succ, hz, neg_one_mul]
  calc
    z^p = z^(4*(p/4)+3) := congrArg (z^·) (by omega)
    _ = -z := by rw [pow_add,pow_mul,h₄,one_pow,one_mul,h₃]

/-- For primes congruent to three modulo four, one complete Gaussian
block has real coordinate two and imaginary coordinate zero modulo p. -/
theorem inert_block {p : ℕ} (hp : Nat.Prime p) (h : p%4=3) :
    (A p : ZMod p) = 2 ∧ (B p : ZMod p) = 0 := by
  let _ : Fact (Nat.Prime p) := ⟨hp⟩
  let j : QuadraticAlgebra (ZMod p) (-1) 0 := QuadraticAlgebra.omega
  let ι := algebraMap (ZMod p) (QuadraticAlgebra (ZMod p) (-1) 0)
  let φ : GaussianInt →+* QuadraticAlgebra (ZMod p) (-1) 0 := {
    toFun := fun z => ⟨(z.re : ZMod p), (z.im : ZMod p)⟩
    map_zero' := by ext <;> simp
    map_one' := by ext <;> simp
    map_add' := by intro z w; ext <;> simp
    map_mul' := by intro z w; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul] }
  have hj : j^2 = -1 := by ext <;> simp [j, pow_two]
  have hφ (k : ℕ) : φ (⟨1,(k:ℤ)⟩ : GaussianInt) = 1+j*ι (k : ZMod p) := by
    ext <;> simp [φ,j,ι]
  have hf (k : ZMod p) : 1+j*ι k = (-j)*(j-ι k) := by
    linear_combination hj
  have hblock : φ (gaussProd p) = 2 := calc
    _ = ∏ k ∈ Finset.Icc 1 p, (1+j*ι (k:ZMod p)) := by
      rw [gaussProd, map_prod]; exact Finset.prod_congr rfl fun k _ => hφ k
    _ = ∏ k : ZMod p, (1+j*ι k) := full_residues (fun k => 1+j*ι k)
    _ = (-j)^p * (j^p-j) := by
      simp only [hf, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ZMod.card]
      rw [finite_product j, ZMod.card]
    _ = 2 := by
      rw [fourth_root_power j hj h, fourth_root_power (-j) (by simpa using hj) h]
      linear_combination -2*hj
  exact ⟨congrArg QuadraticAlgebra.re hblock, congrArg QuadraticAlgebra.im hblock⟩

theorem inert_good {p : ℕ} (hp : Nat.Prime p) (h : p%4=3) :
    (p:ℤ) ∣ B p ∧ ¬ (p:ℤ) ∣ A p := by
  obtain ⟨ha,hb⟩ := inert_block hp h
  refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hb, ?_⟩
  intro hz
  have h₂ : (2 : ZMod p) = 0 := ha.symm.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hz)
  have hn : (p:ℤ) ∣ (2:ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by simpa using h₂)
  have hd : p ∣ 2 := by exact_mod_cast hn
  have := Nat.le_of_dvd (by decide) hd
  omega

end ArctanCert.Periodic

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

namespace ArctanTail

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
      (⟨((z.1/(k : ℤ)-z.2 : ℤ) : ℝ),((z.1+z.2/(k : ℤ) : ℤ) : ℝ)⟩ : ℂ)‖ ≤ 2 := by
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  have hre : ((⟨(z.1 : ℝ),(z.2 : ℝ)⟩ : ℂ) * (⟨1/(k : ℝ),1⟩ : ℂ) -
      (⟨((z.1/(k : ℤ)-z.2 : ℤ) : ℝ),((z.1+z.2/(k : ℤ) : ℤ) : ℝ)⟩ : ℂ)).re =
      (z.1 : ℝ)/k - ((z.1/(k : ℤ) : ℤ) : ℝ) := by
    simp [Complex.sub_re,Complex.mul_re,div_eq_mul_inv]
  have him : ((⟨(z.1 : ℝ),(z.2 : ℝ)⟩ : ℂ) * (⟨1/(k : ℝ),1⟩ : ℂ) -
      (⟨((z.1/(k : ℤ)-z.2 : ℤ) : ℝ),((z.1+z.2/(k : ℤ) : ℤ) : ℝ)⟩ : ℂ)).im =
      (z.2 : ℝ)/k - ((z.2/(k : ℤ) : ℤ) : ℝ) := by
    simp [Complex.sub_im,Complex.mul_im,div_eq_mul_inv]
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
private lemma error_bounds (S : ℤ) (w : ℕ → ℤ × ℤ) (w0 : w 0=(S,0))
    (ws : ∀ j, w (j+1) = ((w j).1 / ((j+1 : ℕ) : ℤ) - (w j).2,
      (w j).1 + (w j).2 / ((j+1 : ℕ) : ℤ))) (n : ℕ) :
    |(S : ℝ)*(A n : ℝ)/(n.factorial : ℝ) - ((w n).1 : ℝ)| ≤ 4*(n : ℝ) ∧
    |(S : ℝ)*(B n : ℝ)/(n.factorial : ℝ) - ((w n).2 : ℝ)| ≤ 4*(n : ℝ) := by
  let p (t : ℕ) : ℂ := ⟨(S : ℝ)*(A t : ℝ)/(t.factorial : ℝ),(S : ℝ)*(B t : ℝ)/(t.factorial : ℝ)⟩
  let z (t : ℕ) : ℂ := ⟨((w t).1 : ℝ),((w t).2 : ℝ)⟩
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
      simp [p,z,w0,A,B,hg]
    | succ t ih =>
      have local_err : ‖z t*f t-z (t+1)‖ ≤ 2 := by
        simpa only [z,f,ws,Nat.cast_succ] using round_step (t+1) (by omega) (w t)
      rw [hp]
      calc
        ‖p t*f t-z (t+1)‖ = ‖(p t-z t)*f t + (z t*f t-z (t+1))‖ := by ring_nf
        _ ≤ ‖(p t-z t)*f t‖ + ‖z t*f t-z (t+1)‖ := norm_add_le _ _
        _ ≤ 4*(t : ℝ)*‖f t‖+2 := by rw [norm_mul]; exact add_le_add (mul_le_mul_of_nonneg_right ih (norm_nonneg _)) local_err
        _ ≤ 4*((t+1 : ℕ) : ℝ) := by simpa only [Nat.cast_succ,f] using step_norm_budget t
  exact ⟨(Complex.abs_re_le_norm (p n-z n)).trans (err n),(Complex.abs_im_le_norm (p n-z n)).trans (err n)⟩

/-- An exact integral slope must lie in the integer window determined by the two rounded coordinates. -/
lemma quotient_window (S m : ℤ) (w : ℕ → ℤ × ℤ) (w0 : w 0=(S,0))
    (ws : ∀ j, w (j+1) = ((w j).1 / ((j+1 : ℕ) : ℤ) - (w j).2,
      (w j).1 + (w j).2 / ((j+1 : ℕ) : ℤ))) (n : ℕ) (H : B n=A n*m) :
    |(w n).2-m*(w n).1| ≤ 4*(n : ℤ)*(1+|m|) := by
  let a := (S : ℝ)*(A n : ℝ)/(n.factorial : ℝ)
  let b := (S : ℝ)*(B n : ℝ)/(n.factorial : ℝ)
  obtain ⟨h₁,h₂⟩ := error_bounds S w w0 ws n
  change |a-((w n).1 : ℝ)| ≤ 4*(n : ℝ) at h₁
  change |b-((w n).2 : ℝ)| ≤ 4*(n : ℝ) at h₂
  have hb : b=(m : ℝ)*a := by dsimp only [b,a]; rw [H,Int.cast_mul]; ring
  have he : ((w n).2 : ℝ)-(m : ℝ)*((w n).1 : ℝ) =
      (m : ℝ)*(a-((w n).1 : ℝ))-(b-((w n).2 : ℝ)) := by rw [hb]; ring
  have hr : |((w n).2 : ℝ)-(m : ℝ)*((w n).1 : ℝ)| ≤ 4*(n : ℝ)*(1+|(m : ℝ)|) := by
    rw [he]
    calc
      _ ≤ |(m : ℝ)*(a-((w n).1 : ℝ))| + |b-((w n).2 : ℝ)| := abs_sub _ _
      _ ≤ |(m : ℝ)| * (4*(n : ℝ)) + 4*(n : ℝ) := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left h₁ (abs_nonneg _)) h₂
      _ = _ := by ring
  exact_mod_cast hr

end ArctanTail

namespace ArctanCert.Periodic

open Arxiv.«2607.05739»

/-- An inert-prime zero in the real coordinate of the short prefix excludes
every integer quotient at the original index. -/
lemma integer_avoids_inert {n : ℕ} (hint : IsIntegerValue n) (p : ℕ)
    (hp : p.Prime) (hmod : p%4=3) : ¬(p:ℤ) ∣ A (n%p) := by
  intro ha
  obtain ⟨hpb,hpa⟩ := inert_good hp hmod
  apply not_integer_of_residue hp hpb hpa ha _ hint
  intro hb
  let r := n%p
  have az : (A r : ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ha
  have bz : (B r : ZMod p)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hb
  have zeros (t : ℕ) : (A (r+t) : ZMod p)=0 ∧ (B (r+t) : ZMod p)=0 := by
    induction t with
    | zero => exact ⟨az,bz⟩
    | succ t ih =>
      obtain ⟨a,b⟩ := coordinate_mod_succ p (r+t)
      rw [Nat.add_succ,a,b,ih.1,ih.2]
      simp
  have h := (zeros (p-r)).1
  have hr : r≤p := (Nat.mod_lt _ hp.pos).le
  rw [show r+(p-r)=p by omega] at h
  exact hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

end ArctanCert.Periodic

namespace ArctanCert

open Arxiv.«2607.05739»

/-- The nonzero Gaussian product bounds the search for a putative integer slope. -/
lemma quotient_bounded {n : ℕ} {m : ℤ} (hm : B n = A n*m) : |m| ≤ 2*(n.factorial:ℤ) := by
  have prod_ne : gaussProd n ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk h
    have bad := congrArg Zsqrtd.re h
    exact (by decide : (1:ℤ)≠0) bad
  have ha : A n ≠ 0 := by
    intro h
    apply prod_ne
    apply Zsqrtd.ext
    · exact h
    · change B n=0
      rw [hm,h,zero_mul]
  calc
    |m| = 1 * |m| := (one_mul _).symm
    _ ≤ |A n| * |m| := mul_le_mul_of_nonneg_right (by have := abs_pos.mpr ha; omega) (abs_nonneg _)
    _ = |B n| := by rw [hm,abs_mul]
    _ ≤ 2*(n.factorial:ℤ) := factorial_bound n

end ArctanCert

namespace OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R1

open Arxiv.«2607.05739»

section InitialRange

/-- Exact nonintegrality through one million. -/
def H1 : Prop := ∀ n : ℕ, 5 ≤ n → n ≤ 1000000 → ¬ IsIntegerValue n

end InitialRange

section FilteredTail

/-- Exclude only the integer slopes that survive every inert, signed and real test. -/
def H2 : Prop :=
  ∀ n : ℕ, 1000000 < n →
    (∀ p : ℕ, p.Prime → p%4=3 → ¬(p:ℤ) ∣ A (n%p)) →
    (n ≤ 900000000000 → (10:ℤ)^119 * |A n| ≤ 2*(n.factorial:ℤ)) →
    let S : ℤ := 2^96 * ((n:ℤ)+1)^6
    let w : ℕ → ℤ × ℤ := Nat.rec (S,0) (fun j z =>
      (z.1 / ((j+1 : ℕ) : ℤ) - z.2, z.1 + z.2 / ((j+1 : ℕ) : ℤ)))
    ∀ m : ℤ, |m| ≤ 2*(n.factorial:ℤ) →
      (n ≤ 900000000000 → (10:ℤ)^119 ≤ |m|) →
      |(w n).2-m*(w n).1| ≤ 4*(n:ℤ)*(1+|m|) →
      (∀ k p : ℕ, 1 ≤ k → k ≤ n → p.Prime → n+k < p → p ∣ 1+k^2 →
        (m : ZMod p) = (k : ZMod p)) → B n ≠ A n*m

end FilteredTail

theorem main : H1 → H2 → type_of% @Arxiv.«2607.05739».tan_arctan_sum_not_integer := by
  intro finite tail n hn
  by_cases small : n ≤ 1000000
  · exact finite n hn small
  intro h
  obtain ⟨m,hm⟩ := h
  have hi : IsIntegerValue n := ⟨m,hm⟩
  let S : ℤ := 2^96 * ((n:ℤ)+1)^6
  let w : ℕ → ℤ × ℤ := Nat.rec (S,0) (fun j z =>
      (z.1 / ((j+1 : ℕ) : ℤ) - z.2, z.1 + z.2 / ((j+1 : ℕ) : ℤ)))
  have window := ArctanTail.quotient_window S m w rfl (fun _ => rfl) n hm
  exact tail n (by omega) (ArctanCert.Periodic.integer_avoids_inert hi)
    (fun bound => ArctanCRT.necessary_real_bound (by omega) bound hi) m
    (ArctanCert.quotient_bounded hm) (fun bound => ArctanCRT.quotient_large (by omega) bound hm)
    window (fun k p hk hkn hp hsize hd => ArctanCert.signed_residue hp hk hkn hsize hd hm) hm

end OMA.R_Arxiv_2607_05739_tan_arctan_sum_not_integer_R1
