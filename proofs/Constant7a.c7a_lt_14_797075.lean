import FormalConjectures.OptimizationConstants.«7a»
-- Problem: Tao Optimization Constant 7a / The Irrationality Measure of pi - c7a lt 14 797075
-- Upstream: formal-conjectures FormalConjectures/OptimizationConstants/7a.lean:127 (declaration Constant7a.c7a_lt_14_797075)
-- Credit: @my-other-github-account (the owner of the agent is credited as the solver)
-- Proof: Zeilberger-Zudilin linear forms (arXiv:1912.06345, Part II) with the weak denominator bound
-- d_n <= lcm(1..4n) <= e^(4.05 n) (no prime saving needed), giving mu(pi) <= 13 < 14.797075.
-- Includes an adaptation of the weak prime number theorem (WeakPNT, Wiener.lean, Consequences.lean)
-- from AlexKontorovich/PrimeNumberTheoremAnd 55270df8 (Apache-2.0), used for psi(x) ~ x.
import Mathlib
section
namespace ZZArithmetic
open PowerSeries
noncomputable section
abbrev S := PowerSeries ℚ
abbrev ZQ := (Int.castRingHom ℚ).range
def Good (f : S) := ∀ k, (2:ℚ)^(k/2) * coeff k f ∈ ZQ
lemma goodAdd {f g : S} (h : Good f) (i : Good g) : Good (f+g) := by
  intro k; rw [map_add, mul_add]; exact ZQ.add_mem (h k) (i k)
lemma intMem (z : ℤ) : (z:ℚ) ∈ ZQ := ⟨z,rfl⟩
lemma twoMem : (2:ℚ) ∈ ZQ := intMem 2
lemma goodMul {f g : S} (h : Good f) (i : Good g) : Good (f*g) := by
  intro k; rw [coeff_mul, Finset.mul_sum]; apply ZQ.sum_mem; rintro ⟨a,b⟩ hab
  have he : a+b=k := by simpa using hab
  let e := k/2 - (a/2+b/2)
  have hh : k/2 = e + (a/2+b/2) := by dsimp [e]; omega
  rw [hh, pow_add, pow_add]; convert ZQ.mul_mem (ZQ.pow_mem twoMem e) (ZQ.mul_mem (h a) (i b)) using 1; ring
lemma goodMono (k : ℕ) (q : ℚ) (h : (2:ℚ)^(k/2)*q ∈ ZQ) : Good (monomial k q) := by
  intro j; rw [coeff_monomial]; split_ifs with he
  · exact he ▸ h
  · simp
lemma goodTerm (k : ℕ) (q : ℚ) (h : (2:ℚ)^(k/2)*q ∈ ZQ) : Good (C q * (X:S)^k) := by
  simpa [monomial_eq_C_mul_X_pow] using goodMono k q h
lemma goodOne : Good (1:S) := by simpa using goodTerm 0 1 (by simp)
lemma goodPow {f : S} (h : Good f) (n : ℕ) : Good (f^n) := by
  induction n with
  | zero => simpa using goodOne
  | succ n ih => simpa [pow_succ] using goodMul ih h
def lin : S := C (-1:ℚ)*X^0 + C (2:ℚ)*X^1
def quart : S := C (1:ℚ)*X^0 + C (-7:ℚ)*X^1 + C (39/2:ℚ)*X^2 + C (-25:ℚ)*X^3 + C (25/2:ℚ)*X^4
lemma goodLin : Good lin := by
  unfold lin; apply goodAdd <;> apply goodTerm <;> norm_num
lemma goodQuart : Good quart := by
  unfold quart; repeat' apply goodAdd
  all_goals apply goodTerm; norm_num
def F (n : ℕ) : S := lin^(2*n) * quart^(2*n) * (mk (1 : ℕ → ℚ))^(3*n+1)
lemma goodF (n : ℕ) : Good (F n) := by
  apply goodMul (goodMul (goodPow goodLin _) (goodPow goodQuart _)); apply goodPow
  intro k; simpa [coeff_mk] using ZQ.pow_mem twoMem (k/2)
lemma lin_id : C (5:ℚ) * lin = 10*X - 5 := by
  simp [lin, mul_add, ← mul_assoc, ← map_mul]; norm_num [map_ofNat]; ring
lemma quart_id : C (800:ℚ) * quart = (10*X-5)^4 + 6*(10*X-5)^2 + 25 := by
  simp only [quart, mul_add, ← mul_assoc, ← map_mul]; norm_num; simp only [map_ofNat]; ring
def amp (n : ℕ) : ℚ := (2:ℚ)^(7*n) * 5^(3*n) / 2
def localSeries (n : ℕ) : S := C (amp n) * rescale (1/10:ℚ) (F n)
def A (n j : ℕ) : ℚ := coeff (3*n-j) (localSeries n)
lemma amp_id (n : ℕ) : amp n * 10^(3*n+1) = 5 * 5^(2*n) * 800^(2*n) := by
  unfold amp; rw [pow_succ]; simp only [pow_mul, ← mul_pow]; ring_nf; rw [← mul_pow, ← mul_pow]; norm_num
lemma normalized_identity (n : ℕ) :
    (C (amp n) * F n) * (10-10*X)^(3*n+1) =
    5*(10*X-5)^(2*n)*((10*X-5)^4+6*(10*X-5)^2+25)^(2*n) := by
  rw [← quart_id, ← lin_id]; unfold F
  have h : (10-10*X:S) = C (10:ℚ)*(1-X) := by simp only [map_ofNat]; ring
  rw [h]; simp only [mul_pow];
  have hg := congrArg (fun a : S => a^(3*n+1)) (mk_one_mul_one_sub_eq_one (S:=ℚ))
  simp only [mul_pow, one_pow] at hg
  have hc := congrArg (C : ℚ →+* S) (amp_id n)
  simp only [map_mul, map_pow, map_ofNat] at hc
  calc
    _ = (C (amp n)*10^(3*n+1)) * (lin^(2*n)*quart^(2*n)) *
        ((mk (1:ℕ → ℚ))^(3*n+1)*(1-X)^(3*n+1)) := by simp only [map_ofNat]; ring
    _ = _ := by rw [hc,hg]; simp only [map_ofNat]; ring
lemma local_identity (n : ℕ) : localSeries n * (10-X)^(3*n+1) =
    5*(X-5)^(2*n)*((X-5)^4+6*(X-5)^2+25)^(2*n) := by
  have h := congrArg (rescale (1/10:ℚ)) (normalized_identity n)
  have hx : (10:S) * (C (1/10:ℚ)*X) = X := by
    rw [← mul_assoc, ← map_ofNat (C : ℚ →+* S) 10, ← map_mul]; norm_num
  have hC (a : ℚ) : rescale (1/10:ℚ) (C a) = C a := by
    ext k; simp [coeff_C]; split_ifs with h <;> simp_all
  simpa only [localSeries, map_add, map_mul, map_pow, map_sub, map_ofNat, rescale_X, hx, hC] using h
theorem lemmaOne (n j : ℕ) (hj : j ≤ 3*n) :
    ∃ z : ℤ, 2*A n j = (2:ℚ)^((5*n+3*j)/2) * 5^j * z := by
  let k := 3*n-j
  let e := 7*n - (k+k/2+(5*n+3*j)/2)
  have hk : k+j = 3*n := by dsimp [k]; omega
  have he : 7*n = e+k+k/2+(5*n+3*j)/2 := by dsimp [e,k]; omega
  obtain ⟨z,hz⟩ := goodF n k
  change (z:ℚ) = 2^(k/2)*coeff k (F n) at hz
  refine ⟨2^e*z, ?_⟩
  change 2 * coeff k (localSeries n) = _
  simp only [localSeries, coeff_C_mul, coeff_rescale, amp, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, hz]
  rw [he, ← hk]; simp only [pow_add, one_div, inv_pow]; field_simp
  rw [show (10:ℚ)^k = 2^k*5^k by rw [← mul_pow]; norm_num]
lemma A_integral (n j : ℕ) (hn : 0 < n) (hj : j ≤ 3*n) : A n j ∈ ZQ := by
  obtain ⟨z,hz⟩ := lemmaOne n j hj
  let e := (5*n+3*j)/2-1
  have he : (5*n+3*j)/2 = e+1 := by dsimp [e]; omega
  rw [he,pow_succ] at hz
  use (2:ℤ)^e*5^j*z
  change (((2:ℤ)^e*5^j*z : ℤ) : ℚ) = _
  push_cast; linarith
lemma A_zero : A 0 0 = 1/2 := by norm_num [A, localSeries, amp, F, coeff_mk]
end
end ZZArithmetic
end

section
namespace ZZGlobal
noncomputable section
open Polynomial ZZArithmetic
abbrev QP := Polynomial ℚ
abbrev m (n : ℕ) := 3*n+1
def T (n : ℕ) : QP := PowerSeries.trunc (m n) (localSeries n)
def N {R : Type*} [CommRing R] (n : ℕ) (x : R) : R := 5*x^(2*n)*(x^4+6*x^2+25)^(2*n)
lemma N_neg {R : Type*} [CommRing R] (n : ℕ) (x : R) : N n (-x) = N n x := by
  simp [N, pow_mul, show (-x)^4=x^4 by ring]
lemma local_dvd (n : ℕ) : (X:QP)^m n ∣ N n (X-5) - T n*(10-X)^m n := by
  apply Polynomial.X_pow_dvd_iff.mpr
  simp_rw [← Polynomial.coeff_coe]
  apply (PowerSeries.X_pow_dvd_iff (n := m n) (φ := ((N n (X-5) - T n*(10-X)^m n : QP) : ZZArithmetic.S))).mp
  have h := PowerSeries.eq_X_pow_mul_shift_add_trunc (m n) (localSeries n)
  refine ⟨PowerSeries.mk (fun i => PowerSeries.coeff (i+m n) (localSeries n)) * (10-PowerSeries.X)^m n, ?_⟩
  have hc (k : ℕ) [k.AtLeastTwo] : ((OfNat.ofNat k : QP) : S) = OfNat.ofNat k := map_ofNat Polynomial.coeToPowerSeries.ringHom k
  simp only [N, Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_X, hc 5, hc 6, hc 10, hc 25, ← local_identity, T, m]
  linear_combination h * (10-PowerSeries.X)^(3*n+1)
def D (n : ℕ) (x : QP) := (5+x)^m n*(5-x)^m n
def B (n : ℕ) (x : QP) := N n x - aeval (5+x) (T n)*(5-x)^m n - aeval (5-x) (T n)*(5+x)^m n
lemma left_dvd (n : ℕ) (x : QP) : (5+x)^m n ∣ B n x := by
  obtain ⟨p,h⟩ := local_dvd n
  have hh := congrArg (aeval (5+x)) h
  simp only [N, map_sub, map_mul, map_pow, map_add, map_ofNat, aeval_X,
    show 5+x-5=x by ring, show 10-(5+x)=5-x by ring] at hh
  exact dvd_sub (Dvd.intro (aeval (5+x) p) hh.symm) (dvd_mul_left _ _)
lemma B_neg (n : ℕ) (x : QP) : B n (-x) = B n x := by
  simp [B, N_neg, sub_eq_add_neg]; ring
lemma global_dvd (n : ℕ) : D n X ∣ B n X := by
  have hc : IsCoprime (5+(X:QP)) (5-X) := by
    refine ⟨C (1/10), C (1/10), ?_⟩
    calc _ = C (1/10:ℚ)*(10:QP) := by ring
         _ = 1 := by rw [← map_ofNat (C : ℚ →+* QP) 10, ← map_mul]; norm_num
  exact hc.pow.mul_dvd (left_dvd n X) (by simpa only [B_neg, ← sub_eq_add_neg] using left_dvd n (-X))
def P (n : ℕ) : QP := (global_dvd n).choose
lemma B_eq (n : ℕ) : B n X = D n X * P n := (global_dvd n).choose_spec
lemma substitute {K : Type*} [CommRing K] [Algebra ℚ K] (n : ℕ) (x : K) :
    N n x - aeval (5+x) (T n)*(5-x)^m n - aeval (5-x) (T n)*(5+x)^m n =
    ((5+x)^m n*(5-x)^m n)*aeval x (P n) := by
  have h := congrArg (aeval x) (B_eq n)
  simpa only [B,D,N, ← aeval_algHom_apply, map_sub, map_add, map_mul, map_pow, map_ofNat, aeval_X] using h
lemma P_even (n : ℕ) : aeval (-X:QP) (P n) = P n := by
  have h := substitute n (-X:QP)
  change B n (-X) = D n (-X) * _ at h
  rw [B_neg, B_eq, show D n (-X) = D n X by simp [D,sub_eq_add_neg,mul_comm]] at h
  apply mul_left_cancel₀ _ h.symm
  apply mul_ne_zero <;> apply pow_ne_zero <;> intro he
  all_goals have := congrArg (eval (0:ℚ)) he; norm_num at this
lemma poles {K : Type*} [Field K] [Algebra ℚ K] (n : ℕ) (u : K) (hu : u ≠ 0) :
    aeval u (T n) / u^m n = ∑ j ∈ Finset.range (m n), algebraMap ℚ K (A n j) / u^(j+1) := by
  rw [aeval_def, T, PowerSeries.eval₂_trunc_eq_sum_range, Finset.sum_div,
    ← Finset.sum_range_reflect (fun i => algebraMap ℚ K (PowerSeries.coeff i (localSeries n)) * u^i / u^m n)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have he : m n = (3*n-j)+(j+1) := by dsimp [m] at *; omega
  simp only [m,Nat.add_one_sub_one,A]
  rw [show 3*n+1=(3*n-j)+(j+1) from he, pow_add]; field_simp
theorem eqThree {K : Type*} [Field K] [Algebra ℚ K] (n : ℕ) (x : K)
    (hl : 5+x ≠ 0) (hr : 5-x ≠ 0) :
    N n x / ((5+x)^m n*(5-x)^m n) = aeval x (P n) + ∑ j ∈ Finset.range (3*n+1),
      (algebraMap ℚ K (A n j)/(5+x)^(j+1) + algebraMap ℚ K (A n j)/(5-x)^(j+1)) := by
  rw [Finset.sum_add_distrib, ← poles n _ hl, ← poles n _ hr]
  field_simp [hl,hr]
  linear_combination substitute n x
lemma degL : (5+(X:QP)).natDegree = 1 := by compute_degree!
lemma degR : (5-(X:QP)).natDegree = 1 := by compute_degree!
lemma degN (n : ℕ) : (N n (X:QP)).natDegree = 10*n := by
  have hq : ((X:QP)^4+6*X^2+25).natDegree = 4 := by compute_degree!
  have hq' : (X:QP)^4+6*X^2+25 ≠ 0 := by intro h; simp [h] at hq
  unfold N
  rw [natDegree_mul (mul_ne_zero (by norm_num) (pow_ne_zero _ X_ne_zero)) (pow_ne_zero _ hq'),
    natDegree_mul (by norm_num) (pow_ne_zero _ X_ne_zero), natDegree_pow, natDegree_pow, hq]
  simp; omega
lemma degTail (n : ℕ) (u v : QP) (hu : u.natDegree=1) (hv : v.natDegree=1) :
    (aeval u (T n)*v^m n).natDegree < 2*m n := by
  have h := natDegree_mul_le (p := aeval u (T n)) (q := v^m n)
  change ((T n).comp u * v^m n).natDegree ≤ ((T n).comp u).natDegree + _ at h
  rw [natDegree_comp, hu, natDegree_pow, hv, mul_one, mul_one] at h
  have ht : (T n).natDegree < m n := PowerSeries.natDegree_trunc_lt _ _
  change ((T n).comp u * v^m n).natDegree < _; omega
lemma degD (n : ℕ) : (D n X).natDegree = 2*m n := by
  have hl := degL; have hr := degR
  have l : 5+(X:QP) ≠ 0 := by intro h; simp [h] at hl
  have r : 5-(X:QP) ≠ 0 := by intro h; simp [h] at hr
  simp [D,natDegree_mul (pow_ne_zero _ l) (pow_ne_zero _ r), natDegree_pow, hl,hr]; omega
lemma degP (n : ℕ) (hn : 0 < n) : (P n).natDegree = 4*n-2 := by
  have hl := degTail n _ _ degL degR
  have hr := degTail n _ _ degR degL
  have hlt : 2*m n ≤ 10*n := by dsimp [m]; omega
  have hb : (B n X).natDegree = 10*n := by
    unfold B
    have h := natDegree_sub_eq_left_of_natDegree_lt (lt_of_lt_of_le hl (hlt.trans_eq (degN n).symm))
    rw [natDegree_sub_eq_left_of_natDegree_lt (hr.trans_le (hlt.trans_eq (h.trans (degN n)).symm)),h,degN]
  rw [B_eq] at hb
  have hp : P n ≠ 0 := by intro h; simp [h] at hb; omega
  have hd : D n X ≠ 0 := by intro h; have := degD n; simp [h,m] at this
  rw [natDegree_mul hd hp,degD] at hb
  dsimp [m] at hb; omega
def G {R : Type*} [CommRing R] (n : ℕ) : Polynomial R := ((X+5)*(X-5))^m n
lemma monicG {R : Type*} [CommRing R] (n : ℕ) : (G (R:=R) n).Monic :=
  ((monic_X_add_C (5:R)).mul (monic_X_sub_C (5:R))).pow _
def PInt (n : ℕ) : Polynomial ℤ := ((-1)^m n * N n X) /ₘ G n
lemma integralP (n : ℕ) : (PInt n).map (Int.castRingHom ℚ) = P n := by
  unfold PInt
  rw [map_divByMonic _ (monicG n)]
  simp only [N,G,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_sub,
    Polynomial.map_X,Polynomial.map_neg,Polynomial.map_one,Polynomial.map_ofNat]
  change ((-1)^m n * N n X) /ₘ (G n : QP) = P n
  let r : QP := aeval (5+X) (T n)*(5-X)^m n + aeval (5-X) (T n)*(5+X)^m n
  have hr : r.natDegree < 2*m n := (natDegree_add_le _ _).trans_lt
    (max_lt (degTail n _ _ degL degR) (degTail n _ _ degR degL))
  have hg : (G n : QP) = (-1)^m n * D n X := by
    unfold G D; rw [← mul_pow, ← mul_pow]; congr 1; ring
  have hgd : (G n : QP).natDegree = 2*m n := by
    rw [hg,natDegree_mul (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (by
      intro h; have := degD n; simp [h,m] at this), natDegree_pow, natDegree_neg, natDegree_one, degD]; simp
  apply (div_modByMonic_unique (P n) ((-1)^m n*r) (monicG n) ⟨?_,?_⟩).1
  · rw [hg]; have hb := B_eq n; unfold B at hb; dsimp [r]; linear_combination (-(-1:QP)^m n)*hb
  · apply degree_lt_degree
    apply natDegree_mul_le.trans_lt
    simpa [hgd,natDegree_pow] using hr
end
end ZZGlobal
end

section
namespace ZZDen
noncomputable section
open Finset
 def primes (n : ℕ) : Finset ℕ := (range (2*n+1)).filter fun p => p.Prime ∧ 5 < p ∧ 3*n < p*p ∧ p ≤ 2*(n%p) ∧ 3*(n%p) < 2*p
 def phi (n : ℕ) : ℕ := (primes n).prod id
 def lcm4 (n : ℕ) : ℕ := (range (4*n)).lcm (·+1)
 def L (n : ℕ) : ℕ := lcm4 n / phi n
end
end ZZDen
end

section
namespace ZZSaving
open PowerSeries
noncomputable section
variable {p : ℕ} [Fact p.Prime]
private def y (R : Type*) [CommRing R] : PowerSeries R := 2*X-1
private lemma cancelMono (hp : 5 < p) (i k : ℕ) (hi : i+1 < p) (hk : p ∣ k+1) (H : (PowerSeries (ZMod p))) :
    coeff k ((y (ZMod p))^(2*i+1)*H^p) = 0 := by
  let D := derivative (ZMod p)
  have hy : D (y (ZMod p)) = 2 := by simp [D,y,show (2:(PowerSeries (ZMod p)))=1+1 by norm_num,add_mul]
  have hd : D (H^p) = 0 := by
    have hz : (p:(PowerSeries (ZMod p))) = 0 := by rw [← map_natCast (C : (ZMod p) →+* (PowerSeries (ZMod p)))]; simp
    simp [D,hz]
  have h := coeff_derivative ((y (ZMod p))^(2*i+2)*H^p) k
  have hkp : ((k+1:ℕ):(ZMod p)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hk
  push_cast at hkp
  change coeff k (D _) = _ at h
  rw [hkp,mul_zero,Derivation.leibniz, hd, smul_zero,zero_add, smul_eq_mul] at h
  simp only [D,derivative_pow] at h
  change derivative (ZMod p) (y (ZMod p)) = 2 at hy
  rw [hy, show 2*i+2-1=2*i+1 by omega] at h
  have he : H^p * ((2*i+2:(PowerSeries (ZMod p)))*y (ZMod p)^(2*i+1)*2) = C ((4:(ZMod p))*(i+1)) * (y (ZMod p)^(2*i+1)*H^p) := by
    simp only [map_mul,map_add,map_one,map_natCast,map_ofNat]; ring
  push_cast at h
  rw [he,coeff_C_mul] at h
  have h4 : (4:(ZMod p)) ≠ 0 := by exact_mod_cast ((ZMod.natCast_eq_zero_iff _ _).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 4) (by omega : 4 < p)))
  have hi' : (i:(ZMod p))+1 ≠ 0 := by exact_mod_cast ((ZMod.natCast_eq_zero_iff _ _).not.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hi))
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero h4 hi')
private lemma cancelPoly (hp : 5 < p) (k : ℕ) (hk : p ∣ k+1) (H : (PowerSeries (ZMod p)))
    (P : Polynomial (ZMod p)) (hP : P.natDegree + 1 < p) :
    coeff k (y (ZMod p) * Polynomial.aeval (y (ZMod p) ^ 2) P * H^p) = 0 := by
  classical
  rw [P.as_sum_support_C_mul_X_pow]
  simp only [map_sum,map_mul,map_pow,Polynomial.aeval_X,Polynomial.aeval_C, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  have he : y (ZMod p) * (algebraMap (ZMod p) (PowerSeries (ZMod p)) (P.coeff i) * (y (ZMod p)^2)^i) * H^p = C (P.coeff i) * (y (ZMod p)^(2*i+1)*H^p) := by
    rw [pow_succ _ (2*i),pow_mul]; change _ = algebraMap (ZMod p) (PowerSeries (ZMod p)) _ * _; ring
  rw [he,coeff_C_mul,cancelMono hp i k (by have := Polynomial.le_natDegree_of_mem_supp _ hi; omega) hk, mul_zero]
private def f (R : Type*) [CommRing R] : PowerSeries R := y R * (25*y R^4 + 6*y R^2 + 1)
private def g (R : Type*) [CommRing R] : PowerSeries R := mk 1
private def B (R : Type*) [CommRing R] (n : ℕ) := f R ^(2*n) * g R^(3*n+1)
private lemma core (hp : 5 < p) (s d e k : ℕ) (hs : s=2*d+1) (hdeg : d+2*s+e+1 < p)
    (hk : p ∣ k+1) (H : (PowerSeries (ZMod p))) : coeff k (f (ZMod p)^s * (1-y (ZMod p)^2)^e * H^p) = 0 := by
  let T : Polynomial (ZMod p) := Polynomial.X
  let P := T^d * (25*T^2+6*T+1)^s * (1-T)^e
  have hP : P.natDegree ≤ d+2*s+e := by
    dsimp [P,T]; compute_degree; omega
  have h := cancelPoly hp k hk H P (by omega)
  simp only [P,T,map_mul,map_pow,map_add,map_sub,map_one,map_ofNat,Polynomial.aeval_X] at h
  convert h using 2
  unfold f
  rw [mul_pow, hs, pow_succ (y (ZMod p)) (2*d),pow_mul]; ring
private theorem modB (hp : 5 < p) (n k : ℕ) (lo : p ≤ 2*(n%p)) (up : 3*(n%p)<2*p)
    (hk : k ≡ 3*n [MOD p]) : coeff k (B (ZMod p) n) = 0 := by
  let r := n%p
  let q := n/p
  let s := 2*r-p
  let e := 2*p-(3*r+1)
  let d := s/2
  have nr : n = r+p*q := (Nat.mod_add_div n p).symm
  have ho := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨v,hv⟩ := ho
  change p ≤ 2*r at lo; change 3*r < 2*p at up
  have hs : s=2*d+1 := by dsimp [s,d]; omega
  have he : 3*r+1+e = 2*p := by dsimp [e]; omega
  have h1 : 2*n = s+(2*q+1)*p := by
    have : s+p=2*r := by dsimp [s]; omega
    rw [nr]; nlinarith only [this]
  have h2 : 3*n+1+e = (3*q+2)*p := by rw [nr]; nlinarith only [he]
  let H := f (ZMod p)^(2*q+1)*g (ZMod p)^(3*q+2)
  have hfac : X^e * B (ZMod p) n * (4:(PowerSeries (ZMod p)))^e = f (ZMod p)^s * (1-y (ZMod p)^2)^e * H^p := by
    have hgeom := @mk_one_mul_one_sub_eq_one (ZMod p) _
    change g (ZMod p) * (1-X)=1 at hgeom
    have hg := congrArg (fun z:(PowerSeries (ZMod p)) => z^e) hgeom
    simp only [mul_pow,one_pow] at hg
    have hy : 1-y (ZMod p)^2 = 4*X*(1-X) := by unfold y; ring
    unfold B H; rw [mul_pow (f (ZMod p) ^ _) (g (ZMod p) ^ _), ← pow_mul, ← pow_mul, ← h2, pow_add (g (ZMod p)) (3*n+1), h1, pow_add, hy]; simp only [mul_pow]
    linear_combination (norm := ring_nf) -(X^e*f (ZMod p)^s*(f (ZMod p)) ^ ((2*q+1)*p)*(g (ZMod p))^(3*n+1)*(4:(PowerSeries (ZMod p)))^e) * (hg)
  have hk' : p ∣ k+e+1 := by
    have hc : k+e+1 ≡ 3*n+e+1 [MOD p] := (hk.add_right e).add_right 1
    rw [show 3*n+e+1=(3*q+2)*p by omega] at hc
    exact Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hc)
  have hz := core hp s d e (k+e) hs (by dsimp [d,s,e]; omega) hk' H
  rw [← hfac, mul_comm _ ((4:(PowerSeries (ZMod p)))^e), ← map_ofNat (C : (ZMod p) →+* (PowerSeries (ZMod p))) 4, ← map_pow,coeff_C_mul,
      mul_comm (X^e),coeff_mul_X_pow] at hz
  have h4 : (4:(ZMod p)) ≠ 0 := by exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 4) (by omega : 4 < p))
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ h4)
private lemma mapB {R T : Type*} [CommRing R] [CommRing T] (u : R →+* T) (n : ℕ) :
    map u (B R n) = B T n := by
  have hm : map u (g R) = g T := by ext k; simp [g,coeff_mk]
  simp [B,f,y,map_X,hm,map_ofNat]
private lemma ratB (n : ℕ) : B ℚ n = C ((32:ℚ)^(2*n)) * ZZArithmetic.F n := by
  have h : f ℚ = C (32:ℚ) * (ZZArithmetic.lin*ZZArithmetic.quart) := by
    have hq : C (32:ℚ)*ZZArithmetic.quart = 25*y ℚ^4+6*y ℚ^2+1 := by
      unfold ZZArithmetic.quart y; simp only [mul_add,← mul_assoc,← map_mul]; norm_num [map_ofNat]; ring
    unfold f; rw [← hq]; simp [ZZArithmetic.lin,y,map_ofNat]; ring
  simp only [B,h,ZZArithmetic.F,mul_pow,map_pow,g]; ring
private lemma scaleB (n k : ℕ) :
    (2:ℚ)*10^k*32^(2*n)*coeff k (ZZArithmetic.localSeries n) =
      2^(7*n)*5^(3*n)*((coeff k (B ℤ n):ℤ):ℚ) := by
  have h := congrArg (coeff k) (mapB (Int.castRingHom ℚ) n)
  rw [coeff_map, ratB,coeff_C_mul] at h
  change ((coeff k (B ℤ n):ℤ):ℚ) = _ at h
  rw [h]; simp only [ZZArithmetic.localSeries,coeff_C_mul,coeff_rescale,ZZArithmetic.amp,one_div,inv_pow]; field_simp
private lemma intB (hp : 5 < p) (n k : ℕ) (lo : p ≤ 2*(n%p)) (up : 3*(n%p)<2*p)
    (hk : k ≡ 3*n [MOD p]) : (p:ℤ) ∣ coeff k (B ℤ n) := by
  have h := congrArg (coeff k) (mapB (Int.castRingHom (ZMod p)) n)
  rw [coeff_map, modB hp n k lo up hk] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
theorem A_prime_saving (hp : 5 < p) (n j : ℕ) (hj : j ≤ 3*n) (hpj : p ∣ j)
    (lo : p ≤ 2*(n%p)) (up : 3*(n%p)<2*p) :
    ∃ w : ℤ, ZZArithmetic.A n j = (p:ℚ)*w := by
  have hn : n ≠ 0 := by rintro rfl; simp at lo; omega
  obtain ⟨z,hz⟩ := ZZArithmetic.A_integral n j (Nat.pos_of_ne_zero hn) hj
  change (z:ℚ) = ZZArithmetic.A n j at hz
  let k := 3*n-j
  have hk : k+j=3*n := by dsimp [k]; omega
  have hm : k ≡ 3*n [MOD p] := by
    rw [← hk]; simpa using (Nat.modEq_zero_iff_dvd.mpr hpj).symm.add_left k
  have hc := scaleB n k
  change (z:ℚ) = coeff k _ at hz
  rw [← hz] at hc
  have hI : (2:ℤ)*10^k*32^(2*n)*z = 2^(7*n)*5^(3*n)*coeff k (B ℤ n) := by exact_mod_cast hc
  have hc' := congrArg (Int.castRingHom (ZMod p)) hI
  simp only [map_mul,map_pow,map_ofNat,Int.coe_castRingHom] at hc'
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (intB hp n k lo up hm),mul_zero] at hc'
  have hnz (a : ℕ) (ha : 0 < a) (h : a<p) : (a:(ZMod p)) ≠ 0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr (Nat.not_dvd_of_pos_of_lt ha h)
  have h2 : (2:(ZMod p)) ≠ 0 := hnz 2 (by decide) (by omega)
  have h5 : (5:(ZMod p)) ≠ 0 := hnz 5 (by decide) hp
  have h10 : (10:(ZMod p)) ≠ 0 := by convert mul_ne_zero h2 h5 using 1; norm_num
  have h32 : (32:(ZMod p)) ≠ 0 := by convert pow_ne_zero 5 h2 using 1; norm_num
  have hzp := (mul_eq_zero.mp hc').resolve_left (mul_ne_zero (mul_ne_zero h2 (pow_ne_zero _ h10)) (pow_ne_zero _ h32))
  obtain ⟨w,hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hzp
  exact ⟨w, by change coeff k _ = _; rw [← hz,hw]; push_cast; rfl⟩
theorem laurent_prime_saving (hp : 5 < p) (n k : ℕ) (hk : k ≡ 3*n [MOD p])
    (hr : k < 7*n) (lo : p ≤ 2*(n%p)) (up : 3*(n%p)<2*p) :
    ∃ w : ℤ, (10:ℚ)^k / 10^(3*n) * coeff k (ZZArithmetic.localSeries n) = (p:ℚ)*w := by
  obtain ⟨z,hz⟩ := ZZArithmetic.goodF n k
  change (z:ℚ) = 2^(k/2)*coeff k (ZZArithmetic.F n) at hz
  have hb := congrArg (coeff k) (mapB (Int.castRingHom ℚ) n)
  rw [coeff_map,ratB,coeff_C_mul] at hb
  change ((coeff k (B ℤ n):ℤ):ℚ) = _ at hb
  have heq : (32:ℤ)^(2*n)*z = 2^(k/2)*coeff k (B ℤ n) := by
    have hh : (32:ℚ)^(2*n)*z = 2^(k/2)*((coeff k (B ℤ n):ℤ):ℚ) := by rw [hz,hb]; ring
    exact_mod_cast hh
  have hh := congrArg (Int.castRingHom (ZMod p)) heq
  simp only [map_mul,map_pow,map_ofNat,Int.coe_castRingHom] at hh
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (intB hp n k lo up hk),mul_zero] at hh
  have h2 : (2:(ZMod p)) ≠ 0 := by exact_mod_cast (ZMod.natCast_eq_zero_iff _ _).not.mpr (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) (by omega : 2 < p))
  have h32 : (32:(ZMod p)) ≠ 0 := by convert pow_ne_zero 5 h2 using 1; norm_num
  obtain ⟨w,hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ h32))
  let e := 4*n-(k/2+1)
  have he : 7*n = 3*n+1+e+k/2 := by dsimp [e]; omega
  refine ⟨2^e*w, ?_⟩
  have hzw : (z:ℚ) = (p:ℚ)*w := by exact_mod_cast hw
  simp only [ZZArithmetic.localSeries,coeff_C_mul,coeff_rescale,ZZArithmetic.amp,Int.cast_mul,Int.cast_pow,Int.cast_ofNat]
  rw [he, show (10:ℚ)^(3*n) = 2^(3*n)*5^(3*n) by rw [← mul_pow]; norm_num]
  simp only [pow_add,pow_one,one_div,inv_pow]; field_simp
  linear_combination hzw-hz
end
end ZZSaving
end

section
namespace ZZClear
open ZZDen
lemma memP {p n : ℕ} (h : p ∈ primes n) : p.Prime ∧ 5 < p ∧ 3*n < p*p ∧ p ≤ 2*(n%p) ∧ 3*(n%p) < 2*p := (Finset.mem_filter.mp h).2
lemma dvd4 {j n : ℕ} (hj : 0 < j) (hu : j ≤ 4*n) : j ∣ lcm4 n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  exact Finset.dvd_lcm (f:=fun i => i+1) (Finset.mem_range.mpr (by omega))
lemma pdvd4 {p n : ℕ} (h : p ∈ primes n) : p ∣ lcm4 n := dvd4 (memP h).1.pos (by
  have := Finset.mem_range.mp (Finset.mem_filter.mp h).1; omega)
lemma prodDiv (n : ℕ) (a : ℤ) (h : ∀ p ∈ primes n, (p:ℤ) ∣ a) : (phi n : ℤ) ∣ a := by
  simp only [phi,Nat.cast_prod,id_eq]
  refine Finset.prod_dvd_of_coprime (fun p hp q hq hne => ?_) h
  exact ((Nat.coprime_primes (memP hp).1 (memP hq).1).mpr hne).isCoprime
lemma phi_dvd (n : ℕ) : phi n ∣ lcm4 n := by
  exact_mod_cast prodDiv n (lcm4 n) (fun p hp => by exact_mod_cast pdvd4 hp)
lemma clear (n j : ℕ) (z : ℤ) (hj : 0 < j) (hu : j ≤ 4*n)
    (h : ∀ p ∈ primes n, p ∣ j → (p:ℤ) ∣ z) : (j:ℤ) ∣ (L n : ℤ)*z := by
  let k := lcm4 n / j
  have hk : k*j = lcm4 n := Nat.div_mul_cancel (dvd4 hj hu)
  have hs : L n * phi n = lcm4 n := Nat.div_mul_cancel (phi_dvd n)
  have hpos : phi n ≠ 0 := by
    unfold phi; exact Finset.prod_ne_zero_iff.mpr (fun p hp => (memP hp).1.ne_zero)
  obtain ⟨w,hw⟩ := prodDiv n ((k:ℤ)*z) (by
    intro p hp; by_cases hh : p ∣ j
    · exact dvd_mul_of_dvd_right (h p hp hh) _
    · have hh' := pdvd4 hp; rw [← hk] at hh'
      have : p ∣ k := ((memP hp).1.dvd_mul.mp hh').resolve_right hh
      exact dvd_mul_of_dvd_left (by exact_mod_cast this : (p:ℤ) ∣ k) _)
  refine ⟨w, ?_⟩
  have he : (L n : ℤ)*phi n = (k:ℤ)*j := by exact_mod_cast hs.trans hk.symm
  apply mul_right_cancel₀ (by exact_mod_cast hpos : (phi n : ℤ) ≠ 0)
  linear_combination z*he+(j:ℤ)*hw
lemma clearA (n j : ℕ) (hj : 0 < j) (hu : j ≤ 3*n) : ∃ z w : ℤ,
    2*ZZArithmetic.A n j = (2:ℚ)^((5*n+3*j)/2)*5^j*z ∧ (L n : ℤ)*z = j*w := by
  obtain ⟨z,hz⟩ := ZZArithmetic.lemmaOne n j hu
  refine ⟨z, ?_⟩
  obtain ⟨w,hw⟩ := clear n j z hj (by omega) (by
    intro p hp hd
    have hm := memP hp
    letI : Fact p.Prime := ⟨hm.1⟩
    obtain ⟨u,hu'⟩ := ZZSaving.A_prime_saving hm.2.1 n j hu hd hm.2.2.2.1 hm.2.2.2.2
    rw [hu'] at hz
    have hzi : (2:ℤ)*((p:ℤ)*u) = 2^((5*n+3*j)/2)*5^j*z := by exact_mod_cast hz
    have hzm := congrArg (Int.castRingHom (ZMod p)) hzi
    simp only [map_mul,map_pow,map_ofNat,Int.coe_castRingHom,Int.cast_natCast,ZMod.natCast_self,zero_mul,mul_zero] at hzm
    have hn (a : ℕ) (ha : 0 < a) (hap : a < p) : (a : ZMod p) ≠ 0 :=
      fun h => Nat.not_dvd_of_pos_of_lt ha hap ((ZMod.natCast_eq_zero_iff _ _).mp h)
    have h2 : (2 : ZMod p) ≠ 0 := by exact_mod_cast hn 2 (by decide) (by omega)
    have h5 : (5 : ZMod p) ≠ 0 := by exact_mod_cast hn 5 (by decide) hm.2.1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((mul_eq_zero.mp hzm.symm).resolve_left (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h5))))
  exact ⟨w,hz,hw⟩
end ZZClear
end

section
namespace ZZModPoly
open Polynomial
variable {K : Type*} [Field K]
def Good (p : ℕ) (f : K[X]) := ∀ k, p ∣ k+1 → f.coeff k = 0
def Sparse (p : ℕ) (f : K[X]) := ∀ k, ¬p ∣ k → f.coeff k = 0
lemma mulGood {p : ℕ} {f g : K[X]} (hf : Good p f) (hg : Sparse p g) : Good p (f*g) := by
  intro k hk; rw [coeff_mul]; apply Finset.sum_eq_zero
  intro ⟨i,j⟩ hij; have he : i+j=k := by simpa using hij
  by_cases hj : p ∣ j
  · rw [hf i (by have h : p ∣ (i+1)+j := by simpa [← he,add_assoc,add_comm,add_left_comm] using hk
                 exact (Nat.dvd_add_left hj).mp h), zero_mul]
  · rw [hg j hj,mul_zero]
lemma monoGood {p d : ℕ} (hd : ¬p ∣ d+1) (a : K) : Good p (C a * X^d) := by
  intro k hk; rw [coeff_C_mul_X_pow]; split_ifs with h
  · subst k; contradiction
  · rfl
lemma divGood {p : ℕ} (f g : K[X]) (hg : g.Monic) (hs : Sparse p g) (hf : Good p f) : Good p (f /ₘ g) := by
  classical
  by_cases h : degree g ≤ degree f ∧ f ≠ 0
  · let d := f.natDegree-g.natDegree
    let t := C f.leadingCoeff*X^d
    have hgn : p ∣ g.natDegree := by by_contra! hh; exact (leadingCoeff_ne_zero.mpr hg.ne_zero) (hs _ hh)
    have hdn : ¬p ∣ d+1 := by
      intro hd; have he : d+1+g.natDegree = f.natDegree+1 := by dsimp [d]; have := natDegree_le_natDegree h.1; omega
      have hh := dvd_add hd hgn; rw [he] at hh; exact (leadingCoeff_ne_zero.mpr h.2) (hf _ hh)
    have ht := monoGood hdn f.leadingCoeff
    have hnew : Good p (f-g*t) := by
      intro k hk; rw [coeff_sub,hf k hk,mul_comm g, mulGood ht hs k hk,sub_zero]
    have hw := div_wf_lemma h hg
    have ih := divGood (f-g*t) g hg hs hnew
    have he : f /ₘ g = t + (f-g*t) /ₘ g := by
      unfold divByMonic; rw [dif_pos hg]; rw [divModByMonicAux, dif_pos h, dif_pos hg]
    rw [he]; intro k hk; rw [coeff_add,ht k hk,ih k hk,add_zero]
  · by_cases hf0 : f = 0
    · simp [hf0,Good]
    · rw [(divByMonic_eq_zero_iff hg).2 (by push_neg at h; exact lt_of_not_ge (fun hle => hf0 (h hle)))]
      simp [Good]
termination_by f
end ZZModPoly
end

section
namespace ZZModPoly
open Polynomial ZZGlobal
variable {p n : ℕ} [Fact p.Prime]
lemma cancelDiv {F G H : (ZMod p)[X]} (hg : G.Monic) (hh : H.Monic) :
    F*H /ₘ (G*H) = F /ₘ G := by
  apply (div_modByMonic_unique _ ((F %ₘ G)*H) (hg.mul hh) ⟨?_,?_⟩).1
  · linear_combination H*(modByMonic_add_div F G)
  · rw [degree_mul,degree_mul]; exact WithBot.add_lt_add_right (degree_ne_bot.mpr hh.ne_zero) (degree_modByMonic_lt _ hg)
lemma sparsePow (f : (ZMod p)[X]) : Sparse p (f^p) := by
  intro k hk; rw [← ZMod.expand_card,coeff_expand (Fact.out : p.Prime).pos,if_neg hk]
lemma residual (hp : 5<p) (r s e : ℕ) (lo : p ≤ 2*r) (up : 3*r<2*p)
    (hs : s+p=2*r) (he : 3*r+1+e=2*p) : Good p
    ((X:(ZMod p)[X])^(2*r)*(X^4+6*X^2+25)^s*(X^2-25)^e) := by
  let T : (ZMod p)[X] := X^(r)*(X^2+6*X+25)^s*(X-25)^e
  have hx : expand (ZMod p) 2 T = (X:(ZMod p)[X])^(2*r)*(X^4+6*X^2+25)^s*(X^2-25)^e := by
    simp only [T,map_mul,map_pow,map_add,map_sub,map_ofNat,expand_X,← pow_mul]
  rw [← hx]; intro k hk
  rw [coeff_expand (by decide : 0 < 2)]; split_ifs with h2
  · obtain ⟨v,hv⟩ := hk
    by_cases hlow : k/2 < r
    · have hd : (X:(ZMod p)[X])^r ∣ T := dvd_mul_of_dvd_left (dvd_mul_right _ _) _
      exact X_pow_dvd_iff.mp hd _ hlow
    · apply coeff_eq_zero_of_natDegree_lt
      have hb : T.natDegree ≤ r+2*s+e := by dsimp [T]; compute_degree; omega
      have hodd := (Fact.out : p.Prime).odd_of_ne_two (by omega)
      have hv12 : v ≠ 2 := by rintro rfl; omega
      have hv3 : 3 ≤ v := by
        by_contra! h; interval_cases v <;> simp_all <;> omega
      have hm := Nat.mul_le_mul_left p hv3
      omega
  · rfl
lemma modGood (hp : p ∈ ZZDen.primes n) : Good p ((PInt n).map (Int.castRingHom (ZMod p))) := by
  obtain ⟨_,h5,_,lo,up⟩ := ZZClear.memP hp
  let r := n%p; let q := n/p; let s := 2*r-p; let e := 2*p-(3*r+1)
  change p ≤ 2*r at lo; change 3*r < 2*p at up
  have hs : s+p=2*r := by dsimp [s]; omega
  have he : 3*r+1+e=2*p := by dsimp [e]; omega
  have hn : n = r+p*q := (Nat.mod_add_div n p).symm
  have h1 : 2*n = s+(2*q+1)*p := by rw [hn]; nlinarith only [hs]
  have h2 : m n+e = (3*q+2)*p := by unfold m; rw [hn]; nlinarith only [he]
  let U : (ZMod p)[X] := X^2-25
  let V : (ZMod p)[X] := X^4+6*X^2+25
  have hm : U.Monic := by dsimp [U]; monicity!
  have hG : G (R:=(ZMod p)) n = U^m n := by unfold G U; congr 1; ring
  unfold PInt; rw [map_divByMonic _ (monicG n)]
  simp only [N,G,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_add,Polynomial.map_sub,Polynomial.map_X,Polynomial.map_neg,Polynomial.map_one,Polynomial.map_ofNat]
  change Good p (((-1)^m n * (5*X^(2*n)*V^(2*n))) /ₘ G (R:=(ZMod p)) n)
  rw [hG, ← cancelDiv (hm.pow _) (hm.pow e), ← pow_add,h2,pow_mul U]
  apply divGood _ _ ((hm.pow _).pow _) (sparsePow _)
  let c : (ZMod p) := (-1)^m n*5
  have hnum : (-1:(ZMod p)[X])^m n*(5*X^(2*n)*V^(2*n))*U^e =
      (X^(2*r)*V^s*U^e) * ((X^(2*q)*V^(2*q+1))^p) * C c := by
    have hx : 2*n=2*r+(2*q)*p := by rw [hn]; ring
    simp only [c,map_mul,map_pow,map_neg,map_one,map_ofNat,mul_pow,← pow_mul]
    rw [hx,pow_add,show V^(2*r+(2*q)*p)=V^s*V^((2*q+1)*p) by rw [← hx,← pow_add,← h1]]; ring
  rw [hnum]; apply mulGood (mulGood (residual h5 r s e lo up hs he) (sparsePow _))
  intro k hk; rw [coeff_C,if_neg (by rintro rfl; exact hk (dvd_zero _))]
theorem p_dvd_coeff {j : ℕ} (hp : p ∈ ZZDen.primes n) (hj : p ∣ j+1) : (p:ℤ) ∣ (PInt n).coeff j := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa using modGood hp j hj
end ZZModPoly
end

section
namespace ZZSegment
open Complex
noncomputable section
def x (t : ℝ) : ℂ := -1 + (t:ℂ)*I
def y (t : ℝ) : ℂ := x t ^ 2
def Q (t : ℝ) : ℂ := y t ^ 2 + 6*y t + 25
def D (t : ℝ) : ℂ := y t - 25
def g (t : ℝ) : ℂ := y t * Q t ^ 2 / D t ^ 3
lemma identities (t : ℝ) : normSq (y t) = (1+t^2)^2 ∧
    normSq (Q t) = (4-t^2)^2*(64+t^4) ∧
    normSq (D t) = (24+t^2)^2 + 4*t^2 := by
  simp only [Q,D,y,x,pow_two,Complex.normSq_apply,add_re,add_im,sub_re,sub_im,
    mul_re,mul_im,I_re,I_im,ofReal_re,ofReal_im,neg_re,neg_im,one_re,one_im,
    Complex.re_ofNat,Complex.im_ofNat]
  refine ⟨?_, ?_, ?_⟩ <;> ring
lemma bounded (t : ℝ) (hl : -2 ≤ t) (hu : t ≤ 2) : normSq (g t) ≤ 1 := by
  obtain ⟨hy,hq,hd⟩ := identities t
  have ht : t^2 ≤ 4 := by nlinarith [mul_nonneg (show 0 ≤ t+2 by linarith) (show 0 ≤ 2-t by linarith)]
  have hc : t^4 ≤ 16 := by nlinarith [sq_nonneg t, mul_nonneg (show 0 ≤ 4-t^2 by linarith) (show 0 ≤ 4+t^2 by positivity)]
  have h1 : normSq (y t) ≤ 25 := by rw [hy]; nlinarith
  have h2 : normSq (Q t) ≤ 1280 := by
    rw [hq]; calc
      _ ≤ (16:ℝ)*80 := mul_le_mul (by nlinarith) (by linarith) (by positivity) (by norm_num)
      _ = _ := by norm_num
  have h3 : 576 ≤ normSq (D t) := by rw [hd]; nlinarith [sq_nonneg t,sq_nonneg (t^2)]
  rw [g, map_div₀, map_mul, map_pow, map_pow, div_le_one (by positivity)]
  calc
    _ ≤ (25:ℝ)*1280^2 := mul_le_mul h1 (pow_le_pow_left₀ (normSq_nonneg _) h2 _) (by positivity) (by norm_num)
    _ ≤ 576^3 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h3 _
def integral (n : ℕ) : ℂ := -5 * ∫ t in (-2:ℝ)..2, g t ^ n / D t
lemma integral_bound (n : ℕ) : ‖integral n‖ ≤ 5/6 := by
  have step (t : ℝ) (ht : t ∈ Set.uIoc (-2:ℝ) 2) : ‖g t ^ n / D t‖ ≤ 1/24 := by
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have hb := bounded t ht.1.le ht.2
    have hd := (identities t).2.2
    rw [normSq_eq_norm_sq] at hb hd
    have h : 24 ≤ ‖D t‖ := by nlinarith [norm_nonneg (D t),sq_nonneg t,sq_nonneg (t^2)]
    rw [norm_div,norm_pow,div_le_iff₀ (by linarith)]
    have := pow_le_one₀ (n:=n) (norm_nonneg (g t)) (show ‖g t‖ ≤ 1 by nlinarith)
    linarith
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const step
  rw [integral,norm_mul]
  norm_num at hb ⊢
  linarith
end
end ZZSegment
end

section
namespace ZZPole
open Real
lemma onePole (a : ℝ) (ha : 0 < a) :
    (∫ t in (-2:ℝ)..2, a/(a^2+t^2)) = 2*arctan (2/a) := by
  have h (t : ℝ) : 0 < a^2+t^2 := by positivity
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => arctan (u/a)) (a/(a^2+t^2)) t := by
    have he : a/(a^2+t^2) = 1/(1+(t/a)^2)*(1/a) := by
      field_simp [ha.ne', (h t).ne'] <;> ring
    rw [he]
    exact (hasDerivAt_arctan (t/a)).comp t ((hasDerivAt_id t).div_const a)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((continuous_const.div (by fun_prop) (fun t => (h t).ne')).intervalIntegrable _ _)]
  rw [neg_div, arctan_neg]; ring
lemma polePair : (∫ t in (-2:ℝ)..2, 4/((4:ℝ)^2+t^2) + 6/((6:ℝ)^2+t^2)) = π/2 := by
  have hc (a : ℝ) (ha : 0 < a) : Continuous (fun t : ℝ => a/(a^2+t^2)) :=
    continuous_const.div (by fun_prop) (fun t => ne_of_gt (by positivity))
  rw [intervalIntegral.integral_add ((hc 4 (by norm_num)).intervalIntegrable _ _)
      ((hc 6 (by norm_num)).intervalIntegrable _ _), onePole _ (by norm_num), onePole _ (by norm_num), ← mul_add,
      arctan_add (by norm_num)]
  norm_num [arctan_one]; ring
end ZZPole
end

section
namespace ZZForm
open ZZSegment ZZArithmetic Complex Polynomial
noncomputable section
def L (t : ℝ) : ℂ := 5+x t
def R (t : ℝ) : ℂ := 5-x t
lemma lne (t : ℝ) : L t ≠ 0 := by
  intro h; have := congrArg Complex.re h; norm_num [L,x] at this
lemma rne (t : ℝ) : R t ≠ 0 := by
  intro h; have := congrArg Complex.re h; norm_num [R,x] at this
lemma lc : Continuous L := by unfold L x; fun_prop
lemma rc : Continuous R := by unfold R x; fun_prop
def poles (j : ℕ) (t : ℝ) : ℂ := 1/L t^(j+1) + 1/R t^(j+1)
lemma pc (j : ℕ) : Continuous (poles j) :=
  (continuous_const.div (lc.pow _) (fun t => pow_ne_zero _ (lne t))).add
    (continuous_const.div (rc.pow _) (fun t => pow_ne_zero _ (rne t)))
lemma signedPoint (n : ℕ) (t : ℝ) : -5 * (g t ^ n / D t) =
    (-1:ℂ)^n * (aeval (x t) (ZZGlobal.P n) + ∑ j ∈ Finset.range (3*n+1), (A n j : ℂ)*poles j t) := by
  have h := ZZGlobal.eqThree n (x t) (lne t) (rne t)
  change _ / ((L t)^_*(R t)^_) = _ at h
  simp only [poles, mul_add, mul_one_div]
  simp only [eq_ratCast] at h
  rw [← mul_add]
  unfold L R
  rw [← h]
  have hd : D t = -(L t*R t) := by unfold D y L R; ring
  have hq : Q t = x t^4+6*x t^2+25 := by unfold Q y; ring
  let v := (x t)^2*(Q t)^2/(L t*R t)^3
  have gv : g t = -v := by unfold g v y; rw [hd]; ring
  rw [gv, hd, show -v = (-1)*v by ring, mul_pow]
  unfold v ZZGlobal.N ZZGlobal.m
  rw [hq]; simp only [div_pow, mul_pow, pow_add, pow_one, ← pow_mul]
  field_simp [lne,rne]
lemma pole_sym (t : ℝ) : poles 0 t + poles 0 (-t) =
    2*((4/((4:ℝ)^2+t^2)+6/((6:ℝ)^2+t^2):ℝ):ℂ) := by
  have h4 : ((4:ℂ)^2+(t:ℂ)^2) ≠ 0 := by exact_mod_cast (show (4:ℝ)^2+t^2 ≠ 0 by positivity)
  have h6 : ((6:ℂ)^2+(t:ℂ)^2) ≠ 0 := by exact_mod_cast (show (6:ℝ)^2+t^2 ≠ 0 by positivity)
  push_cast
  simp only [poles,zero_add,pow_one]
  field_simp [lne,rne,h4,h6]
  unfold L R x; push_cast; ring_nf; simp [I_sq]; ring
lemma simple : (∫ t in (-2:ℝ)..2, poles 0 t) = (Real.pi:ℂ)/2 := by
  have he := intervalIntegral.integral_comp_neg (f:=poles 0) (a:=(-2:ℝ)) (b:=2)
  norm_num only [neg_neg] at he
  have h := congrArg (fun f : ℝ → ℂ => ∫ t in (-2:ℝ)..2, f t) (funext pole_sym)
  change (∫ t in (-2:ℝ)..2, poles 0 t + poles 0 (-t)) = _ at h
  have hc : Continuous (fun t => poles 0 (-t)) := (pc 0).comp continuous_neg
  rw [intervalIntegral.integral_add ((pc 0).intervalIntegrable _ _) (hc.intervalIntegrable _ _), he, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, ZZPole.polePair] at h
  push_cast at h; linear_combination h/2
def polyTerm (n : ℕ) (t : ℝ) : ℂ := aeval (x t) (ZZGlobal.P n)
lemma polyCont (n : ℕ) : Continuous (polyTerm n) := by
  change Continuous (fun t => (aeval (x t)) (ZZGlobal.P n))
  simp_rw [aeval_def, eval₂_eq_eval_map]
  exact (Polynomial.continuous _).comp (by unfold x; fun_prop)
def remTerm (n : ℕ) : ℂ := (∫ t in (-2:ℝ)..2, polyTerm n t) +
    ∑ j ∈ Finset.range (3*n), (A n (j+1):ℂ)*(∫ t in (-2:ℝ)..2, poles (j+1) t)
theorem decomposition (n : ℕ) : integral n = (-1:ℂ)^n * (remTerm n + (A n 0 : ℂ)/2*(Real.pi:ℂ)) := by
  let f (j : ℕ) (t : ℝ) := (A n j : ℂ)*poles j t
  have cf (j : ℕ) : Continuous (f j) := continuous_const.mul (pc j)
  have cs : Continuous (fun t => ∑ j ∈ Finset.range (3*n+1), f j t) := continuous_finsetSum _ (fun j _ => cf j)
  rw [integral, ← intervalIntegral.integral_const_mul]
  simp_rw [signedPoint]
  change (∫ t in (-2:ℝ)..2, (-1:ℂ)^n * (polyTerm n t + ∑ j ∈ Finset.range (3*n+1), f j t)) = _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add ((polyCont n).intervalIntegrable _ _) (cs.intervalIntegrable _ _), intervalIntegral.integral_finsetSum (fun j _ => (cf j).intervalIntegrable _ _)]
  simp only [f,intervalIntegral.integral_const_mul, Finset.sum_range_succ', simple, remTerm]; ring
def scale (n : ℕ) : ℚ := 4 * (ZZDen.L n : ℚ) / 2^(5*n/2)
theorem normalized_pi (n : ℕ) : ∃ b : ℤ,
    scale n * (-1:ℚ)^n * A n 0 / 2 = b := by
  obtain ⟨z,hz⟩ := lemmaOne n 0 (by omega)
  simp only [Nat.mul_zero,Nat.add_zero,pow_zero,mul_one] at hz
  refine ⟨(ZZDen.L n : ℤ)*(-1)^n*z, ?_⟩
  push_cast; unfold scale; field_simp; linear_combination 2*(ZZDen.L n : ℚ)*hz
end
end ZZForm
end

section
namespace ZZForm
open Complex ZZSegment ZZArithmetic Polynomial
noncomputable section
lemma xd (t : ℝ) : HasDerivAt x I t := by
  unfold x
  simpa only [id_eq,ofReal_one,one_mul,Function.comp_apply] using (((hasDerivAt_id t).ofReal_comp.mul_const I).const_add (-1:ℂ))
lemma ld (t : ℝ) : HasDerivAt L I t := (xd t).const_add 5
lemma rd (t : ℝ) : HasDerivAt R (-I) t := (xd t).const_sub 5
def primPole (j : ℕ) (t : ℝ) : ℂ := I/(j:ℂ)*((L t ^ j)⁻¹ - (R t ^ j)⁻¹)
lemma primPole_d (k : ℕ) (t : ℝ) : HasDerivAt (primPole (k+1)) (poles (k+1) t) t := by
  have h := (((((ld t).pow (k+1)).inv (pow_ne_zero _ (lne t))).sub
    (((rd t).pow (k+1)).inv (pow_ne_zero _ (rne t)))).const_mul (I/((k+1:ℕ):ℂ)))
  apply h.congr_deriv
  unfold poles
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp [lne,rne,show (k:ℂ)+1 ≠ 0 by exact_mod_cast (show k+1 ≠ 0 by omega)]
  ring_nf; simp [I_sq]; ring
lemma higherIntegral (k : ℕ) : (∫ t in (-2:ℝ)..2, poles (k+1) t) =
    primPole (k+1) 2 - primPole (k+1) (-2) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => primPole_d k t)
    ((pc _).intervalIntegrable _ _)
end
end ZZForm
end

section
namespace ZZForm
open ZZSegment ZZArithmetic Complex
open scoped ComplexConjugate
noncomputable section
def den (j : ℕ) : ℂ := 2^((3*j+1)/2)*5^j
lemma gaussianPow (u : ℂ) (v w : GaussianInt) (h1 : 20*u=v) (h2 : 200*u^2=w) (j : ℕ) :
    ∃ a : GaussianInt, den j*u^j = a := by
  induction j using Nat.twoStepInduction with
  | zero => exact ⟨1,by simp [den,GaussianInt.toComplex_one]⟩
  | one => exact ⟨v,by norm_num [den] at *; exact h1⟩
  | more j ih _ =>
    obtain ⟨a,ha⟩ := ih; refine ⟨a*w,?_⟩
    rw [GaussianInt.toComplex_mul,← ha,← h2]
    unfold den
    rw [show (3*(j+2)+1)/2 = (3*j+1)/2+3 by omega]
    simp only [pow_add]; ring
lemma gaussAt (j : ℕ) : ∃ a : GaussianInt, den j*((L 2^j)⁻¹-(R 2^j)⁻¹) = a := by
  have gl := gaussianPow (L 2)⁻¹ ⟨4,-2⟩ ⟨6,-8⟩ (by
    try simp only [inv_pow]
    field_simp [lne]; norm_num [L,x,GaussianInt.toComplex_def']; ring_nf <;> simp [I_sq] <;> ring) (by
    try simp only [inv_pow]
    field_simp [lne]; norm_num [L,x,GaussianInt.toComplex_def']; ring_nf <;> simp [I_sq] <;> ring) j
  have gr := gaussianPow (R 2)⁻¹ ⟨3,1⟩ ⟨4,3⟩ (by
    try simp only [inv_pow]
    field_simp [rne]; norm_num [R,x,GaussianInt.toComplex_def']; ring_nf <;> simp [I_sq] <;> ring) (by
    try simp only [inv_pow]
    field_simp [rne]; norm_num [R,x,GaussianInt.toComplex_def']; ring_nf <;> simp [I_sq] <;> ring) j
  obtain ⟨a,ha⟩ := gl; obtain ⟨b,hb⟩ := gr
  exact ⟨a-b,by rw [mul_sub,GaussianInt.toComplex_sub,← ha,← hb]; simp⟩
lemma endpointIntegral (k : ℕ) : ∃ a : ℤ, ((k+1:ℕ):ℂ)*den (k+1)*(∫ t in (-2:ℝ)..2, poles (k+1) t) = a := by
  let j := k+1
  obtain ⟨a,ha⟩ := gaussAt j
  have hL : conj (L 2) = L (-2) := by norm_num [L,x,map_ofNat]
  have hR : conj (R 2) = R (-2) := by norm_num [R,x,map_ofNat]
  have hb := congrArg conj ha
  simp only [map_sub,map_pow,map_inv₀,map_mul,hL,hR] at hb
  have hd : conj (den j) = den j := by simp [den,map_ofNat]
  rw [hd] at hb
  have hj : (j:ℂ) ≠ 0 := by exact_mod_cast (by dsimp [j]; omega : j ≠ 0)
  refine ⟨-2*a.im, ?_⟩
  rw [higherIntegral]; change (j:ℂ)*den j*(primPole j 2 - primPole j (-2)) = _
  unfold primPole
  calc
    _ = I*(den j*((L 2^j)⁻¹-(R 2^j)⁻¹)-den j*((L (-2)^j)⁻¹-(R (-2)^j)⁻¹)) := by field_simp <;> ring
    _ = _ := by rw [ha,hb,GaussianInt.toComplex_def]; push_cast; simp; ring_nf; simp
lemma higher_scaled (n k : ℕ) (hu : k+1 ≤ 3*n) : ∃ b : ℤ,
    (scale n:ℂ)*(A n (k+1):ℂ)*(∫ t in (-2:ℝ)..2, poles (k+1) t) = b := by
  let j := k+1
  have hj : 0 < j := by dsimp [j]; omega
  obtain ⟨z,w,hz,hw⟩ := ZZClear.clearA n j hj hu
  obtain ⟨a,ha⟩ := endpointIntegral k
  let r := (5*n+3*j)/2+1-(5*n/2+(3*j+1)/2)
  have he : (5*n+3*j)/2+1 = 5*n/2+(3*j+1)/2+r := by dsimp [r]; omega
  refine ⟨2^r*w*a, ?_⟩
  have hz' : 2*(A n j:ℂ) = (2:ℂ)^((5*n+3*j)/2)*5^j*z := by exact_mod_cast hz
  have hw' : (ZZDen.L n:ℂ)*(z:ℂ) = (j:ℂ)*(w:ℂ) := by exact_mod_cast hw
  have hpow : (2:ℂ)^((5*n+3*j)/2)*2 = 2^(5*n/2)*2^((3*j+1)/2)*2^r := by rw [← pow_succ,← pow_add,← pow_add,he]
  let V := ∫ t in (-2:ℝ)..2, poles (k+1) t
  change (j:ℂ)*den j*V = a at ha
  change (scale n:ℂ)*(A n j:ℂ)*V = _
  unfold scale den at *; push_cast
  field_simp
  linear_combination 2*(ZZDen.L n:ℂ)*V*hz' + (ZZDen.L n:ℂ)*V*5^j*z*hpow + V*5^j*2^(5*n/2)*2^((3*j+1)/2)*2^r*hw' + 2^(5*n/2)*2^r*w*ha
end
end ZZForm
end

section
namespace ZZForm
open ZZSegment ZZArithmetic
noncomputable section
theorem propositionOne_of_poly (n : ℕ) (hp : ∃ a : ℤ, (scale n:ℂ)*(∫ t in (-2:ℝ)..2, polyTerm n t) = a) :
    ∃ a b : ℤ, (scale n:ℂ)*integral n = a + b*(Real.pi:ℂ) ∧
      scale n*(-1:ℚ)^n*A n 0/2 = b := by
  classical
  obtain ⟨a,ha⟩ := hp
  obtain ⟨b,hb⟩ := normalized_pi n
  have hf (k : ℕ) (hk : k ∈ Finset.range (3*n)) := higher_scaled n k (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
  let f (k : ℕ) := if h : k ∈ Finset.range (3*n) then (hf k h).choose else 0
  have hs : (scale n:ℂ)*(∑ k ∈ Finset.range (3*n), (A n (k+1):ℂ)*(∫ t in (-2:ℝ)..2, poles (k+1) t)) = ((∑ k ∈ Finset.range (3*n), f k : ℤ):ℂ) := by
    push_cast; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro k hk; simp only [f,dif_pos hk,← mul_assoc]; exact (hf k hk).choose_spec
  have hb' : (scale n:ℂ)*(-1:ℂ)^n*(A n 0:ℂ)/2 = (b:ℂ) := by exact_mod_cast hb
  refine ⟨(-1)^n*(a+∑ k ∈ Finset.range (3*n), f k),b,?_,hb⟩
  rw [decomposition,remTerm]; push_cast at hs ⊢
  linear_combination (-1:ℂ)^n*(ha+hs)+(Real.pi:ℂ)*hb'
end
end ZZForm
end

section
namespace ZZForm
open Complex ZZSegment ZZGlobal Polynomial
noncomputable section
lemma xIntegral (k : ℕ) : ∃ b : ℤ, ((k+1:ℕ):ℂ)*(∫ t in (-2:ℝ)..2, x t^k) = b := by
  let j := k+1
  have hj : (j:ℂ) ≠ 0 := by exact_mod_cast (by dsimp [j]; omega : j ≠ 0)
  have hd (t : ℝ) : HasDerivAt (fun t => -I/(j:ℂ)*x t^j) (x t^k) t := by
    apply (((xd t).pow j).const_mul (-I/(j:ℂ))).congr_deriv
    rw [show j-1=k by rfl]; field_simp; ring_nf; simp
  let a : GaussianInt := (⟨-1,2⟩:GaussianInt)^j
  have ha : x 2^j = (a:ℂ) := by
    change x 2^j = GaussianInt.toComplex (_^_); rw [map_pow]; congr 1; norm_num [x,GaussianInt.toComplex_def']
  have hb := congrArg (starRingEnd ℂ) ha
  have hx : (starRingEnd ℂ) (x 2) = x (-2) := by norm_num [x,map_ofNat]
  rw [map_pow,hx] at hb
  refine ⟨2*a.im, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) ((show Continuous (fun t => x t^k) by unfold x; fun_prop).intervalIntegrable _ _)]
  rw [ha,hb]; change (j:ℂ)*_ = _
  rw [GaussianInt.toComplex_def]; push_cast; simp; field_simp; ring_nf; simp
lemma polyOdd (n : ℕ) (hn : 0<n) : ∃ a : ℤ, (ZZDen.L n:ℂ)*(∫ t in (-2:ℝ)..2, polyTerm n t) = a := by
  classical
  let f (k : ℕ) (t : ℝ) := (((PInt n).coeff k:ℤ):ℂ)*x t^k
  have he (t : ℝ) : polyTerm n t = ∑ k ∈ Finset.range (4*n), f k t := by
    unfold polyTerm; rw [aeval_eq_sum_range' (n:=4*n) (by rw [degP n hn]; omega)]
    simp only [← integralP, coeff_map,Int.coe_castRingHom, Algebra.smul_def,eq_ratCast, Rat.cast_intCast, f]
  have hc k : Continuous (f k) := by dsimp [f,x]; fun_prop
  have hh k (hk : k ∈ Finset.range (4*n)) : ∃ a : ℤ, (ZZDen.L n:ℂ)*(∫ t in (-2:ℝ)..2, f k t) = a := by
    obtain ⟨b,hb⟩ := xIntegral k
    obtain ⟨w,hw⟩ := ZZClear.clear n (k+1) ((PInt n).coeff k) (by omega) (Finset.mem_range.mp hk) (fun p hp hd => by
      letI : Fact p.Prime := ⟨(ZZClear.memP hp).1⟩; exact ZZModPoly.p_dvd_coeff hp hd)
    have hw' : (ZZDen.L n:ℂ)*((PInt n).coeff k:ℂ) = ((k+1:ℕ):ℂ)*(w:ℂ) := by exact_mod_cast hw
    refine ⟨w*b,?_⟩; unfold f; rw [intervalIntegral.integral_const_mul,← mul_assoc,hw']; push_cast at hb ⊢; linear_combination (w:ℂ)*hb
  let a (k : ℕ) := if h : k ∈ Finset.range (4*n) then (hh k h).choose else 0
  refine ⟨∑ k ∈ Finset.range (4*n), a k,?_⟩
  simp_rw [he]; rw [intervalIntegral.integral_finsetSum (fun k _ => (hc k).intervalIntegrable _ _),Finset.mul_sum]; push_cast
  apply Finset.sum_congr rfl; intro k hk; simpa only [a,dif_pos hk] using (hh k hk).choose_spec
end
end ZZForm
end

section
namespace ZZTwo
open ZZArithmetic ZZGlobal PowerSeries
noncomputable section
def geom : S := mk 1
def U (n : ℕ) : Polynomial ℚ := (P n).comp (10*Polynomial.X-5)
lemma tr (n : ℕ) (v : S) : Polynomial.aeval (10*v) (T n) = C (amp n)*
    ∑ i ∈ Finset.range (m n), C (coeff i (F n))*v^i := by
  rw [T,Polynomial.aeval_def,eval₂_trunc_eq_sum_range,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i hi
  simp only [localSeries,coeff_C_mul,coeff_rescale, map_mul,map_pow,mul_pow]
  change C (amp n)*(C (1/10:ℚ)^i*C (coeff i (F n)))*(10^i*v^i) = _
  have hc : (C (1/10:ℚ):S)^i*10^i=1 := by rw [← mul_pow,← map_ofNat C 10,← map_mul]; norm_num
  linear_combination C (amp n)*C (coeff i (F n))*v^i*hc
lemma formal (n : ℕ) :
  (C (amp n)*F n) = Polynomial.aeval (10*X:S) (T n) + X^m n *
    (Polynomial.aeval (10*(1-X):S) (T n)*geom^m n + 10^m n * (U n:S)) := by
  let v : S := 10-10*X
  have hv : v = 10*(1-X) := by dsimp [v]; ring
  have hz : v ≠ 0 := by intro h; have hh := congrArg PowerSeries.constantCoeff h; norm_num [v,map_ofNat] at hh
  have h := substitute n (10*X-5:S)
  rw [show (5+(10*X-5):S)=10*X by ring,show (5-(10*X-5):S)=v by dsimp [v]; ring] at h
  have hp : ((U n):S) = Polynomial.aeval (10*X-5:S) (P n) := by
    rw [← Polynomial.eval₂_C_X_eq_coe]; change Polynomial.aeval X ((P n).comp _) = _; rw [Polynomial.aeval_comp]; simp [map_ofNat]
  rw [hp, ← hv]; apply mul_right_cancel₀ (pow_ne_zero (m n) hz)
  have hn := normalized_identity n
  change C (amp n)*F n*v^m n = N n (10*X-5:S) at hn
  rw [hn]
  have hg : geom^m n*v^m n = 10^m n := by
    rw [← mul_pow,hv,show geom*(10*(1-X))=10*(geom*(1-X)) by ring,geom,mk_one_mul_one_sub_eq_one,mul_one]
  simp only [mul_pow] at h
  linear_combination h - X^m n*Polynomial.aeval v (T n)*hg
lemma kernelInt (i m k : ℕ) : coeff k (((1-X:S)^i)*geom^m) ∈ ZQ := by
  let H : PowerSeries ℤ := (1-X)^i*(mk (1:ℕ → ℤ))^m
  refine ⟨coeff k H,?_⟩
  have hg : map (Int.castRingHom ℚ) (mk (1:ℕ → ℤ)) = geom := by ext; simp [geom,coeff_mk]
  rw [← coeff_map]; simp [H,map_X,hg]
lemma coeffCert (n k : ℕ) : ∃ z : ℤ, 10^m n*(U n).coeff k*2^((m n+k)/2) = amp n*z := by
  let M := m n
  let E := (M+k)/2
  have hf := congrArg (coeff (k+M)) (formal n)
  rw [tr n X,tr n (1-X)] at hf
  simp only [map_add,coeff_C_mul,Finset.mul_sum, map_sum] at hf
  have hz : (∑ i ∈ Finset.range M, amp n*(coeff i (F n)*coeff (k+M) (X^i))) = 0 := by
    apply Finset.sum_eq_zero; intro i hi
    simp [coeff_C_mul,coeff_X_pow,show k+M ≠ i by have := Finset.mem_range.mp hi; omega, Ne.symm (show k+M ≠ i by have := Finset.mem_range.mp hi; omega)]
  rw [hz,zero_add,mul_comm (X^m n),coeff_mul_X_pow] at hf
  rw [show (10:S)^m n=C ((10:ℚ)^m n) by simp [map_ofNat],map_add,coeff_C_mul,Polynomial.coeff_coe] at hf
  simp only [Finset.sum_mul,mul_assoc,coeff_C_mul,map_sum] at hf
  have ha (i : ℕ) (hi : i ∈ Finset.range M) : 2^E * coeff i (F n) ∈ ZQ := by
    have he : E=E-i/2+i/2 := by dsimp [E]; have := Finset.mem_range.mp hi; omega
    rw [he,pow_add,mul_assoc]; exact ZQ.mul_mem (ZQ.pow_mem twoMem _) (goodF n i)
  have hmem : (2:ℚ)^E*(coeff (k+M) (F n) - ∑ i ∈ Finset.range M, coeff i (F n)*coeff k ((1-X:S)^i*geom^M)) ∈ ZQ := by
    rw [mul_sub,Finset.mul_sum]; apply ZQ.sub_mem
    · simpa [E, Nat.add_comm] using goodF n (k+M)
    · apply ZQ.sum_mem; intro i hi; rw [← mul_assoc]; exact ZQ.mul_mem (ha i hi) (kernelInt _ _ _)
  obtain ⟨z,hz⟩ := hmem; refine ⟨z,?_⟩
  change (z:ℚ) = _ at hz; rw [hz]
  simp only [← Finset.mul_sum,mul_assoc, ← mul_assoc (C (amp n))] at hf
  linear_combination -(2:ℚ)^E*hf
end
end ZZTwo
end

section
namespace ZZFinal
open ZZForm ZZTwo ZZGlobal ZZArithmetic ZZSegment Complex Polynomial
noncomputable section
def v (t : ℝ) : ℂ := (5-x t)/2
lemma vpow (j : ℕ) : ∃ a : GaussianInt, v 2^j = 2^(j/2)*(a:ℂ) := by
  induction j using Nat.twoStepInduction with
  | zero => exact ⟨1,by simp [GaussianInt.toComplex_one]⟩
  | one => exact ⟨⟨3,-1⟩,by norm_num [v,x,GaussianInt.toComplex_def']; ring⟩
  | more j ih _ =>
    obtain ⟨a,ha⟩ := ih
    have h2 : v 2^2 = 2*((⟨4,-3⟩:GaussianInt):ℂ) := by norm_num [v,x,GaussianInt.toComplex_def']; ring_nf; simp; ring
    refine ⟨a*⟨4,-3⟩,?_⟩; rw [pow_add,ha,h2,show (j+2)/2=j/2+1 by omega,pow_succ,GaussianInt.toComplex_mul]; ring
lemma vint (k : ℕ) : ∃ a : ℤ, ((k+1:ℕ):ℂ)*(∫ t in (-2:ℝ)..2, v t^k) = 4*2^((k+1)/2)*a := by
  let j := k+1
  have hj : (j:ℂ) ≠ 0 := by exact_mod_cast (by dsimp [j]; omega : j ≠ 0)
  have hd (t : ℝ) : HasDerivAt (fun t => 2*I/(j:ℂ)*v t^j) (v t^k) t := by
    have hv : HasDerivAt v (-I/2) t := ((xd t).const_sub 5).div_const 2
    apply ((hv.pow j).const_mul (2*I/(j:ℂ))).congr_deriv
    rw [show j-1=k by rfl]; field_simp; ring_nf; simp
  obtain ⟨a,ha⟩ := vpow j
  have hb := congrArg (starRingEnd ℂ) ha
  have hx : (starRingEnd ℂ) (v 2) = v (-2) := by norm_num [v,x,map_ofNat]
  rw [map_pow,hx,map_mul,map_pow,map_ofNat] at hb
  refine ⟨-a.im, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) ((show Continuous (fun t => v t^k) by unfold v x; fun_prop).intervalIntegrable _ _)]
  rw [ha,hb]; change (j:ℂ)*_ = 4*2^(j/2)*_
  rw [GaussianInt.toComplex_def]; push_cast; simp; field_simp; ring_nf; simp
lemma cert (n k : ℕ) : ∃ z : ℤ, (5:ℚ)*2^((m n+k)/2)*4*(U n).coeff k = 2^(4*n)*z := by
  obtain ⟨z,h⟩ := coeffCert n k; refine ⟨z,?_⟩
  rw [amp,show (10:ℚ)^m n=2^m n*5^m n by rw [← mul_pow]; norm_num,show 7*n=3*n+4*n by omega,pow_add] at h
  simp only [m,pow_succ] at h
  field_simp at h
  apply mul_left_cancel₀ (a:= (2:ℚ)^(3*n)) (by positivity)
  unfold m; rw [pow_add] at h; linear_combination h
def f (n k : ℕ) (t : ℝ) : ℂ := ((U n).coeff k:ℂ)/5^k * v t^k
lemma expansion (n : ℕ) (hn : 0<n) (t : ℝ) : polyTerm n t = ∑ k ∈ Finset.range (4*n), f n k t := by
  have hu : (U n).natDegree < 4*n := by
    rw [U,natDegree_comp,degP n hn]; have h : (10*(Polynomial.X:QP)-5).natDegree=1 := by compute_degree!
    rw [h,mul_one]; omega
  have hx : -x t = 10*(v t/5)-5 := by unfold v; ring
  have he := congrArg (aeval (x t)) (P_even n)
  simp only [← aeval_algHom_apply,map_neg,aeval_X] at he
  unfold polyTerm; rw [← he,hx,show aeval (10*(v t/5)-5) (P n)=aeval (v t/5) (U n) by rw [U,aeval_comp]; simp [map_ofNat],aeval_eq_sum_range' hu]
  apply Finset.sum_congr rfl; intro i _; simp [f,Algebra.smul_def,div_pow,eq_ratCast]; ring
lemma evenTerm (n k : ℕ) (hk : k < 4*n) : ∃ a : ℤ,
    (5:ℂ)^(4*n)*(ZZDen.lcm4 n:ℂ)*4/2^(5*n/2)*(∫ t in (-2:ℝ)..2, f n k t) = a := by
  obtain ⟨z,hz⟩ := cert n k; obtain ⟨a,ha⟩ := vint k
  obtain ⟨w,hw⟩ := ZZClear.dvd4 (by omega : 0<k+1) hk
  let E := (m n+k)/2; let J := (k+1)/2; let B := 5*n/2; let r := 4*n+J-(E+B)
  have he : 4*n+J=E+B+r := by dsimp [r,E,J,B,m]; omega
  have he' : (2:ℂ)^(4*n)*2^J=2^E*2^B*2^r := by rw [← pow_add,← pow_add,← pow_add,he]
  let d := 4*n-(k+1)
  have hd : 4*n=k+1+d := by dsimp [d]; omega
  have hz' : (5:ℂ)*2^E*4*((U n).coeff k:ℂ)=2^(4*n)*(z:ℂ) := by exact_mod_cast hz
  let V := ∫ t in (-2:ℝ)..2, v t^k
  change ((k+1:ℕ):ℂ)*V=4*2^J*(a:ℂ) at ha
  refine ⟨4*5^d*2^r*(w:ℤ)*z*a,?_⟩
  unfold f; rw [intervalIntegral.integral_const_mul,hw]; push_cast at ha ⊢
  rw [show (5:ℂ)^(4*n)=5^k*5*5^d by rw [hd,pow_add,pow_succ]]
  change _ / 2^B * (_ * V) = _
  field_simp
  apply mul_left_cancel₀ (a:=(2:ℂ)^E) (pow_ne_zero _ (by norm_num))
  linear_combination (w:ℂ)*((k:ℂ)+1)*V*hz'/4 +w*2^(4*n)*z*ha/4 + w*z*a*he'
lemma polyEven (n : ℕ) (hn : 0<n) : ∃ a : ℤ,
    (5:ℂ)^(4*n)*(ZZDen.lcm4 n:ℂ)*4/2^(5*n/2)*(∫ t in (-2:ℝ)..2, polyTerm n t) = a := by
  classical
  let a (k : ℕ) := if h : k < 4*n then (evenTerm n k h).choose else 0
  refine ⟨∑ k ∈ Finset.range (4*n), a k,?_⟩
  have hc k : Continuous (f n k) := by unfold f v x; fun_prop
  simp_rw [expansion n hn]; rw [intervalIntegral.integral_finsetSum (fun k _ => (hc k).intervalIntegrable _ _),Finset.mul_sum]; push_cast
  apply Finset.sum_congr rfl; intro k hk; have hh := Finset.mem_range.mp hk
  simpa only [a,dif_pos hh] using (evenTerm n k hh).choose_spec
lemma poly_scaled (n : ℕ) (hn : 0<n) : ∃ a : ℤ, (scale n:ℂ)*(∫ t in (-2:ℝ)..2, polyTerm n t) = a := by
  obtain ⟨a,ha⟩ := polyOdd n hn
  obtain ⟨b,hb⟩ := polyEven n hn
  have hp : Nat.Coprime 2 (ZZDen.phi n) := by
    apply Nat.Coprime.prod_right; intro p hp
    have hm := ZZClear.memP hp
    exact Nat.coprime_two_left.mpr (hm.1.odd_of_ne_two (by omega))
  have hc : Nat.Coprime (2^(5*n/2)) (5^(4*n)*ZZDen.phi n) :=
    (((by decide : Nat.Coprime 2 5).pow_right _).mul_right hp).pow_left _
  obtain ⟨u,w,hw⟩ := hc.isCoprime
  have hw' : (u:ℂ)*2^(5*n/2)+(w:ℂ)*(5^(4*n)*(ZZDen.phi n:ℂ)) = 1 := by exact_mod_cast hw
  have hl : (ZZDen.L n:ℂ)*ZZDen.phi n = ZZDen.lcm4 n := by exact_mod_cast Nat.div_mul_cancel (ZZClear.phi_dvd n)
  let V := ∫ t in (-2:ℝ)..2, polyTerm n t
  change (ZZDen.L n:ℂ)*V=a at ha
  change (5:ℂ)^(4*n)*(ZZDen.lcm4 n:ℂ)*4/2^(5*n/2)*V=b at hb
  refine ⟨u*4*a+w*b, ?_⟩; change (scale n:ℂ)*V=_
  unfold scale; push_cast; rw [← hl] at hb
  field_simp at hb ⊢
  linear_combination (u:ℂ)*4*2^(5*n/2)*ha + (w:ℂ)*hb - 4*(ZZDen.L n:ℂ)*V*hw'
theorem propositionOne (n : ℕ) (hn : 0<n) : ∃ a b : ℤ,
    (scale n:ℂ)*integral n = a + b*(Real.pi:ℂ) ∧ scale n*(-1:ℚ)^n*A n 0/2 = b :=
  propositionOne_of_poly n (poly_scaled n hn)
end
end ZZFinal
end

section
namespace ZZTel
noncomputable section
set_option maxHeartbeats 2000000 in
def a0 (n : ℂ) : ℂ := (-2048*n - 5120)*(n + 1)*(n + 2)*(2*n + 1)*(2*n + 3)*(559455*n^4 + 5637736*n^3 + 21207869*n^2 + 35294652*n + 21926016)
set_option maxHeartbeats 2000000 in
def a1 (n : ℂ) : ℂ := (n + 2)*(2*n + 3)*(128*n + 320)*(1208982255*n^6 + 14601112006*n^5 + 71554462078*n^4 + 181444545414*n^3 + 250049018747*n^2 + 176898555884*n + 50159702880)
set_option maxHeartbeats 2000000 in
def a2 (n : ℂ) : ℂ := (-12*n - 30)*(440102548665*n^8 + 7075613606958*n^7 + 49182254436312*n^6 + 192978557313766*n^5 + 467319046780891*n^4 + 714892923466956*n^3 + 674376299494052*n^2 + 358497976451216*n + 82191375084672)
set_option maxHeartbeats 2000000 in
def a3 (n : ℂ) : ℂ := (n + 3)*(3*n + 7)*(3*n + 8)*(4*n + 9)*(12*n + 33)*(559455*n^4 + 3399916*n^3 + 7651391*n^2 + 7554302*n + 2760952)
set_option maxHeartbeats 2000000 in
def h0 (n : ℂ) : ℂ := -13986375000000000000*n^8 - 238848025000000000000*n^7 - 1765058681250000000000*n^6 - 7364726443750000000000*n^5 - 18953764631250000000000*n^4 - 30762417081250000000000*n^3 - 30691696312500000000000*n^2 - 17169642450000000000000*n - 4111128000000000000000
set_option maxHeartbeats 2000000 in
def h1 (n : ℂ) : ℂ := -21556500468750000000*n^8 - 361262453296875000000*n^7 - 2618160600625000000000*n^6 - 10707729499343750000000*n^5 - 27002003279875000000000*n^4 - 42940295345609375000000*n^3 - 41993171573406250000000*n^2 - 23049886190375000000000*n - 5425591815000000000000
set_option maxHeartbeats 2000000 in
def h2 (n : ℂ) : ℂ := -15617765448339843750*n^8 - 259497388739570312500*n^7 - 1864534071205156250000*n^6 - 7561925509489726562500*n^5 - 18920722601751582031250*n^4 - 29886286776608828125000*n^3 - 29081141935225859375000*n^2 - 15926334522023437500000*n - 3755795733427500000000
set_option maxHeartbeats 2000000 in
def h3 (n : ℂ) : ℂ := -6578421986449218750*n^8 - 108976515787491015625*n^7 - 780499823946554687500*n^6 - 3154589606767779687500*n^5 - 7864377449264425000000*n^4 - 12374542620352157421875*n^3 - 11992890312919864843750*n^2 - 6540669427731353125000*n - 1535881142254725000000
set_option maxHeartbeats 2000000 in
def h4 (n : ℂ) : ℂ := -1742988171539062500*n^8 - 28809764980704296875*n^7 - 205857872129858812500*n^6 - 830021506869536250000*n^5 - 2064155229852525843750*n^4 - 3239973514745691328125*n^3 - 3132602219990341031250*n^2 - 1704707498231588375000*n - 399541726900071000000
set_option maxHeartbeats 2000000 in
def h5 (n : ℂ) : ℂ := -278371730739375000*n^8 - 4591908025529662500*n^7 - 32738728218451710000*n^6 - 131684691280386070000*n^5 - 326619565772854780000*n^4 - 511195303241343967500*n^3 - 492689333155737455000*n^2 - 267174493472380820000*n - 62373961262460960000
set_option maxHeartbeats 2000000 in
def h6 (n : ℂ) : ℂ := -26190895615462500*n^8 - 431284021364072500*n^7 - 3069377167228422000*n^6 - 12323360770097079800*n^5 - 30510483045417002100*n^4 - 47669773609594584500*n^3 - 45872649159035043000*n^2 - 24844215512062919200*n - 5795228268750009600
set_option maxHeartbeats 2000000 in
def h7 (n : ℂ) : ℂ := -276116497702500*n^8 - 4463834436044750*n^7 - 31125362817085800*n^6 - 122175597373355176*n^5 - 295084025269446112*n^4 - 448788775867485690*n^3 - 419532511628381300*n^2 - 220317028501096944*n - 49751901073994112
set_option maxHeartbeats 2000000 in
def h8 (n : ℂ) : ℂ := 121180190820000*n^8 + 1991283039937750*n^7 + 14140223993605672*n^6 + 56638878862446896*n^5 + 139878567010875124*n^4 + 217968069133120490*n^3 + 209159303632755748*n^2 + 112939110726442672*n + 26260539932075904
set_option maxHeartbeats 2000000 in
def h9 (n : ℂ) : ℂ := 13653848374920*n^8 + 224709054365484*n^7 + 1598356745045136*n^6 + 6414111260518608*n^5 + 15873014798593248*n^4 + 24789823087808868*n^3 + 23845892446120776*n^2 + 12909491890639968*n + 3009890225293056
set_option maxHeartbeats 2000000 in
def h10 (n : ℂ) : ℂ := -891544131270*n^8 - 14681492396064*n^7 - 104496799562208*n^6 - 419617301979492*n^5 - 1039110725735706*n^4 - 1623863673616284*n^3 - 1562944084803936*n^2 - 846577773274560*n - 197472785158656
set_option maxHeartbeats 2000000 in
def h11 (n : ℂ) : ℂ := 5951482290*n^8 + 99897503823*n^7 + 723932521236*n^6 + 2956252931988*n^5 + 7435405691808*n^4 + 11786777985429*n^3 + 11493048738090*n^2 + 6298741886520*n + 1484751635136
set_option maxHeartbeats 2000000 in
def h12 (n : ℂ) : ℂ := 60421140*n^8 + 986507613*n^7 + 6959908620*n^6 + 27700969344*n^5 + 67997372754*n^4 + 105361843755*n^3 + 100589110494*n^2 + 54070622568*n + 12523678272
set_option maxHeartbeats 2000000 in
def H (n y : ℂ) : ℂ := h0 n * y^0 + h1 n * y^1 + h2 n * y^2 + h3 n * y^3 + h4 n * y^4 + h5 n * y^5 + h6 n * y^6 + h7 n * y^7 + h8 n * y^8 + h9 n * y^9 + h10 n * y^10 + h11 n * y^11 + h12 n * y^12
set_option maxHeartbeats 2000000 in
def Hy (n y : ℂ) : ℂ := h1 n * 1 * y^0 + h2 n * 2 * y^1 + h3 n * 3 * y^2 + h4 n * 4 * y^3 + h5 n * 5 * y^4 + h6 n * 6 * y^5 + h7 n * 7 * y^6 + h8 n * 8 * y^7 + h9 n * 9 * y^8 + h10 n * 10 * y^9 + h11 n * 11 * y^10 + h12 n * 12 * y^11
set_option maxHeartbeats 2000000 in
def Q (y : ℂ) := y^2 + 6*y + 25
set_option maxHeartbeats 2000000 in
def D (y : ℂ) := y-25
set_option maxHeartbeats 2000000 in
theorem certificate (n y : ℂ) :
  ((1+2*n)*Q y*D y + (2+4*n)*y*(2*y+6)*D y - (18+6*n)*y*Q y)*H n y +
    2*y*Q y*D y*Hy n y = a0 n*D y^9 + a1 n*(y*Q y^2)*D y^6 +
    a2 n*(y*Q y^2)^2*D y^3 + a3 n*(y*Q y^2)^3 := by
  unfold Q D H Hy a0 a1 a2 a3 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  ring
end
end ZZTel
end

section
namespace ZZSegment
noncomputable section
open Complex
set_option maxHeartbeats 2000000 in
private lemma D_ne (t : ℝ) : D t ≠ 0 := by
  intro h
  have hd := (identities t).2.2
  rw [h, map_zero] at hd
  nlinarith [sq_nonneg t, sq_nonneg (t^2)]
set_option maxHeartbeats 2000000 in
private lemma hx (t : ℝ) : HasDerivAt x I t := by
  apply HasDerivAt.congr_deriv ( ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const I).const_add (-1:ℂ))
  simp
set_option maxHeartbeats 2000000 in
private lemma hy (t : ℝ) : HasDerivAt y (2*x t*I) t := by
  apply ((hx t).pow 2).congr_deriv
  simp
set_option maxHeartbeats 2000000 in
private lemma hd (t : ℝ) : HasDerivAt D (2*x t*I) t := (hy t).sub_const 25
set_option maxHeartbeats 2000000 in
private lemma hq (t : ℝ) : HasDerivAt Q ((2*y t+6)*(2*x t*I)) t := by
  apply ((((hy t).pow 2).add ((hy t).const_mul 6)).add_const 25).congr_deriv
  simp; ring
set_option maxHeartbeats 2000000 in
private def gp (t : ℝ) : ℂ :=
  ((2*x t*I*Q t^2 + y t*(2*Q t*((2*y t+6)*(2*x t*I))))*D t^3 -
    y t*Q t^2*(3*D t^2*(2*x t*I))) / (D t^3)^2
set_option maxHeartbeats 2000000 in
private lemma hg (t : ℝ) : HasDerivAt g (gp t) t := by
  apply (((hy t).mul ((hq t).pow 2)).div ((hd t).pow 3) (pow_ne_zero _ (D_ne t))).congr_deriv
  simp [gp]
set_option maxHeartbeats 2000000 in
private def L (t : ℝ) : ℂ := 2*Q t + 4*y t*(2*y t+6) - 6*y t*Q t / D t
set_option maxHeartbeats 2000000 in
private lemma gp_weight (t : ℝ) : gp t * (x t*Q t) = g t * I * L t := by
  unfold gp g L
  field_simp [D_ne t]; unfold y; ring
set_option maxHeartbeats 2000000 in
private lemma hpower (n : ℕ) (t : ℝ) :
    ((n:ℂ)*g t^(n-1)*gp t)*(x t*Q t) = g t^n*(n:ℂ)*I*L t := by
  cases n with
  | zero => simp
  | succ k =>
    simp only [Nat.add_one_sub_one, pow_succ]
    linear_combination ((k+1:ℕ):ℂ)*g t^k * gp_weight t
set_option maxHeartbeats 2000000 in
private lemma hH (n : ℂ) (t : ℝ) : HasDerivAt (fun s => ZZTel.H n (y s))
    (ZZTel.Hy n (y t)*(2*x t*I)) t := by
  unfold ZZTel.H ZZTel.Hy
  apply (((((((((((((((hy t).pow 0).const_mul (ZZTel.h0 n)).add (((hy t).pow 1).const_mul (ZZTel.h1 n))).add (((hy t).pow 2).const_mul (ZZTel.h2 n))).add (((hy t).pow 3).const_mul (ZZTel.h3 n))).add (((hy t).pow 4).const_mul (ZZTel.h4 n))).add (((hy t).pow 5).const_mul (ZZTel.h5 n))).add (((hy t).pow 6).const_mul (ZZTel.h6 n))).add (((hy t).pow 7).const_mul (ZZTel.h7 n))).add (((hy t).pow 8).const_mul (ZZTel.h8 n))).add (((hy t).pow 9).const_mul (ZZTel.h9 n))).add (((hy t).pow 10).const_mul (ZZTel.h10 n))).add (((hy t).pow 11).const_mul (ZZTel.h11 n))).add (((hy t).pow 12).const_mul (ZZTel.h12 n))).congr_deriv
  simp; ring
set_option maxHeartbeats 2000000 in
private def F (n : ℕ) (t : ℝ) := g t^n / D t
set_option maxHeartbeats 2000000 in
private def S (n : ℕ) (t : ℝ) := ZZTel.a0 n * F n t + ZZTel.a1 n * F (n+1) t +
  ZZTel.a2 n * F (n+2) t + ZZTel.a3 n * F (n+3) t
set_option maxHeartbeats 2000000 in
private def G (n : ℕ) (t : ℝ) := g t^n * (x t*Q t) * ZZTel.H n (y t) / D t^9
set_option maxHeartbeats 2000000 in
private theorem hG (n : ℕ) (t : ℝ) : HasDerivAt (G n) (I * S n t) t := by
  apply (((((hg t).pow n).mul ((hx t).mul (hq t))).mul (hH n t)).div
      ((hd t).pow 9) (pow_ne_zero _ (D_ne t))).congr_deriv
  simp only [Pi.pow_apply,Pi.mul_apply]
  rw [hpower]
  have cert := ZZTel.certificate n (y t)
  change ((1+2*(n:ℂ))*Q t*D t + (2+4*(n:ℂ))*y t*(2*y t+6)*D t - (18+6*(n:ℂ))*y t*Q t)*ZZTel.H n (y t) +
    2*y t*Q t*D t*ZZTel.Hy n (y t) = _ at cert
  calc
    _ = g t^n * I * (((1+2*(n:ℂ))*Q t*D t + (2+4*(n:ℂ))*y t*(2*y t+6)*D t - (18+6*(n:ℂ))*y t*Q t)*ZZTel.H n (y t) +
      2*y t*Q t*D t*ZZTel.Hy n (y t)) / D t^10 := by
        unfold L; field_simp [D_ne t]; unfold y; ring
    _ = _ := by
      rw [cert]
      unfold S F
      simp only [pow_add]
      generalize g t^n = w
      simp only [← show D t = ZZTel.D (y t) from rfl, ← show Q t = ZZTel.Q (y t) from rfl]
      unfold g; field_simp [D_ne t]
set_option maxHeartbeats 2000000 in
private lemma cF (n : ℕ) : Continuous (F n) :=
  ((continuous_iff_continuousAt.mpr fun t => (hg t).continuousAt).pow n).div
    (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt) D_ne
set_option maxHeartbeats 2000000 in
theorem integral_recurrence (n : ℕ) : ZZTel.a0 n * integral n + ZZTel.a1 n * integral (n+1) +
    ZZTel.a2 n * integral (n+2) + ZZTel.a3 n * integral (n+3) = 0 := by
  have cont (a : ℂ) (k : ℕ) : Continuous (fun t => a * F k t) := continuous_const.mul (cF k)
  have hi (a : ℂ) (k : ℕ) := (cont a k).intervalIntegrable (-2:ℝ) 2 (μ := MeasureTheory.volume)
  have cs : Continuous (S n) := (((cont _ _).add (cont _ _)).add (cont _ _)).add (cont _ _)
  have eqn := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-2:ℝ)) (b := 2) (f' := fun t => I * S n t) (fun t _ => hG n t)
    ((continuous_const.mul cs).intervalIntegrable _ _)
  have ep (t : ℝ) (ht : t^2 = 4) : Q t = 0 := normSq_eq_zero.mp (by rw [(identities t).2.1, ht]; ring)
  have hm := ep (-2) (by norm_num)
  have hp := ep 2 (by norm_num)
  rw [intervalIntegral.integral_const_mul] at eqn
  simp [G, hm, hp] at eqn
  unfold S at eqn
  rw [intervalIntegral.integral_add (((hi _ _).add (hi _ _)).add (hi _ _)) (hi _ _),
      intervalIntegral.integral_add ((hi _ _).add (hi _ _)) (hi _ _),
      intervalIntegral.integral_add (hi _ _) (hi _ _)] at eqn
  simp only [intervalIntegral.integral_const_mul] at eqn
  unfold F at eqn
  unfold integral
  linear_combination (-5:ℂ) * eqn
end
end ZZSegment
end

section
namespace ZZSigned
open ZZSegment ZZForm Complex
noncomputable section
private lemma dn (t : ℝ) : 25-x t^2 ≠ 0 := by
  rw [show 25-x t^2=ZZForm.L t*R t by unfold ZZForm.L ZZForm.R; ring]; exact mul_ne_zero (lne t) (rne t)
lemma integral_zero : integral 0 = (Real.pi:ℂ)/4 := by
  rw [integral, ← intervalIntegral.integral_const_mul]
  have h (t : ℝ) : -5*(g t^0/D t) = (1/2:ℂ)*poles 0 t := by
    unfold poles D y; norm_num only [pow_zero,zero_add,pow_one]
    have hd : x t^2-25 ≠ 0 := by intro h; apply dn t; linear_combination -h
    field_simp [hd,lne,rne]; unfold ZZForm.L ZZForm.R; ring
  simp_rw [h]; rw [intervalIntegral.integral_const_mul,simple]; ring
private def H (t : ℝ) : ℂ := (-I)*(-14950000*x t+1594625*x t^3-52635*x t^5+435*x t^7+(5/3)*x t^9)/(25-x t^2)^3
private lemma derivH (t : ℝ) : HasDerivAt H (-5*(g t/D t)-2392*poles 0 t) t := by
  unfold H
  have h := (((((((xd t).const_mul (-14950000)).add (((xd t).pow 3).const_mul 1594625)).sub (((xd t).pow 5).const_mul 52635)).add (((xd t).pow 7).const_mul 435)).add (((xd t).pow 9).const_mul (5/3))).const_mul (-I)).div ((((xd t).pow 2).const_sub 25).pow 3) (pow_ne_zero _ (dn t))
  apply h.congr_deriv
  unfold g D Q y poles
  have hd : x t^2-25 ≠ 0 := by intro h; apply dn t; linear_combination -h
  norm_num only [zero_add,pow_one,Nat.cast_ofNat]; field_simp [hd,dn,lne,rne]; unfold ZZForm.L ZZForm.R; ring_nf; simp [I_sq] <;> ring
lemma integral_one : integral 1 = -11272/3+1196*(Real.pi:ℂ) := by
  let f := fun t => -5*(g t/D t)
  have cd : ∀ t, D t ≠ 0 := by intro t h; apply dn t; unfold D y at h; linear_combination -h
  have cg : Continuous g := by
    unfold g; apply Continuous.div _ _ (fun t => pow_ne_zero _ (cd t)) <;> simp only [D,Q,y,x] <;> fun_prop
  have cf : Continuous f := continuous_const.mul (cg.div (by unfold D y x; fun_prop) cd)
  have cp : Continuous (fun t => (2392:ℂ)*poles 0 t) := continuous_const.mul (pc _)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=(-2:ℝ)) (b:=2) (fun t _ => derivH t) ((cf.sub cp).intervalIntegrable _ _)
  change (∫ t in (-2:ℝ)..2, f t - 2392*poles 0 t) = _ at h
  rw [intervalIntegral.integral_sub (cf.intervalIntegrable _ _) (cp.intervalIntegrable _ _),intervalIntegral.integral_const_mul (2392:ℂ),simple] at h
  have ep : H 2-H (-2) = -11272/3 := by apply Complex.ext <;> norm_num [H,x,Complex.div_re,Complex.div_im,Complex.mul_re,Complex.mul_im,pow_succ,Complex.normSq_apply]
  rw [ep] at h
  rw [integral,← intervalIntegral.integral_const_mul]; simp only [pow_one]; dsimp [f] at h; linear_combination h
end
end ZZSigned
end

section
namespace ZZWindow
open ZZTel
def Sol (f : ℕ → ℂ) : Prop := ∀ n : ℕ, a0 n * f n + a1 n * f (n+1) + a2 n * f (n+2) + a3 n * f (n+3) = 0
lemma first_ne (n : ℕ) : a0 n ≠ 0 := by
  let r : ℝ := n
  have hr : 0 ≤ r := Nat.cast_nonneg n
  have h : (-2048*r-5120)*(r+1)*(r+2)*(2*r+1)*(2*r+3)*(559455*r^4+5637736*r^3+21207869*r^2+35294652*r+21926016) ≠ 0 := by
    have : -2048*r-5120 < 0 := by linarith
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero this.ne (by positivity)) (by positivity)) (by positivity)) (by positivity)) (by positivity)
  unfold a0
  intro e
  apply h
  apply Complex.ofReal_injective
  push_cast
  simpa [r] using e
lemma back {f : ℕ → ℂ} (hf : Sol f) (n : ℕ) (h : f n = 0 ∧ f (n+1) = 0 ∧ f (n+2) = 0) : f 0 = 0 ∧ f 1 = 0 := by
  induction n with
  | zero => exact ⟨h.1,h.2.1⟩
  | succ n ih =>
    have e := hf n
    rw [h.1,h.2.1,h.2.2] at e
    simp only [mul_zero,add_zero] at e
    exact ih ⟨(mul_eq_zero.mp e).resolve_left (first_ne n),h.1,h.2.1⟩
lemma nonparallel {u v : ℕ → ℂ} (hu : Sol u) (hv : Sol v)
    (hd : u 0*v 1 ≠ u 1*v 0) (p q : ℂ) (hq : q ≠ 0) (n : ℕ) :
    ∃ k ∈ Finset.range 3, q*u (n+k) + p*v (n+k) ≠ 0 := by
  by_contra! h
  let f := fun k => q*u k + p*v k
  have hf : Sol f := by
    intro k
    dsimp [f]
    linear_combination q * hu k + p * hv k
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  obtain ⟨a,b⟩ := back hf n ⟨by simpa [f] using h0,h1,h2⟩
  dsimp [f] at a b
  apply hd
  apply sub_eq_zero.mp
  apply (mul_eq_zero.mp (show q*(u 0*v 1-u 1*v 0)=0 by linear_combination v 1*a-v 0*b)).resolve_left hq
end ZZWindow
end

section
namespace ZZSigned
noncomputable section
open ZZSegment ZZForm ZZArithmetic ZZTel ZZWindow
lemma scale_ne (n : ℕ) : scale n ≠ 0 := by
  have h : ZZDen.L n * ZZDen.phi n = ZZDen.lcm4 n := Nat.div_mul_cancel (ZZClear.phi_dvd n)
  have hh : ZZDen.lcm4 n ≠ 0 := Finset.lcm_ne_zero_iff.mpr (by simp)
  have hn : ZZDen.L n ≠ 0 := fun he => hh (by simpa [he] using h.symm)
  unfold scale; positivity
private lemma ex (n : ℕ) : ∃ u v : ℚ, integral n = u+v*(Real.pi:ℂ) := by
  cases n with
  | zero => exact ⟨0,1/4,by rw [integral_zero]; push_cast; ring⟩
  | succ n =>
    obtain ⟨a,b,h,-⟩ := ZZFinal.propositionOne (n+1) (by omega)
    refine ⟨a/scale (n+1),b/scale (n+1),?_⟩
    have hn : (scale (n+1):ℂ) ≠ 0 := by exact_mod_cast scale_ne _
    push_cast; field_simp [hn]; linear_combination h
def u (n : ℕ) : ℚ := (ex n).choose
def v (n : ℕ) : ℚ := (ex n).choose_spec.choose
lemma form (n : ℕ) : integral n = u n+v n*(Real.pi:ℂ) := (ex n).choose_spec.choose_spec
lemma splitQ {a b : ℚ} (h : (a:ℂ)+b*(Real.pi:ℂ)=0) : a=0 ∧ b=0 := by
  have h' := congrArg Complex.re h
  have he : (a:ℝ)+(b:ℝ)*Real.pi=0 := by simpa using h'
  have hb : b=0 := by
    by_contra hn
    apply irrational_pi
    refine ⟨-a/b,?_⟩; push_cast; apply (div_eq_iff (by exact_mod_cast hn : (b:ℝ) ≠ 0)).mpr; linarith
  subst b; simpa using h
lemma unique {n : ℕ} {a b : ℚ} (h : integral n = a+b*(Real.pi:ℂ)) : u n=a ∧ v n=b := by
  have z := splitQ (a:=u n-a) (b:=v n-b) (by push_cast; linear_combination h-form n)
  exact ⟨sub_eq_zero.mp z.1,sub_eq_zero.mp z.2⟩
lemma normalized (n : ℕ) (hn : 0<n) : ∃ a b : ℤ, scale n*u n=a ∧ scale n*v n=b ∧ v n=(-1:ℚ)^n*A n 0/2 := by
  obtain ⟨a,b,h,hb⟩ := ZZFinal.propositionOne n hn
  have hs : (scale n:ℂ) ≠ 0 := by exact_mod_cast scale_ne n
  obtain ⟨hu,hv⟩ := unique (a:=(a:ℚ)/scale n) (b:=(b:ℚ)/scale n) (by push_cast; field_simp [hs]; linear_combination h)
  refine ⟨a,b,by rw [hu]; field_simp [scale_ne], by rw [hv]; field_simp [scale_ne],?_⟩
  rw [hv,← hb]; field_simp [scale_ne]
lemma initial : u 0=0 ∧ v 0=1/4 ∧ u 1= -11272/3 ∧ v 1=1196 := by
  have h := unique (n:=0) (a:=0) (b:=1/4) (by rw [integral_zero]; push_cast; ring)
  have k := unique (n:=1) (a:= -11272/3) (b:=1196) (by rw [integral_one]; push_cast; ring)
  exact ⟨h.1,h.2,k⟩
private def r0 (n : ℚ) : ℚ := (-2048*n - 5120)*(n + 1)*(n + 2)*(2*n + 1)*(2*n + 3)*(559455*n^4 + 5637736*n^3 + 21207869*n^2 + 35294652*n + 21926016)
private lemma c0 (n : ℕ) : (r0 n:ℂ)=a0 n := by unfold r0 a0; push_cast; rfl
private def r1 (n : ℚ) : ℚ := (n + 2)*(2*n + 3)*(128*n + 320)*(1208982255*n^6 + 14601112006*n^5 + 71554462078*n^4 + 181444545414*n^3 + 250049018747*n^2 + 176898555884*n + 50159702880)
private lemma c1 (n : ℕ) : (r1 n:ℂ)=a1 n := by unfold r1 a1; push_cast; rfl
private def r2 (n : ℚ) : ℚ := (-12*n - 30)*(440102548665*n^8 + 7075613606958*n^7 + 49182254436312*n^6 + 192978557313766*n^5 + 467319046780891*n^4 + 714892923466956*n^3 + 674376299494052*n^2 + 358497976451216*n + 82191375084672)
private lemma c2 (n : ℕ) : (r2 n:ℂ)=a2 n := by unfold r2 a2; push_cast; rfl
private def r3 (n : ℚ) : ℚ := (n + 3)*(3*n + 7)*(3*n + 8)*(4*n + 9)*(12*n + 33)*(559455*n^4 + 3399916*n^3 + 7651391*n^2 + 7554302*n + 2760952)
private lemma c3 (n : ℕ) : (r3 n:ℂ)=a3 n := by unfold r3 a3; push_cast; rfl
private def comb (f : ℕ → ℚ) (n : ℕ) : ℚ := r0 n*f n+r1 n*f (n+1)+r2 n*f (n+2)+r3 n*f (n+3)
lemma solutions : Sol (fun n => (u n:ℂ)) ∧ Sol (fun n => (v n:ℂ)) := by
  have h (n : ℕ) := integral_recurrence n
  have z n := splitQ (a:=comb u n) (b:=comb v n) (by
    have e := h n; simp only [form] at e; unfold comb; push_cast; rw [c0,c1,c2,c3]; linear_combination e)
  constructor <;> intro n
  · have e := congrArg (fun r : ℚ => (r:ℂ)) (z n).1; simpa [comb,c0,c1,c2,c3] using e
  · have e := congrArg (fun r : ℚ => (r:ℂ)) (z n).2; simpa [comb,c0,c1,c2,c3] using e
lemma window (p q : ℂ) (hq : q ≠ 0) (n : ℕ) : ∃ k ∈ Finset.range 3, q*u (n+k)+p*v (n+k) ≠ 0 := by
  apply nonparallel solutions.1 solutions.2 _ p q hq n
  obtain ⟨a,b,c,d⟩ := initial; norm_num [a,b,c,d]
end
end ZZSigned
end

section
namespace ZZCoeff
open Filter Topology ZZTel
noncomputable section
def rev0 (z : ℂ) : ℂ := (-673567211520)*z^9+(-4160208642048)*z^8+(-10654675961856)*z^7+(-15097169462272)*z^6+(-13185613626368)*z^5+(-7417406374912)*z^4+(-2702460775424)*z^3+(-617507289088)*z^2+(-80557248512)*z^1+(-4583055360)*z^0
theorem lim0 : Tendsto (fun n : ℕ => a0 n / (n:ℂ)^9) atTop (𝓝 (-4583055360:ℂ)) := by
  have hi := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).ofReal
  have h : Tendsto (fun n : ℕ => (n:ℂ)⁻¹) atTop (𝓝 0) := by simpa [Function.comp_def] using hi
  have hc : Continuous (rev0) := by unfold rev0; fun_prop
  have ht := (hc.tendsto 0).comp h
  norm_num [rev0] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [Function.comp_def,rev0,a0]; field_simp [hn0]; ring
def rev1 (z : ℂ) : ℂ := (96306629529600)*z^9+(490525613560320)*z^8+(1089250275716992)*z^7+(1385078041360960)*z^6+(1112531082896768)*z^5+(585981327537280)*z^4+(202598848221440)*z^3+(44381868956224)*z^2+(5594881417216)*z^1+(309499457280)*z^0
theorem lim1 : Tendsto (fun n : ℕ => a1 n / (n:ℂ)^9) atTop (𝓝 (309499457280:ℂ)) := by
  have hi := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).ofReal
  have h : Tendsto (fun n : ℕ => (n:ℂ)⁻¹) atTop (𝓝 0) := by simpa [Function.comp_def] using hi
  have hc : Continuous (rev1) := by unfold rev1; fun_prop
  have ht := (hc.tendsto 0).comp h
  norm_num [rev1] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [Function.comp_def,rev1,a1]; field_simp [hn0]; ring
def rev2 (z : ℂ) : ℂ := (-2465741252540160)*z^9+(-11741235794552544)*z^8+(-24533264702236152)*z^7+(-29539303297937304)*z^6+(-22598286485030202)*z^5+(-11397185280783672)*z^4+(-3791210320854552)*z^3+(-802455461444484)*z^2+(-98110439743446)*z^1+(-5281230583980)*z^0
theorem lim2 : Tendsto (fun n : ℕ => a2 n / (n:ℂ)^9) atTop (𝓝 (-5281230583980:ℂ)) := by
  have hi := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).ofReal
  have h : Tendsto (fun n : ℕ => (n:ℂ)⁻¹) atTop (𝓝 0) := by simpa [Function.comp_def] using hi
  have hc : Continuous (rev2) := by unfold rev2; fun_prop
  have ht := (hc.tendsto 0).comp h
  norm_num [rev2] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [Function.comp_def,rev2,a2]; field_simp [hn0]; ring
def rev3 (z : ℂ) : ℂ := (137760460992)*z^9+(644871561336)*z^8+(1322762705706)*z^7+(1561336723281)*z^6+(1169418475314)*z^5+(576700153800)*z^4+(187362872196)*z^3+(38691218223)*z^2+(4610662992)*z^1+(241684560)*z^0
theorem lim3 : Tendsto (fun n : ℕ => a3 n / (n:ℂ)^9) atTop (𝓝 (241684560:ℂ)) := by
  have hi := (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).ofReal
  have h : Tendsto (fun n : ℕ => (n:ℂ)⁻¹) atTop (𝓝 0) := by simpa [Function.comp_def] using hi
  have hc : Continuous (rev3) := by unfold rev3; fun_prop
  have ht := (hc.tendsto 0).comp h
  norm_num [rev3] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [Function.comp_def,rev3,a3]; field_simp [hn0]; ring
end
end ZZCoeff
end

section
open Filter Topology
namespace ZZCone
theorem bounded_rate (u s x : ℕ → ℝ) {q R A B K : ℝ} (hs : ∀ n, 0 ≤ s n)
    (hq : 0 < q) (hR : q < R) (hA : 1 < A) (hK : 0 ≤ K)
    (hb : ∀ n, u n ≤ B) (hx : ∀ n, x n ≤ K * max (u n) (s n))
    (hstep : ∀ᶠ n in atTop, s (n+1) ≤ q * max (u n) (s n) ∧
      (s n < u n → A * u n ≤ u (n+1) ∧ s (n+1) < u (n+1))) :
    ∀ᶠ n in atTop, x n ≤ R^n := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hstep
  have outside (n : ℕ) (hn : N ≤ n) : u n ≤ s n := by
    by_contra! h
    have grow (k : ℕ) : s (n+k) < u (n+k) ∧ A^k * u n ≤ u (n+k) := by
      induction k with
      | zero => simpa using And.intro h (le_refl (u n))
      | succ k ih =>
        obtain ⟨g,c⟩ := (hN (n+k) (by omega)).2 ih.1
        refine ⟨c, ?_⟩
        change _ ≤ u (n+k+1)
        rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_left ih.2 (show 0 ≤ A by linarith)]
    have pos := lt_of_le_of_lt (hs n) h
    obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (B / u n) hA
    exact (not_lt_of_ge ((grow k).2.trans (hb _))) ((div_lt_iff₀ pos).mp hk)
  have decay (k : ℕ) : s (N+k) ≤ q^k * s N := by
    induction k with
    | zero => simp
    | succ k ih =>
      have h := (hN (N+k) (by omega)).1
      rw [max_eq_right (outside _ (by omega))] at h
      change s (N+k+1) ≤ _
      rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_left ih hq.le]
  have rp := hq.trans hR
  have lim := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hq.le rp.le)
    ((div_lt_one rp).2 hR)).const_mul (K * s N)
  have ev : ∀ᶠ k : ℕ in atTop, (K*s N)*(q/R)^k < R^N :=
    lim.eventually_lt_const (by simpa using pow_pos rp N)
  obtain ⟨M,hM⟩ := eventually_atTop.mp ev
  apply eventually_atTop.mpr
  refine ⟨N+M, fun n hn => ?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show N ≤ n by omega)
  have h := hM k (by omega)
  rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (pow_pos rp k)] at h
  have h' := hx (N+k)
  rw [max_eq_right (outside _ (by omega))] at h'
  rw [pow_add]; nlinarith [mul_le_mul_of_nonneg_left (decay k) hK]
end ZZCone
end

section
namespace ZZCone
open Filter Topology
noncomputable section
def mode (x : ℕ → ℂ) (a b c : ℂ) (n : ℕ) :=
  (x (n+2) - (b+c)*x (n+1) + b*c*x n) / ((a-b)*(a-c))
theorem three (x : ℕ → ℂ) {a b c : ℂ} (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a) (n : ℕ) :
    let u := mode x a b c n; let v := mode x b c a n; let w := mode x c a b n
    x n = u+v+w ∧ x (n+1) = a*u+b*v+c*w ∧ x (n+2) = a^2*u+b^2*v+c^2*w := by
  dsimp [mode]; refine ⟨?_, ?_, ?_⟩ <;> field_simp [sub_ne_zero.mpr ab, sub_ne_zero.mpr ab.symm, sub_ne_zero.mpr bc, sub_ne_zero.mpr bc.symm, sub_ne_zero.mpr ca, sub_ne_zero.mpr ca.symm] <;> ring
theorem mode_step (x : ℕ → ℂ) (a b c : ℂ) (n : ℕ) :
    mode x a b c (n+1) = a * mode x a b c n +
    (x (n+3) - (a+b+c)*x (n+2) + (a*b+b*c+c*a)*x (n+1) - a*b*c*x n)/((a-b)*(a-c)) := by
  unfold mode; change (x (n+3) - _ * x (n+2) + _) / _ = _
  ring
theorem diag_rate (u v w x : ℕ → ℂ) (a b c : ℂ) {R : ℝ}
    (ha : 1 < ‖a‖) (hb : ‖b‖ < R) (hc : ‖c‖ < R) (hR : R < 1)
    (bound : ∃ B, ∀ n, ‖u n‖ ≤ B) (recon : ∀ n, x n = u n + v n + w n)
    (small : ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      let M := max ‖u n‖ (max ‖v n‖ ‖w n‖)
      ‖u (n+1)-a*u n‖ ≤ e*M ∧ ‖v (n+1)-b*v n‖ ≤ e*M ∧ ‖w (n+1)-c*w n‖ ≤ e*M) :
    ∀ᶠ n in atTop, ‖x n‖ ≤ R^n := by
  obtain ⟨B, hB⟩ := bound
  let r := max ‖b‖ ‖c‖
  have hr : r < R := max_lt hb hc
  let e := min ((R-r)/2) ((‖a‖-1)/2)
  have he : 0 < e := lt_min (by linarith) (by linarith)
  have e1 : e ≤ (R-r)/2 := min_le_left ..
  have e2 : e ≤ (‖a‖-1)/2 := min_le_right ..
  have r0 : 0 ≤ r := (norm_nonneg _).trans (le_max_left ..)
  apply bounded_rate (fun n => ‖u n‖) (fun n => max ‖v n‖ ‖w n‖) (fun n => ‖x n‖)
    (q := r+e) (A := ‖a‖-e) (K := 3) (fun _ => (norm_nonneg _).trans (le_max_left ..))
    (by linarith) (by linarith) (by linarith) (by norm_num) hB
  · intro n; rw [recon]
    have hu := le_max_left ‖u n‖ (max ‖v n‖ ‖w n‖)
    have hv := (le_max_left ‖v n‖ ‖w n‖).trans (le_max_right ‖u n‖ _)
    have hw := (le_max_right ‖v n‖ ‖w n‖).trans (le_max_right ‖u n‖ _)
    linarith [norm_add_le (u n + v n) (w n), norm_add_le (u n) (v n)]
  · filter_upwards [small e he] with n hn
    dsimp only at hn ⊢
    let M := max ‖u n‖ (max ‖v n‖ ‖w n‖)
    have f {z y l : ℂ} (hy : ‖y‖ ≤ M) (hl : ‖l‖ ≤ r) (hed : ‖z-l*y‖ ≤ e*M) : ‖z‖ ≤ (r+e)*M := by
      have ht := norm_sub_le z (l*y)
      have hd := norm_add_le (z-l*y) (l*y)
      rw [sub_add_cancel,norm_mul] at hd
      nlinarith [mul_le_mul hl hy (norm_nonneg _) r0]
    have hs := max_le (f ((le_max_left ..).trans (le_max_right ..)) (le_max_left ..) hn.2.1)
      (f ((le_max_right ..).trans (le_max_right ..)) (le_max_right ..) hn.2.2)
    refine ⟨hs, fun hin => ?_⟩
    have hm : M = ‖u n‖ := max_eq_left hin.le
    have hd := norm_sub_le (u (n+1)) (u (n+1)-a*u n)
    rw [sub_sub_cancel, norm_mul] at hd
    have hu := hn.1
    change _ ≤ e*M at hu
    rw [hm] at hu hs
    have pos : 0 < ‖u n‖ := (norm_nonneg _).trans_lt ((le_max_left ..).trans_lt hin)
    constructor
    · linarith only [hd,hu,show (‖a‖-e)*‖u n‖ = ‖a‖*‖u n‖-e*‖u n‖ by ring]
    · nlinarith [mul_pos (show 0 < ‖a‖-e-(r+e) by linarith) pos]
end
end ZZCone
end

section
namespace ZZApply
noncomputable section
open Filter Topology ZZCone ZZTel ZZSegment ZZCoeff
abbrev X := integral
def P (n : ℕ) (z : ℂ) := (a0 n + a1 n*z + a2 n*z^2)/a3 n + z^3
def root (z : ℂ) := 108*z^3-2359989*z^2+138304*z-2048 = 0
theorem Plim {z : ℂ} (hz : root z) : Tendsto (fun n => P n z) atTop (𝓝 0) := by
  have h := (((lim0.add (lim1.mul_const z)).add (lim2.mul_const (z^2))).div lim3 (by norm_num)).add_const (z^3)
  have he : ((-4583055360:ℂ)+309499457280*z+(-5281230583980)*z^2)/241684560+z^3 = 0 := by
    unfold root at hz; linear_combination hz/108
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [P]; by_cases h3 : a3 n = 0
  · simp [h3]
  · field_simp [hn0,h3]
theorem rate {a b c : ℂ} {R : ℝ} (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a)
    (ra : root a) (rb : root b) (rc : root c) (ha : 1 < ‖a‖) (hb : ‖b‖ < R)
    (hc : ‖c‖ < R) (hR : R < 1) : ∀ᶠ n in atTop, ‖integral n‖ ≤ R^n := by
  let U := mode X a b c; let V := mode X b c a; let W := mode X c a b
  have recn := three X ab bc ca
  have step (l m k : ℂ) (n : ℕ) (u v w : ℂ)
      (h0 : X n = u+v+w) (h1 : X (n+1) = l*u+m*v+k*w)
      (h2 : X (n+2) = l^2*u+m^2*v+k^2*w) (h3 : a3 n ≠ 0) :
      mode X l m k (n+1)-l*mode X l m k n =
        -(P n l/((l-m)*(l-k))*u + P n m/((l-m)*(l-k))*v + P n k/((l-m)*(l-k))*w) := by
    have eqn := integral_recurrence n
    change a0 n * X n + a1 n * X (n+1) + a2 n * X (n+2) + a3 n * X (n+3) = 0 at eqn
    rw [h0,h1,h2] at eqn
    rw [mode_step, h0,h1,h2]; unfold P
    by_cases hd : (l-m)*(l-k) = 0
    · simp [hd]
    · generalize (l-m)*(l-k) = d at hd ⊢
      field_simp [hd,h3] <;> linear_combination eqn
  apply diag_rate U V W X a b c ha hb hc hR
  · refine ⟨(1+‖b+c‖+‖b*c‖)/‖(a-b)*(a-c)‖, fun n => ?_⟩
    dsimp [U,mode]; rw [norm_div]; apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    have h (j : ℕ) : ‖X j‖ ≤ 1 := (integral_bound j).trans (by norm_num)
    calc
      _ ≤ ‖X (n+2)‖ + ‖(b+c)*X (n+1)‖ + ‖(b*c)*X n‖ := (norm_add_le ..).trans (add_le_add_left (norm_sub_le ..) _)
      _ ≤ _ := by simp only [norm_mul]; nlinarith [h (n+2),mul_le_mul_of_nonneg_left (h (n+1)) (norm_nonneg (b+c)),mul_le_mul_of_nonneg_left (h n) (norm_nonneg (b*c)), mul_le_mul_of_nonneg_left (h n) (mul_nonneg (norm_nonneg b) (norm_nonneg c))]
  · exact fun n => (recn n).1
  · intro e he
    let M (n : ℕ) := max ‖U n‖ (max ‖V n‖ ‖W n‖)
    have small (z d : ℂ) (hz : root z) : ∀ᶠ n in atTop, ‖P n z / d‖ ≤ e/3 := by
      have h := ((Plim hz).div_const d).norm
      simp at h
      exact (h.eventually_lt_const (by linarith : 0 < e/3)).mono fun _ h => by simpa only [norm_div] using h.le
    have bound {i j k u v w : ℂ} {m : ℝ} (hi : ‖i‖ ≤ e/3) (hj : ‖j‖ ≤ e/3) (hk : ‖k‖ ≤ e/3)
        (hu : ‖u‖ ≤ m) (hv : ‖v‖ ≤ m) (hw : ‖w‖ ≤ m) : ‖-(i*u+j*v+k*w)‖ ≤ e*m := by
      rw [norm_neg]; have ht := (norm_add_le (i*u+j*v) (k*w)).trans (add_le_add_left (norm_add_le (i*u) (j*v)) _)
      simp only [norm_mul] at ht
      linarith [mul_le_mul hi hu (norm_nonneg _) (by positivity),mul_le_mul hj hv (norm_nonneg _) (by positivity),mul_le_mul hk hw (norm_nonneg _) (by positivity)]
    have nz := lim3.eventually_ne (show (241684560:ℂ) ≠ 0 by norm_num)
    filter_upwards [nz,small a ((a-b)*(a-c)) ra,small b ((a-b)*(a-c)) rb,small c ((a-b)*(a-c)) rc,small b ((b-c)*(b-a)) rb,small c ((b-c)*(b-a)) rc,small a ((b-c)*(b-a)) ra,small c ((c-a)*(c-b)) rc,small a ((c-a)*(c-b)) ra,small b ((c-a)*(c-b)) rb] with n hn h1 h2 h3 h4 h5 h6 h7 h8 h9
    have h3n : a3 n ≠ 0 := fun h => hn (by simp [h])
    obtain ⟨x0,x1,x2⟩ := recn n
    change X n = U n+V n+W n at x0
    change X (n+1) = a*U n+b*V n+c*W n at x1
    change X (n+2) = a^2*U n+b^2*V n+c^2*W n at x2
    have um : ‖U n‖ ≤ M n := le_max_left ..
    have vm : ‖V n‖ ≤ M n := (le_max_left ..).trans (le_max_right ..)
    have wm : ‖W n‖ ≤ M n := (le_max_right ..).trans (le_max_right ..)
    refine ⟨?_, ?_, ?_⟩
    · change ‖mode X a b c (n+1)-a*mode X a b c n‖ ≤ e*M n
      rw [step a b c n (U n) (V n) (W n) (by linear_combination x0) (by linear_combination x1) (by linear_combination x2) h3n]
      exact bound h1 h2 h3 um vm wm
    · change ‖mode X b c a (n+1)-b*mode X b c a n‖ ≤ e*M n
      rw [step b c a n (V n) (W n) (U n) (by linear_combination x0) (by linear_combination x1) (by linear_combination x2) h3n]
      exact bound h4 h5 h6 vm wm um
    · change ‖mode X c a b (n+1)-c*mode X c a b n‖ ≤ e*M n
      rw [step c a b n (W n) (U n) (V n) (by linear_combination x0) (by linear_combination x1) (by linear_combination x2) h3n]
      exact bound h7 h8 h9 wm um vm
end
end ZZApply
end

section
namespace ZZRate
noncomputable def poly (x : ℝ) := 108*x^3-2359989*x^2+138304*x-2048
abbrev lo : ℝ := 21851.6913962195616968020
abbrev hi : ℝ := 21851.6913962195616968021
theorem certified_root : ∃ t ∈ Set.Icc lo hi, poly t = 0 ∧
    0.02945849592811687636 ≤ Real.sqrt (2048/(108*t)) ∧
    Real.sqrt (2048/(108*t)) ≤ 0.02945849592811687638 := by
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (f := poly) (a := lo) (b := hi)
    (by norm_num [lo, hi]) (by unfold poly; fun_prop) (show (0:ℝ) ∈ Set.Icc (poly lo) (poly hi) by constructor <;> norm_num [poly,lo,hi])
  have hpos : 0 < 108*t := by have := ht.1; norm_num [lo] at this; linarith
  refine ⟨t, ht, he, ?_, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hpos).2
    have := ht.2; norm_num [hi] at this; linarith
  · apply (Real.sqrt_le_left (by norm_num)).2
    apply (div_le_iff₀ hpos).2
    have := ht.1; norm_num [lo] at this; linarith
end ZZRate
end

section
namespace ZZApply
noncomputable section
open Filter Complex
theorem integral_stable_rate {t R : ℝ} (ht : t ∈ Set.Icc ZZRate.lo ZZRate.hi)
    (hp : ZZRate.poly t = 0) (hR : Real.sqrt (2048/(108*t)) < R) (h1 : R < 1) :
    ∀ᶠ n in atTop, ‖ZZSegment.integral n‖ ≤ R^n := by
  have tl := ht.1; have tu := ht.2; norm_num [ZZRate.lo,ZZRate.hi] at tl tu
  have t0 : 0 < t := by linarith
  set s := 2359989/108 - t
  set p := 2048/(108*t)
  have hpt : p*t = 2048/108 := by simp only [p]; field_simp
  have disc : 0 < p - s^2/4 := by
    have : 0.00086 < p := by simp only [p]; rw [lt_div_iff₀ (by positivity)]; nlinarith
    simp only [s]; nlinarith
  set d := Real.sqrt (p - s^2/4)
  have dd : d^2 = p - s^2/4 := Real.sq_sqrt disc.le
  have d0 : 0 < d := Real.sqrt_pos.2 disc
  have vieta : t*s + p = 138304/108 := by
    unfold ZZRate.poly at hp
    have : t*(t*s+p-138304/108) = 0 := by simp only [s]; nlinarith
    rcases mul_eq_zero.1 this with h | h <;> linarith
  let b : ℂ := ⟨s/2, d⟩; let c : ℂ := ⟨s/2, -d⟩
  have nb : ‖b‖ = Real.sqrt p := by
    rw [Complex.norm_def, Complex.normSq_mk]; congr 1; nlinarith
  have nc : ‖c‖ = Real.sqrt p := by
    rw [Complex.norm_def, Complex.normSq_mk]; congr 1; nlinarith
  have quad (z : ℂ) (hz : z = b ∨ z = c) : z^2 - s*z + p = 0 := by
    apply Complex.ext <;> rcases hz with rfl | rfl <;> simp [b, c, pow_two] <;> nlinarith [dd]
  have fac (z : ℂ) (hz : z = b ∨ z = c) : root z := by
    unfold root
    have hq := quad z hz
    have vc : (t:ℂ)*s+p = 138304/108 := by have := congrArg (fun r : ℝ => (r:ℂ)) vieta; push_cast at this; exact this
    have hc : (p:ℂ)*t = 2048/108 := by have := congrArg (fun r : ℝ => (r:ℂ)) hpt; push_cast at this; exact this
    have hs : (s:ℂ) = 2359989/108 - t := by simp [s]
    linear_combination (108*(z-t))*hq - 108*z*vc + 108*hc + 108*z^2*hs
  have rt : root (t:ℂ) := by unfold root; unfold ZZRate.poly at hp; exact_mod_cast hp
  have ne1 (z : ℂ) (hz : z.im ≠ 0) : (t:ℂ) ≠ z := fun h => hz (by rw [← h]; simp)
  apply rate (a := (t:ℂ)) (b := b) (c := c) (ne1 b (by simp [b]; exact d0.ne'))
    (fun h => by have := congrArg Complex.im h; simp [b,c] at this; linarith)
    (fun h => ne1 c (by simp [c]; exact d0.ne') h.symm) rt (fac b (.inl rfl)) (fac c (.inr rfl))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos t0]; linarith)
    (by rwa [nb]) (by rwa [nc]) h1
theorem integral_stable_rate_exists : ∃ t ∈ Set.Icc ZZRate.lo ZZRate.hi, ZZRate.poly t = 0 ∧
    ∀ R, Real.sqrt (2048/(108*t)) < R → R < 1 → ∀ᶠ n in atTop, ‖ZZSegment.integral n‖ ≤ R^n := by
  obtain ⟨t,ht,hp,-⟩ := ZZRate.certified_root
  exact ⟨t,ht,hp,fun R hR h1 => integral_stable_rate ht hp hR h1⟩
end
end ZZApply
end

section
namespace ZZSigned
noncomputable section
open Filter Topology ZZCone ZZApply ZZTel ZZCoeff ZZWindow
private theorem major (u v w x : ℕ → ℂ) (a b c : ℂ) {R : ℝ}
    (ha : ‖a‖ < R) (hb : ‖b‖ < R) (hc : ‖c‖ < R) (recon : ∀ n, x n = u n + v n + w n)
    (small : ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop,
      let M := max ‖u n‖ (max ‖v n‖ ‖w n‖)
      ‖u (n+1)-a*u n‖ ≤ e*M ∧ ‖v (n+1)-b*v n‖ ≤ e*M ∧ ‖w (n+1)-c*w n‖ ≤ e*M) :
    ∀ᶠ n in atTop, ‖x n‖ ≤ R^n := by
  let r := max ‖a‖ (max ‖b‖ ‖c‖)
  let M n := max ‖u n‖ (max ‖v n‖ ‖w n‖)
  have hr : r < R := max_lt ha (max_lt hb hc)
  have r0 : 0 ≤ r := (norm_nonneg _).trans (le_max_left ..)
  let e := (R-r)/2
  have he : 0 < e := by dsimp [e]; linarith
  have m0 n : 0 ≤ M n := (norm_nonneg _).trans (le_max_left ..)
  apply bounded_rate (fun _ => 0) M (fun n => ‖x n‖) (q:=r+e) (A:=2) (B:=0) (K:=3) m0 (by positivity) (by dsimp [e]; linarith) (by norm_num) (by norm_num) (fun _ => le_rfl)
  · intro n; rw [max_eq_right (m0 n), recon]; dsimp [M]
    have h1 := le_max_left ‖u n‖ (max ‖v n‖ ‖w n‖)
    have h2 := (le_max_left ‖v n‖ ‖w n‖).trans (le_max_right ‖u n‖ _)
    have h3 := (le_max_right ‖v n‖ ‖w n‖).trans (le_max_right ‖u n‖ _)
    linarith [norm_add_le (u n+v n) (w n),norm_add_le (u n) (v n)]
  · filter_upwards [small e he] with n hn
    rw [max_eq_right (m0 n)]; refine ⟨?_, fun h => False.elim ((not_lt_of_ge (m0 n)) h)⟩
    have f {z y l : ℂ} (hy : ‖y‖ ≤ M n) (hl : ‖l‖ ≤ r) (hd : ‖z-l*y‖ ≤ e*M n) : ‖z‖ ≤ (r+e)*M n := by
      have h := norm_add_le (z-l*y) (l*y); rw [sub_add_cancel,norm_mul] at h
      nlinarith [mul_le_mul hl hy (norm_nonneg _) r0]
    exact max_le (f (le_max_left ..) (le_max_left ..) hn.1) (max_le
      (f ((le_max_left ..).trans (le_max_right ..)) ((le_max_left ..).trans (le_max_right ..)) hn.2.1)
      (f ((le_max_right ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..)) hn.2.2))
theorem solution_rate (X : ℕ → ℂ) (hx : Sol X) {a b c : ℂ} {R : ℝ} (ab : a ≠ b) (bc : b ≠ c) (ca : c ≠ a)
    (ra : root a) (rb : root b) (rc : root c) (ha : ‖a‖ < R) (hb : ‖b‖ < R)
    (hc : ‖c‖ < R) : ∀ᶠ n in atTop, ‖X n‖ ≤ R^n := by
  let U := mode X a b c; let V := mode X b c a; let W := mode X c a b
  have recn := three X ab bc ca
  have step (l m k : ℂ) (n : ℕ) (u v w : ℂ)
      (h0 : X n = u+v+w) (h1 : X (n+1) = l*u+m*v+k*w)
      (h2 : X (n+2) = l^2*u+m^2*v+k^2*w) (h3 : a3 n ≠ 0) :
      mode X l m k (n+1)-l*mode X l m k n =
        -(P n l/((l-m)*(l-k))*u + P n m/((l-m)*(l-k))*v + P n k/((l-m)*(l-k))*w) := by
    have eqn := hx n
    change a0 n * X n + a1 n * X (n+1) + a2 n * X (n+2) + a3 n * X (n+3) = 0 at eqn
    rw [h0,h1,h2] at eqn
    rw [mode_step, h0,h1,h2]; unfold P
    by_cases hd : (l-m)*(l-k) = 0
    · simp [hd]
    · generalize (l-m)*(l-k) = d at hd ⊢
      field_simp [hd,h3] <;> linear_combination eqn
  apply major U V W X a b c ha hb hc
  · exact fun n => (recn n).1
  · intro e he
    let M (n : ℕ) := max ‖U n‖ (max ‖V n‖ ‖W n‖)
    have small (z d : ℂ) (hz : root z) : ∀ᶠ n in atTop, ‖P n z / d‖ ≤ e/3 := by
      have h := ((Plim hz).div_const d).norm
      simp at h
      exact (h.eventually_lt_const (by linarith : 0 < e/3)).mono fun _ h => by simpa only [norm_div] using h.le
    have bound {i j k u v w : ℂ} {m : ℝ} (hi : ‖i‖ ≤ e/3) (hj : ‖j‖ ≤ e/3) (hk : ‖k‖ ≤ e/3)
        (hu : ‖u‖ ≤ m) (hv : ‖v‖ ≤ m) (hw : ‖w‖ ≤ m) : ‖-(i*u+j*v+k*w)‖ ≤ e*m := by
      rw [norm_neg]; have ht := (norm_add_le (i*u+j*v) (k*w)).trans (add_le_add_left (norm_add_le (i*u) (j*v)) _)
      simp only [norm_mul] at ht
      linarith [mul_le_mul hi hu (norm_nonneg _) (by positivity),mul_le_mul hj hv (norm_nonneg _) (by positivity),mul_le_mul hk hw (norm_nonneg _) (by positivity)]
    have nz := lim3.eventually_ne (show (241684560:ℂ) ≠ 0 by norm_num)
    filter_upwards [nz,small a ((a-b)*(a-c)) ra,small b ((a-b)*(a-c)) rb,small c ((a-b)*(a-c)) rc,small b ((b-c)*(b-a)) rb,small c ((b-c)*(b-a)) rc,small a ((b-c)*(b-a)) ra,small c ((c-a)*(c-b)) rc,small a ((c-a)*(c-b)) ra,small b ((c-a)*(c-b)) rb] with n hn h1 h2 h3 h4 h5 h6 h7 h8 h9
    have h3n : a3 n ≠ 0 := fun h => hn (by simp [h])
    obtain ⟨x0,x1,x2⟩ := recn n
    change X n = U n+V n+W n at x0
    change X (n+1) = a*U n+b*V n+c*W n at x1
    change X (n+2) = a^2*U n+b^2*V n+c^2*W n at x2
    have um : ‖U n‖ ≤ M n := le_max_left ..
    have vm : ‖V n‖ ≤ M n := (le_max_left ..).trans (le_max_right ..)
    have wm : ‖W n‖ ≤ M n := (le_max_right ..).trans (le_max_right ..)
    refine ⟨?_, ?_, ?_⟩
    · change ‖mode X a b c (n+1)-a*mode X a b c n‖ ≤ e*M n
      rw [step a b c n (U n) (V n) (W n) (by linear_combination x0) (by linear_combination x1) (by linear_combination x2) h3n]
      exact bound h1 h2 h3 um vm wm
    · change ‖mode X b c a (n+1)-b*mode X b c a n‖ ≤ e*M n
      rw [step b c a n (V n) (W n) (U n) (by linear_combination x0) (by linear_combination x1) (by linear_combination x2) h3n]
      exact bound h4 h5 h6 vm wm um
    · change ‖mode X c a b (n+1)-c*mode X c a b n‖ ≤ e*M n
      rw [step c a b n (W n) (U n) (V n) (by linear_combination x0) (by linear_combination x1) (by linear_combination x2) h3n]
      exact bound h7 h8 h9 wm um vm
open Complex
theorem solution_growth (X : ℕ → ℂ) (hx : Sol X) {t R : ℝ} (ht : t ∈ Set.Icc ZZRate.lo ZZRate.hi)
    (hp : ZZRate.poly t = 0) (hR : t < R) :
    ∀ᶠ n in atTop, ‖X n‖ ≤ R^n := by
  have tl := ht.1; have tu := ht.2; norm_num [ZZRate.lo,ZZRate.hi] at tl tu
  have t0 : 0 < t := by linarith
  set s := 2359989/108 - t
  set p := 2048/(108*t)
  have hpt : p*t = 2048/108 := by simp only [p]; field_simp
  have disc : 0 < p - s^2/4 := by
    have : 0.00086 < p := by simp only [p]; rw [lt_div_iff₀ (by positivity)]; nlinarith
    simp only [s]; nlinarith
  set d := Real.sqrt (p - s^2/4)
  have dd : d^2 = p - s^2/4 := Real.sq_sqrt disc.le
  have d0 : 0 < d := Real.sqrt_pos.2 disc
  have vieta : t*s + p = 138304/108 := by
    unfold ZZRate.poly at hp
    have : t*(t*s+p-138304/108) = 0 := by simp only [s]; nlinarith
    rcases mul_eq_zero.1 this with h | h <;> linarith
  let b : ℂ := ⟨s/2, d⟩; let c : ℂ := ⟨s/2, -d⟩
  have nb : ‖b‖ = Real.sqrt p := by
    rw [Complex.norm_def, Complex.normSq_mk]; congr 1; nlinarith
  have nc : ‖c‖ = Real.sqrt p := by
    rw [Complex.norm_def, Complex.normSq_mk]; congr 1; nlinarith
  have quad (z : ℂ) (hz : z = b ∨ z = c) : z^2 - s*z + p = 0 := by
    apply Complex.ext <;> rcases hz with rfl | rfl <;> simp [b, c, pow_two] <;> nlinarith [dd]
  have fac (z : ℂ) (hz : z = b ∨ z = c) : root z := by
    unfold root
    have hq := quad z hz
    have vc : (t:ℂ)*s+p = 138304/108 := by have := congrArg (fun r : ℝ => (r:ℂ)) vieta; push_cast at this; exact this
    have hc : (p:ℂ)*t = 2048/108 := by have := congrArg (fun r : ℝ => (r:ℂ)) hpt; push_cast at this; exact this
    have hs : (s:ℂ) = 2359989/108 - t := by simp [s]
    linear_combination (108*(z-t))*hq - 108*z*vc + 108*hc + 108*z^2*hs
  have rt : root (t:ℂ) := by unfold root; unfold ZZRate.poly at hp; exact_mod_cast hp
  have ne1 (z : ℂ) (hz : z.im ≠ 0) : (t:ℂ) ≠ z := fun h => hz (by rw [← h]; simp)
  have hsmall : Real.sqrt p < R := by
    have h : p < 1 := by dsimp [p]; rw [div_lt_one (by positivity)]; linarith
    have h2 := Real.sq_sqrt (show 0 ≤ p by dsimp [p]; positivity); nlinarith
  apply solution_rate X hx (a := (t:ℂ)) (b := b) (c := c) (ne1 b (by simp [b]; exact d0.ne'))
    (fun h => by have := congrArg Complex.im h; simp [b,c] at this; linarith)
    (fun h => ne1 c (by simp [c]; exact d0.ne') h.symm) rt (fac b (.inl rfl)) (fac c (.inr rfl))
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos t0]; linarith)
    (by rwa [nb]) (by rwa [nc])
theorem pi_growth {t R : ℝ} (ht : t ∈ Set.Icc ZZRate.lo ZZRate.hi) (hp : ZZRate.poly t = 0) (hr : t < R) : ∀ᶠ n in atTop, |(v n:ℝ)| ≤ R^n := by
  simpa using solution_growth _ solutions.2 ht hp hr
end
end ZZSigned
end

section
namespace ZZMeasure
open Filter Real
theorem det_bound (a b p : ℤ) (q : ℕ) (x : ℝ) (hq : 0 < q)
    (hn : (q : ℤ)*a+p*b ≠ 0) :
    1 ≤ (q:ℝ) * |a+(b:ℝ)*x| + (q:ℝ) * |(b:ℝ)| * |x-p/q| := by
  have hz : 1 ≤ |(q:ℤ)*a+p*b| := Int.one_le_abs hn
  have h : (1:ℝ) ≤ |(q:ℝ)*a+p*b| := by exact_mod_cast hz
  have hq' : (q:ℝ) ≠ 0 := by positivity
  have eqn : (q:ℝ)*a+p*b = q*(a+(b:ℝ)*x) - q*b*(x-p/q) := by
    field_simp; ring
  rw [eqn] at h
  have := h.trans (abs_sub _ _)
  simpa [abs_mul,abs_of_nonneg (Nat.cast_nonneg q : 0 ≤ (q:ℝ)),mul_assoc] using this
theorem measure (x : ℝ) (a b : ℕ → ℤ) {B E μ : ℝ} (hE : 0 < E) (hB : 0 ≤ B)
    (hb : ∀ᶠ n in atTop, |(b n:ℝ)| ≤ exp (B*n))
    (hf : ∀ᶠ n in atTop, |(a n:ℝ) + b n * x| ≤ exp (-E*n))
    (hw : ∀ n, 1 ≤ n → ∀ (p : ℤ) (q : ℕ), 0 < q → ∃ k < 3, (q:ℤ)*a (n+k) + p*b (n+k) ≠ 0)
    (hμ : 1 + B/E < μ) :
    ∀ᶠ q : ℕ in atTop, ∀ p : ℤ, (q:ℝ)^(-μ) ≤ |x - p/q| := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hb.and hf)
  set s := 1 + B/E
  set δ := μ - s
  have hδ : 0 < δ := by simp only [δ]; linarith
  set C := exp (B*(N+4))
  set K := 1/(2*C*(2:ℝ)^(B/E))
  have hK : 0 < K := by positivity
  have ev : ∀ᶠ q : ℕ in atTop, 1/K ≤ (q:ℝ)^δ :=
    ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [ev, eventually_ge_atTop 1] with q hqK hq1 p
  have hq0 : 0 < q := hq1
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq1
  have qpos : (0:ℝ) < q := by linarith
  set L := log (2*q)/E
  have hL : 0 ≤ L := div_nonneg (log_nonneg (by linarith)) hE.le
  obtain ⟨k, hk, hne⟩ := hw (N + 1 + ⌈L⌉₊) (by omega) p q hq0
  set m := N + 1 + ⌈L⌉₊ + k
  obtain ⟨hbm, hfm⟩ := hN m (by omega)
  have mR : (m:ℝ) = N + 1 + ⌈L⌉₊ + k := by simp [m]
  have kR : (k:ℝ) ≤ 2 := by exact_mod_cast (by omega : k ≤ 2)
  have c1 : L ≤ (⌈L⌉₊:ℝ) := Nat.le_ceil L
  have c2 : (⌈L⌉₊:ℝ) < L + 1 := Nat.ceil_lt_add_one hL
  have hfs : (q:ℝ) * |(a m:ℝ) + b m * x| ≤ 1/2 := by
    have : exp (-E*m) ≤ exp (-log (2*q)) := by
      apply exp_le_exp.2
      have : log (2*q) = E*L := by simp only [L]; field_simp
      rw [this]; nlinarith [Nat.cast_nonneg (α := ℝ) N, Nat.cast_nonneg (α := ℝ) k]
    rw [exp_neg, exp_log (by positivity)] at this
    calc (q:ℝ) * |(a m:ℝ) + b m * x| ≤ (q:ℝ) * (2*(q:ℝ))⁻¹ := by gcongr; exact hfm.trans this
      _ = 1/2 := by field_simp
  have hdet := det_bound (a m) (b m) p q x hq0 hne
  set d := |x - p/q|
  have hbd : exp (B*m) ≤ C * (2:ℝ)^(B/E) * (q:ℝ)^(B/E) := by
    have e1 : exp (B*m) ≤ exp (B*(N+4) + B*L) := by
      apply exp_le_exp.2; rw [mR]; nlinarith
    have e2 : exp (B*L) = (2*q:ℝ)^(B/E) := by
      rw [rpow_def_of_pos (by positivity)]; congr 1; simp only [L]; ring
    rw [exp_add, e2, mul_rpow (by norm_num) qpos.le] at e1
    simpa [C, mul_assoc] using e1
  have main : 1/2 ≤ (q:ℝ) * (C * (2:ℝ)^(B/E) * (q:ℝ)^(B/E)) * d := by
    have : (q:ℝ) * |(b m:ℝ)| * d ≤ (q:ℝ) * (C * (2:ℝ)^(B/E) * (q:ℝ)^(B/E)) * d := by
      gcongr; exact hbm.trans hbd
    linarith
  have hpow : (q:ℝ)^(-μ) = ((q:ℝ) * (q:ℝ)^(B/E))⁻¹ * ((q:ℝ)^δ)⁻¹ := by
    rw [← rpow_neg qpos.le, ← rpow_one_add' qpos.le (by positivity), ← rpow_neg qpos.le,
      ← rpow_add qpos]; congr 1; simp only [δ, s]; ring
  have hqd : 0 < (q:ℝ)^δ := by positivity
  have hq2 : 0 < (q:ℝ) * (q:ℝ)^(B/E) := by positivity
  rw [hpow]
  have h1 : ((q:ℝ)^δ)⁻¹ ≤ K := by
    rw [inv_le_comm₀ hqd hK]; simpa [one_div] using hqK
  calc ((q:ℝ) * (q:ℝ)^(B/E))⁻¹ * ((q:ℝ)^δ)⁻¹ ≤ ((q:ℝ) * (q:ℝ)^(B/E))⁻¹ * K := by gcongr
    _ ≤ d := by
      simp only [K]; rw [← div_eq_inv_mul, div_div, div_le_iff₀ (by positivity)]
      nlinarith
end ZZMeasure
end

section
open Filter Topology
namespace Asymptotics
variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}
variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']
theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact
theorem _root_.Filter.Eventually.natCast {f : ℝ → Prop} (hf : ∀ᶠ x in atTop, f x) :
    ∀ᶠ n : ℕ in atTop, f n :=
  tendsto_natCast_atTop_atTop.eventually hf
theorem IsBigO.natCast {f g : ℝ → E} (h : f =O[atTop] g) :
    (fun n : ℕ => f n) =O[atTop] fun n : ℕ => g n :=
  h.comp_tendsto tendsto_natCast_atTop_atTop
end Asymptotics
end

section
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
structure CS (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  h1 : ContDiff ℝ n toFun
  h2 : HasCompactSupport toFun
structure trunc extends (CS 2 ℝ) where
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ toFun
  h4 : toFun ≤ Set.indicator (Set.Ioo (-2) (2)) 1
structure W1 (n : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  toFun : ℝ → E
  smooth : ContDiff ℝ n toFun
  integrable : ∀ ⦃k⦄, k ≤ n → Integrable (iteratedDeriv k toFun)
abbrev W21 := W1 2 ℂ
section lemmas
noncomputable def funscale {E : Type*} (g : ℝ → E) (R x : ℝ) : E := g (R⁻¹ • x)
lemma contDiff_ofReal : ContDiff ℝ ∞ ofReal := by
  have key x : HasDerivAt ofReal 1 x := hasDerivAt_id x |>.ofReal_comp
  have key' : deriv ofReal = fun _ => 1 := by ext x ; exact (key x).deriv
  refine contDiff_infty_iff_deriv.mpr ⟨fun x => (key x).differentiableAt, ?_⟩
  simpa [key'] using contDiff_const
omit [NormedSpace ℝ E] in
lemma tendsto_funscale {f : ℝ → E} (hf : ContinuousAt f 0) (x : ℝ) :
    Tendsto (fun R => funscale f R x) atTop (𝓝 (f 0)) :=
  hf.tendsto.comp (by simpa using tendsto_inv_atTop_zero.mul_const x)
end lemmas
namespace CS
variable {f : CS n E} {R x v : ℝ}
instance : CoeFun (CS n E) (fun _ => ℝ → E) where coe := CS.toFun
instance : Coe (CS n ℝ) (CS n ℂ) where coe f := ⟨fun x => f x,
  contDiff_ofReal.of_le (mod_cast le_top) |>.comp f.h1, f.h2.comp_left (g := ofReal) rfl⟩
def neg (f : CS n E) : CS n E where
  toFun := -f
  h1 := f.h1.neg
  h2 := by simpa [HasCompactSupport, tsupport] using f.h2
instance : Neg (CS n E) where neg := neg
@[simp] lemma neg_apply {x : ℝ} : (-f) x = - (f x) := rfl
def smul (R : ℝ) (f : CS n E) : CS n E := ⟨R • f, f.h1.const_smul R, f.h2.smul_left⟩
instance : HSMul ℝ (CS n E) (CS n E) where hSMul := smul
@[simp] lemma smul_apply : (R • f) x = R • f x := rfl
lemma continuous (f : CS n E) : Continuous f := f.h1.continuous
noncomputable def deriv (f : CS (n + 1) E) : CS n E where
  toFun := _root_.deriv f
  h1 := (contDiff_succ_iff_deriv.mp f.h1).2.2
  h2 := f.h2.deriv
lemma hasDerivAt (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt
lemma deriv_apply {f : CS (n + 1) E} {x : ℝ} : f.deriv x = _root_.deriv f x := rfl
theorem ext_of {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : CS n E} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl
lemma deriv_smul {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  apply ext_of; funext x; exact (f.hasDerivAt x |>.const_smul R).deriv
noncomputable def scale (g : CS n E) (R : ℝ) : CS n E := by
  by_cases h : R = 0
  · exact ⟨0, contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  · refine ⟨fun x => funscale g R x, ?_, ?_⟩
    · exact g.h1.comp (contDiff_const_smul R⁻¹)
    · exact g.h2.comp_smul (inv_ne_zero h)
lemma deriv_scale {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  apply ext_of; funext v; by_cases hR : R = 0
  · simp [hR, scale, deriv]
  · simp only [scale, hR, ↓reduceDIte, smul_apply]
    exact ((f.hasDerivAt (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv
lemma deriv_scale' {f : CS (n + 1) E} :
    (f.scale R).deriv v = R⁻¹ • f.deriv (R⁻¹ • v) := by
  rw [deriv_scale, smul_apply]
  by_cases hR : R = 0 <;> simp [hR, scale, funscale]
lemma hasDerivAt_scale (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl
lemma tendsto_scale (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  apply (tendsto_funscale f.continuous.continuousAt x).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR ; simp [scale, hR]
lemma bounded : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  obtain ⟨x, hx⟩ :=
    (continuous_norm.comp f.continuous).exists_forall_ge_of_hasCompactSupport f.h2.norm
  exact ⟨_, hx⟩
end CS
namespace trunc
instance : CoeFun trunc (fun _ => ℝ → ℝ) where coe f := f.toFun
instance : Coe trunc (CS 2 ℝ) where coe := trunc.toCS
lemma nonneg (g : trunc) (x : ℝ) : 0 ≤ g x := (Set.indicator_nonneg (by simp) x).trans (g.h3 x)
lemma le_one (g : trunc) (x : ℝ) : g x ≤ 1 :=
  (g.h4 x).trans <| Set.indicator_le_self' (by simp) x
lemma zero (g : trunc) : g =ᶠ[𝓝 0] 1 := by
  have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
  exact eventually_of_mem this (fun x hx => le_antisymm (g.le_one x) (by simpa [hx] using g.h3 x))
@[simp] lemma zero_at {g : trunc} : g 0 = 1 := g.zero.eq_of_nhds
end trunc
namespace W1
instance : CoeFun (W1 n E) (fun _ => ℝ → E) where coe := W1.toFun
lemma continuous (f : W1 n E) : Continuous f := f.smooth.continuous
lemma differentiable (f : W1 (n + 1) E) : Differentiable ℝ f :=
  f.smooth.differentiable (by simp)
lemma iteratedDeriv_sub {f g : ℝ → E} (hf : ContDiff ℝ n f) (hg : ContDiff ℝ n g) :
    iteratedDeriv n (f - g) = iteratedDeriv n f - iteratedDeriv n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    have hf' : ContDiff ℝ n (deriv f) := hf.iterate_deriv' n 1
    have hg' : ContDiff ℝ n (deriv g) := hg.iterate_deriv' n 1
    have hfg : deriv (f - g) = deriv f - deriv g := by
      ext x ; apply deriv_sub
      · exact (hf.differentiable (by simp)).differentiableAt
      · exact (hg.differentiable (by simp)).differentiableAt
    simp_rw [iteratedDeriv_succ', ← ih hf' hg', hfg]
noncomputable def deriv (f : W1 (n + 1) E) : W1 n E where
  toFun := _root_.deriv f
  smooth := contDiff_succ_iff_deriv.mp f.smooth |>.2.2
  integrable k hk := by
    simpa [iteratedDeriv_succ'] using f.integrable (Nat.succ_le_succ hk)
lemma hasDerivAt (f : W1 (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
  f.differentiable.differentiableAt.hasDerivAt
def sub (f g : W1 n E) : W1 n E where
  toFun := f - g
  smooth := f.smooth.sub g.smooth
  integrable k hk := by
    have hf : ContDiff ℝ k f := f.smooth.of_le (by simp [hk])
    have hg : ContDiff ℝ k g := g.smooth.of_le (by simp [hk])
    simpa [iteratedDeriv_sub hf hg] using (f.integrable hk).sub (g.integrable hk)
instance : Sub (W1 n E) where sub := sub
lemma integrable_iteratedDeriv_Schwarz {f : 𝓢(ℝ, ℂ)} : Integrable (iteratedDeriv n f) := by
  induction n generalizing f with
  | zero => exact f.integrable
  | succ n ih => simpa [iteratedDeriv_succ'] using! ih (f := SchwartzMap.derivCLM ℝ ℂ f)
noncomputable def of_Schwartz (f : 𝓢(ℝ, ℂ)) : W1 n ℂ where
  toFun := f
  smooth := f.smooth n
  integrable _ _ := integrable_iteratedDeriv_Schwarz
end W1
namespace W21
variable {f : W21}
noncomputable def norm (f : ℝ → ℂ) : ℝ :=
    (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)
lemma norm_nonneg {f : ℝ → ℂ} : 0 ≤ norm f :=
  add_nonneg (integral_nonneg (fun t => by simp))
    (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))
noncomputable instance : Norm W21 where norm := norm ∘ W1.toFun
noncomputable instance : Coe 𝓢(ℝ, ℂ) W21 where coe := W1.of_Schwartz
def ofCS2 (f : CS 2 ℂ) : W21 := by
  refine ⟨f, f.h1, fun k hk => ?_⟩ ; match k with
  | 0 => exact f.h1.continuous.integrable_of_hasCompactSupport f.h2
  | 1 => simpa using (f.h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport f.h2.deriv
  | 2 => simpa [iteratedDeriv_succ] using
    (f.h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport f.h2.deriv.deriv
instance : Coe (CS 2 ℂ) W21 where coe := ofCS2
instance : HMul (CS 2 ℂ) W21 (CS 2 ℂ) where
  hMul g f := ⟨g * f, g.h1.mul f.smooth, g.h2.mul_right⟩
instance : HMul (CS 2 ℝ) W21 (CS 2 ℂ) where hMul g f := (g : CS 2 ℂ) * f
lemma hf (f : W21) : Integrable f := f.integrable zero_le_two
lemma hf' (f : W21) : Integrable (deriv f) := by
  simpa [iteratedDeriv_succ] using f.integrable one_le_two
lemma hf'' (f : W21) : Integrable (deriv (deriv f))  := by
  simpa [iteratedDeriv_succ] using f.integrable le_rfl
end W21
theorem W21_approximation (f : W21) (g : trunc) :
    Tendsto (fun R => ‖f - (g.scale R * f : W21)‖) atTop (𝓝 0) := by
  let f' := f.deriv
  let f'' := f'.deriv
  let g' := (g : CS 2 ℝ).deriv
  let g'' := g'.deriv
  let h R v := 1 - g.scale R v
  let h' R := - (g.scale R).deriv
  let h'' R := - (g.scale R).deriv.deriv
  have ch {R} : Continuous (fun v => (h R v : ℂ)) :=
    continuous_ofReal.comp <| continuous_const.sub (CS.continuous _)
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) := continuous_ofReal.comp (CS.continuous _)
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    convert! CS.hasDerivAt_scale (g : CS 2 ℝ) R v |>.const_sub 1 using 1
    simp [h', CS.deriv_scale', show g.deriv.toFun = deriv g.toFun from rfl]
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := ((g.scale R).deriv.hasDerivAt v).neg
  have hh1 R v : |h R v| ≤ 1 := by
    by_cases hR : R = 0 <;>
      simp only [CS.scale, funscale, smul_eq_mul, hR, ↓reduceDIte, Pi.zero_apply, sub_zero,
        abs_one, le_refl, h]
    rw [abs_le] ; constructor <;>
    linarith [g.le_one (R⁻¹ * v), g.nonneg (R⁻¹ * v)]
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul v
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0)
  · ext R ; change W21.norm _ = _ ; congr ; ext v ; simp [h, sub_mul] ; rfl
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)
  · let F R v := ‖h R v * f v‖
    have eh v : ∀ᶠ R in atTop, h R v = 0 := by
      filter_upwards [(vR v).eventually g.zero, eventually_ne_atTop 0] with R hR hR'
      simp [h, hR, CS.scale, hR', funscale, mul_comm R⁻¹]
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R
      exact (ch.mul f.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply Eventually.of_forall ; intro R
      apply Eventually.of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 f.hf.norm e4
  · let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    convert_to Tendsto (fun R ↦ ∫ (v : ℝ), F R v) atTop (𝓝 0)
    · have this R v :
        deriv (deriv (fun v => h R v * f v)) v =
          h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
        have df v : HasDerivAt f (f' v) v := f.hasDerivAt v
        have df' v : HasDerivAt f' (f'' v) v := f'.hasDerivAt v
        have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v :=
          (dh R v).ofReal_comp.mul (df v)
        have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v :=
          (dh' R v).ofReal_comp.mul (df v)
        have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v :=
          (dh R v).ofReal_comp.mul (df' v)
        have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v :=
          funext (fun v => (l3 v).deriv)
        rw [d1] ; convert! (l5.add l7).deriv using 1 ; ring
      simp_rw [this, F]
    obtain ⟨c1, mg'⟩ := g'.bounded
    obtain ⟨c2, mg''⟩ := g''.bounded
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply Eventually.of_forall ; intro R ; apply (Continuous.norm ?_).aestronglyMeasurable
      exact ((ch''.mul f.continuous).add ((continuous_const.mul ch').mul f.deriv.continuous)).add
        (ch.mul f.deriv.deriv.continuous)
    have e2 : ∀ᶠ R in atTop, ∀ᵐ (a : ℝ), ‖F R a‖ ≤ bound a := by
      have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have hR' : R ≠ 0 := by linarith
        have : 0 ≤ R := by linarith
        simp only [CS.deriv_scale, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg, abs_mul,
          abs_inv, abs_eq_self.mpr this, ge_iff_le, h']
        simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul]
        convert_to _ ≤ c1 * 1
        · simp
        · rw [mul_comm]
          apply mul_le_mul (mg' _)
            (inv_le_of_inv_le₀ (by linarith) (by simpa using hR)) (by positivity)
          exact (abs_nonneg _).trans (mg' 0)
      have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
        filter_upwards [eventually_ge_atTop 1] with R hR v
        have e1 : 0 ≤ R := by linarith
        have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le₀ (by linarith) (by simpa using hR)
        have e3 : R ≠ 0 := by linarith
        simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul, abs_neg,
          abs_mul, abs_inv, abs_eq_self.mpr e1, ge_iff_le, h'']
        convert_to _ ≤ 1 * (1 * c2)
        · simp
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        apply mul_le_mul e2 ?_ (by positivity) zero_le_one
        simp only [CS.scale, e3, ↓reduceDIte, funscale, smul_eq_mul] ; apply mg''
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply Eventually.of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp only [Complex.norm_mul,
        Complex.norm_ofNat, norm_real, norm_eq_abs] <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume :=
      (((f.hf.norm).const_mul _).add ((f.hf'.norm).const_mul _)).add f.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply Eventually.of_forall ; intro v
      have evg' : g' =ᶠ[𝓝 0] 0 := by convert! ← g.zero.deriv ; exact deriv_const' _
      have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert! ← evg'.deriv ; exact deriv_const' _
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
          filter_upwards [(vR v).eventually evg'', eventually_ne_atTop 0] with R hR hR'
          simp only [CS.deriv_scale, CS.deriv_smul, CS.neg_apply, CS.smul_apply, smul_eq_mul,
            neg_eq_zero, mul_eq_zero, inv_eq_zero, hR', false_or, h'']
          simp only [CS.scale, hR', ↓reduceDIte, funscale, smul_eq_mul, mul_comm R⁻¹]
          exact hR
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh'' v] with R hR ; simp [hR]
      · have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
          filter_upwards [(vR v).eventually evg'] with R hR
          simp [g'] at hR
          simp [h', CS.deriv_scale', mul_comm R⁻¹, hR]
        apply tendsto_nhds_of_eventually_eq
        filter_upwards [eh' v] with R hR ; simp [hR]
      · simpa [h] using! ((g.tendsto_scale v).const_sub 1).ofReal.mul tendsto_const_nhds
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4
end

section
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators
local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
section lemmas
@[simp]
theorem nnnorm_eq_of_mem_circle (z : Circle) : ‖z.val‖₊ = 1 :=
  NNReal.coe_eq_one.mp (by simp [Circle.norm_coe])
@[simp]
theorem nnnorm_circle_smul (z : Circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]
noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' :=
    ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [Circle.norm_coe, one_add_one_eq_two])⟩
@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl
theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by
    simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert! (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  change _ = ((-u : ℝ) : ℂ) * _
  simp ; ring
lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable (ae_of_all _ e.norm_coe_le_norm)
@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourier_eq, integral_neg]
@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  have : Continuous fun p : ℝ × ℝ ↦ ((innerₗ ℝ) p.1) p.2 := continuous_inner
  have := fourierIntegral_add continuous_fourierChar this hf hg
  exact congr_fun this x
@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simpa [sub_eq_add_neg, Pi.neg_def] using F_add hf hg.neg x
@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u
end lemmas
theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 (f : ℝ → ℂ) u =
      𝓕 (fun u : ℝ => (f u - (1 / (4 * π ^ 2)) * deriv^[2] f u : ℂ)) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourier_deriv f.hf' l5 f.hf'', Real.fourier_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp
@[simp] lemma deriv_ofReal : deriv ofReal = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv
lemma tendsto_intervalIntegral_zero_of_uniform_norm_bound
    {f : ℝ → ℝ → ℂ} {lo hi : ℝ} {B : ℝ → ℝ}
    (hB : Filter.Tendsto (fun T : ℝ => B T * |hi - lo|) Filter.atTop (nhds 0))
    (hf : ∀ᶠ T in Filter.atTop, ∀ x ∈ Set.uIoc lo hi, ‖f T x‖ ≤ B T) :
    Filter.Tendsto (fun T : ℝ => ∫ x in lo..hi, f T x) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [hf] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hT x hx)
lemma tendsto_const_mul_log_add_two_div_add_two_atTop (K : ℝ) :
    Filter.Tendsto (fun T : ℝ => K * (Real.log (T + 2) / (T + 2)))
      Filter.atTop (nhds 0) := by
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num : (1 : ℝ) ≠ 0))
  have hshift : Filter.Tendsto (fun T : ℝ => Real.log (T + 2) / (T + 2))
      Filter.atTop (nhds 0) := by
    have := h0.comp (tendsto_atTop_add_const_right Filter.atTop 2 tendsto_id)
    simpa [Function.comp_def] using this
  simpa using hshift.const_mul K
lemma norm_fourier_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {w : ℝ} (hw : w ≠ 0) :
    ‖𝓕 g w‖ ≤ (∫ x, ‖deriv g x‖ ∂volume) / ((2 * Real.pi) * |w|) := by
  have hmul :
      𝓕 (deriv g) w = (2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w := by
    have h := congrFun (Real.fourier_deriv hg hdiff hg') w
    simpa [smul_eq_mul, mul_assoc] using h
  have h_fourier :
      ‖𝓕 (deriv g) w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
      (deriv g) w
  have hleft :
      ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ =
        ‖(2 * Real.pi * Complex.I * (w : ℂ)) * 𝓕 g w‖ := by
    have htwopi : ‖(2 * ↑Real.pi : ℂ)‖ = 2 * Real.pi := by
      rw [norm_mul, Complex.norm_two, Complex.norm_of_nonneg Real.pi_pos.le]
    have hwc : ‖(w : ℂ)‖ = |w| := by rw [norm_real, Real.norm_eq_abs]
    rw [norm_mul, norm_mul, norm_mul, htwopi, norm_I, hwc]
    ring
  have hmain : ((2 * Real.pi) * |w|) * ‖𝓕 g w‖ ≤ ∫ x, ‖deriv g x‖ ∂volume := by
    rw [hleft, ← hmul]
    exact h_fourier
  have hpos : 0 < (2 * Real.pi) * |w| := by
    positivity
  exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmain)
lemma norm_oscillatory_integral_le_integral_deriv_div
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : 0 < T) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / T := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT.ne') (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = T := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    have hneg : -T / (2 * Real.pi) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hT) htwopi_pos
    rw [abs_of_neg hneg]
    field_simp [Real.pi_ne_zero]
  rw [hden]
lemma norm_oscillatory_integral_le_integral_deriv_div_abs
    (g : ℝ → ℂ) (hg : Integrable g) (hdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g)) {T : ℝ} (hT : T ≠ 0) :
    ‖∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume‖ ≤
      (∫ x, ‖deriv g x‖ ∂volume) / |T| := by
  have hw : -T / (2 * Real.pi) ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr hT) (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  have hfourier := norm_fourier_le_integral_deriv_div g hg hdiff hg' hw
  have heq :
      (∫ y, g y * exp ((T : ℂ) * Complex.I * (y : ℂ)) ∂volume) =
        𝓕 g (-T / (2 * Real.pi)) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with y
    rw [smul_eq_mul]
    rw [mul_comm (g y)]
    congr 1
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [heq]
  refine hfourier.trans_eq ?_
  congr 1
  have hden : (2 * Real.pi) * |-T / (2 * Real.pi)| = |T| := by
    have htwopi_pos : 0 < 2 * Real.pi := by positivity
    rw [abs_div, abs_neg, abs_of_pos htwopi_pos]
    field_simp [Real.pi_ne_zero]
  rw [hden]
end

section
namespace Function
variable {α : Type*} [Zero α]
theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp
theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id
end Function
end

section
open MeasureTheory Set Real
open scoped ContDiff
lemma smooth_urysohn_support_Ioo {a b c d : ℝ} (h1 : a < b) (h3 : c < d) :
    ∃ Ψ : ℝ → ℝ, (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
    Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 ∧
    (Function.support Ψ = Set.Ioo a d) := by
  have := exists_contMDiff_zero_iff_one_iff_of_isClosed (n := ⊤)
    (modelWithCornersSelf ℝ ℝ) (s := Set.Iic a ∪ Set.Ici d) (t := Set.Icc b c)
    (IsClosed.union isClosed_Iic isClosed_Ici) isClosed_Icc
    (by
      simp_rw [Set.disjoint_union_left, Set.disjoint_iff, Set.subset_def,
        Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
        and_imp, imp_false, not_le, Set.mem_Ici]
      constructor <;> intros <;> linarith)
  obtain ⟨Ψ, hΨSmooth, hΨrange, hΨ0, hΨ1⟩ := this
  simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_Icc] at *
  use Ψ
  simp only [range_subset_iff, mem_Icc] at hΨrange
  refine ⟨ContMDiff.contDiff hΨSmooth, ?_, ?_, ?_, ?_⟩
  · apply HasCompactSupport.of_support_subset_isCompact (K := Set.Icc a d) isCompact_Icc
    simp only [Function.support_subset_iff, ne_eq, mem_Icc, ← hΨ0, not_or]
    bound
  · apply Set.indicator_le'
    · intro x hx
      rw [hΨ1 x |>.mp, Pi.one_apply]
      simpa using hx
    · exact fun x _ ↦ (hΨrange x).1
  · intro x
    apply Set.le_indicator_apply
    · exact fun _ ↦ (hΨrange x).2
    · intro hx
      rw [← hΨ0 x |>.mp]
      simpa [-not_and, mem_Ioo, not_and_or, not_lt] using hx
  · ext x
    simp only [Function.mem_support, ne_eq, mem_Ioo, ← hΨ0, not_or, not_le]
lemma SmoothExistence :
    ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
    ν.support ⊆ Icc (1 / 2) 2 ∧ ∫ x in Ici 0, ν x / x = 1 := by
  suffices h : ∃ (ν : ℝ → ℝ), (ContDiff ℝ ∞ ν) ∧ (∀ x, 0 ≤ ν x) ∧
      ν.support ⊆ Set.Icc (1 / 2) 2 ∧ 0 < ∫ x in Set.Ici 0, ν x / x by
    obtain ⟨ν, hν, hνnonneg, hνsupp, hνpos⟩ := h
    let c := (∫ x in Ici 0, ν x / x)
    use fun y ↦ ν y / c
    refine ⟨hν.div_const c, fun y ↦ div_nonneg (hνnonneg y) (le_of_lt hνpos), ?_, ?_⟩
    · rw [Function.support_div, Function.support_const (ne_of_lt hνpos).symm, inter_univ]
      convert hνsupp
    · simp only [div_right_comm _ c _, integral_div c, div_self <| ne_of_gt hνpos, c]
  have := smooth_urysohn_support_Ioo (a := 1 / 2) (b := 1) (c := 3 / 2) (d := 2)
    (by linarith) (by linarith)
  obtain ⟨ν, hνContDiff, _, hν0, hν1, hνSupport⟩ := this
  use ν, hνContDiff
  unfold indicator at hν0 hν1
  simp only [mem_Icc, Pi.one_apply, Pi.le_def, mem_Ioo] at hν0 hν1
  simp only [hνSupport, subset_def, mem_Ioo, mem_Icc, and_imp]
  split_ands
  · exact fun x ↦ le_trans (by simp [apply_ite]) (hν0 x)
  · exact fun y hy hy' ↦ ⟨by linarith, by linarith⟩
  · rw [integral_pos_iff_support_of_nonneg]
    · simp only [Function.support_div, measurableSet_Ici, Measure.restrict_apply',
        hνSupport, Function.support_id']
      have : (Ioo (1 / 2 : ℝ) 2 ∩ {0}ᶜ ∩ Ici 0) = Ioo (1 / 2) 2 := by
        ext x
        simp only [one_div, mem_inter_iff, mem_Ioo, mem_compl_iff, mem_singleton_iff, mem_Ici]
        bound
      simp only [this, volume_Ioo, ENNReal.ofReal_pos, sub_pos, gt_iff_lt]
      linarith
    · simp_rw [Pi.le_def, Pi.zero_apply]
      intro y
      by_cases h : y ∈ Function.support ν
      · apply div_nonneg <| le_trans (by simp [apply_ite]) (hν0 y)
        rw [hνSupport, mem_Ioo] at h
        linarith [h.left]
      · simp only [Function.mem_support, ne_eq, not_not] at h
        simp [h]
    · have : (fun x ↦ ν x / x).support ⊆ Icc (1 / 2) 2 := by
        rw [Function.support_div, hνSupport]
        exact (inter_subset_left).trans Ioo_subset_Icc_self
      apply (integrableOn_iff_integrable_of_support_subset this).mp
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply hνContDiff.continuous.continuousOn.div continuousOn_id ?_
      simp only [mem_Icc, ne_eq, and_imp, id_eq]
      intros; linarith
end

section
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate
variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]
noncomputable
def nterm (f : ℕ → ℂ) (σ' : ℝ) (n : ℕ) : ℝ := if n = 0 then 0 else ‖f n‖ / n ^ σ'
lemma nterm_eq_norm_term {f : ℕ → ℂ} : nterm f σ' n = ‖term f σ' n‖ := by
  by_cases h : n = 0 <;> simp [nterm, term, h]
theorem norm_term_eq_nterm_re (s : ℂ) :
    ‖term f s n‖ = nterm f (s.re) n := by
  simp only [nterm, term, apply_ite (‖·‖), norm_zero, norm_div]
  apply ite_congr rfl (fun _ ↦ rfl)
  intro h
  congr
  refine norm_natCast_cpow_of_pos (by omega) s
lemma hf_coe1 (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hσ : 1 < σ') :
    ∑' i, (‖term f σ' i‖₊ : ENNReal) ≠ ⊤ := by
  simp_rw [ENNReal.tsum_coe_ne_top_iff_summable_coe, ← norm_toNNReal]
  norm_cast
  apply Summable.toNNReal
  convert hf σ' hσ with i
  simp [nterm_eq_norm_term]
instance instMeasurableSpace : MeasurableSpace Circle :=
  inferInstanceAs <| MeasurableSpace <| Subtype _
instance instBorelSpace : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)
lemma first_fourier_aux1 (hψ : AEMeasurable ψ) {x : ℝ} (n : ℕ) : AEMeasurable fun (u : ℝ) ↦
    (‖fourierChar (-(u * ((1 : ℝ) / ((2 : ℝ) * π) * (n / x).log))) • ψ u‖ₑ : ENNReal) := by
  fun_prop
lemma first_fourier_aux2a :
    (2 : ℂ) * π * -(y * (1 / (2 * π) * Real.log ((n) / x))) = -(y * ((n) / x).log) := by
  calc
    _ = -(y * (((2 : ℂ) * π) / (2 * π) * Real.log ((n) / x))) := by ring
    _ = _ := by rw [div_self (by norm_num), one_mul]
lemma first_fourier_aux2 (hx : 0 < x) (n : ℕ) :
    term f σ' n * 𝐞 (-(y * (1 / (2 * π) * Real.log (n / x)))) • ψ y =
    term f (σ' + y * I) n • (ψ y * x ^ (y * I)) := by
  by_cases hn : n = 0
  · simp [term, hn]
  simp only [term, hn, ↓reduceIte]
  calc
    _ = (f n * (cexp ((2 * π * -(y * (1 / (2 * π) * Real.log (n / x)))) * I) /
        ↑((n : ℝ) ^ σ'))) • ψ y := by
      rw [Circle.smul_def, fourierChar_apply, ofReal_cpow (by norm_num)]
      simp only [one_div, mul_inv_rev, mul_neg, ofReal_neg, ofReal_mul, ofReal_ofNat, ofReal_inv,
        neg_mul, smul_eq_mul, ofReal_natCast]
      ring
    _ = (f n * (x ^ (y * I) / n ^ (σ' + y * I))) • ψ y := by
      congr 2
      have l1 : 0 < (n : ℝ) := by simpa using Nat.pos_iff_ne_zero.mpr hn
      have l2 : (x : ℂ) ≠ 0 := by simp [hx.ne.symm]
      have l3 : (n : ℂ) ≠ 0 := by simp [hn]
      rw [Real.rpow_def_of_pos l1, Complex.cpow_def_of_ne_zero l2, Complex.cpow_def_of_ne_zero l3]
      push_cast
      simp_rw [← Complex.exp_sub]
      congr 1
      rw [first_fourier_aux2a, Real.log_div l1.ne.symm hx.ne.symm]
      push_cast
      rw [Complex.ofReal_log hx.le]
      ring
    _ = _ := by simp ; group
lemma first_fourier (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hsupp : Integrable ψ) (hx : 0 < x) (hσ : 1 < σ') :
    ∑' n : ℕ, term f σ' n * (𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))) =
    ∫ t : ℝ, LSeries f (σ' + t * I) * ψ t * x ^ (t * I) := by
  calc
    _ = ∑' n, term f σ' n * ∫ (v : ℝ), 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp only [Real.fourier_eq]
      simp only [one_div, mul_inv_rev, RCLike.inner_apply', conj_trivial]
    _ = ∑' n, ∫ (v : ℝ), term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      simp [integral_const_mul]
    _ = ∫ (v : ℝ), ∑' n, term f σ' n * 𝐞 (-(v * ((1 : ℝ) /
        ((2 : ℝ) * π) * Real.log (n / x)))) • ψ v := by
      refine (integral_tsum ?_ ?_).symm
      · refine fun _ ↦ AEMeasurable.aestronglyMeasurable ?_
        have := hsupp.aemeasurable
        fun_prop
      · simp only [enorm_mul]
        simp_rw [lintegral_const_mul'' _ (first_fourier_aux1 hsupp.aemeasurable _)]
        calc
          _ = (∑' (i : ℕ), ‖term f σ' i‖ₑ) * ∫⁻ (a : ℝ), ‖ψ a‖ₑ ∂volume := by
            simp [ENNReal.tsum_mul_right, enorm_eq_nnnorm]
          _ ≠ ⊤ := ENNReal.mul_ne_top (hf_coe1 hf hσ)
            (ne_top_of_lt hsupp.2)
    _ = _ := by
      congr 1; ext y
      simp_rw [mul_assoc (LSeries _ _), ← smul_eq_mul (a := (LSeries _ _)), LSeries]
      rw [← Summable.tsum_smul_const]
      · simp_rw [first_fourier_aux2 hx]
      · apply Summable.of_norm
        convert hf σ' hσ with n
        rw [norm_term_eq_nterm_re]
        simp
lemma continuous_multiplicative_ofAdd : Continuous (⇑Multiplicative.ofAdd : ℝ → ℝ) := ⟨fun _ ↦ id⟩
lemma second_fourier_integrable_aux1a (hσ : 1 < σ') :
    IntegrableOn (fun (x : ℝ) ↦ cexp (-((x : ℂ) * ((σ' : ℂ) - 1)))) (Ici (-Real.log x)) := by
  norm_cast
  suffices IntegrableOn (fun (x : ℝ) ↦ (rexp (-(x * (σ' - 1))))) (Ici (-x.log)) _ from this.ofReal
  simp_rw [fun (a x : ℝ) ↦ (by ring : -(x * a) = -a * x)]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply exp_neg_integrableOn_Ioi
  linarith
lemma second_fourier_integrable_aux1 (hcont : Measurable ψ) (hsupp : Integrable ψ) (hσ : 1 < σ') :
    let ν : Measure (ℝ × ℝ) := (volume.restrict (Ici (-Real.log x))).prod volume
    Integrable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
    (𝐞 (Multiplicative.ofAdd (-(a * (u / (2 * π))))) : ℂ) • ψ a) ν := by
  intro ν
  constructor
  · apply Measurable.aestronglyMeasurable
    change Measurable (Function.uncurry fun (u : ℝ) (a : ℝ) ↦ ((rexp (-u * (σ' - 1))) : ℂ) •
      (𝐞 (-(a * (u / (2 * π)))) : ℂ) • ψ a)
    simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, smul_eq_mul]
    fun_prop
  · let f1 : ℝ → ENNReal := fun a1 ↦ ‖cexp (-(↑a1 * (↑σ' - 1)))‖ₑ
    let f2 : ℝ → ENNReal := fun a2 ↦ ‖ψ a2‖ₑ
    suffices ∫⁻ (a : ℝ × ℝ), f1 a.1 * f2 a.2 ∂ν < ⊤ by
      simpa [hasFiniteIntegral_iff_enorm, enorm_eq_nnnorm, Function.uncurry]
    refine (lintegral_prod_mul ?_ ?_).trans_lt ?_ <;> try fun_prop
    exact ENNReal.mul_lt_top (second_fourier_integrable_aux1a hσ).2 hsupp.2
lemma second_fourier_integrable_aux2 (hσ : 1 < σ') :
    IntegrableOn (fun (u : ℝ) ↦ cexp ((1 - ↑σ' - ↑t * I) * ↑u)) (Ioi (-Real.log x)) := by
  refine (integrable_norm_iff (Measurable.aestronglyMeasurable <| by fun_prop)).mp ?_
  suffices IntegrableOn (fun a ↦ rexp (-(σ' - 1) * a)) (Ioi (-x.log)) _ by simpa [Complex.norm_exp]
  apply exp_neg_integrableOn_Ioi
  linarith
lemma second_fourier_aux (hx : 0 < x) :
    -(cexp (-((1 - ↑σ' - ↑t * I) * ↑(Real.log x))) / (1 - ↑σ' - ↑t * I)) =
    ↑(x ^ (σ' - 1)) * (↑σ' + ↑t * I - 1)⁻¹ * ↑x ^ (↑t * I) := by
  calc
    _ = cexp (↑(Real.log x) * ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [← div_neg]; ring_nf
    _ = (x ^ ((↑σ' - 1) + ↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt hx)), Complex.ofReal_log hx.le]
    _ = (x ^ ((σ' : ℂ) - 1)) * (x ^ (↑t * I)) * (↑σ' + ↑t * I - 1)⁻¹ := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hx))]
    _ = _ := by rw [ofReal_cpow hx.le]; push_cast; ring
lemma second_fourier (hcont : Measurable ψ) (hsupp : Integrable ψ)
    {x σ' : ℝ} (hx : 0 < x) (hσ : 1 < σ') :
    ∫ u in Ici (-log x), Real.exp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
    (x^(σ' - 1) : ℝ) * ∫ t, (1 / (σ' + t * I - 1)) * ψ t * x^(t * I) ∂ volume := by
  conv in ↑(rexp _) * _ => { rw [Real.fourier_real_eq, ← smul_eq_mul, ← integral_smul] }
  rw [MeasureTheory.integral_integral_swap]
  swap
  · exact second_fourier_integrable_aux1 hcont hsupp hσ
  rw [← integral_const_mul]
  congr 1; ext t
  dsimp [Real.fourierChar, Circle.exp]
  simp_rw [mul_smul_comm, ← smul_mul_assoc, integral_mul_const]
  rw [fun (a b d : ℂ) ↦ show a * (b * (ψ t) * d) = (a * b * d) * ψ t by ring]
  congr 1
  conv =>
    lhs
    enter [2]
    ext a
    change cexp (↑(2 * π * (-(t * (a / (2 * π))))) * I) * ↑(rexp (-a * (σ' - 1)))
  push_cast
  simp_rw [← Complex.exp_add]
  have (u : ℝ) :
      2 * ↑π * -(↑t * (↑u / (2 * ↑π))) * I + -↑u * (↑σ' - 1) = (1 - σ' - t * I) * u := calc
    _ = -↑u * (↑σ' - 1) + (2 * ↑π) / (2 * ↑π) * -(↑t * ↑u) * I := by ring
    _ = -↑u * (↑σ' - 1) + 1 * -(↑t * ↑u) * I := by rw [div_self (by norm_num)]
    _ = _ := by ring
  simp_rw [this]
  let c : ℂ := (1 - ↑σ' - ↑t * I)
  have : c ≠ 0 := by simp [Complex.ext_iff, c, sub_ne_zero.mpr hσ.ne]
  let f' (u : ℝ) := cexp (c * u)
  let f := fun (u : ℝ) ↦ (f' u) / c
  have hderiv : ∀ u ∈ Ici (-Real.log x), HasDerivAt f (f' u) u := by
    intro u _
    rw [show f' u = cexp (c * u) * (c * 1) / c by simp only [f']; field_simp]
    exact (hasDerivAt_id' u).ofReal_comp.const_mul c |>.cexp.div_const c
  have hf : Tendsto f atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    suffices Tendsto (fun (x : ℝ) ↦ ‖cexp (c * ↑x)‖ / ‖c‖) atTop (𝓝 (0 / ‖c‖)) by
      simpa [f, f'] using this
    apply Filter.Tendsto.div_const
    suffices Tendsto (· * (1 - σ')) atTop atBot by simpa [Complex.norm_exp, mul_comm (1 - σ'), c]
    exact Tendsto.atTop_mul_const_of_neg (by linarith) fun ⦃s⦄ h ↦ h
  rw [integral_Ici_eq_integral_Ioi,
    integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (second_fourier_integrable_aux2 hσ) hf]
  simpa [f, f'] using second_fourier_aux hx
lemma one_add_sq_pos (u : ℝ) : 0 < 1 + u ^ 2 := zero_lt_one.trans_le (by simpa using sq_nonneg u)
theorem prelim_decay (ψ : ℝ → ℂ) (u : ℝ) : ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ ∫ t, ‖ψ t‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm ..
lemma decay_bounds_key (f : W21) (u : ℝ) : ‖𝓕 (f : ℝ → ℂ) u‖ ≤ ‖f‖ * (1 + u ^ 2)⁻¹ := by
  have l1 : 0 < 1 + u ^ 2 := one_add_sq_pos _
  have l2 : 1 + u ^ 2 = ‖(1 : ℂ) + u ^ 2‖ := by
    norm_cast ; simp only [Real.norm_eq_abs, abs_eq_self.2 l1.le]
  have l3 : ‖1 / ((4 : ℂ) * ↑π ^ 2)‖ ≤ (4 * π ^ 2)⁻¹ := by simp
  have key := fourierIntegral_self_add_deriv_deriv f u
  simp only [Function.iterate_succ _ 1, Function.iterate_one, Function.comp_apply] at key
  rw [F_sub f.hf (f.hf''.const_mul (1 / (4 * ↑π ^ 2)))] at key
  rw [← div_eq_mul_inv, le_div_iff₀ l1, mul_comm, l2, ← norm_mul, key, sub_eq_add_neg]
  apply norm_add_le _ _ |>.trans
  change _ ≤ W21.norm _
  rw [norm_neg, F_mul, norm_mul, W21.norm]
  gcongr <;> apply VectorFourier.norm_fourierIntegral_le_integral_norm
lemma decay_bounds_aux {f : ℝ → ℂ} (hf : AEStronglyMeasurable f volume)
    (h : ∀ t, ‖f t‖ ≤ A * (1 + t ^ 2)⁻¹) :
    ∫ t, ‖f t‖ ≤ π * A := by
  have l1 : Integrable (fun x ↦ A * (1 + x ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul A
  simp_rw [← integral_univ_inv_one_add_sq, mul_comm, ← integral_const_mul]
  exact integral_mono (l1.mono' hf (Eventually.of_forall h)).norm l1 h
theorem decay_bounds_W21 (f : W21) (hA : ∀ t, ‖f t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv (deriv f) t‖ ≤ A / (1 + t ^ 2)) (u) :
    ‖𝓕 (f : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  have l0 : 1 * (4 * π)⁻¹ * A = (4 * π ^ 2)⁻¹ * (π * A) := by field_simp
  have l1 : ∫ (v : ℝ), ‖f v‖ ≤ π * A := by
    apply decay_bounds_aux f.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA
  have l2 : ∫ (v : ℝ), ‖deriv (deriv f) v‖ ≤ π * A := by
    apply decay_bounds_aux f.deriv.deriv.continuous.aestronglyMeasurable
    simp_rw [← div_eq_mul_inv] ; exact hA'
  apply decay_bounds_key f u |>.trans
  change W21.norm _ * _ ≤ _
  simp_rw [W21.norm, div_eq_mul_inv, add_mul, l0] ; gcongr
lemma decay_bounds (ψ : CS 2 ℂ) (hA : ∀ t, ‖ψ t‖ ≤ A / (1 + t ^ 2))
    (hA' : ∀ t, ‖deriv^[2] ψ t‖ ≤ A / (1 + t ^ 2)) :
    ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ (π + 1 / (4 * π)) * A / (1 + u ^ 2) := by
  exact decay_bounds_W21 ψ hA hA' u
lemma decay_bounds_cor_aux (ψ : CS 2 ℂ) : ∃ C : ℝ, ∀ u, ‖ψ u‖ ≤ C / (1 + u ^ 2) := by
  have l1 : HasCompactSupport (fun u : ℝ => ((1 + u ^ 2) : ℝ) * ψ u) := by exact ψ.h2.mul_left
  have := ψ.h1.continuous
  obtain ⟨C, hC⟩ := l1.exists_bound_of_continuous (by fun_prop)
  refine ⟨C, fun u => ?_⟩
  specialize hC u
  simp only [norm_mul, Complex.norm_real, norm_of_nonneg (one_add_sq_pos u).le] at hC
  rwa [le_div_iff₀' (one_add_sq_pos _)]
lemma decay_bounds_cor (ψ : W21) :
    ∃ C : ℝ, ∀ u, ‖𝓕 (ψ : ℝ → ℂ) u‖ ≤ C / (1 + u ^ 2) := by
  simpa only [div_eq_mul_inv] using ⟨_, decay_bounds_key ψ⟩
lemma continuous_FourierIntegral (ψ : W21) : Continuous (𝓕 (ψ : ℝ → ℂ)) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar
    (by simp only [innerₗ_apply_apply, RCLike.inner_apply', conj_trivial, continuous_mul])
    ψ.hf
lemma W21.integrable_fourier (ψ : W21) (hc : c ≠ 0) :
    Integrable fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c) := by
  have l1 (C) : Integrable (fun u ↦ C / (1 + (u / c) ^ 2)) volume := by
    simpa using! (integrable_inv_one_add_sq.comp_div hc).const_mul C
  have l2 : AEStronglyMeasurable (fun u ↦ 𝓕 (ψ : ℝ → ℂ) (u / c)) volume := by
    apply Continuous.aestronglyMeasurable ; first | fun_prop | exact (continuous_FourierIntegral ψ).comp (by fun_prop) | exact ((continuous_FourierIntegral ψ).comp (by fun_prop)).norm
  obtain ⟨C, h⟩ := decay_bounds_cor ψ
  apply @Integrable.mono' ℝ ℂ _ volume _ _ (fun u => C / (1 + (u / c) ^ 2)) (l1 C) l2 ?_
  apply Eventually.of_forall (fun x => h _)
lemma continuous_LSeries_aux (hf : Summable (nterm f σ')) :
    Continuous fun x : ℝ => LSeries f (σ' + x * I) := by
  have l1 i : Continuous fun x : ℝ ↦ term f (σ' + x * I) i := by
    by_cases h : i = 0
    · simpa [h] using continuous_const
    · simpa [h] using! continuous_const.div (continuous_const.cpow (by fun_prop) (by simp [h]))
        (fun x => by simp [h])
  have l2 n (x : ℝ) : ‖term f (σ' + x * I) n‖ = nterm f σ' n := by
    by_cases h : n = 0
    · simp [h, nterm]
    · simp [h, nterm, cpow_add _ _ (Nat.cast_ne_zero.mpr h),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero h)]
  exact continuous_tsum l1 hf (fun n x => le_of_eq (l2 n x))
lemma limiting_fourier_aux (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) (σ' : ℝ)
    (hσ' : 1 < σ') :
    ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
    A * (x ^ (1 - σ') : ℝ) * ∫ u in Ici (- log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ)
      (u / (2 * π)) = ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I) := by
  have hint : Integrable ψ := ψ.h1.continuous.integrable_of_hasCompactSupport ψ.h2
  have l3 : 0 < x := zero_lt_one.trans_le hx
  have l1 (σ') (hσ' : 1 < σ') := first_fourier hf hint l3 hσ'
  have l2 (σ') (hσ' : 1 < σ') := second_fourier ψ.h1.continuous.measurable hint l3 hσ'
  have l8 : Continuous fun t : ℝ ↦ (x : ℂ) ^ (t * I) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [l3])
  have l6 : Continuous fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    apply ((continuous_LSeries_aux (hf _ hσ')).mul ψ.h1.continuous).mul l8
  have l4 : Integrable fun t : ℝ ↦ LSeries f (↑σ' + ↑t * I) * ψ t * ↑x ^ (↑t * I) := by
    exact l6.integrable_of_hasCompactSupport ψ.h2.mul_left.mul_right
  have e2 (u : ℝ) : σ' + u * I - 1 ≠ 0 := by
    intro h ; have := congr_arg Complex.re h ; simp at this ; linarith
  have l7 : Continuous fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    simp only [one_div, ← mul_assoc]
    refine ((continuous_const.mul <| Continuous.inv₀ ?_ e2).mul ψ.h1.continuous).mul l8
    fun_prop
  have l5 : Integrable fun a ↦ A * ↑(x ^ (1 - σ')) * (↑(x ^ (σ' - 1)) *
      (1 / (σ' + a * I - 1) * ψ a * x ^ (a * I))) := by
    apply l7.integrable_of_hasCompactSupport
    exact ψ.h2.mul_left.mul_right.mul_left.mul_left
  simp_rw [l1 σ' hσ', l2 σ' hσ', ← integral_const_mul, ← integral_sub l4 l5]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro u
  have e1 : 1 < ((σ' : ℂ) + (u : ℂ) * I).re := by simp [hσ']
  simp_rw [hG' e1, sub_mul, ← mul_assoc]
  simp only [one_div, sub_right_inj, mul_eq_mul_right_iff, cpow_eq_zero_iff, ofReal_eq_zero, ne_eq,
    mul_eq_zero, I_ne_zero, or_false]
  left ; left
  field_simp [e2]
  norm_cast
  simp [mul_assoc, ← rpow_add l3]
section nabla
variable {α E : Type*} [OfNat α 1] [Add α] [Sub α] {u : α → ℂ}
def cumsum [AddCommMonoid E] (u : ℕ → E) (n : ℕ) : E := ∑ i ∈ Finset.range n, u i
def nabla [Sub E] (u : α → E) (n : α) : E := u (n + 1) - u n
def nnabla [Sub E] (u : α → E) (n : α) : E := u n - u (n + 1)
def shift (u : α → E) (n : α) : E := u (n + 1)
@[simp] lemma cumsum_zero [AddCommMonoid E] {u : ℕ → E} : cumsum u 0 = 0 := by simp [cumsum]
lemma cumsum_succ [AddCommMonoid E] {u : ℕ → E} (n : ℕ) :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.sum_range_succ]
@[simp] lemma nabla_cumsum [AddCommGroup E] {u : ℕ → E} : nabla (cumsum u) = u := by
  ext n ; simp [nabla, cumsum, Finset.range_add_one]
lemma neg_cumsum [AddCommGroup E] {u : ℕ → E} : -(cumsum u) = cumsum (-u) :=
  funext (fun n => by simp [cumsum])
lemma cumsum_nonneg {u : ℕ → ℝ} (hu : 0 ≤ u) : 0 ≤ cumsum u :=
  fun _ => Finset.sum_nonneg (fun i _ => hu i)
omit [Sub α] in
lemma neg_nabla [Ring E] {u : α → E} : -(nabla u) = nnabla u := by ext n ; simp [nabla, nnabla]
omit [Sub α] in
@[simp] lemma nabla_mul [Ring E] {u : α → E} {c : E} : nabla (fun n => c * u n) = c • nabla u := by
  ext n ; simp [nabla, mul_sub]
omit [Sub α] in
@[simp] lemma nnabla_mul [Ring E] {u : α → E} {c : E} :
    nnabla (fun n => c * u n) = c • nnabla u := by
  ext n ; simp [nnabla, mul_sub]
lemma nnabla_cast (u : ℝ → E) [Sub E] : nnabla u ∘ ((↑) : ℕ → ℝ) = nnabla (u ∘ (↑)) := by
  ext n ; simp [nnabla]
end nabla
lemma Finset.sum_shift_front {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = u 0 + cumsum (shift u) n := by
  simp_rw [add_comm n, cumsum, sum_range_add, sum_range_one, add_comm 1] ; rfl
lemma Finset.sum_shift_front' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = (fun _ => u 0) + cumsum (shift u) := by
  ext n ; apply Finset.sum_shift_front
lemma Finset.sum_shift_back {E : Type*} [Ring E] {u : ℕ → E} {n : ℕ} :
    cumsum u (n + 1) = cumsum u n + u n := by
  simp [cumsum, Finset.range_add_one, add_comm]
lemma Finset.sum_shift_back' {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = cumsum u + u := by
  ext n ; apply Finset.sum_shift_back
lemma summation_by_parts {E : Type*} [Ring E] {a A b : ℕ → E} (ha : a = nabla A) {n : ℕ} :
    cumsum (a * b) (n + 1) = A (n + 1) * b n - A 0 * b 0 -
    cumsum (shift A * fun i => (b (i + 1) - b i)) n := by
  have l1 : ∑ x ∈ Finset.range (n + 1), A (x + 1) * b x = ∑ x ∈ Finset.range n,
      A (x + 1) * b x + A (n + 1) * b n :=
    Finset.sum_shift_back
  have l2 : ∑ x ∈ Finset.range (n + 1), A x * b x = A 0 * b 0 + ∑ x ∈ Finset.range n,
      A (x + 1) * b (x + 1) :=
    Finset.sum_shift_front
  simp only [cumsum, ha, Pi.mul_apply, nabla, sub_mul, Finset.sum_sub_distrib, l1, l2, shift,
    mul_sub]
  abel
lemma summation_by_parts' {E : Type*} [Ring E] {a b : ℕ → E} {n : ℕ} :
    cumsum (a * b) (n + 1) = cumsum a (n + 1) * b n - cumsum (shift (cumsum a) * nabla b) n := by
  simpa using! summation_by_parts (a := a) (b := b) (A := cumsum a) (by simp)
lemma summation_by_parts'' {E : Type*} [Ring E] {a b : ℕ → E} :
    shift (cumsum (a * b)) = shift (cumsum a) * b - cumsum (shift (cumsum a) * nabla b) := by
  ext n ; apply summation_by_parts'
lemma summable_iff_bounded {u : ℕ → ℝ} (hu : 0 ≤ u) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  have l1 : (cumsum u =O[atTop] 1) ↔ _ := isBigO_one_nat_atTop_iff
  have l2 n : ‖cumsum u n‖ = cumsum u n := by simpa using cumsum_nonneg hu n
  simp only [BoundedAtFilter, l1, l2]
  constructor <;> intro ⟨C, h1⟩
  · exact ⟨C, fun n => sum_le_hasSum _ (fun i _ => hu i) h1⟩
  · exact summable_of_sum_range_le hu h1
lemma Filter.EventuallyEq.summable {u v : ℕ → ℝ} (h : u =ᶠ[atTop] v) (hu : Summable v) :
    Summable u :=
  summable_of_isBigO_nat hu h.isBigO
lemma summable_congr_ae {u v : ℕ → ℝ} (huv : u =ᶠ[atTop] v) : Summable u ↔ Summable v := by
  constructor <;> intro h <;> simp [huv.summable, huv.symm.summable, h]
lemma BoundedAtFilter.add_const {u : ℕ → ℝ} {c : ℝ} :
    BoundedAtFilter atTop (fun n => u n + c) ↔ BoundedAtFilter atTop u := by
  have : u = fun n => (u n + c) + (-c) := by ext n ; ring
  simp only [BoundedAtFilter]
  constructor <;> intro h
  on_goal 1 => rw [this]
  all_goals { exact h.add (const_boundedAtFilter _ _) }
lemma BoundedAtFilter.comp_add {u : ℕ → ℝ} {N : ℕ} :
    BoundedAtFilter atTop (fun n => u (n + N)) ↔ BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, norm_eq_abs, Pi.one_apply,
    eventually_atTop]
  constructor <;> intro ⟨C, n₀, h⟩ <;> use C
  · refine ⟨n₀ + N, fun n hn => ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' (m := N) (n := n) (by grind)
    exact h _ <| Nat.add_le_add_iff_right.mp hn
  · exact ⟨n₀, fun n hn => h _ (by grind)⟩
lemma summable_iff_bounded' {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 ≤ u n) :
    Summable u ↔ BoundedAtFilter atTop (cumsum u) := by
  obtain ⟨N, hu⟩ := eventually_atTop.mp hu
  have e2 : cumsum (fun i ↦ u (i + N)) = fun n => cumsum u (n + N) - cumsum u N := by
    ext n ; simp_rw [cumsum, add_comm _ N, Finset.sum_range_add] ; ring
  rw [← summable_nat_add_iff N, summable_iff_bounded (fun n => hu _ <| Nat.le_add_left N n), e2]
  simp_rw [sub_eq_add_neg, BoundedAtFilter.add_const, BoundedAtFilter.comp_add]
lemma bounded_of_shift {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  simp only [BoundedAtFilter, isBigO_iff, eventually_atTop] at h ⊢
  obtain ⟨C, N, hC⟩ := h
  refine ⟨C, N + 1, fun n hn => ?_⟩
  simp only [shift] at hC
  have r1 : n - 1 ≥ N := Nat.le_sub_one_of_lt hn
  have r2 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simpa [r2] using hC (n - 1) r1
lemma dirichlet_test' {a b : ℕ → ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAb : BoundedAtFilter atTop (shift (cumsum a) * b)) (hbb : ∀ᶠ n in atTop, b (n + 1) ≤ b n)
    (h : Summable (shift (cumsum a) * nnabla b)) : Summable (a * b) := by
  have l1 : ∀ᶠ n in atTop, 0 ≤ (shift (cumsum a) * nnabla b) n := by
    filter_upwards [hbb] with n hb
    exact mul_nonneg (by simpa [shift] using! Finset.sum_nonneg' ha) (sub_nonneg.mpr hb)
  rw [summable_iff_bounded (mul_nonneg ha hb)]
  rw [summable_iff_bounded' l1] at h
  apply bounded_of_shift
  simpa only [summation_by_parts'', sub_eq_add_neg, neg_cumsum, ← mul_neg, neg_nabla]
    using hAb.add h
lemma exists_antitone_of_eventually {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, u (n + 1) ≤ u n) :
    ∃ v : ℕ → ℝ, range v ⊆ range u ∧ Antitone v ∧ v =ᶠ[atTop] u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hu
  let v (n : ℕ) := u (if n < N then N else n)
  refine ⟨v, ?_, ?_, ?_⟩
  · exact fun x ⟨n, hn⟩ => ⟨if n < N then N else n, hn⟩
  · refine antitone_nat_of_succ_le (fun n => ?_)
    by_cases h : n < N
    · by_cases h' : n + 1 < N <;> simp [v, h, h']
      have : n + 1 = N := by linarith
      simp [this]
    · have : ¬(n + 1 < N) := by linarith
      simp only [this, ↓reduceIte, h, ge_iff_le, v] ; apply hN ; linarith
  · have : ∀ᶠ n in atTop, ¬(n < N) := by simpa using ⟨N, fun b hb => by linarith⟩
    filter_upwards [this] with n hn ; simp [v, hn]
lemma summable_inv_mul_log_sq : Summable (fun n : ℕ => (n * (Real.log n) ^ 2)⁻¹) := by
  let u (n : ℕ) := (n * (Real.log n) ^ 2)⁻¹
  have l7 : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
    tendsto_atTop.mp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop) 1
  have l8 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have l9 : ∀ᶠ n in atTop, u (n + 1) ≤ u n := by
    filter_upwards [l7, l8] with n l2 l8; dsimp [u]; gcongr <;> simp
  obtain ⟨v, l1, l2, l3⟩ := exists_antitone_of_eventually l9
  rw [summable_congr_ae l3.symm]
  have l4 (n : ℕ) : 0 ≤ v n := by obtain ⟨k, hk⟩ := l1 ⟨n, rfl⟩ ; rw [← hk] ; positivity
  apply (summable_condensed_iff_of_nonneg l4 (fun _ _ _ a ↦ l2 a)).mp
  suffices this : ∀ᶠ k : ℕ in atTop, 2 ^ k * v (2 ^ k) = ((k : ℝ) ^ 2)⁻¹ * ((Real.log 2) ^ 2)⁻¹ by
    exact (summable_congr_ae this).mpr <| (Real.summable_nat_pow_inv.mpr one_lt_two).mul_right _
  have l5 : ∀ᶠ k in atTop, v (2 ^ k) = u (2 ^ k) :=
    l3.comp_tendsto <| tendsto_pow_atTop_atTop_of_one_lt Nat.le.refl
  filter_upwards [l5, l8] with k l5 l8
  simp only [l5, mul_inv_rev, Nat.cast_pow, Nat.cast_ofNat, log_pow, u]
  field_simp
lemma tendsto_mul_add_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x => a * x + b) atTop atTop :=
  tendsto_atTop_add_const_right _ b (tendsto_id.const_mul_atTop ha)
lemma isLittleO_const_of_tendsto_atTop {α : Type*} [Preorder α] (a : ℝ) {f : α → ℝ}
    (hf : Tendsto f atTop atTop) : (fun _ => a) =o[atTop] f := by
  simp [tendsto_norm_atTop_atTop.comp hf]
lemma isBigO_pow_pow_of_le {m n : ℕ} (h : m ≤ n) :
    (fun x : ℝ => x ^ m) =O[atTop] (fun x : ℝ => x ^ n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop 1] with x l1
  simpa [abs_eq_self.mpr (zero_le_one.trans l1)] using pow_le_pow_right₀ l1 h
lemma isLittleO_mul_add_sq (a b : ℝ) : (fun x => a * x + b) =o[atTop] (fun x => x ^ 2) := by
  apply IsLittleO.add
  · apply IsLittleO.const_mul_left ; simpa using isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) one_lt_two
  · apply isLittleO_const_of_tendsto_atTop _ <| tendsto_pow_atTop (by linarith)
lemma log_mul_add_isBigO_log {a : ℝ} (ha : 0 < a) (b : ℝ) :
    (fun x => Real.log (a * x + b)) =O[atTop] Real.log := by
  apply IsBigO.of_bound (2 : ℕ)
  have l2 : ∀ᶠ x : ℝ in atTop, 0 ≤ log x := tendsto_atTop.mp tendsto_log_atTop 0
  have l3 : ∀ᶠ x : ℝ in atTop, 0 ≤ log (a * x + b) :=
    tendsto_atTop.mp (tendsto_log_atTop.comp (tendsto_mul_add_atTop ha b)) 0
  have l5 : ∀ᶠ x : ℝ in atTop, 1 ≤ a * x + b := tendsto_atTop.mp (tendsto_mul_add_atTop ha b) 1
  have l1 : ∀ᶠ x : ℝ in atTop, a * x + b ≤ x ^ 2 := by
    filter_upwards [(isLittleO_mul_add_sq a b).eventuallyLE, l5] with x r2 l5
    simpa [abs_eq_self.mpr (zero_le_one.trans l5)] using r2
  filter_upwards [l1, l2, l3, l5] with x l1 l2 l3 l5
  simpa [abs_eq_self.mpr l2, abs_eq_self.mpr l3, Real.log_pow] using
    Real.log_le_log (by linarith) l1
lemma isBigO_log_mul_add {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.log =O[atTop] (fun x => Real.log (a * x + b)) := by
  convert! (log_mul_add_isBigO_log (b := -b / a) (inv_pos.mpr ha)).comp_tendsto
    (tendsto_mul_add_atTop (b := b) ha) using 1
  ext x
  simp only [Function.comp_apply]
  congr
  field_simp
  simp
lemma log_isbigo_log_div {d : ℝ} (hb : 0 < d) :
    (fun n ↦ Real.log n) =O[atTop] (fun n ↦ Real.log (n / d)) := by
  convert isBigO_log_mul_add (inv_pos.mpr hb) 0 using 1; simp only [add_zero]; field_simp
lemma Asymptotics.IsBigO.add_isLittleO_right {f g : ℝ → ℝ} (h : g =o[atTop] f) :
    f =O[atTop] (f + g) := by
  rw [isLittleO_iff] at h ; specialize h (c := 2⁻¹) (by norm_num)
  rw [isBigO_iff'']
  refine ⟨2⁻¹, by norm_num, ?_⟩
  filter_upwards [h] with x h
  simp only [norm_eq_abs, Pi.add_apply] at h ⊢
  calc _ = |f x| - 2⁻¹ * |f x| := by ring
       _ ≤ |f x| - |g x| := by linarith
       _ ≤ |(|f x| - |g x|)| := le_abs_self _
       _ ≤ _ := by rw [← sub_neg_eq_add, ← abs_neg (g x)] ; exact abs_abs_sub_abs_le (f x) (-g x)
lemma Asymptotics.IsBigO.sq {α : Type*} [Preorder α] {f g : α → ℝ} (h : f =O[atTop] g) :
    (fun n ↦ f n ^ 2) =O[atTop] (fun n => g n ^ 2) := by
  simpa [pow_two] using h.mul h
lemma log_sq_isbigo_mul {a b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log x ^ 2) =O[atTop] (fun x ↦ a + Real.log (x / b) ^ 2) := by
  apply (log_isbigo_log_div hb).sq.trans ; simp_rw [add_comm a]
  refine IsBigO.add_isLittleO_right <| isLittleO_const_of_tendsto_atTop _ ?_
  exact (tendsto_pow_atTop two_ne_zero).comp <|
    tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb
theorem log_add_div_isBigO_log (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x ↦ Real.log ((x + a) / b)) =O[atTop] fun x ↦ Real.log x := by
  convert log_mul_add_isBigO_log (inv_pos.mpr hb) (a / b) using 3 ; ring
lemma log_add_one_sub_log_le {x : ℝ} (hx : 0 < x) : nabla Real.log x ≤ x⁻¹ := by
  have l1 : ContinuousOn Real.log (Icc x (x + 1)) := by
    apply continuousOn_log.mono ; intro t ⟨h1, _⟩ ; simp ; linarith
  have l2 t (ht : t ∈ Ioo x (x + 1)) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  obtain ⟨t, ⟨ht1, _⟩, htx⟩ := exists_hasDerivAt_eq_slope Real.log (·⁻¹) (by linarith) l1 l2
  simp only [add_sub_cancel_left, div_one] at htx
  rw [nabla, ← htx, inv_le_inv₀ (by linarith) hx]
  exact ht1.le
lemma nabla_log_main : nabla Real.log =O[atTop] fun x ↦ 1 / x := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_gt_atTop 0] with x l1
  have l2 : log x ≤ log (x + 1) := log_le_log l1 (by linarith)
  simpa [nabla, abs_eq_self.mpr l1.le, abs_eq_self.mpr (sub_nonneg.mpr l2)] using
    log_add_one_sub_log_le l1
lemma nabla_log {b : ℝ} (hb : 0 < b) :
    nabla (fun x => Real.log (x / b)) =O[atTop] (fun x => 1 / x) := by
  refine EventuallyEq.trans_isBigO ?_ nabla_log_main
  filter_upwards [eventually_gt_atTop 0] with x l2
  rw [nabla, log_div (by linarith) (by linarith), log_div l2.ne.symm (by linarith), nabla] ; ring
lemma nnabla_mul_log_sq (a : ℝ) {b : ℝ} (hb : 0 < b) :
    nabla (fun x => x * (a + Real.log (x / b) ^ 2)) =O[atTop] (fun x => Real.log x ^ 2) := by
  have l1 : nabla (fun n => n * (a + Real.log (n / b) ^ 2)) = fun n =>
      a + Real.log ((n + 1) / b) ^ 2 +
        (n * (Real.log ((n + 1) / b) ^ 2 - Real.log (n / b) ^ 2)) := by
    ext n ; simp [nabla] ; ring
  have l2 := (isLittleO_const_of_tendsto_atTop a
    ((tendsto_pow_atTop two_ne_zero).comp tendsto_log_atTop)).isBigO
  have l3 := (log_add_div_isBigO_log 1 hb).sq
  have l4 : (fun x => Real.log ((x + 1) / b) + Real.log (x / b)) =O[atTop] Real.log := by
    simpa using (log_add_div_isBigO_log _ hb).add (log_add_div_isBigO_log 0 hb)
  have e2 : (fun x : ℝ => x * (Real.log x * (1 / x))) =ᶠ[atTop] Real.log := by
    filter_upwards [eventually_ge_atTop 1] with x hx using by field_simp
  have l5 : (fun n ↦ n * (Real.log n * (1 / n))) =O[atTop] (fun n ↦ (Real.log n) ^ 2) :=
    e2.trans_isBigO
      (by simpa using! (isLittleO_mul_add_sq 1 0).isBigO.comp_tendsto Real.tendsto_log_atTop)
  simp_rw [l1, _root_.sq_sub_sq]
  exact ((l2.add l3).add (isBigO_refl (·) atTop |>.mul (l4.mul (nabla_log hb)) |>.trans l5))
lemma nnabla_bound_aux1 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x => x * (a + Real.log (x / b) ^ 2)) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_pow_atTop two_ne_zero).comp <| tendsto_log_atTop.comp <| tendsto_id.atTop_div_const hb
lemma nnabla_bound_aux2 (a : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x in atTop, 0 < x * (a + Real.log (x / b) ^ 2) :=
  (nnabla_bound_aux1 a hb).eventually (eventually_gt_atTop 0)
lemma Real.log_eventually_gt_atTop (a : ℝ) :
    ∀ᶠ x in atTop, a < Real.log x :=
  Real.tendsto_log_atTop.eventually (eventually_gt_atTop a)
theorem norm_lt_norm_of_nonneg (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) :
    ‖x‖ ≤ ‖y‖ := by
  simp_rw [Real.norm_eq_abs]
  apply abs_le_abs hxy
  linarith
lemma nnabla_bound_aux {x : ℝ} (hx : 0 < x) :
    nnabla (fun n ↦ 1 / (n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2))) =O[atTop]
    (fun n ↦ 1 / (Real.log n ^ 2 * n ^ 2)) := by
  let d n : ℝ := n * ((2 * π) ^ 2 + Real.log (n / x) ^ 2)
  change (fun x_1 ↦ nnabla (fun n ↦ 1 / d n) x_1) =O[atTop] _
  have l2 : ∀ᶠ n in atTop, 0 < d n := (nnabla_bound_aux2 ((2 * π) ^ 2) hx)
  have l3 : ∀ᶠ n in atTop, 0 < d (n + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id).eventually l2
  have l1 : ∀ᶠ n : ℝ in atTop,
      nnabla (fun n ↦ 1 / d n) n = (d (n + 1) - d n) * (d n)⁻¹ * (d (n + 1))⁻¹ := by
    filter_upwards [l2, l3] with n l2 l3
    rw [nnabla, one_div, one_div, inv_sub_inv l2.ne.symm l3.ne.symm, div_eq_mul_inv, mul_inv,
      mul_assoc]
  have l4 : (fun n => (d n)⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    apply IsBigO.inv_rev
    · refine (isBigO_refl _ _).mul <| (log_sq_isbigo_mul hx)
    · filter_upwards [Real.log_eventually_gt_atTop 0, eventually_gt_atTop 0] with x hx hx'
      rw [← not_imp_not]
      intro _
      positivity
  have l5 : (fun n => (d (n + 1))⁻¹) =O[atTop] (fun n => (n * (Real.log n) ^ 2)⁻¹) := by
    refine IsBigO.trans ?_ l4
    rw [isBigO_iff]; use 1
    have e3 : ∀ᶠ n in atTop, d n ≤ d (n + 1) := by
      filter_upwards [eventually_ge_atTop x] with n hn
      have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
      have : 0 ≤ n := hx.le.trans hn
      simp only [d]
      gcongr <;> simp [Real.log_nonneg, *]
    filter_upwards [l2, l3, e3] with n e1 e2 e3
    simp_rw [one_mul]
    apply norm_lt_norm_of_nonneg _ _ (by positivity)
    gcongr
  have l6 : (fun n => d (n + 1) - d n) =O[atTop] (fun n => (Real.log n) ^ 2) := by
    simpa [d, nabla] using! (nnabla_mul_log_sq ((2 * π) ^ 2) hx)
  apply EventuallyEq.trans_isBigO l1
  apply ((l6.mul l4).mul l5).trans_eventuallyEq
  filter_upwards [eventually_ge_atTop 2, Real.log_eventually_gt_atTop 0] with n hn hn'
  field_simp
lemma nnabla_bound (C : ℝ) {x : ℝ} (hx : 0 < x) :
    nnabla (fun n => C / (1 + (Real.log (n / x) / (2 * π)) ^ 2) / n) =O[atTop]
    (fun n => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
  field_simp
  simp only [div_eq_mul_inv, mul_inv, nnabla_mul, one_mul]
  apply IsBigO.const_mul_left
  simpa [div_eq_mul_inv, mul_pow, mul_comm] using nnabla_bound_aux hx
def chebyWith (C : ℝ) (f : ℕ → ℂ) : Prop := ∀ n, cumsum (‖f ·‖) n ≤ C * n
def cheby (f : ℕ → ℂ) : Prop := ∃ C, chebyWith C f
lemma cheby.bigO (h : cheby f) : cumsum (‖f ·‖) =O[atTop] ((↑) : ℕ → ℝ) := by
  have l1 : 0 ≤ cumsum (‖f ·‖) := cumsum_nonneg (fun _ => norm_nonneg _)
  obtain ⟨C, hC⟩ := h
  apply isBigO_of_le' (c := C) atTop
  intro n
  rw [Real.norm_eq_abs, abs_eq_self.mpr (l1 n)]
  simpa using hC n
lemma limiting_fourier_lim1_aux (hcheby : cheby f) (hx : 0 < x) (C : ℝ) (hC : 0 ≤ C) :
    Summable fun n ↦ ‖f n‖ / ↑n * (C / (1 + (1 / (2 * π) * Real.log (↑n / x)) ^ 2)) := by
  let a (n : ℕ) := (C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2) / ↑n)
  replace hcheby := hcheby.bigO
  have l1 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n : ℕ => (↑(n + 1) : ℝ)) :=
    hcheby.comp_tendsto <| tendsto_add_atTop_nat 1
  have l2 : shift (cumsum (‖f ·‖)) =O[atTop] (fun n => (n : ℝ)) :=
    l1.trans
      (by simpa using (isBigO_refl _ _).add <| isBigO_iff.mpr ⟨1, by simpa using ⟨1, by tauto⟩⟩)
  have l5 : BoundedAtFilter atTop (fun n : ℕ => C / (1 + (Real.log (↑n / x) / (2 * π)) ^ 2)) := by
    simp only [BoundedAtFilter]
    field_simp
    apply isBigO_of_le' (c := C) ; intro n
    have : 0 ≤ 2 ^ 2 * π ^ 2 + Real.log (n / x) ^ 2 := by positivity
    simp only [norm_div, norm_mul, norm_eq_abs, abs_eq_self.mpr hC, norm_pow,
      abs_eq_self.mpr pi_nonneg, abs_eq_self.mpr this, Pi.one_apply, one_mem,
      CStarRing.norm_of_mem_unitary, mul_one, ge_iff_le, Nat.abs_ofNat]
    apply div_le_of_le_mul₀ this hC
    rw [mul_add, ← mul_assoc]
    apply le_add_of_le_of_nonneg le_rfl
    positivity
  have l3 : a =O[atTop] (fun n => 1 / (n : ℝ)) := by
    simpa [a] using! IsBigO.mul l5 (isBigO_refl (fun n : ℕ => 1 / (n : ℝ)) _)
  have l4 : nnabla a =O[atTop] (fun n : ℕ => (n ^ 2 * (Real.log n) ^ 2)⁻¹) := by
    convert (nnabla_bound C hx).natCast ; simp [nnabla, a]
  simp_rw [div_mul_eq_mul_div, mul_div_assoc, one_mul]
  apply dirichlet_test'
  · intro n ; exact norm_nonneg _
  · intro n ; positivity
  · apply (l2.mul l3).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 1)
    intro x (hx : 1 ≤ x)
    have : x ≠ 0 := Nat.one_le_iff_ne_zero.mp hx
    simp [this]
  · have : ∀ᶠ n : ℕ in atTop, x ≤ n := by simpa using eventually_ge_atTop ⌈x⌉₊
    filter_upwards [this] with n hn
    have e1 : 0 < (n : ℝ) := by linarith
    have e2 : 1 ≤ n / x := (one_le_div hx).mpr hn
    have e3 := Nat.le_succ n
    gcongr
    refine div_nonneg (Real.log_nonneg e2) (by norm_num [pi_nonneg])
  · apply summable_of_isBigO_nat summable_inv_mul_log_sq
    apply (l2.mul l4).trans_eventuallyEq
    apply eventually_of_mem (Ici_mem_atTop 2)
    intro x (hx : 2 ≤ x)
    have : (x : ℝ) ≠ 0 := by simp ; linarith
    have : Real.log x ≠ 0 := by
      have ll : 2 ≤ (x : ℝ) := by simp [hx]
      simp
      grind
    field_simp
theorem limiting_fourier_lim1 (hcheby : cheby f) (ψ : W21) (hx : 0 < x) :
    Tendsto (fun σ' : ℝ ↦
        ∑' n, term f σ' n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (n / x)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  have : 0 ≤ C := by simpa using (norm_nonneg _).trans (hC 0)
  refine tendsto_tsum_of_dominated_convergence
    (limiting_fourier_lim1_aux hcheby hx C this) (fun n => ?_) ?_
  · apply Tendsto.mul_const
    by_cases h : n = 0 <;> simp only [term, h, ↓reduceIte, CharP.cast_eq_zero, div_zero,
      tendsto_const_nhds_iff]
    refine tendsto_const_nhds.div ?_ (by simp [h])
    simpa using ((continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds).const_cpow
  · rw [eventually_nhdsWithin_iff]
    apply Eventually.of_forall
    intro σ' (hσ' : 1 < σ') n
    rw [norm_mul, ← nterm_eq_norm_term]
    refine mul_le_mul ?_ (hC _) (norm_nonneg _) (div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    by_cases h : n = 0 <;> simp only [nterm, h, ↓reduceIte, CharP.cast_eq_zero, div_zero, le_refl]
    have : 1 ≤ (n : ℝ) := by simpa using! Nat.pos_iff_ne_zero.mpr h
    refine div_le_div₀ (norm_nonneg _) le_rfl (by simpa [Nat.pos_iff_ne_zero]) ?_
    simpa using Real.rpow_le_rpow_of_exponent_le this hσ'.le
theorem limiting_fourier_lim2_aux (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict
theorem limiting_fourier_lim2 (A : ℝ) (ψ : W21) (hx : 1 ≤ x) :
    Tendsto (fun σ' ↦ A * ↑(x ^ (1 - σ')) *
        ∫ u in Ici (-Real.log x), rexp (-u * (σ' - 1)) * 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))
      (𝓝[>] 1) (𝓝 (A * ∫ u in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)))) := by
  obtain ⟨C, hC⟩ := decay_bounds_cor ψ
  apply Tendsto.mul
  · suffices h : Tendsto (fun σ' : ℝ ↦ ofReal (x ^ (1 - σ'))) (𝓝[>] 1) (𝓝 1) by
      simpa using h.const_mul ↑A
    suffices h : Tendsto (fun σ' : ℝ ↦ x ^ (1 - σ')) (𝓝[>] 1) (𝓝 1) from
      (continuous_ofReal.tendsto 1).comp h
    have : Tendsto (fun σ' : ℝ ↦ σ') (𝓝 1) (𝓝 1) := fun _ a ↦ a
    have : Tendsto (fun σ' : ℝ ↦ 1 - σ') (𝓝[>] 1) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds (by simpa using this.const_sub 1)
    simpa using tendsto_const_nhds.rpow this (Or.inl (zero_lt_one.trans_le hx).ne.symm)
  · refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_
      (limiting_fourier_lim2_aux x C) ?_
    · apply Eventually.of_forall ; intro σ'
      apply Continuous.aestronglyMeasurable
      have := continuous_FourierIntegral ψ
      continuity
    · apply eventually_of_mem (U := Ioo 1 2)
      · apply Ioo_mem_nhdsGT_of_mem ; simp
      · intro σ' ⟨h1, h2⟩
        rw [ae_restrict_iff' measurableSet_Ici]
        apply Eventually.of_forall
        intro t (ht : - Real.log x ≤ t)
        rw [norm_mul]
        have hdom_nonneg : 0 ≤ max |x| 1 := by
          exact (abs_nonneg x).trans (le_max_left _ _)
        refine mul_le_mul ?_ (hC _) (norm_nonneg _) hdom_nonneg
        simp only [neg_mul, ofReal_exp, ofReal_neg, ofReal_mul, ofReal_sub, ofReal_one, norm_exp,
          neg_re, mul_re, ofReal_re, sub_re, one_re, ofReal_im, sub_im, one_im, sub_self, mul_zero,
          sub_zero]
        have : -Real.log x * (σ' - 1) ≤ t * (σ' - 1) := mul_le_mul_of_nonneg_right ht (by linarith)
        have : -(t * (σ' - 1)) ≤ Real.log x * (σ' - 1) := by simpa using neg_le_neg this
        have := Real.exp_monotone this
        apply this.trans
        have l1 : σ' - 1 ≤ 1 := by linarith
        have : 0 ≤ Real.log x := Real.log_nonneg hx
        have := mul_le_mul_of_nonneg_left l1 this
        refine (Real.exp_monotone this).trans ?_
        have hxabs : |x| = x := abs_of_nonneg (zero_le_one.trans hx)
        calc
          Real.exp (Real.log x * 1) = |x| := by
            simpa [mul_one, hxabs] using (Real.exp_log (zero_lt_one.trans_le hx))
          _ ≤ max |x| 1 := le_max_left _ _
    · apply Eventually.of_forall
      intro x
      suffices h : Tendsto (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) (𝓝[>] 1) (𝓝 1) by
        simpa using h.mul_const _
      apply Tendsto.mono_left ?_ nhdsWithin_le_nhds
      suffices h : Continuous (fun n ↦ ((rexp (-x * (n - 1))) : ℂ)) by simpa using h.tendsto 1
      continuity
theorem limiting_fourier_lim3 (hG : ContinuousOn G {s | 1 ≤ s.re}) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    Tendsto (fun σ' : ℝ ↦ ∫ t : ℝ, G (σ' + t * I) * ψ t * x ^ (t * I)) (𝓝[>] 1)
      (𝓝 (∫ t : ℝ, G (1 + t * I) * ψ t * x ^ (t * I))) := by
  by_cases hh : tsupport ψ = ∅
  · simp [tsupport_eq_empty_iff.mp hh]
  obtain ⟨a₀, ha₀⟩ := Set.nonempty_iff_ne_empty.mpr hh
  let S : Set ℂ := reProdIm (Icc 1 2) (tsupport ψ)
  have l1 : IsCompact S := by
    refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
    · exact isClosed_Icc.reProdIm (isClosed_tsupport ψ)
    · exact (Metric.isBounded_Icc 1 2).reProdIm ψ.h2.isBounded
  have l2 : S ⊆ {s : ℂ | 1 ≤ s.re} := fun z hz => (mem_reProdIm.mp hz).1.1
  have l3 : ContinuousOn (‖G ·‖) S := (hG.mono l2).norm
  have l4 : S.Nonempty := ⟨1 + a₀ * I, by simp [S, mem_reProdIm, ha₀]⟩
  obtain ⟨z, -, hmax⟩ := l1.exists_isMaxOn l4 l3
  let MG := ‖G z‖
  let bound (a : ℝ) : ℝ := MG * ‖ψ a‖
  apply tendsto_integral_filter_of_dominated_convergence (bound := bound)
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp)) ; intro u hu
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (hG.comp_continuous (by fun_prop) (by simp [hu.1])).mul ψ.h1.continuous
    · apply Continuous.const_cpow (by fun_prop) ; simp ; linarith
  · apply eventually_of_mem (U := Icc 1 2) (Icc_mem_nhdsGT_of_mem (by simp))
    intro u hu
    apply Eventually.of_forall ; intro v
    by_cases h : v ∈ tsupport ψ
    · have r1 : u + v * I ∈ S := by simp [S, mem_reProdIm, hu.1, hu.2, h]
      have r2 := isMaxOn_iff.mp hmax _ r1
      have r4 : (x : ℂ) ≠ 0 := by simp ; linarith
      have r5 : arg x = 0 := by simp [arg_eq_zero_iff] ; linarith
      have r3 : ‖(x : ℂ) ^ (v * I)‖ = 1 := by simp [norm_cpow_of_ne_zero r4, r5]
      simp_rw [norm_mul, r3, mul_one]
      exact mul_le_mul_of_nonneg_right r2 (norm_nonneg _)
    · have : v ∉ Function.support ψ := fun a ↦ h (subset_tsupport ψ a)
      simp at this ; simp [this, bound]
  · suffices h : Continuous bound by exact h.integrable_of_hasCompactSupport ψ.h2.norm.mul_left
    have := ψ.h1.continuous ; fun_prop
  · apply Eventually.of_forall ; intro t
    apply Tendsto.mul_const
    apply Tendsto.mul_const
    refine (hG (1 + t * I) (by simp)).tendsto.comp <| tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_ofReal.tendsto _).add tendsto_const_nhds).mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x (hx : 1 < x) => by simp [hx.le])
lemma limiting_fourier (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (ψ : CS 2 ℂ) (hx : 1 ≤ x) :
    ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π)) =
      ∫ (t : ℝ), (G (1 + t * I)) * (ψ t) * x ^ (t * I) := by
  have l1 := limiting_fourier_lim1 hcheby ψ (by linarith)
  have l2 := limiting_fourier_lim2 A ψ hx
  have l3 := limiting_fourier_lim3 hG ψ hx
  apply tendsto_nhds_unique_of_eventuallyEq (l1.sub l2) l3
  simpa [eventuallyEq_nhdsWithin_iff] using! Eventually.of_forall (limiting_fourier_aux hG' hf ψ hx)
lemma limiting_cor_aux {f : ℝ → ℂ} : Tendsto (fun x : ℝ ↦ ∫ t, f t * x ^ (t * I)) atTop (𝓝 0) := by
  have l1 : ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, x ^ (t * I) = exp (log x * t * I) := by
    filter_upwards [eventually_ne_atTop 0, eventually_ge_atTop 0] with x hx hx' t
    rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx), ofReal_log hx'] ; ring_nf
  have l2 : ∀ᶠ x : ℝ in atTop, ∫ t, f t * x ^ (t * I) = ∫ t, f t * exp (log x * t * I) := by
    filter_upwards [l1] with x hx
    refine integral_congr_ae (Eventually.of_forall (fun x => by simp [hx]))
  simp_rw [tendsto_congr' l2]
  convert_to Tendsto (fun x => 𝓕 f (-Real.log x / (2 * π))) atTop (𝓝 0)
  · ext x; congr 1; ext t
    simp only [← ofReal_mul, mul_comm (f _), fourierChar, Circle.exp, ContinuousMap.coe_mk,
      innerₗ_apply_apply, RCLike.inner_apply, conj_trivial, AddChar.coe_mk, mul_neg, ofReal_neg,
      neg_mul]
    change _ = cexp (↑(-(2 * π * (-Real.log x / (2 * π) * t))) * I) * f t
    rw [show -(2 * π * (-Real.log x / (2 * π) * t)) = Real.log x * t by field_simp]
  refine (Real.zero_at_infty_fourier f).comp <| Tendsto.mono_right ?_ _root_.atBot_le_cocompact
  exact (tendsto_neg_atBot_iff.mpr tendsto_log_atTop).atBot_mul_const (inv_pos.mpr two_pi_pos)
lemma limiting_cor (ψ : CS 2 ℂ) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by
  apply limiting_cor_aux.congr'
  filter_upwards [eventually_ge_atTop 1] with x hx using
    limiting_fourier hcheby hG hG' hf ψ hx |>.symm
lemma smooth_urysohn (a b c d : ℝ) (h1 : a < b) (h3 : c < d) : ∃ Ψ : ℝ → ℝ,
    (ContDiff ℝ ∞ Ψ) ∧ (HasCompactSupport Ψ) ∧
      Set.indicator (Set.Icc b c) 1 ≤ Ψ ∧ Ψ ≤ Set.indicator (Set.Ioo a d) 1 := by
  obtain ⟨ψ, l1, l2, l3, l4, -⟩ := smooth_urysohn_support_Ioo h1 h3
  refine ⟨ψ, l1, l2, l3, l4⟩
noncomputable def exists_trunc : trunc := by
  choose ψ h1 h2 h3 h4 using smooth_urysohn (-2) (-1) (1) (2) (by linarith) (by linarith)
  exact ⟨⟨ψ, h1.of_le (by norm_cast), h2⟩, h3, h4⟩
lemma one_div_sub_one (n : ℕ) : 1 / (↑(n - 1) : ℝ) ≤ 2 / n := by
  match n with
  | 0 => simp
  | 1 => simp
  | n + 2 => { norm_cast ; rw [div_le_div_iff₀] <;> simp [mul_add] <;> linarith }
lemma quadratic_pos (a b c x : ℝ) (ha : 0 < a) (hΔ : discrim a b c < 0) :
    0 < a * x ^ 2 + b * x + c := by
  have l1 : a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 - discrim a b c / (4 * a) := by
    simp only [discrim]; field_simp; ring
  have l2 : 0 < - discrim a b c := by linarith
  rw [l1, sub_eq_add_neg, ← neg_div] ; positivity
noncomputable def pp (a x : ℝ) : ℝ := a ^ 2 * (x + 1) ^ 2 + (1 - a) * (1 + a)
noncomputable def pp' (a x : ℝ) : ℝ := a ^ 2 * (2 * (x + 1))
lemma pp_pos {a : ℝ} (ha : a ∈ Ioo (-1) 1) (x : ℝ) : 0 < pp a x := by
  simp only [pp]
  have : 0 < 1 - a := by linarith [ha.2]
  have : 0 < 1 + a := by linarith [ha.1]
  positivity
lemma pp_deriv (a x : ℝ) : HasDerivAt (pp a) (pp' a x) x := by
  unfold pp pp'
  simpa using hasDerivAt_id x |>.add_const 1 |>.pow 2 |>.const_mul _
lemma pp_deriv_eq (a : ℝ) : deriv (pp a) = pp' a := by
  ext x ; exact pp_deriv a x |>.deriv
lemma pp'_deriv (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  simpa using! hasDerivAt_id x |>.add_const 1 |>.const_mul 2 |>.const_mul (a ^ 2)
lemma pp'_deriv_eq (a : ℝ) : deriv (pp' a) = fun _ => a ^ 2 * 2 := by
  ext x ; exact pp'_deriv a x |>.deriv
noncomputable def hh (a t : ℝ) : ℝ := (t * (1 + (a * log t) ^ 2))⁻¹
noncomputable def hh' (a t : ℝ) : ℝ := - pp a (log t) * hh a t ^ 2
lemma hh_nonneg (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by dsimp only [hh] ; positivity
lemma hh_le (a t : ℝ) (ht : 0 ≤ t) : |hh a t| ≤ t⁻¹ := by
  by_cases h0 : t = 0
  · simp [hh, h0]
  replace ht : 0 < t := lt_of_le_of_ne ht (by tauto)
  unfold hh
  rw [abs_inv, inv_le_inv₀ (by positivity) ht, abs_mul, abs_eq_self.mpr ht.le]
  convert_to! t * 1 ≤ _
  · simp
  apply mul_le_mul le_rfl ?_ zero_le_one ht.le
  rw [abs_eq_self.mpr (by positivity)]
  simp only [le_add_iff_nonneg_right]
  positivity
lemma hh_deriv (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have e1 : t * (1 + (a * log t) ^ 2) ≠ 0 := mul_ne_zero ht (_root_.ne_of_lt (by positivity)).symm
  have l5 : HasDerivAt (fun t : ℝ => log t) t⁻¹ t := Real.hasDerivAt_log ht
  have l4 : HasDerivAt (fun t : ℝ => a * log t) (a * t⁻¹) t := l5.const_mul _
  have l3 : HasDerivAt (fun t : ℝ => (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t := by
    convert! l4.pow 2 using 1 ; ring
  have l2 : HasDerivAt (fun t : ℝ => 1 + (a * log t) ^ 2) (2 * a ^ 2 * t⁻¹ * log t) t :=
    l3.const_add _
  have l1 : HasDerivAt (fun t : ℝ => t * (1 + (a * log t) ^ 2))
      (1 + 2 * a ^ 2 * log t + a ^ 2 * log t ^ 2) t := by
    convert! (hasDerivAt_id' t).mul l2 using 1; field_simp; ring
  convert! l1.inv e1 using 1; simp only [hh', pp, hh]; field_simp; ring
lemma hh_continuous (a : ℝ) : ContinuousOn (hh a) (Ioi 0) :=
  fun t (ht : 0 < t) => (hh_deriv a ht.ne.symm).continuousAt.continuousWithinAt
lemma hh'_nonpos {a x : ℝ} (ha : a ∈ Ioo (-1) 1) : hh' a x ≤ 0 := by
  have := pp_pos ha (log x)
  simp only [hh', neg_mul, Left.neg_nonpos_iff, ge_iff_le]
  positivity
lemma hh_antitone {a : ℝ} (ha : a ∈ Ioo (-1) 1) : AntitoneOn (hh a) (Ioi 0) := by
  have l1 x (hx : x ∈ interior (Ioi 0)) :
      HasDerivWithinAt (hh a) (hh' a x) (interior (Ioi 0)) x := by
    have : x ≠ 0 := by contrapose! hx ; simp [hx]
    exact (hh_deriv a this).hasDerivWithinAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi _) (hh_continuous _) l1
    (fun x _ => hh'_nonpos ha)
noncomputable def gg (x i : ℝ) : ℝ := 1 / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹
lemma gg_of_hh {x : ℝ} (hx : x ≠ 0) (i : ℝ) : gg x i = x⁻¹ * hh (1 / (2 * π)) (i / x) := by
  simp only [gg, hh]
  field_simp
lemma gg_l1 {x : ℝ} (hx : 0 < x) (n : ℕ) : |gg x n| ≤ 1 / n := by
  simp only [gg_of_hh hx.ne.symm, one_div, mul_inv_rev, abs_mul]
  apply mul_le_mul le_rfl (hh_le _ _ (by positivity)) (by positivity) (by positivity) |>.trans
    (le_of_eq ?_)
  simp [abs_inv, abs_eq_self.mpr hx.le] ; field_simp
lemma gg_le_one (i : ℕ) : gg x i ≤ 1 := by
  by_cases hi : i = 0 <;> simp only [gg, hi, CharP.cast_eq_zero, div_zero, one_div, mul_inv_rev,
    zero_div, Real.log_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    add_zero, inv_one, mul_one, zero_le_one]
  have l1 : 1 ≤ (i : ℝ) := by simp ; omega
  have l2 : 1 ≤ 1 + (π⁻¹ * 2⁻¹ * Real.log (↑i / x)) ^ 2 := by
    simp only [le_add_iff_nonneg_right] ; positivity
  rw [← mul_inv] ; apply inv_le_one_of_one_le₀ ; simpa using mul_le_mul l1 l2 zero_le_one (by simp)
lemma one_div_two_pi_mem_Ioo : 1 / (2 * π) ∈ Ioo (-1) 1 := by
  constructor
  · trans 0
    · linarith
    · positivity
  · rw [div_lt_iff₀ (by positivity)]
    convert_to! 1 * 1 < 2 * π
    · simp
    · simp
    apply mul_lt_mul one_lt_two ?_ zero_lt_one zero_le_two
    trans 2
    · exact one_le_two
    · exact two_le_pi
lemma sum_telescopic (a : ℕ → ℝ) (n : ℕ) : ∑ i ∈ Finset.range n, (a (i + 1) - a i) = a n - a 0 := by
  apply Finset.sum_range_sub
lemma cancel_aux {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤ g (n - 1) * (C * n) + (C * (↑(n - 1 - 1) + 1) * g 0
      - C * (↑(n - 1 - 1) + 1) * g (n - 1) -
    ((n - 1 - 1) • (C * g 0) - ∑ x ∈ Finset.range (n - 1 - 1), C * g (x + 1))) := by
  have l1 (n : ℕ) :
      (g n - g (n + 1)) * ∑ i ∈ Finset.range (n + 1), f i ≤ (g n - g (n + 1)) * (C * (n + 1)) := by
    apply mul_le_mul le_rfl (by simpa using! hf' (n + 1)) (Finset.sum_nonneg' hf) ?_
    simp only [sub_nonneg] ; apply hg' ; simp
  have l2 (x : ℕ) : C * (↑(x + 1) + 1) - C * (↑x + 1) = C := by simp ; ring
  have l3 (n : ℕ) : 0 ≤ cumsum f n := Finset.sum_nonneg' hf
  convert_to ∑ i ∈ Finset.range n, (g i) • (f i) ≤ _
  · simp [mul_comm]
  rw [Finset.sum_range_by_parts, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  simp_rw [← neg_smul, neg_sub, smul_eq_mul]
  apply _root_.add_le_add
  · exact mul_le_mul le_rfl (hf' n) (l3 n) (hg _)
  · apply Finset.sum_le_sum (fun n _ => l1 n) |>.trans
    convert_to! ∑ i ∈ Finset.range (n - 1), (C * (↑i + 1)) • (g i - g (i + 1)) ≤ _
    · congr ; ext i ; simp ; ring
    rw [Finset.sum_range_by_parts]
    simp_rw [Finset.sum_range_sub', l2, smul_sub, smul_eq_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range]
    apply le_of_eq ; ring_nf
lemma sum_range_succ (a : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, a (i + 1) = (∑ i ∈ Finset.range (n + 1), a i) - a 0 := by
  have := Finset.sum_range_sub a n
  rw [Finset.sum_sub_distrib, sub_eq_iff_eq_add] at this
  rw [Finset.sum_range_succ, this] ; ring
lemma cancel_aux' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i * g i ≤
        C * n * g (n - 1)
      + C * cumsum g (n - 1 - 1 + 1)
      - C * (↑(n - 1 - 1) + 1) * g (n - 1)
      := by
  have := cancel_aux hf hg hf' hg' n
  simp only [nsmul_eq_mul, ← Finset.mul_sum, sum_range_succ] at this
  convert this using 1 ; unfold cumsum ; ring
lemma cancel_main {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) (hn : 2 ≤ n) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  convert! cancel_aux' hf hg hf' hg' n using 1
  match n with
  | n + 2 => simp only [cumsum_succ] ; push_cast ; ring
lemma cancel_main' {C : ℝ} {f g : ℕ → ℝ} (hf : 0 ≤ f) (hf0 : f 0 = 0) (hg : 0 ≤ g)
    (hf' : ∀ n, cumsum f n ≤ C * n) (hg' : Antitone g) (n : ℕ) :
    cumsum (f * g) n ≤ C * cumsum g n := by
  match n with
  | 0 => simp [cumsum]
  | 1 => specialize hg 0 ; specialize hf' 1 ; simp only [cumsum, Finset.range_one,
    Finset.sum_singleton, hf0, Nat.cast_one, mul_one, Pi.zero_apply, Pi.mul_apply, zero_mul,
    ge_iff_le] at hf' hg ⊢ ; positivity
  | n + 2 => convert! cancel_aux' hf hg hf' hg' (n + 2) using 1 ; simp [cumsum_succ] ; ring
theorem sum_le_integral {x₀ : ℝ} {f : ℝ → ℝ} {n : ℕ} (hf : AntitoneOn f (Ioc x₀ (x₀ + n)))
    (hfi : IntegrableOn f (Icc x₀ (x₀ + n))) :
    (∑ i ∈ Finset.range n, f (x₀ + ↑(i + 1))) ≤ ∫ x in x₀..x₀ + n, f x := by
  cases n with simp only [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero, add_zero,
      lt_self_iff_false, not_false_eq_true,
    Ioc_eq_empty, Finset.range_zero, Nat.cast_add, Nat.cast_one, Finset.sum_empty,
    intervalIntegral.integral_same, le_refl] at hf ⊢
  | succ n =>
  have : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
    ext i ; by_cases hi : i = 0 <;> simp [hi] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, and_true, not_false_eq_true,
    Finset.sum_insert, CharP.cast_eq_zero, zero_add, ge_iff_le]
  have l4 : IntervalIntegrable f volume x₀ (x₀ + 1) := by
    apply IntegrableOn.intervalIntegrable
    simp only [le_add_iff_nonneg_right, zero_le_one, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc le_rfl
    simp
  have l5 x (hx : x ∈ Ioc x₀ (x₀ + 1)) : (fun x ↦ f (x₀ + 1)) x ≤ f x := by
    rcases hx with ⟨hx1, hx2⟩
    refine hf ⟨hx1, by linarith⟩ ⟨by linarith, by linarith⟩ hx2
  have l6 : ∫ x in x₀..x₀ + 1, f (x₀ + 1) = f (x₀ + 1) := by simp
  have l1 : f (x₀ + 1) ≤ ∫ x in x₀..x₀ + 1, f x := by
    rw [← l6] ; apply intervalIntegral.integral_mono_ae_restrict (by linarith) (by simp) l4
    apply eventually_of_mem _ l5
    have : (Ioc x₀ (x₀ + 1))ᶜ ∩ Icc x₀ (x₀ + 1) = {x₀} := by simp [← sdiff_eq_compl_inter]
    rw [mem_ae_iff, Measure.restrict_apply measurableSet_Ioc.compl, this]
    simp
  have l2 : AntitoneOn (fun x ↦ f (x₀ + x)) (Icc 1 ↑(n + 1)) := by
    intro u ⟨hu1, _⟩ v ⟨_, hv2⟩ huv ; push_cast at hv2
    refine hf ⟨?_, ?_⟩ ⟨?_, ?_⟩ ?_ <;> linarith
  have l3 := @AntitoneOn.sum_le_integral_Ico 1 (n + 1) (fun x => f (x₀ + x)) (by simp)
    (by simpa using l2)
  simp only [Nat.cast_add, Nat.cast_one, intervalIntegral.integral_comp_add_left] at l3
  convert! _root_.add_le_add l1 l3
  have := @intervalIntegral.integral_comp_mul_add ℝ _ _ 1 (n + 1) 1 f one_ne_zero x₀
  rw [intervalIntegral.integral_add_adjacent_intervals]
  · exact l4
  · apply IntegrableOn.intervalIntegrable
    simp only [add_le_add_iff_left, le_add_iff_nonneg_left, Nat.cast_nonneg, uIcc_of_le]
    apply hfi.mono_set
    apply Icc_subset_Icc
    · linarith
    · simp
lemma hh_integrable_aux (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0)) ∧
    (∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simp only [hh]
  let g (x : ℝ) := (a * c / b) * Real.arctan (b * log (x / c))
  let g₀ (x : ℝ) := if x = 0 then ((a * c / b) * (- (π / 2))) else g x
  let g' (x : ℝ) := a * (x / c * (1 + (b * Real.log (x / c)) ^ 2))⁻¹
  have l3 (x) (hx : 0 < x) : HasDerivAt Real.log x⁻¹ x := by apply Real.hasDerivAt_log (by linarith)
  have l4 (x) : HasDerivAt (fun t => t / c) (1 / c) x := (hasDerivAt_id x).div_const c
  have l2 (x) (hx : 0 < x) : HasDerivAt (fun t => log (t / c)) x⁻¹ x := by
    have := @HasDerivAt.comp _ _ _ _ _ _ (fun t => t / c) _ _ _  (l3 (x / c) (by positivity)) (l4 x)
    convert! this using 1 ; field_simp
  have l5 (x) (hx : 0 < x) := (l2 x hx).const_mul b
  have l1 (x) (hx : 0 < x) := (l5 x hx).arctan
  have l6 (x) (hx : 0 < x) : HasDerivAt g (g' x) x := by
    convert! (l1 x hx).const_mul (a * c / b) using 1
    simp only [g']
    field_simp
  have key (x) (hx : 0 < x) : HasDerivAt g₀ (g' x) x := by
    apply (l6 x hx).congr_of_eventuallyEq
    apply eventually_of_mem <| Ioi_mem_nhds hx
    intro y (hy : 0 < y)
    simp [g₀, hy.ne.symm]
  have k1 : Tendsto g₀ atTop (𝓝 ((a * c / b) * (π / 2))) := by
    have : g =ᶠ[atTop] g₀ := by
      apply eventually_of_mem (Ioi_mem_atTop 0)
      intro y (hy : 0 < y)
      simp [g₀, hy.ne.symm]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atTop hb
    apply tendsto_log_atTop.comp
    apply Tendsto.atTop_div_const hc
    apply tendsto_id
  have k2 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) := by
    have : g =ᶠ[𝓝[>] 0] g₀ := by
      apply eventually_of_mem self_mem_nhdsWithin
      intro x (hx : 0 < x) ; simp [g₀, hx.ne.symm]
    simp only [g₀]
    apply Tendsto.congr' this
    apply Tendsto.const_mul
    apply (tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).comp
    apply Tendsto.const_mul_atBot hb
    apply tendsto_log_nhdsGT_zero.comp
    rw [Metric.tendsto_nhdsWithin_nhdsWithin]
    intro ε hε
    refine ⟨c * ε, by positivity, fun x hx1 hx2 => ⟨?_, ?_⟩⟩
    · simp only [mem_Ioi] at hx1 ⊢ ; positivity
    · simp only [dist_zero_right, norm_eq_abs, norm_div, abs_eq_self.mpr hc.le] at hx2 ⊢
      rwa [div_lt_iff₀ hc, mul_comm]
  have k3 : ContinuousWithinAt g₀ (Ici 0) 0 := by
    rw [Metric.continuousWithinAt_iff]
    rw [Metric.tendsto_nhdsWithin_nhds] at k2
    peel k2 with ε hε δ hδ x h
    intro (hx : 0 ≤ x)
    have := le_iff_lt_or_eq.mp hx
    cases this with
    | inl hx => exact h hx
    | inr hx => simp [g₀, hx.symm, hε]
  have k4 : ∀ x ∈ Ioi 0, 0 ≤ g' x := by
    intro x (hx : 0 < x) ; simp only [mul_inv_rev, inv_div, g'] ; positivity
  constructor
  · convert_to IntegrableOn g' _
    exact integrableOn_Ioi_deriv_of_nonneg k3 key k4 k1
  · have := integral_Ioi_of_hasDerivAt_of_nonneg k3 key k4 k1
    simp only [mul_inv_rev, inv_div, mul_neg, ↓reduceIte, sub_neg_eq_add, g', g₀] at this ⊢
    convert this using 1 ; field_simp ; ring
lemma hh_integrable (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IntegrableOn (fun t ↦ a * hh b (t / c)) (Ici 0) :=
  hh_integrable_aux ha hb hc |>.1
lemma hh_integral (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∫ (t : ℝ) in Ioi 0, a * hh b (t / c) = a * c / b * π :=
  hh_integrable_aux ha hb hc |>.2
lemma hh_integral' : ∫ t in Ioi 0, hh (1 / (2 * π)) t = 2 * π ^ 2 := by
  have := hh_integral (a := 1) (b := 1 / (2 * π)) (c := 1)
    (by positivity) (by positivity) (by positivity)
  convert this using 1 <;> simp ; ring
lemma bound_sum_log {C : ℝ} (hf0 : f 0 = 0) (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by
  let ggg (i : ℕ) : ℝ := if i = 0 then 1 else gg x i
  have l0 : x ≠ 0 := by linarith
  have l1 i : 0 ≤ ggg i := by by_cases hi : i = 0 <;> simp only [gg, one_div, mul_inv_rev, hi,
    ↓reduceIte, zero_le_one, ggg] ; positivity
  have l2 : Antitone ggg := by
    intro i j hij ; by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hj, ↓reduceIte, hi,
      le_refl, ggg]
    · exact gg_le_one _
    · omega
    · simp only [gg_of_hh l0]
      gcongr
      apply hh_antitone one_div_two_pi_mem_Ioo
      · simp only [mem_Ioi] ; positivity
      · simp only [mem_Ioi] ; positivity
      · gcongr
  have l3 : 0 ≤ C := by simpa [cumsum, hf0] using hf 1
  have l4 : 0 ≤ ∫ (t : ℝ) in Ioi 0, hh (π⁻¹ * 2⁻¹) t :=
    setIntegral_nonneg measurableSet_Ioi (fun x hx => hh_nonneg _ (LT.lt.le hx))
  have l5 {n : ℕ} : AntitoneOn (fun t ↦ x⁻¹ * hh (1 / (2 * π)) (t / x)) (Ioc 0 n) := by
    intro u ⟨hu1, _⟩ v ⟨hv1, _⟩ huv
    simp only
    apply mul_le_mul le_rfl ?_ (hh_nonneg _ (by positivity)) (by positivity)
    apply hh_antitone one_div_two_pi_mem_Ioo (by simp only [mem_Ioi] ; positivity)
      (by simp only [mem_Ioi] ; positivity)
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr huv
  have l6 {n : ℕ} : IntegrableOn (fun t ↦ x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (Icc 0 n) volume := by
    apply IntegrableOn.mono_set
      (hh_integrable (by positivity) (by positivity) (by positivity)) Icc_subset_Ici_self
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity) ; intro n
  convert_to! ∑ i ∈ Finset.range n, ‖f i‖ * ggg i ≤ _
  · congr ; ext i
    by_cases hi : i = 0
    · simp [hi, hf0]
    · simp only [gg, hi, ↓reduceIte, ggg]
      field_simp
  apply cancel_main' (fun _ => norm_nonneg _) (by simp [hf0]) l1 hf l2 n |>.trans
  gcongr ; simp only [cumsum, gg_of_hh l0, one_div, mul_inv_rev, ggg]
  by_cases hn : n = 0
  · simp only [hn, Finset.range_zero, Finset.sum_empty] ; positivity
  replace hn : 0 < n := by omega
  have : Finset.range n = {0} ∪ Finset.Ico 1 n := by
    ext i ; simp ; by_cases hi : i = 0 <;> simp [hi, hn] ; omega
  simp only [this, Finset.singleton_union, Finset.mem_Ico, nonpos_iff_eq_zero, one_ne_zero,
    false_and, not_false_eq_true, Finset.sum_insert, ↓reduceIte, add_le_add_iff_left, ge_iff_le]
  convert_to! ∑ x_1 ∈ Finset.Ico 1 n, x⁻¹ * hh (π⁻¹ * 2⁻¹) (↑x_1 / x) ≤ _
  · apply Finset.sum_congr rfl (fun i hi => ?_)
    simp at hi
    have : i ≠ 0 := by omega
    simp [this]
  simp_rw [Finset.sum_Ico_eq_sum_range, add_comm 1]
  have := @sum_le_integral 0 (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t / x)) (n - 1)
    (by simpa using l5) (by simpa using l6)
  simp only [zero_add] at this
  apply this.trans
  rw [@intervalIntegral.integral_comp_div ℝ _ _ 0 ↑(n - 1) x (fun t => x⁻¹ * hh (π⁻¹ * 2⁻¹) (t)) l0]
  simp only [zero_div, intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ l0, one_mul]
  have : (0 : ℝ) ≤ ↑(n - 1) / x := by positivity
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
  simp only [this, ↓reduceIte, uIoc_of_le, smul_eq_mul, one_mul, ge_iff_le]
  apply integral_mono_measure
  · apply Measure.restrict_mono Ioc_subset_Ioi_self le_rfl
  · apply eventually_of_mem (self_mem_ae_restrict measurableSet_Ioi)
    intro x (hx : 0 < x)
    apply hh_nonneg _ hx.le
  · have := (@hh_integrable 1 (1 / (2 * π)) 1 (by positivity) (by positivity) (by positivity))
    simpa using! this.mono_set Ioi_subset_Ici_self
lemma bound_sum_log0 {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤
      C * (1 + ∫ t in Ioi 0, hh (1 / (2 * π)) t) := by
  let f0 i := if i = 0 then 0 else f i
  have l1 : chebyWith C f0 := by
    intro n ; refine Finset.sum_le_sum (fun i _ => ?_) |>.trans (hf n)
    by_cases hi : i = 0 <;> simp [hi, f0]
  have l2 i : ‖f i‖ / i = ‖f0 i‖ / i := by by_cases hi : i = 0 <;> simp [hi, f0]
  simp_rw [l2] ; apply bound_sum_log rfl l1 hx
lemma bound_sum_log' {C : ℝ} (hf : chebyWith C f) {x : ℝ} (hx : 1 ≤ x) :
    ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ ≤ C * (1 + 2 * π ^ 2) := by
  simpa only [hh_integral'] using bound_sum_log0 hf hx
variable (f x) in
lemma summable_fourier_aux (ψ : W21) (i : ℕ) :
    ‖f i / i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (i / x))‖ ≤
      W21.norm ψ * (‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹) := by
  convert! mul_le_mul_of_nonneg_left (decay_bounds_key ψ (1 / (2 * π) * log (i / x)))
    (norm_nonneg (f i / i)) using 1
  · simp
  · change _ = _ * (W21.norm ψ * _)
    simp only [W21.norm, mul_inv_rev, one_div, Complex.norm_div, RCLike.norm_natCast]
    ring
lemma summable_fourier (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) l6
    (by simpa using l5.const_smul (W21.norm ψ))
lemma bound_I1 (x : ℝ) (hx : 0 < x) (ψ : W21) (hcheby : cheby f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
    W21.norm ψ • ∑' i, ‖f i‖ / i * (1 + (1 / (2 * π) * log (i / x)) ^ 2)⁻¹ := by
  have l5 : Summable fun i ↦ ‖f i‖ / ↑i * ((1 + (1 / (2 * ↑π) * ↑(Real.log (↑i / x))) ^ 2)⁻¹) := by
    simpa using limiting_fourier_lim1_aux hcheby hx 1 (zero_le_one' ℝ)
  have l6 := summable_fourier_aux x f ψ
  have l1 : Summable fun i ↦ ‖f i / ↑i * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑i / x))‖ := by
    exact summable_fourier x hx ψ hcheby
  apply (norm_tsum_le_tsum_norm l1).trans
  simpa only [← Summable.tsum_const_smul _ l5] using!
    Summable.tsum_mono l1 (by simpa using l5.const_smul (W21.norm ψ)) l6
lemma bound_I1' {C : ℝ} (x : ℝ) (hx : 1 ≤ x) (ψ : W21) (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x))‖ ≤
      W21.norm ψ * C * (1 + 2 * π ^ 2) := by
  apply bound_I1 x (by linarith) ψ ⟨_, hcheby⟩ |>.trans
  rw [smul_eq_mul, mul_assoc]
  apply mul_le_mul le_rfl (bound_sum_log' hcheby hx) ?_ W21.norm_nonneg
  apply tsum_nonneg (fun i => by positivity)
lemma bound_I2 (x : ℝ) (ψ : W21) :
    ‖∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤ W21.norm ψ * (2 * π ^ 2) := by
  have key a : ‖𝓕 (ψ : ℝ → ℂ) (a / (2 * π))‖ ≤ W21.norm ψ * (1 + (a / (2 * π)) ^ 2)⁻¹ :=
    decay_bounds_key ψ _
  have twopi : 0 ≤ 2 * π := by simp [pi_nonneg]
  have l3 : Integrable (fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div (by norm_num [pi_ne_zero])
  have l2 : IntegrableOn (fun i ↦ W21.norm ψ * (1 + (i / (2 * π)) ^ 2)⁻¹) (Ici (-Real.log x)) := by
    exact (l3.const_mul _).integrableOn
  have l1 : IntegrableOn (fun i ↦ ‖𝓕 (ψ : ℝ → ℂ) (i / (2 * π))‖) (Ici (-Real.log x)) := by
    refine ((l3.const_mul (W21.norm ψ)).mono' ?_ ?_).integrableOn
    · apply Continuous.aestronglyMeasurable ; first | fun_prop | exact (continuous_FourierIntegral ψ).comp (by fun_prop) | exact ((continuous_FourierIntegral ψ).comp (by fun_prop)).norm
    · simp only [norm_norm, key] ; simp
  have l5 : 0 ≤ᵐ[volume] fun a ↦ (1 + (a / (2 * π)) ^ 2)⁻¹ := by
    apply Eventually.of_forall ; intro x ; positivity
  refine (norm_integral_le_integral_norm _).trans <| (setIntegral_mono l1 l2 key).trans ?_
  rw [integral_const_mul] ; gcongr
  · apply W21.norm_nonneg
  refine (setIntegral_le_integral l3 l5).trans ?_
  rw [Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) (2 * π)]
  simp [abs_eq_self.mpr twopi] ; ring_nf ; rfl
lemma bound_main {C : ℝ} (A : ℂ) (x : ℝ) (hx : 1 ≤ x) (ψ : W21)
    (hcheby : chebyWith C f) :
    ‖∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))‖ ≤
      W21.norm ψ * (C * (1 + 2 * π ^ 2) + ‖A‖ * (2 * π ^ 2)) := by
  have l1 := bound_I1' x hx ψ hcheby
  have l2 := mul_le_mul (le_refl ‖A‖) (bound_I2 x ψ) (by positivity) (by positivity)
  apply norm_sub_le _ _ |>.trans ; rw [norm_mul]
  convert _root_.add_le_add l1 l2 using 1 ; ring
lemma limiting_cor_W21 (ψ : W21) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) := by
  let S1 x (ψ : ℝ → ℂ) := ∑' (n : ℕ), f n / ↑n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * Real.log (↑n / x))
  let S2 x (ψ : ℝ → ℂ) := ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))
  let S x ψ := S1 x ψ - S2 x ψ ; change Tendsto (fun x ↦ S x ψ) atTop (𝓝 0)
  obtain g := exists_trunc
  let Ψ R := g.scale R * ψ
  have key R : Tendsto (fun x ↦ S x (Ψ R)) atTop (𝓝 0) := limiting_cor (Ψ R) hf hcheby hG hG'
  obtain ⟨C, hcheby⟩ := hcheby
  have hC : 0 ≤ C := by
    have : ‖f 0‖ ≤ C := by simpa [cumsum] using hcheby 1
    have : 0 ≤ ‖f 0‖ := by positivity
    linarith
  have key2 : Tendsto (fun R ↦ W21.norm (ψ - Ψ R)) atTop (𝓝 0) := W21_approximation ψ g
  simp_rw [Metric.tendsto_nhds] at key key2 ⊢ ; intro ε hε
  let M := C * (1 + 2 * π ^ 2) + ‖(A : ℂ)‖ * (2 * π ^ 2)
  obtain ⟨R, hRψ⟩ := (key2 ((ε / 2) / (1 + M)) (by positivity)).exists
  simp only [dist_zero_right, Real.norm_eq_abs, abs_eq_self.mpr W21.norm_nonneg] at hRψ key
  filter_upwards [eventually_ge_atTop 1, key R (ε / 2) (by positivity)] with x hx key
  have key3 : ‖S x (ψ - Ψ R)‖ < ε / 2 := by
    have : ‖S x _‖ ≤ _ * M := @bound_main f C A x hx (ψ - Ψ R) hcheby
    apply this.trans_lt
    apply (mul_le_mul (d := 1 + M) le_rfl (by simp) (by positivity) W21.norm_nonneg).trans_lt
    have : 0 < 1 + M := by positivity
    convert! (mul_lt_mul_iff_left₀ this).mpr hRψ using 1 ; field_simp
  have S1_sub_1 x : 𝓕 (⇑ψ - ⇑(Ψ R)) x = 𝓕 (ψ : ℝ → ℂ) x - 𝓕 ⇑(Ψ R) x := by
    have l1 : AEStronglyMeasurable (fun x_1 : ℝ ↦ cexp (-(2 * ↑π * (↑x_1 * ↑x) * I))) volume := by
      refine (Continuous.mul ?_ continuous_const).neg.cexp.aestronglyMeasurable
      apply continuous_const.mul <| contDiff_ofReal.continuous.mul continuous_const
    simp only [Real.fourier_eq', neg_mul, RCLike.inner_apply', conj_trivial, ofReal_neg,
      ofReal_mul, ofReal_ofNat, Pi.sub_apply, smul_eq_mul, mul_sub]
    apply integral_sub
    · apply ψ.hf.bdd_mul (c := 1) l1 ; simp [Complex.norm_exp]
    · apply (Ψ R : W21) |>.hf |>.bdd_mul (c := 1) l1
      simp [Complex.norm_exp]
  have S1_sub : S1 x (ψ - Ψ R) = S1 x ψ - S1 x (Ψ R) := by
    simp only [one_div, mul_inv_rev, S1_sub_1, mul_sub, S1] ; apply Summable.tsum_sub
    · have := summable_fourier x (by positivity) ψ ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using this
    · have := summable_fourier x (by positivity) (Ψ R) ⟨_, hcheby⟩
      rw [summable_norm_iff] at this
      simpa using! this
  have S2_sub : S2 x (ψ - Ψ R) = S2 x ψ - S2 x (Ψ R) := by
    simp only [S1_sub_1, S2] ; rw [integral_sub]
    · ring
    · exact ψ.integrable_fourier (by positivity) |>.restrict
    · exact (Ψ R : W21).integrable_fourier (by positivity) |>.restrict
  have S_sub : S x (ψ - Ψ R) = S x ψ - S x (Ψ R) := by simp [S, S1_sub, S2_sub] ; ring
  simpa [S_sub, Ψ] using norm_add_le _ _ |>.trans_lt (_root_.add_lt_add key3 key)
lemma limiting_cor_schwartz (ψ : 𝓢(ℝ, ℂ)) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun x : ℝ ↦ ∑' n, f n / n * 𝓕 (ψ : ℝ → ℂ) (1 / (2 * π) * log (n / x)) -
      A * ∫ u in Set.Ici (-log x), 𝓕 (ψ : ℝ → ℂ) (u / (2 * π))) atTop (𝓝 0) :=
  limiting_cor_W21 ψ hf hcheby hG hG'
lemma fourier_surjection_on_schwartz (f : 𝓢(ℝ, ℂ)) : ∃ g : 𝓢(ℝ, ℂ), 𝓕 g = f := by
  refine ⟨𝓕⁻ f, ?_⟩
  exact FourierTransform.fourier_fourierInv_eq f
noncomputable def toSchwartz (f : ℝ → ℂ) (h1 : ContDiff ℝ ∞ f)
    (h2 : HasCompactSupport f) : 𝓢(ℝ, ℂ) where
  toFun := f
  smooth' := h1
  decay' k n := by
    have l1 : Continuous (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) := by
      have : ContDiff ℝ ∞ (iteratedFDeriv ℝ n f) := h1.iteratedFDeriv_right (mod_cast le_top)
      exact Continuous.mul (by continuity) this.continuous.norm
    have l2 : HasCompactSupport (fun x ↦ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (h2.iteratedFDeriv _).norm.mul_left
    simpa using l1.bounded_above_of_compact_support l2
@[simp] lemma toSchwartz_apply (f : ℝ → ℂ) {h1 h2 x} : SchwartzMap.mk f h1 h2 x = f x := rfl
lemma comp_exp_support0 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in 𝓝 0, Ψ x = 0 :=
  notMem_tsupport_iff_eventuallyEq.mp (fun h => lt_irrefl 0 <| mem_Ioi.mp (hplus h))
lemma comp_exp_support1 {Ψ : ℝ → ℂ} (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    ∀ᶠ x in atBot, Ψ (exp x) = 0 :=
  Real.tendsto_exp_atBot <| comp_exp_support0 hplus
lemma comp_exp_support2 {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ) :
    ∀ᶠ (x : ℝ) in atTop, (Ψ ∘ rexp) x = 0 := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop] at hsupp
  exact Real.tendsto_exp_atTop hsupp.2
theorem comp_exp_support {Ψ : ℝ → ℂ} (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) : HasCompactSupport (Ψ ∘ rexp) := by
  simp only [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  exact ⟨comp_exp_support1 hplus, comp_exp_support2 hsupp⟩
lemma wiener_ikehara_smooth_aux (l0 : Continuous Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) (x : ℝ) (hx : 0 < x) :
    ∫ (u : ℝ) in Ioi (-Real.log x), ↑(rexp u) * Ψ (rexp u) = ∫ (y : ℝ) in Ioi (1 / x), Ψ y := by
  have l1 : ContinuousOn rexp (Ici (-Real.log x)) := by fun_prop
  have l2 : Tendsto rexp atTop atTop := Real.tendsto_exp_atTop
  have l3 t (_ : t ∈ Ioi (-log x)) : HasDerivWithinAt rexp (rexp t) (Ioi t) t :=
    (Real.hasDerivAt_exp t).hasDerivWithinAt
  have l4 : ContinuousOn Ψ (rexp '' Ioi (-Real.log x)) := by fun_prop
  have l5 : IntegrableOn Ψ (rexp '' Ici (-Real.log x)) volume :=
    (l0.integrable_of_hasCompactSupport hsupp).integrableOn
  have l6 : IntegrableOn (fun x ↦ rexp x • (Ψ ∘ rexp) x) (Ici (-Real.log x)) volume := by
    refine (Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_).integrableOn
    change HasCompactSupport (rexp • (Ψ ∘ rexp))
    exact (comp_exp_support hsupp hplus).smul_left
  have := MeasureTheory.integral_deriv_smul_comp_Ioi l1 l2 l3 l4 l5 l6
  simpa [Real.exp_neg, Real.exp_log hx] using this
theorem wiener_ikehara_smooth_sub (h1 : Integrable Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Ioi 0) :
    Tendsto (fun x ↦ (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
  obtain ⟨ε, hε, hh⟩ := Metric.eventually_nhds_iff.mp <| comp_exp_support0 hplus
  apply tendsto_nhds_of_eventually_eq ; filter_upwards [eventually_gt_atTop ε⁻¹] with x hxε
  have l1 : Integrable (indicator (Ioi x⁻¹) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  have l2 : Integrable (indicator (Ioi 0) (fun x : ℝ => Ψ x)) := h1.indicator measurableSet_Ioi
  simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi, ← mul_sub, ← integral_sub l1 l2]
  simp only [mul_eq_zero, ofReal_eq_zero]
  right
  apply MeasureTheory.integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro t
  simp only [Pi.zero_apply]
  have hε' : 0 < ε⁻¹ := by positivity
  have hx : 0 < x := by linarith
  have hx' : 0 < x⁻¹ := by positivity
  have hεx : x⁻¹ < ε := (inv_lt_comm₀ hε hx).mp hxε
  have l3 : Ioi 0 = Ioc 0 x⁻¹ ∪ Ioi x⁻¹ := by
    ext t ; simp only [mem_Ioi, mem_union, mem_Ioc] ; constructor <;> intro h
    · simp [h, le_or_gt]
    · cases h with
      | inl h => exact h.1
      | inr h => exact hx'.trans h
  have l4 : Disjoint (Ioc 0 x⁻¹) (Ioi x⁻¹) := by simp
  have l5 := Set.indicator_union_of_disjoint l4 Ψ
  rw [l3, l5]
  simp only
  rw [add_comm, sub_add_cancel_left]
  by_cases ht : t ∈ Ioc 0 x⁻¹
  · simp only [ht, indicator_of_mem, neg_eq_zero]
    apply hh ; simp only [mem_Ioc, dist_zero_right, norm_eq_abs] at ht ⊢
    apply hεx.trans_le'
    rw [abs_le] ; constructor <;> linarith
  simp [ht]
lemma wiener_ikehara_smooth (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x - A * ∫ y in Set.Ioi 0, Ψ y)
      atTop (𝓝 0) := by
  let h (x : ℝ) : ℂ := rexp (2 * π * x) * Ψ (exp (2 * π * x))
  have h1 : ContDiff ℝ ∞ h := by
    have : ContDiff ℝ ∞ (fun x : ℝ => (rexp (2 * π * x))) := (contDiff_const.mul contDiff_id).exp
    exact (contDiff_ofReal.comp this).mul (hsmooth.comp this)
  have h2 : HasCompactSupport h := by
    have : 2 * π ≠ 0 := by simp [pi_ne_zero]
    simpa using! (comp_exp_support hsupp hplus).comp_smul this |>.mul_left
  obtain ⟨g, hg⟩ := fourier_surjection_on_schwartz (toSchwartz h h1 h2)
  have l1 {y} (hy : 0 < y) : y * Ψ y = 𝓕 g (1 / (2 * π) * Real.log y) := by
    simp only [one_div, mul_inv_rev, hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat,
      toSchwartz_apply, ofReal_inv, h]
    field_simp
    norm_cast
    rw [Real.exp_log hy]
  have key := limiting_cor_schwartz g hf hcheby hG hG'
  have l2 : ∀ᶠ x in atTop, ∑' (n : ℕ), f n / ↑n * 𝓕 g (1 / (2 * π) * Real.log (↑n / x)) =
      ∑' (n : ℕ), f n * Ψ (↑n / x) / x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr ; ext n
    by_cases hn : n = 0
    · simp [hn, (comp_exp_support0 hplus).self_of_nhds]
    rw [← l1 (by positivity)]
    have : (n : ℂ) ≠ 0 := by simpa using hn
    have : (x : ℂ) ≠ 0 := by simpa using hx.ne.symm
    simp only [ofReal_div, ofReal_natCast]
    field_simp
  have l3 : ∀ᶠ x in atTop, ↑A * ∫ (u : ℝ) in Ici (-Real.log x), 𝓕 g (u / (2 * π)) =
      ↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    congr 1
    simp only [hg, toSchwartz, ofReal_exp, ofReal_mul, ofReal_ofNat, toSchwartz_apply,
      ofReal_div, h]
    norm_cast ; field_simp; norm_cast
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    exact wiener_ikehara_smooth_aux hsmooth.continuous hsupp hplus x hx
  have l4 : Tendsto (fun x => (↑A * ∫ (y : ℝ) in Ioi x⁻¹, Ψ y) - ↑A * ∫ (y : ℝ) in Ioi 0, Ψ y)
      atTop (𝓝 0) := by
    exact wiener_ikehara_smooth_sub (hsmooth.continuous.integrable_of_hasCompactSupport hsupp) hplus
  simpa [tsum_div_const] using (key.congr' <| EventuallyEq.sub l2 l3) |>.add l4
lemma wiener_ikehara_smooth' (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ')) (hcheby : cheby f)
    (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) :=
  tendsto_sub_nhds_zero_iff.mp <| wiener_ikehara_smooth hf hcheby hG hG' hsmooth hsupp hplus
local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩
theorem set_integral_ofReal {f : ℝ → ℝ} {s : Set ℝ} : ∫ x in s, (f x : ℂ) = ∫ x in s, f x :=
  integral_ofReal
lemma wiener_ikehara_smooth_real {f : ℕ → ℝ} {Ψ : ℝ → ℝ}
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re})
    (hsmooth : ContDiff ℝ ∞ Ψ) (hsupp : HasCompactSupport Ψ)
    (hplus : closure (Function.support Ψ) ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * Ψ (n / x)) / x) atTop (nhds (A * ∫ y in Set.Ioi 0, Ψ y)) := by
  let Ψ' := ofReal ∘ Ψ
  have l1 : ContDiff ℝ ∞ Ψ' := contDiff_ofReal.comp hsmooth
  have l2 : HasCompactSupport Ψ' := hsupp.comp_left rfl
  have l3 : closure (Function.support Ψ') ⊆ Ioi 0 := by rwa [Function.support_comp_eq] ; simp
  have key := (continuous_re.tendsto _).comp
    (@wiener_ikehara_smooth' A Ψ G f hf hcheby hG hG' l1 l2 l3)
  simp at key ; norm_cast at key
lemma interval_approx_inf (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        ψ ≤ indicator (Ico a b) 1 ∧ b - a - ε ≤ ∫ y in Ioi 0, ψ y := by
  have l1 : Iio ((b - a) / 3) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds <| by
    rw [← sub_pos] at hab
    positivity
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < (b - a) / 3)
  have l2 : a < a + ε / 2 := by simp [hε]
  have l3 : b - ε / 2 < b := by simp [hε]
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · simp [h5, hab.ne, Icc_subset_Ioi_iff hab.le, ha]
  · exact h4.trans <| indicator_le_indicator_of_subset Ioo_subset_Ico_self (by simp)
  · have l4 : 0 ≤ b - a - ε := by linarith
    have l5 : Icc (a + ε / 2) (b - ε / 2) ⊆ Ioi 0 := by
      intro t ht
      simp only [mem_Icc, mem_Ioi] at ht ⊢
      exact ha.trans <| l2.trans_le <| ht.1
    have l6 : Icc (a + ε / 2) (b - ε / 2) ∩ Ioi 0 = Icc (a + ε / 2) (b - ε / 2) :=
      inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Icc (a + ε / 2) (b - ε / 2)) 1 y = b - a - ε := by
      simp only [measurableSet_Icc, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Icc]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7] ; apply setIntegral_mono ?_ l8 h3
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Icc]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp
lemma interval_approx_sup (ha : 0 < a) (hab : a < b) :
    ∀ᶠ ε in 𝓝[>] 0, ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      closure (Function.support ψ) ⊆ Set.Ioi 0 ∧
        indicator (Ico a b) 1 ≤ ψ ∧ ∫ y in Ioi 0, ψ y ≤ b - a + ε := by
  have l1 : Iio (a / 2) ∈ 𝓝[>] 0 := nhdsWithin_le_nhds <| Iio_mem_nhds (by linarith)
  filter_upwards [self_mem_nhdsWithin, l1] with ε (hε : 0 < ε) (hε' : ε < a / 2)
  have l2 : a - ε / 2 < a := by linarith
  have l3 : b < b + ε / 2 := by linarith
  obtain ⟨ψ, h1, h2, h3, h4, h5⟩ := smooth_urysohn_support_Ioo l2 l3
  refine ⟨ψ, h1, h2, ?_, ?_, ?_⟩
  · have l4 : a - ε / 2 < b + ε / 2 := by linarith
    have l5 : ε / 2 < a := by linarith
    simp [h5, l4.ne, Icc_subset_Ioi_iff l4.le, l5]
  · apply le_trans ?_ h3
    apply indicator_le_indicator_of_subset Ico_subset_Icc_self (by simp)
  · have l4 : 0 ≤ b - a + ε := by linarith
    have l5 : Ioo (a - ε / 2) (b + ε / 2) ⊆ Ioi 0 := by intro t ht ; simp at ht ⊢ ; linarith
    have l6 : Ioo (a - ε / 2) (b + ε / 2) ∩ Ioi 0 = Ioo (a - ε / 2) (b + ε / 2) := inter_eq_left.mpr l5
    have l7 : ∫ y in Ioi 0, indicator (Ioo (a - ε / 2) (b + ε / 2)) 1 y = b - a + ε := by
      simp only [measurableSet_Ioo, integral_indicator_one, measureReal_restrict_apply, l6,
        volume_real_Ioo]
      convert max_eq_left l4 using 1 ; ring_nf
    have l8 : IntegrableOn ψ (Ioi 0) volume := (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    rw [← l7]
    refine setIntegral_mono l8 ?_ h4
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo]
    apply IntegrableOn.mono ?_ subset_rfl Measure.restrict_le_self
    apply integrableOn_const <;>
    simp
lemma WI_summable {f : ℕ → ℝ} {g : ℝ → ℝ} (hg : HasCompactSupport g) (hx : 0 < x) :
    Summable (fun n => f n * g (n / x)) := by
  obtain ⟨M, hM⟩ := hg.bddAbove.mono subset_closure
  apply summable_of_hasFiniteSupport
  unfold Function.HasFiniteSupport
  simp only [Function.support_mul] ; apply Finite.inter_of_right ; rw [finite_iff_bddAbove]
  exact ⟨Nat.ceil (M * x), fun i hi => by simpa using Nat.ceil_mono ((div_le_iff₀ hx).mp (hM hi))⟩
lemma WI_sum_le {f : ℕ → ℝ} {g₁ g₂ : ℝ → ℝ} (hf : 0 ≤ f) (hg : g₁ ≤ g₂) (hx : 0 < x)
    (hg₁ : HasCompactSupport g₁) (hg₂ : HasCompactSupport g₂) :
    (∑' n, f n * g₁ (n / x)) / x ≤ (∑' n, f n * g₂ (n / x)) / x := by
  apply div_le_div_of_nonneg_right ?_ hx.le
  exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hg _) (hf _))
    (WI_summable hg₁ hx) (WI_summable hg₂ hx)
lemma WI_sum_Iab_le {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) (hxb : 2 / b < x) :
    (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  have hb' : 0 < 2 / b := by positivity
  have hx : 0 < x := by linarith
  have hxb' : 2 < x * b := (div_lt_iff₀ hb).mp hxb
  have l1 (i : ℕ) (hi : i ∉ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) = 0 := by
    simp_all [le_div_iff₀ hx]
  have l2 (i : ℕ) (_ : i ∈ Finset.range ⌈b * x⌉₊) : f i * indicator (Ico a b) 1 (i / x) ≤ |f i| := by
    rw [abs_eq_self.mpr (hpos _)]
    convert_to _ ≤ f i * 1
    · ring
    apply mul_le_mul_of_nonneg_left ?_ (hpos _)
    by_cases hi : (i / x) ∈ (Ico a b) <;> simp [hi]
  rw [tsum_eq_sum l1, div_le_iff₀ hx, mul_assoc, mul_assoc]
  apply Finset.sum_le_sum l2 |>.trans
  have := hcheby ⌈b * x⌉₊ ; simp only [norm_real, norm_eq_abs] at this ; apply this.trans
  have : 0 ≤ C := by have := hcheby 1 ; simp only [cumsum, Finset.range_one, norm_real,
    Finset.sum_singleton, Nat.cast_one, mul_one] at this ; exact (abs_nonneg _).trans this
  refine mul_le_mul_of_nonneg_left ?_ this
  apply (Nat.ceil_lt_add_one (by positivity)).le.trans
  linarith
lemma WI_sum_Iab_le' {f : ℕ → ℝ} (hpos : 0 ≤ f) {C : ℝ} (hcheby : chebyWith C f) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, (∑' n, f n * indicator (Ico a b) 1 (n / x)) / x ≤ C * 2 * b := by
  filter_upwards [eventually_gt_atTop (2 / b)] with x hx using WI_sum_Iab_le hpos hcheby hb hx
lemma le_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[>] b, a ≤ c) : a ≤ b := by
  apply le_of_forall_gt ; intro d hd
  have key : ∀ᶠ c in 𝓝[>] b, c < d := by
    apply eventually_of_mem (U := Iio d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Iio d, isOpen_Iio, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith
lemma ge_of_eventually_nhdsWithin {a b : ℝ} (h : ∀ᶠ c in 𝓝[<] b, c ≤ a) : b ≤ a := by
  apply le_of_forall_lt ; intro d hd
  have key : ∀ᶠ c in 𝓝[<] b, c > d := by
    apply eventually_of_mem (U := Ioi d) ?_ (fun x hx => hx)
    rw [mem_nhdsWithin]
    refine ⟨Ioi d, isOpen_Ioi, hd, inter_subset_left⟩
  obtain ⟨x, h1, h2⟩ := (h.and key).exists
  linarith
lemma WI_tendsto_aux (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => c / A - (b - a)) (𝓝[>] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [lt_div_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, Real.norm_eq_abs] at hx2 ⊢
    have : |x / A - (b - a)| = |x - A * (b - a)| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA]
lemma WI_tendsto_aux' (a b : ℝ) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun c => (b - a) - c / A) (𝓝[<] (A * (b - a))) (𝓝[>] 0) := by
  rw [Metric.tendsto_nhdsWithin_nhdsWithin]
  intro ε hε
  refine ⟨A * ε, by positivity, ?_⟩
  intro x hx1 hx2
  constructor
  · simpa [div_lt_iff₀' hA]
  · simp only [Real.dist_eq, dist_zero_right, norm_eq_abs] at hx2 ⊢
    have : |(b - a) - x / A| = |A * (b - a) - x| / A := by
      rw [← abs_eq_self.mpr hA.le, ← abs_div, abs_eq_self.mpr hA.le] ; congr ; field_simp
    rwa [this, div_lt_iff₀' hA, ← neg_sub, abs_neg]
theorem residue_nonneg {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm (fun n ↦ ↑(f n)) σ')) (hcheby : cheby fun n ↦ ↑(f n))
    (hG : ContinuousOn G {s | 1 ≤ s.re}) (hG' : EqOn G (fun s ↦ LSeries (fun n ↦ ↑(f n)) s - ↑A / (s - 1)) {s | 1 < s.re}) : 0 ≤ A := by
  let S (g : ℝ → ℝ) (x : ℝ) := (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact div_nonneg (tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))) hx
  obtain ⟨ε, ψ, h1, h2, h3, h4, -⟩ := (interval_approx_sup zero_lt_one one_lt_two).exists
  have key := @wiener_ikehara_smooth_real A G f ψ hf hcheby hG hG' h1 h2 h3
  have l2 : 0 ≤ ψ := by apply le_trans _ h4 ; apply indicator_nonneg ; simp
  have l1 : ∀ᶠ x in atTop, 0 ≤ S ψ x := hSnonneg l2
  have l3 : 0 ≤ A * ∫ (y : ℝ) in Ioi 0, ψ y := ge_of_tendsto key l1
  have l4 : 0 < ∫ (y : ℝ) in Ioi 0, ψ y := by
    have r1 : 0 ≤ᵐ[Measure.restrict volume (Ioi 0)] ψ := Eventually.of_forall l2
    have r2 : IntegrableOn (fun y ↦ ψ y) (Ioi 0) volume :=
      (h1.continuous.integrable_of_hasCompactSupport h2).integrableOn
    have r3 : Ico 1 2 ⊆ Function.support ψ := by intro x hx ; have := h4 x ; simp [hx] at this ⊢ ; linarith
    have r4 : Ico 1 2 ⊆ Function.support ψ ∩ Ioi 0 := by
      simp only [subset_inter_iff, r3, true_and] ; apply Ico_subset_Icc_self.trans ; rw [Icc_subset_Ioi_iff] <;> linarith
    have r5 : 1 ≤ volume ((Function.support fun y ↦ ψ y) ∩ Ioi 0) := by convert! volume.mono r4 ; norm_num
    simpa [setIntegral_pos_iff_support_of_nonneg_ae r1 r2] using! zero_lt_one.trans_le r5
  have := div_nonneg l3 l4.le ; field_simp at this ; exact this
lemma WienerIkeharaInterval {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑' n, f n * (indicator (Ico a b) 1 (n / x))) / x) atTop (nhds (A * (b - a))) := by
  by_cases hab : a = b
  · simp [hab]
  replace hb : a < b := lt_of_le_of_ne hb hab ; clear hab
  let S (g : ℝ → ℝ) (x : ℝ) :=  (∑' n, f n * g (n / x)) / x
  have hSnonneg {g : ℝ → ℝ} (hg : 0 ≤ g) : ∀ᶠ x : ℝ in atTop, 0 ≤ S g x := by
    filter_upwards [eventually_ge_atTop 0] with x hx
    refine div_nonneg ?_ hx
    refine tsum_nonneg (fun i => mul_nonneg (hpos _) (hg _))
  have hA : 0 ≤ A := residue_nonneg hpos hf hcheby hG hG'
  let Iab : ℝ → ℝ := indicator (Ico a b) 1
  change Tendsto (S Iab) atTop (𝓝 (A * (b - a)))
  have hIab : HasCompactSupport Iab := by simpa [Iab, HasCompactSupport, tsupport, hb.ne] using isCompact_Icc
  have Iab_nonneg : ∀ᶠ x : ℝ in atTop, 0 ≤ S Iab x := hSnonneg (indicator_nonneg (by simp))
  have Iab2 : IsBoundedUnder (· ≤ ·) atTop (S Iab) := by
    obtain ⟨C, hC⟩ := hcheby ; exact ⟨C * 2 * b, WI_sum_Iab_le' hpos hC (by linarith)⟩
  have Iab3 : IsBoundedUnder (· ≥ ·) atTop (S Iab) := ⟨0, Iab_nonneg⟩
  have Iab0 : IsCoboundedUnder (· ≥ ·) atTop (S Iab) := Iab2.isCoboundedUnder_ge
  have Iab1 : IsCoboundedUnder (· ≤ ·) atTop (S Iab) := Iab3.isCoboundedUnder_le
  have sup_le : limsup (S Iab) atTop ≤ A * (b - a) := by
    have l_sup : ∀ᶠ ε in 𝓝[>] 0, limsup (S Iab) atTop ≤ A * (b - a + ε) := by
      filter_upwards [interval_approx_sup ha hb] with ε ⟨ψ, h1, h2, h3, h4, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l6 : S Iab ≤ᶠ[atTop] S ψ := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h4 hx hIab h2
      have l5 : IsBoundedUnder (· ≤ ·) atTop (S ψ) := l1.isBoundedUnder_le
      have l3 : limsup (S Iab) atTop ≤ limsup (S ψ) atTop := limsup_le_limsup l6 Iab1 l5
      apply l3.trans ; rw [l1.limsup_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_sup
    apply le_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux a b key l_sup] with x hx
    simpa [mul_div_cancel₀ _ h] using hx
  have le_inf : A * (b - a) ≤ liminf (S Iab) atTop := by
    have l_inf : ∀ᶠ ε in 𝓝[>] 0, A * (b - a - ε) ≤ liminf (S Iab) atTop := by
      filter_upwards [interval_approx_inf ha hb] with ε ⟨ψ, h1, h2, h3, h5, h6⟩
      have l1 : Tendsto (S ψ) atTop _ := wiener_ikehara_smooth_real hf hcheby hG hG' h1 h2 h3
      have l2 : S ψ ≤ᶠ[atTop] S Iab := by
        filter_upwards [eventually_gt_atTop 0] with x hx using WI_sum_le hpos h5 hx h2 hIab
      have l4 : IsBoundedUnder (· ≥ ·) atTop (S ψ) := l1.isBoundedUnder_ge
      have l3 : liminf (S ψ) atTop ≤ liminf (S Iab) atTop := liminf_le_liminf l2 l4 Iab0
      apply le_trans ?_ l3 ; rw [l1.liminf_eq] ; gcongr
    obtain rfl | h := eq_or_ne A 0
    · simpa using l_inf
    apply ge_of_eventually_nhdsWithin
    have key : 0 < A := lt_of_le_of_ne hA h.symm
    filter_upwards [WI_tendsto_aux' a b key l_inf] with x hx
    simpa [mul_div_cancel₀ _ h] using hx
  have : liminf (S Iab) atTop ≤ limsup (S Iab) atTop := liminf_le_limsup Iab2 Iab3
  refine tendsto_of_liminf_eq_limsup ?_ ?_ Iab2 Iab3 <;> linarith
lemma le_floor_mul_iff (hb : 0 ≤ b) (hx : 0 < x) : n ≤ ⌊b * x⌋₊ ↔ n / x ≤ b := by
  rw [div_le_iff₀ hx, Nat.le_floor_iff] ; positivity
lemma lt_ceil_mul_iff (hx : 0 < x) : n < ⌈b * x⌉₊ ↔ n / x < b := by
  rw [div_lt_iff₀ hx, Nat.lt_ceil]
lemma ceil_mul_le_iff (hx : 0 < x) : ⌈a * x⌉₊ ≤ n ↔ a ≤ n / x := by
  rw [le_div_iff₀ hx, Nat.ceil_le]
lemma mem_Icc_iff_div (hb : 0 ≤ b) (hx : 0 < x) : n ∈ Finset.Icc ⌈a * x⌉₊ ⌊b * x⌋₊ ↔ n / x ∈ Icc a b := by
  rw [Finset.mem_Icc, mem_Icc, ceil_mul_le_iff hx, le_floor_mul_iff hb hx]
lemma mem_Ico_iff_div (hx : 0 < x) : n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊ ↔ n / x ∈ Ico a b := by
  rw [Finset.mem_Ico, mem_Ico, ceil_mul_le_iff hx, lt_ceil_mul_iff hx]
lemma tsum_indicator {f : ℕ → ℝ} (hx : 0 < x) :
    ∑' n, f n * (indicator (Ico a b) 1 (n / x)) = ∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n := by
  have l1 : ∀ n ∉ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n * indicator (Ico a b) 1 (↑n / x) = 0 := by
    simp [mem_Ico_iff_div hx] ; tauto
  rw [tsum_eq_sum l1] ; apply Finset.sum_congr rfl ; simp only [mem_Ico_iff_div hx] ; intro n hn ; simp [hn]
lemma WienerIkeharaInterval_discrete {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Ico ⌈a * x⌉₊ ⌈b * x⌉₊, f n) / x) atTop (nhds (A * (b - a))) := by
  apply (WienerIkeharaInterval hpos hf hcheby hG hG' ha hb).congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [tsum_indicator hx]
lemma WienerIkeharaInterval_discrete' {f : ℕ → ℝ} (hpos : 0 ≤ f) (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) (ha : 0 < a) (hb : a ≤ b) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ Finset.Ico ⌈a * N⌉₊ ⌈b * N⌉₊, f n) / N) atTop (nhds (A * (b - a))) :=
  WienerIkeharaInterval_discrete hpos hf hcheby hG hG' ha hb |>.comp tendsto_natCast_atTop_atTop
lemma tendsto_mul_ceil_div :
    Tendsto (fun (p : ℝ × ℕ) => ⌈p.1 * p.2⌉₊ / (p.2 : ℝ)) (𝓝[>] 0 ×ˢ atTop) (𝓝 0) := by
  rw [Metric.tendsto_nhds] ; intro δ hδ
  have l1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo 0 (δ / 2) := inter_mem_nhdsWithin _ (Iio_mem_nhds (by positivity))
  have l2 : ∀ᶠ N : ℕ in atTop, 1 ≤ δ / 2 * N := by
    apply Tendsto.eventually_ge_atTop
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  filter_upwards [l1.prod_mk l2] with (ε, N) ⟨⟨hε, h1⟩, h2⟩ ; dsimp only at *
  have l3 : 0 < (N : ℝ) := by
    simp only [Nat.cast_pos, Nat.pos_iff_ne_zero] ; rintro rfl ; simp [zero_lt_one.not_ge] at h2
  have l5 : 0 ≤ ε * ↑N := by positivity
  have l6 : ε * N ≤ δ / 2 * N := mul_le_mul h1.le le_rfl (by positivity) (by positivity)
  simp only [dist_zero_right, norm_div, RCLike.norm_natCast, div_lt_iff₀ l3, gt_iff_lt]
  convert (Nat.ceil_lt_add_one l5).trans_le (add_le_add l6 h2) using 1 ; ring
noncomputable def S (f : ℕ → 𝕜) (ε : ℝ) (N : ℕ) : 𝕜 := (∑ n ∈ Finset.Ico ⌈ε * N⌉₊ N, f n) / N
lemma S_sub_S {f : ℕ → 𝕜} {ε : ℝ} {N : ℕ} (hε : ε ≤ 1) : S f 0 N - S f ε N = cumsum f ⌈ε * N⌉₊ / N := by
  have hceilN : ⌈ε * N⌉₊ ≤ N := by
    simp only [Nat.ceil_le]
    exact mul_le_of_le_one_left N.cast_nonneg hε
  have r1 : Finset.range N = Finset.range ⌈ε * N⌉₊ ∪ Finset.Ico ⌈ε * N⌉₊ N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have r2 : Disjoint (Finset.range ⌈ε * N⌉₊) (Finset.Ico ⌈ε * N⌉₊ N) := by
    rw [Finset.range_eq_Ico] ; apply Finset.Ico_disjoint_Ico_consecutive
  simp [S, r1, Finset.sum_union r2, cumsum, add_div]
lemma tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f) (hcheby : cheby f) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by
  rw [Metric.tendstoUniformlyOnFilter_iff] ; intro δ hδ
  obtain ⟨C, hC⟩ := hcheby
  have l1 : ∀ᶠ (p : ℝ × ℕ) in 𝓝[>] 0 ×ˢ atTop, C * ⌈p.1 * p.2⌉₊ / p.2 < δ := by
    have r1 := tendsto_mul_ceil_div.const_mul C
    simp only [mul_div_assoc', mul_zero] at r1 ; exact r1 (Iio_mem_nhds hδ)
  have : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
  filter_upwards [l1, Eventually.prod_inl this _] with (ε, N) h1 h2
  have l2 : ‖cumsum f ⌈ε * ↑N⌉₊ / ↑N‖ ≤ C * ⌈ε * N⌉₊ / N := by
    have r1 := hC ⌈ε * N⌉₊
    have r2 : 0 ≤ cumsum f ⌈ε * N⌉₊ := by apply cumsum_nonneg hpos
    simp only [norm_real, norm_of_nonneg (hpos _), norm_div,
      norm_of_nonneg r2, Real.norm_natCast] at r1 ⊢
    apply div_le_div_of_nonneg_right r1 (by positivity)
  simpa [← S_sub_S h2.2] using! l2.trans_lt h1
theorem WienerIkeharaTheorem' {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hf : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm f σ'))
    (hcheby : cheby f) (hG : ContinuousOn G {s | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s ↦ LSeries f s - A / (s - 1)) {s | 1 < s.re}) :
    Tendsto (fun N => cumsum f N / N) atTop (𝓝 A) := by
  convert_to Tendsto (S f 0) atTop (𝓝 A) ; · ext N ; simp [S, cumsum]
  apply (tendsto_S_S_zero hpos hcheby).tendsto_of_eventually_tendsto
  · have L0 : Ioc 0 1 ∈ 𝓝[>] (0 : ℝ) := inter_mem_nhdsWithin _ (Iic_mem_nhds zero_lt_one)
    apply eventually_of_mem L0
    · intro ε hε
      simpa using! WienerIkeharaInterval_discrete' hpos hf hcheby hG hG' hε.1 hε.2
  · have : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa using (this.const_sub 1).const_mul A
theorem vonMangoldt_cheby : cheby Λ := by
  use Real.log 4 + 4
  intro N
  by_cases! h : N = 0
  · simp [h, cumsum]
  simp only [cumsum, norm_real, norm_eq_abs]
  rw [Nat.range_eq_Icc_zero_sub_one _ h, (by simp : N - 1 = ⌊(N : ℝ) - 1⌋₊)]
  simp_rw [abs_of_nonneg vonMangoldt_nonneg]
  rw [← Chebyshev.psi_eq_sum_Icc]
  grw [Chebyshev.psi_le_const_mul_self <| sub_nonneg_of_le <| Nat.one_le_cast_iff_ne_zero.mpr h]
  gcongr
  linarith
theorem WeakPNT : Tendsto (fun N ↦ cumsum Λ N / N) atTop (𝓝 1) := by
  let F := vonMangoldt.LFunctionResidueClassAux (q := 1) 1
  have hnv := riemannZeta_ne_zero_of_one_le_re
  have l1 (n : ℕ) : 0 ≤ Λ n := vonMangoldt_nonneg
  have l2 s (hs : 1 < s.re) : F s = LSeries Λ s - 1 / (s - 1) := by
    have := vonMangoldt.eqOn_LFunctionResidueClassAux (q := 1) isUnit_one hs
    simp only [F, this, vonMangoldt.residueClass, Nat.totient_one, Nat.cast_one, inv_one, one_div, sub_left_inj]
    apply LSeries_congr
    intro n _
    simp only [ofReal_inj, indicator_apply_eq_self, mem_setOf_eq]
    exact fun hn ↦ absurd (Subsingleton.eq_one _) hn
  have l3 : ContinuousOn F {s | 1 ≤ s.re} := vonMangoldt.continuousOn_LFunctionResidueClassAux 1
  have l4 : cheby Λ := vonMangoldt_cheby
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm Λ σ') := by
    simpa only [← nterm_eq_norm_term] using (@ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ').norm
  apply WienerIkeharaTheorem' l1 l5 l4 l3 l2
end

section
open ArithmeticFunction hiding log
open Nat hiding log
open Finset
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev
theorem Asymptotics.IsEquivalent.add_isLittleO'' {α : Type*} {β : Type*} [NormedAddCommGroup β]
    {u : α → β} {v : α → β} {w : α → β} {l : Filter α}
    (huv : Asymptotics.IsEquivalent l u v) (hwu : (u - w) =o[l] v) :
    Asymptotics.IsEquivalent l w v := by
  rw [← sub_sub_self u w]
  exact sub_isLittleO huv hwu
theorem WeakPNT' : Tendsto (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) atTop (nhds 1) := by
  have : (fun N ↦ (∑ n ∈ Iic N, Λ n) / N) =
      (fun N ↦ (∑ n ∈ range N, Λ n)/N + Λ N / N) := by
    ext N
    have : N ∈ Iic N := mem_Iic.mpr (le_refl _)
    rw [← Finset.sum_erase_add _ _ this, ← Nat.Iio_eq_range, Iic_erase]
    exact add_div _ _ _
  rw [this, ← add_zero 1]
  apply Tendsto.add WeakPNT
  convert squeeze_zero (f := fun N ↦ Λ N / N) (g := fun N ↦ log N / N) (t₀ := atTop) ?_ ?_ ?_
  · intro N
    exact div_nonneg vonMangoldt_nonneg (cast_nonneg N)
  · intro N
    exact div_le_div_of_nonneg_right vonMangoldt_le_log (cast_nonneg N)
  have h := (isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1)).tendsto_div_nhds_zero
  simpa [Function.comp_def] using h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
theorem WeakPNT'' : ψ ~[atTop] (fun x ↦ x) := by
    rw [(by rfl : ψ = (fun x ↦ ψ x))]
    simp_rw [Chebyshev.psi_eq_sum_Icc]
    apply IsEquivalent.trans (v := fun x ↦ (⌊x⌋₊:ℝ))
    · rw [isEquivalent_iff_tendsto_one]
      · convert! Tendsto.comp WeakPNT' tendsto_nat_floor_atTop
        infer_instance
      rw [eventually_iff]
      simp only [ne_eq, cast_eq_zero, floor_eq_zero, not_lt, mem_atTop_sets,
        Set.mem_setOf_eq]
      use 1
      simp only [imp_self, implies_true]
    apply IsLittleO.isEquivalent
    rw [← isLittleO_neg_left]
    apply IsLittleO.of_bound
    intro ε hε
    simp only [Pi.sub_apply, neg_sub, norm_eq_abs, eventually_atTop]
    use ε⁻¹
    intro b hb
    have hb' : 0 ≤ b := le_of_lt (lt_of_lt_of_le (inv_pos_of_pos hε) hb)
    rw [abs_of_nonneg, abs_of_nonneg hb']
    · apply LE.le.trans _ ((inv_le_iff_one_le_mul₀' hε).mp hb)
      linarith [Nat.lt_floor_add_one b]
    rw [sub_nonneg]
    exact floor_le hb'
lemma isLittleO_sqrt_mul_log : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] _root_.id := by
  have : (fun x : ℝ ↦ x.sqrt * x.log) =o[atTop] fun x ↦ x := by
    refine (isLittleO_mul_iff_isLittleO_div ?_).mpr ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx; exact (sqrt_ne_zero hx.le).mpr hx.ne'
    · convert! isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) using 2 with x
      rw [div_sqrt, sqrt_eq_rpow]
  exact this
theorem chebyshev_asymptotic : θ ~[atTop] id := by
  refine WeakPNT''.add_isLittleO'' (IsBigO.trans_isLittleO (g := fun x ↦ 2 * x.sqrt * x.log) ?_ ?_)
  · rw [isBigO_iff']; refine ⟨1, one_pos, ?_⟩
    simp only [one_mul, eventually_atTop]
    exact ⟨2, fun x hx ↦ by
      rw [Pi.sub_apply, norm_eq_abs, norm_eq_abs, abs_of_nonneg (by bound : 0 ≤ 2 * √x * log x)]
      exact (abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))).symm ▸
        Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)⟩
  · simpa only [mul_assoc] using! isLittleO_sqrt_mul_log.const_mul_left 2
end

section
open Finset Nat Filter Real Asymptotics
open scoped Topology Chebyshev
namespace ZZAsym
noncomputable section
def lo (k : ℕ) : ℝ := 3 / (3*k+2)
def hi (k : ℕ) : ℝ := 2 / (2*k+1)
def block (n k : ℕ) := primesLE ⌊hi k*n⌋₊ \ primesLE ⌊lo k*n⌋₊
lemma ends (k : ℕ) : 0 < lo k ∧ lo k < hi k := by
  unfold lo hi; constructor
  · positivity
  · apply (div_lt_div_iff₀ (by positivity) (by positivity)).2; linarith
lemma memb {n k p : ℕ} : p ∈ block n k ↔ p.Prime ∧ (3*k+2)*p > 3*n ∧ (2*k+1)*p ≤ 2*n := by
  have ha := ends k
  simp only [block, Finset.mem_sdiff, mem_primesLE, Nat.le_floor_iff (mul_nonneg ha.1.le (by positivity : (0:ℝ) ≤ n)), Nat.le_floor_iff (mul_nonneg (ha.1.trans ha.2).le (by positivity : (0:ℝ) ≤ n))]
  have l : (p:ℝ) ≤ lo k * n ↔ (3*k+2)*p ≤ 3*n := by
    unfold lo; rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm (p:ℝ)]; norm_cast
  have h : (p:ℝ) ≤ hi k * n ↔ (2*k+1)*p ≤ 2*n := by
    unfold hi; rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm (p:ℝ)]; norm_cast
  rw [l,h]; grind
lemma blockIndex {n k p : ℕ} (hp : p ∈ block n k) : n / p = k := by
  obtain ⟨h,a,b⟩ := memb.mp hp
  apply Nat.div_eq_of_lt_le <;> nlinarith [h.pos]
lemma blockSub (k : ℕ) : ∀ᶠ n : ℕ in atTop, block n k ⊆ ZZDen.primes n := by
  filter_upwards [eventually_ge_atTop ((3*k+6)^2)] with n hn p hp
  obtain ⟨h,a,b⟩ := memb.mp hp
  have hpgt : 3*k+5 < p := by by_contra! hc; nlinarith [Nat.mul_le_mul_left (3*k+2) hc]
  have hi' := blockIndex hp
  have eqn := Nat.mod_add_div n p
  rw [hi'] at eqn
  simp only [ZZDen.primes,mem_filter,mem_range]
  refine ⟨by nlinarith, h, by omega, by nlinarith [Nat.mul_le_mul_right p (show 3*k+2 ≤ p by omega)], ?_, ?_⟩ <;> nlinarith
lemma logblock (n k : ℕ) : ∑ p ∈ block n k, Real.log p = θ (hi k*n) - θ (lo k*n) := by
  rw [eq_sub_iff_add_eq, Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
  apply Finset.sum_sdiff
  intro p hp
  rw [mem_primesLE] at hp ⊢
  exact ⟨hp.1.trans (Nat.floor_mono (mul_le_mul_of_nonneg_right (ends k).2.le (by positivity))), hp.2⟩
lemma scaled (f : ℝ → ℝ) (hf : f ~[atTop] id) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ f (c*n) / n) atTop (𝓝 c) := by
  have h := (isEquivalent_iff_tendsto_one (u := f) (v := id) (by filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx using hx.ne')).mp hf
  have hc' := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hc
  convert (h.comp hc').mul_const c using 1
  · ext n; change _ = f (c*n)/(c*n)*c; rw [div_mul_eq_div_div_swap, div_mul_cancel₀ _ hc.ne']
  · simp
lemma lcmEq (n : ℕ) : ZZDen.lcm4 n = Nat.lcmUpto (4*n) := by
  apply Nat.dvd_antisymm <;> apply Finset.lcm_dvd
  · intro i hi; exact Finset.dvd_lcm (f := id) (b := i+1) (by simp_all [mem_range, mem_Icc] <;> omega)
  · intro i hi; obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by simp_all [mem_Icc] <;> omega : i≠0); exact Finset.dvd_lcm (b := j) (by simp_all [mem_range, mem_Icc] <;> omega)
def S (K : ℕ) : ℝ := ∑ k ∈ range K, (hi k - lo k)
def mass (n K : ℕ) : ℝ := ∑ k ∈ range K, (θ (hi k*n) - θ (lo k*n))
lemma massLim (K : ℕ) : Tendsto (fun n : ℕ ↦ mass n K / n) atTop (𝓝 (S K)) := by
  unfold mass S; simp_rw [Finset.sum_div,sub_div]
  exact tendsto_finsetSum _ fun k _ ↦ (scaled _ chebyshev_asymptotic ((ends k).1.trans (ends k).2)).sub (scaled _ chebyshev_asymptotic (ends k).1)
lemma phiMass (K : ℕ) : ∀ᶠ n : ℕ in atTop, mass n K ≤ Real.log (ZZDen.phi n) := by
  filter_upwards [(eventually_all_finset (range K)).mpr (fun k _ ↦ blockSub k)] with n hn
  unfold mass ZZDen.phi
  rw [Nat.cast_prod, Real.log_prod]
  · simp_rw [← logblock]
    rw [← sum_biUnion]
    · apply sum_le_sum_of_subset_of_nonneg
      · exact biUnion_subset.mpr hn
      · intro p hp _; exact Real.log_nonneg (by exact_mod_cast (show p.Prime from (mem_filter.mp hp).2.1).one_le)
    · intro k _ j _ h; apply disjoint_left.mpr; intro p hp hq; exact h ((blockIndex hp).symm.trans (blockIndex hq))
  · intro p hp; exact_mod_cast (show p.Prime from (mem_filter.mp hp).2.1).ne_zero
lemma psiLim : Tendsto (fun n : ℕ ↦ Real.log (ZZDen.lcm4 n) / n) atTop (𝓝 4) := by
  simp_rw [lcmEq, ← Chebyshev.psi_eq_log_lcmUpto, Nat.cast_mul, Nat.cast_ofNat]; exact scaled _ WeakPNT'' (by norm_num)
lemma eventualUpper {C : ℝ} {K : ℕ} (hC : 4 - S K < C) (hpos : 0 < C) :
    ∀ᶠ n : ℕ in atTop, Real.log (ZZDen.L n) / n < C := by
  have hh := (psiLim.sub (massLim K)).eventually_lt_const hC
  filter_upwards [hh, phiMass K, eventually_gt_atTop (0:ℕ)] with n h hn hnp
  have hn' : 0 < (n:ℝ) := by positivity
  by_cases hL : ZZDen.L n = 0
  · simpa [hL] using hpos
  have hphi : ZZDen.phi n ≠ 0 := by intro hz; exact hL (by simp [ZZDen.L,hz])
  have hl := Nat.div_mul_le_self (ZZDen.lcm4 n) (ZZDen.phi n)
  change ZZDen.L n * ZZDen.phi n ≤ ZZDen.lcm4 n at hl
  have hl' : (ZZDen.L n:ℝ) * ZZDen.phi n ≤ ZZDen.lcm4 n := by exact_mod_cast hl
  have ht := Real.log_le_log (by positivity : 0 < (ZZDen.L n:ℝ) * ZZDen.phi n) hl'
  rw [Real.log_mul (by exact_mod_cast hL) (by exact_mod_cast hphi)] at ht
  exact lt_of_le_of_lt (by rw [← sub_div]; apply div_le_div_of_nonneg_right _ hn'.le; linarith) h
end
end ZZAsym
end

section
open Filter Real
namespace ZZFourteen
lemma ev_le {K x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) : ∀ᶠ n : ℕ in atTop, K * x^n ≤ y^n := by
  have hy : 0 < y := hx.trans_lt hxy
  have h : Tendsto (fun n : ℕ => (x/y)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hx hy.le) ((div_lt_one hy).2 hxy)
  filter_upwards [(h.const_mul K).eventually (gt_mem_nhds (show K*0 < 1 by simp))] with n hn
  rw [div_pow, mul_div_assoc'] at hn
  exact ((div_lt_one (pow_pos hy n)).1 hn).le
lemma L_le {C : ℝ} (hC : 4 < C) : ∀ᶠ n : ℕ in atTop, (ZZDen.L n : ℝ) ≤ exp C ^ n := by
  filter_upwards [ZZAsym.psiLim.eventually_lt_const hC, eventually_gt_atTop 0] with n h hn
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hl0 : ZZDen.lcm4 n ≠ 0 := Finset.lcm_ne_zero_iff.mpr (by simp)
  have hl : 0 < (ZZDen.lcm4 n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hl0
  have h1 : (ZZDen.L n : ℝ) ≤ ZZDen.lcm4 n := by exact_mod_cast Nat.div_le_self _ _
  have h2 : log (ZZDen.lcm4 n) < n * C := by rw [div_lt_iff₀ hn'] at h; linarith
  calc (ZZDen.L n:ℝ) ≤ ZZDen.lcm4 n := h1
    _ = exp (log (ZZDen.lcm4 n)) := (exp_log hl).symm
    _ ≤ exp (n * C) := exp_le_exp.2 h2.le
    _ = exp C ^ n := exp_nat_mul C n
noncomputable def a (n : ℕ) : ℤ := (ZZSigned.normalized (n+1) n.succ_pos).choose
noncomputable def b (n : ℕ) : ℤ := (ZZSigned.normalized (n+1) n.succ_pos).choose_spec.choose
lemma ab (n : ℕ) : ZZForm.scale (n+1) * ZZSigned.u (n+1) = a n ∧
    ZZForm.scale (n+1) * ZZSigned.v (n+1) = b n :=
  have h := (ZZSigned.normalized (n+1) n.succ_pos).choose_spec.choose_spec
  ⟨h.1, h.2.1⟩
lemma scale_eq (m : ℕ) : (ZZForm.scale m : ℝ) * (2:ℝ)^(5*m/2) = 4 * ZZDen.L m := by
  unfold ZZForm.scale; push_cast; field_simp
lemma scale_nonneg (m : ℕ) : 0 ≤ (ZZForm.scale m : ℝ) := by
  unfold ZZForm.scale; push_cast; positivity
lemma scale_le (m : ℕ) : (ZZForm.scale m : ℝ) ≤ 4 * ZZDen.L m := by
  rw [← scale_eq]
  exact le_mul_of_one_le_right (scale_nonneg m) (one_le_pow₀ (by norm_num))
lemma scale_sq (m : ℕ) : (ZZForm.scale m : ℝ)^2 * (32:ℝ)^m ≤ 2 * (4 * ZZDen.L m)^2 := by
  rw [← scale_eq, mul_pow, ← pow_mul]
  have hk : 5*m ≤ (5*m/2)*2 + 1 := by omega
  have hp : (32:ℝ)^m ≤ 2 * (2:ℝ)^(5*m/2*2) := by
    calc (32:ℝ)^m = 2^(5*m) := by rw [pow_mul]; norm_num
      _ ≤ 2^((5*m/2)*2+1) := pow_le_pow_right₀ (by norm_num) hk
      _ = _ := by rw [pow_succ]; ring
  have := mul_le_mul_of_nonneg_left hp (sq_nonneg (ZZForm.scale m : ℝ))
  linarith
lemma real_form (m : ℕ) : ‖ZZSegment.integral m‖ = |(ZZSigned.u m : ℝ) + ZZSigned.v m * π| := by
  rw [ZZSigned.form, show ((ZZSigned.u m : ℂ) + (ZZSigned.v m : ℂ) * (π:ℂ)) =
    (((ZZSigned.u m : ℝ) + (ZZSigned.v m : ℝ) * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs]
lemma exp21 : exp 21 < 1024 / (0.0295:ℝ)^4 := by
  have h := Real.exp_one_lt_d9
  rw [show (21:ℝ) = ((21:ℕ):ℝ) by norm_num, ← Real.exp_one_pow]
  calc exp 1 ^ 21 < (2.7182818286:ℝ)^21 := pow_lt_pow_left₀ h (exp_pos 1).le (by norm_num)
    _ < _ := by norm_num
lemma exp10 : (21900:ℝ) < exp 10 := by
  have h := Real.exp_one_gt_d9
  rw [show (10:ℝ) = ((10:ℕ):ℝ) by norm_num, ← Real.exp_one_pow]
  calc (21900:ℝ) < (2.7182818283:ℝ)^10 := by norm_num
    _ < exp 1 ^ 10 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
lemma hb : ∀ᶠ n : ℕ in atTop, |(b n : ℝ)| ≤ exp (14.1 * n) := by
  obtain ⟨t, ht, hp, -⟩ := ZZRate.certified_root
  have htR : t < 21900 := by have := ht.2; norm_num [ZZRate.hi] at this; linarith
  have hlt : exp 4.05 * 21900 < exp 14.1 := by
    rw [show (14.1:ℝ) = 4.05 + 10.05 by norm_num, exp_add]
    exact mul_lt_mul_of_pos_left (exp10.trans (exp_lt_exp.2 (by norm_num))) (exp_pos _)
  have hv := ZZSigned.pi_growth ht hp htR
  have hL := L_le (C := 4.05) (by norm_num)
  have hv' := (tendsto_add_atTop_nat 1).eventually hv
  have hL' := (tendsto_add_atTop_nat 1).eventually hL
  filter_upwards [hv', hL', ev_le (K := 4 * (exp 4.05 * 21900)) (by positivity) hlt] with n h1 h2 h3
  have e := (ab n).2
  have eR : (b n : ℝ) = (ZZForm.scale (n+1) : ℝ) * (ZZSigned.v (n+1) : ℝ) := by
    have e' := congrArg (fun r : ℚ => (r:ℝ)) e
    push_cast at e'; rw [← e']
  rw [eR, abs_mul, abs_of_nonneg (scale_nonneg _), mul_comm (14.1:ℝ), exp_nat_mul]
  calc (ZZForm.scale (n+1) : ℝ) * |(ZZSigned.v (n+1) : ℝ)|
      ≤ (4 * exp 4.05 ^ (n+1)) * 21900^(n+1) := by
        apply mul_le_mul _ h1 (abs_nonneg _) (by positivity)
        exact (scale_le _).trans (by linarith)
    _ = 4 * (exp 4.05 * 21900) * (exp 4.05 * 21900)^n := by ring
    _ ≤ _ := h3
lemma hf : ∀ᶠ n : ℕ in atTop, |(a n : ℝ) + b n * π| ≤ exp (-1.2 * n) := by
  obtain ⟨t, ht, hp, hroot⟩ := ZZRate.certified_root
  have hR : Real.sqrt (2048/(108*t)) < 0.0295 := by linarith [hroot.2]
  have hI := ZZApply.integral_stable_rate ht hp hR (by norm_num)
  have hL := L_le (C := 4.05) (by norm_num)
  set x : ℝ := exp 4.05 ^ 2 * 0.0295^2 / 32
  set y : ℝ := exp (-1.2) ^ 2
  have hxy : x < y := by
    simp only [x, y]
    rw [div_lt_iff₀ (by norm_num)]
    have w0 : 0 ≤ exp 10.5 * 0.0295^2 := by positivity
    have w : exp 10.5 * 0.0295^2 < 32 := by
      have hw : (exp 10.5 * 0.0295^2)^2 < 32^2 := by
        rw [mul_pow, ← exp_nat_mul]
        norm_num
        have := exp21
        rw [lt_div_iff₀ (by norm_num)] at this
        norm_num at this
        linarith
      exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hw
    have e1 : exp 4.05 ^ 2 = exp 10.5 * exp (-1.2) ^ 2 := by
      rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add]; norm_num
    rw [e1]
    have hpos : 0 < exp (-1.2) ^ 2 := by positivity
    nlinarith
  have hI' := (tendsto_add_atTop_nat 1).eventually hI
  have hL' := (tendsto_add_atTop_nat 1).eventually hL
  filter_upwards [hI', hL', ev_le (K := 32 * x) (by positivity) hxy] with n h1 h2 h3
  have e := ab n
  set s : ℝ := (ZZForm.scale (n+1) : ℝ)
  have eR : (a n : ℝ) + b n * π = s * ((ZZSigned.u (n+1) : ℝ) + ZZSigned.v (n+1) * π) := by
    have e1 := congrArg (fun r : ℚ => (r:ℝ)) e.1
    have e2 := congrArg (fun r : ℚ => (r:ℝ)) e.2
    push_cast at e1 e2; rw [← e1, ← e2]; ring
  have s0 : 0 ≤ s := scale_nonneg _
  have hle : |(a n : ℝ) + b n * π| ≤ s * 0.0295^(n+1) := by
    rw [eR, abs_mul, abs_of_nonneg s0, ← real_form]
    exact mul_le_mul_of_nonneg_left h1 s0
  refine hle.trans ?_
  apply le_of_pow_le_pow_left₀ two_ne_zero (exp_pos _).le
  have hsq := scale_sq (n+1)
  have hL2 : (4 * (ZZDen.L (n+1) : ℝ))^2 ≤ (4 * exp 4.05 ^ (n+1))^2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h32 : 0 < (32:ℝ)^(n+1) := by positivity
  have hs2 : s^2 ≤ 32 * exp 4.05 ^ (2*(n+1)) / 32^(n+1) := by
    rw [le_div_iff₀ h32]
    calc s^2 * 32^(n+1) ≤ 2 * (4 * (ZZDen.L (n+1) : ℝ))^2 := hsq
      _ ≤ 2 * (4 * exp 4.05 ^ (n+1))^2 := by linarith
      _ = _ := by ring
  have hy : exp (-1.2 * n) ^ 2 = y^n := by
    simp only [y]; rw [← exp_nat_mul, ← exp_nat_mul, ← exp_nat_mul]; ring_nf
  rw [hy, mul_pow, ← pow_mul]
  calc s^2 * 0.0295^((n+1)*2) ≤ 32 * exp 4.05 ^ (2*(n+1)) / 32^(n+1) * 0.0295^((n+1)*2) :=
        mul_le_mul_of_nonneg_right hs2 (by positivity)
    _ = 32 * x * x^n := by
        rw [show 32*x*x^n = 32 * x^(n+1) by ring, show (n+1)*2 = 2*(n+1) by ring]
        simp only [x]; rw [div_pow, mul_pow, ← pow_mul, ← pow_mul]; ring
    _ ≤ y^n := h3
lemma hw (n : ℕ) (_ : 1 ≤ n) (p : ℤ) (q : ℕ) (hq : 0 < q) : ∃ k < 3, (q:ℤ) * a (n+k) + p * b (n+k) ≠ 0 := by
  obtain ⟨k, hk, hne⟩ := ZZSigned.window (p:ℂ) (q:ℂ) (by exact_mod_cast hq.ne') (n+1)
  refine ⟨k, Finset.mem_range.1 hk, fun h0 => hne ?_⟩
  have e := ab (n+k)
  rw [show n+k+1 = n+1+k by omega] at e
  have hs := ZZSigned.scale_ne (n+1+k)
  have hQ : (q:ℚ) * ZZSigned.u (n+1+k) + p * ZZSigned.v (n+1+k) = 0 := by
    have h1 : ((q:ℤ) * a (n+k) + p * b (n+k) : ℚ) = 0 := by exact_mod_cast h0
    rw [← e.1, ← e.2] at h1
    have : ZZForm.scale (n+1+k) * ((q:ℚ) * ZZSigned.u (n+1+k) + p * ZZSigned.v (n+1+k)) = 0 := by
      push_cast at h1; linear_combination h1
    exact (mul_eq_zero.1 this).resolve_left hs
  have := congrArg (fun r : ℚ => (r:ℂ)) hQ
  push_cast at this
  exact this
theorem pi_measure : ∀ᶠ q : ℕ in atTop, ∀ p : ℤ, (q:ℝ)^(-(13:ℝ)) ≤ |π - p/q| :=
  ZZMeasure.measure π a b (by norm_num) (by norm_num) hb hf hw (by norm_num)
theorem upper13 : Constant7a.C7a ≤ 13 := by
  unfold Constant7a.C7a Constant7a.irrationalityExponent
  apply sSup_le
  rintro _ ⟨p, hp, rfl⟩
  by_contra! hlt
  have hp13 : (13 : NNReal) < p := by exact_mod_cast hlt
  have hpR : (13 : ℝ) < p := by exact_mod_cast hp13
  obtain ⟨q, hq, c, _, hc⟩ := (pi_measure.and_frequently (hp.frequently_lt_rpow_neg hpR)).exists
  exact (not_lt_of_ge (hq c)) hc
end ZZFourteen
theorem OMA.solution : type_of% @Constant7a.c7a_lt_14_797075 :=
  lt_of_le_of_lt ZZFourteen.upper13 (by
    change (↑(13 : NNReal) : ENNReal) < ↑(14.797075 : NNReal)
    exact ENNReal.coe_lt_coe.mpr (by norm_num))
end
