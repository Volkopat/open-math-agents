import OMAStatements.S_oeis_a099038

-- Credit: @CubeJerry (the owner of the agent is credited as the solver)

/-!
A diagonal generating-function proof of Mathar's recurrence for A099038.
The defining binomial double sum is the diagonal of a bivariate rational
series. Differentiating its denominator identity gives a polynomial
certificate whose diagonal coefficients telescope under the difference of
the two Euler derivatives. Coefficient extraction yields the exact recurrence.
-/

namespace OMA.T099038

section Generic
variable {R : Type*} [CommRing R]

def fibTerm (u v : R) (n k : ℕ) : R :=
  ((n-k).choose k : R)*u^(n-2*k)*v^k

def fibSum (u v : R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n+1), fibTerm u v n k

lemma fibTerm_zero (u v : R) (n k : ℕ) (h : n < 2*k) : fibTerm u v n k = 0 := by
  have h' : n-k < k := by omega
  simp [fibTerm, Nat.choose_eq_zero_of_lt h']

lemma fibTerm_at_zero (u v : R) (n : ℕ) : fibTerm u v n 0 = u^n := by
  simp [fibTerm]

lemma fibTerm_step (u v : R) (n k : ℕ) :
    fibTerm u v (n+2) (k+1) = u*fibTerm u v (n+1) (k+1) + v*fibTerm u v n k := by
  by_cases hk : 2*k < n
  · have hchoose : (n+2-(k+1)).choose (k+1) =
        (n+1-(k+1)).choose (k+1) + (n-k).choose k := by
      rw [show n+2-(k+1)=(n-k)+1 by omega, Nat.choose_succ_succ]
      rw [show n+1-(k+1)=n-k by omega]
      simp only [Nat.succ_eq_add_one, add_comm]
    unfold fibTerm
    rw [hchoose, Nat.cast_add]
    rw [show n+2-2*(k+1)=n-2*k by omega,
      show n+1-2*(k+1)=n-2*k-1 by omega]
    have hp : u^(n-2*k) = u*u^(n-2*k-1) := by
      conv_lhs => rw [show n-2*k=n-2*k-1+1 by omega, pow_succ]
      ring
    rw [hp, pow_succ]
    ring
  · by_cases he : n=2*k
    · subst n
      simp [fibTerm, show 2*k+2-(k+1)=k+1 by omega,
        show 2*k+1-(k+1)=k by omega, show 2*k-k=k by omega,
        show 2*k+2-2*(k+1)=0 by omega, Nat.choose_eq_zero_of_lt (Nat.lt_succ_self k),
        pow_succ]
      ring
    · rw [fibTerm_zero u v (n+2) (k+1) (by omega),
        fibTerm_zero u v (n+1) (k+1) (by omega), fibTerm_zero u v n k (by omega)]
      simp

lemma fibSum_zero (u v : R) : fibSum u v 0 = 1 := by
  simp [fibSum, fibTerm]
lemma fibSum_one (u v : R) : fibSum u v 1 = u := by
  simp [fibSum, Finset.sum_range_succ, fibTerm]

lemma fibSum_step (u v : R) (n : ℕ) :
    fibSum u v (n+2) = u*fibSum u v (n+1)+v*fibSum u v n := by
  unfold fibSum
  rw [Finset.sum_range_succ' (fibTerm u v (n+2)) (n+2)]
  simp_rw [fibTerm_step, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [Finset.sum_range_succ (fun k => fibTerm u v (n+1) (k+1)) (n+1),
    Finset.sum_range_succ (fibTerm u v n) (n+1),
    fibTerm_zero u v (n+1) (n+1+1) (by omega), fibTerm_zero u v n (n+1) (by omega)]
  rw [Finset.sum_range_succ' (fibTerm u v (n+1)) (n+1)]
  rw [fibTerm_at_zero, fibTerm_at_zero]
  simp only [add_zero]
  rw [pow_succ]
  ring
end Generic

open Polynomial

noncomputable def P (n : ℕ) : ℚ[X] := fibSum (X+X^2) (X-X^2) n

lemma P_zero : P 0 = 1 := fibSum_zero _ _
lemma P_one : P 1 = X+X^2 := fibSum_one _ _
lemma P_step (n : ℕ) : P (n+2) = (X+X^2)*P (n+1)+(X-X^2)*P n := fibSum_step _ _ n


lemma coeff_one_sub_X_pow (k i : ℕ) :
    ((1-X : ℚ[X])^k).coeff i = (-1:ℚ)^i*(k.choose i:ℚ) := by
  have hpow : (1-X : ℚ[X])^k =
      ∑ j ∈ Finset.range (k+1), C ((-1:ℚ)^j*(k.choose j:ℚ))*X^j := by
    rw [show (1-X : ℚ[X])=(-X)+1 by ring, add_pow]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [one_pow, mul_one]
    rw [neg_pow]
    rw [map_mul, map_pow, map_neg, map_one, C_eq_natCast]
    ring
  rw [hpow, ← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Ne.symm hji]
  · intro hi
    have hki : k < i := by simpa using hi
    simp [Nat.choose_eq_zero_of_lt hki]

lemma inner_coeff (n k : ℕ) (hk : k ≤ n) :
    (((1-X : ℚ[X])^k)*((1+X)^(n-2*k))).coeff k =
      ∑ i ∈ Finset.range (n+1), (-1:ℚ)^i*(k.choose i:ℚ)*
        (if i ≤ k then ((n-2*k).choose (k-i):ℚ) else 0) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_one_sub_X_pow, coeff_one_add_X_pow]
  calc
    (∑ i ∈ Finset.range (k+1),
        (-1:ℚ)^i*(k.choose i:ℚ)*((n-2*k).choose (k-i):ℚ)) =
      ∑ i ∈ Finset.range (k+1), (-1:ℚ)^i*(k.choose i:ℚ)*
        (if i ≤ k then ((n-2*k).choose (k-i):ℚ) else 0) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [if_pos (by have := Finset.mem_range.mp hi; omega)]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i hi hik
      have hki : ¬i ≤ k := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hik
      simp [hki]

lemma term_coeff (n k : ℕ) (hk : 2*k ≤ n) :
    (fibTerm (X+X^2 : ℚ[X]) (X-X^2) n k).coeff n =
      ((n-k).choose k:ℚ)*∑ i ∈ Finset.range (n+1), (-1:ℚ)^i*(k.choose i:ℚ)*
        (if i ≤ k then ((n-2*k).choose (k-i):ℚ) else 0) := by
  have hpow : (X : ℚ[X])^(n-2*k)*X^k = X^(n-k) := by
    rw [← pow_add]
    congr 1
    omega
  have hterm : fibTerm (X+X^2 : ℚ[X]) (X-X^2) n k =
      C ((n-k).choose k:ℚ)*(X^(n-k)*((1-X)^k*(1+X)^(n-2*k))) := by
    unfold fibTerm
    rw [show (X+X^2 : ℚ[X])=X*(1+X) by ring,
      show (X-X^2 : ℚ[X])=X*(1-X) by ring, mul_pow, mul_pow]
    rw [C_eq_natCast]
    calc
      _ = ((n-k).choose k:ℚ[X])*(X^(n-2*k)*X^k)*((1-X)^k*(1+X)^(n-2*k)) := by ring
      _ = _ := by rw [hpow]; ring
  rw [hterm, coeff_C_mul, coeff_X_pow_mul', if_pos (by omega),
    show n-(n-k)=k by omega, inner_coeff n k (by omega)]

lemma P_diagonal (n : ℕ) : (P n).coeff n = (OMA.S_oeis_a099038.a n : ℚ) := by
  unfold P fibSum
  rw [← lcoeff_apply, map_sum]
  simp only [lcoeff_apply]
  calc
    (∑ k ∈ Finset.range (n+1), (fibTerm (X+X^2 : ℚ[X]) (X-X^2) n k).coeff n) =
      ∑ k ∈ Finset.range (n/2+1), (fibTerm (X+X^2 : ℚ[X]) (X-X^2) n k).coeff n := by
        symm
        apply Finset.sum_subset (Finset.range_mono (by omega))
        intro k hk hkn
        have hnk : n < 2*k := by
          simp only [Finset.mem_range, not_lt] at hkn
          omega
        rw [fibTerm_zero _ _ n k hnk, coeff_zero]
    _ = _ := by
      unfold OMA.S_oeis_a099038.a
      push_cast
      apply Finset.sum_congr rfl
      intro k hk
      exact term_coeff n k (by have := Finset.mem_range.mp hk; omega)


noncomputable def idx (n m : ℕ) : Bool →₀ ℕ := Finsupp.single false n + Finsupp.single true m

@[simp] lemma idx_false (n m : ℕ) : idx n m false = n := by simp [idx]
@[simp] lemma idx_true (n m : ℕ) : idx n m true = m := by simp [idx]

lemma idx_le (a b n m : ℕ) : idx a b ≤ idx n m ↔ a ≤ n ∧ b ≤ m := by
  simp only [Finsupp.le_def]
  constructor
  · intro h
    exact ⟨by simpa using h false, by simpa using h true⟩
  · rintro ⟨ha,hb⟩ i
    cases i <;> simpa

lemma idx_sub (n m a b : ℕ) : idx n m - idx a b = idx (n-a) (m-b) := by
  ext i
  cases i <;> simp

lemma idx_eq_zero (n m : ℕ) : idx n m = 0 ↔ n=0 ∧ m=0 := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (fun d : Bool →₀ ℕ => d false) h,
      by simpa using congrArg (fun d : Bool →₀ ℕ => d true) h⟩
  · rintro ⟨rfl,rfl⟩
    simp [idx]

noncomputable def Z : MvPowerSeries Bool ℚ := MvPowerSeries.X false
noncomputable def Y : MvPowerSeries Bool ℚ := MvPowerSeries.X true
noncomputable def G : MvPowerSeries Bool ℚ := fun d => (P (d false)).coeff (d true)

lemma coeff_G (n m : ℕ) : MvPowerSeries.coeff (idx n m) G = (P n).coeff m := by
  change (P (idx n m false)).coeff (idx n m true) = _
  simp

lemma G_diagonal (n : ℕ) :
    MvPowerSeries.coeff (idx n n) G = (OMA.S_oeis_a099038.a n : ℚ) := by
  rw [coeff_G, P_diagonal]

lemma ZY_monomial (a b : ℕ) : Z^a*Y^b = MvPowerSeries.monomial (idx a b) (1:ℚ) := by
  unfold Z Y idx
  rw [MvPowerSeries.X_pow_eq, MvPowerSeries.X_pow_eq, MvPowerSeries.monomial_mul_monomial]
  simp

lemma coeff_ZY_mul (H : MvPowerSeries Bool ℚ) (a b n m : ℕ) :
    MvPowerSeries.coeff (idx n m) ((Z^a*Y^b)*H) =
      if (a ≤ n ∧ b ≤ m) then MvPowerSeries.coeff (idx (n-a) (m-b)) H else 0 := by
  rw [ZY_monomial, MvPowerSeries.coeff_monomial_mul]
  simp only [idx_le, idx_sub, one_mul]

lemma G_eq : (1-Z*Y*(1+Y)-Z^2*Y*(1-Y))*G = 1 := by
  have he : (1-Z*Y*(1+Y)-Z^2*Y*(1-Y))*G =
      G-(Z^1*Y^1)*G-(Z^1*Y^2)*G-(Z^2*Y^1)*G+(Z^2*Y^2)*G := by ring
  rw [he]
  apply MvPowerSeries.ext
  intro d
  have hd : d = idx (d false) (d true) := by
    ext i
    cases i <;> simp
  rw [hd]
  generalize d false = n, d true = m
  simp only [map_add, map_sub, coeff_G, coeff_ZY_mul, MvPowerSeries.coeff_one, idx_eq_zero]
  rcases n with _|n
  · simp [P_zero, Polynomial.coeff_one]
  rcases n with _|n
  · have hp : P 1 = (X:ℚ[X])^1*P 0 + X^2*P 0 := by rw [P_one,P_zero]; ring
    simp only [Nat.reduceAdd, Nat.zero_add, Nat.succ_eq_add_one, show (1:ℕ)≤1 by decide,
      show ¬(2:ℕ)≤1 by decide, true_and, false_and, if_false, sub_zero, add_zero,
      Nat.sub_self, coeff_G]
    rw [hp, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
    simp
  · have hp : P (n+1+1) =
        (X:ℚ[X])^1*P (n+1)+X^2*P (n+1)+X^1*P n-X^2*P n := by
      rw [P_step]
      ring
    rw [hp]
    simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_X_pow_mul',
      show 1≤n+1+1 by omega, show 2≤n+1+1 by omega, true_and, coeff_G,
      show n+1+1-1=n+1 by omega, show n+1+1-2=n by omega,
      show ¬n+1+1=0 by omega, false_and, if_false]
    ring

end OMA.T099038

namespace OMA.T099038

lemma rational_certificate {R : Type*} [CommRing R] (z x g gz gx : R)
    (hQ : (1-z*x*(1+x)-z^2*x*(1-x))*g=1)
    (hz : (1-z*x*(1+x)-z^2*x*(1-x))*gz
      -(x*(1+x)+2*z*x*(1-x))*g=0)
    (hx : (1-z*x*(1+x)-z^2*x*(1-x))*gx
      -(z*(1+2*x)+z^2*(1-2*x))*g=0) :
    2*(1-2*(z*x)+3*(z*x)^2-6*(z*x)^3+(z*x)^4)*gz
      +x*(-2+6*(z*x)-18*(z*x)^2+4*(z*x)^3)*g =
    x*(x*((2-6*z^2*x^2+8*z^2*x+2*z^2)*g+
      (2*x-2*z^2*x^3+4*z^2*x^2-4*z+2*z^2*x)*gx)
      -z*((-4*z*x^3+8*z*x^2-4+4*z*x)*g+
      (2*x-2*z^2*x^3+4*z^2*x^2-4*z+2*z^2*x)*gz)) := by
  let q := 1-z*x*(1+x)-z^2*x*(1-x)
  let l := 2*(1-2*(z*x)+3*(z*x)^2-6*(z*x)^3+(z*x)^4)*gz
      +x*(-2+6*(z*x)-18*(z*x)^2+4*(z*x)^3)*g -
    x*(x*((2-6*z^2*x^2+8*z^2*x+2*z^2)*g+
      (2*x-2*z^2*x^3+4*z^2*x^2-4*z+2*z^2*x)*gx)
      -z*((-4*z*x^3+8*z*x^2-4+4*z*x)*g+
      (2*x-2*z^2*x^3+4*z^2*x^2-4*z+2*z^2*x)*gz))
  have hh : q*l=0 := by
    dsimp [q,l]
    linear_combination
      (2*(1-2*(z*x)+3*(z*x)^2-6*(z*x)^3+(z*x)^4)+
        x*z*(2*x-2*z^2*x^3+4*z^2*x^2-4*z+2*z^2*x))*hz
      -x^2*(2*x-2*z^2*x^3+4*z^2*x^2-4*z+2*z^2*x)*hx
  apply sub_eq_zero.mp
  change l=0
  calc
    l = g*(q*l) := by rw [← mul_assoc, mul_comm g q, hQ, one_mul]
    _ = 0 := by rw [hh,mul_zero]

open MvPowerSeries

lemma pderiv_nat (i : Bool) (n : ℕ) [n.AtLeastTwo] :
    pderiv ℚ i (no_index (OfNat.ofNat n : MvPowerSeries Bool ℚ)) = 0 := by
  exact (pderiv ℚ i).map_natCast n

lemma bivariate_certificate (G : MvPowerSeries Bool ℚ)
    (hQ : (1-X false*X true*(1+X true)-(X false)^2*X true*(1-X true))*G=1) :
    let z : MvPowerSeries Bool ℚ := X false
    let x : MvPowerSeries Bool ℚ := X true
    let d := 1-2*(z*x)+3*(z*x)^2-6*(z*x)^3+(z*x)^4
    let dp := -2+6*(z*x)-18*(z*x)^2+4*(z*x)^3
    let N := 2*x-2*z^2*x^3+4*z^2*x^2-4*z+2*z^2*x
    2*d*pderiv ℚ false G+x*dp*G =
      x*(x*pderiv ℚ true (N*G)-z*pderiv ℚ false (N*G)) := by
  dsimp only
  have hz := congrArg (pderiv ℚ false) hQ
  have hx := congrArg (pderiv ℚ true) hQ
  simp only [map_sub, map_add, Derivation.leibniz, pderiv_pow,
    pderiv_one, pderiv_nat, pderiv_X_self, pderiv_X_of_ne (by decide : true ≠ false),
    pderiv_X_of_ne (by decide : false ≠ true), smul_eq_mul] at hz hx
  norm_num at hz hx
  have hz' : (1-X false*X true*(1+X true)-(X false)^2*X true*(1-X true))*
      pderiv ℚ false G -
      (X true*(1+X true)+2*X false*X true*(1-X true))*G=0 := by
    linear_combination hz
  have hx' : (1-X false*X true*(1+X true)-(X false)^2*X true*(1-X true))*
      pderiv ℚ true G -
      (X false*(1+2*X true)+(X false)^2*(1-2*X true))*G=0 := by
    linear_combination hx
  have h := rational_certificate (X false) (X true) G
    (pderiv ℚ false G) (pderiv ℚ true G) hQ hz' hx'
  simp only [Derivation.leibniz, map_sub, map_add, pderiv_pow,
    pderiv_one, pderiv_nat, pderiv_X_self, pderiv_X_of_ne (by decide : true ≠ false),
    pderiv_X_of_ne (by decide : false ≠ true), smul_eq_mul]
  norm_num
  linear_combination h

lemma scaled_certificate (G E : MvPowerSeries Bool ℚ)
    (h : let z : MvPowerSeries Bool ℚ := X false
         let x : MvPowerSeries Bool ℚ := X true
         2*(1-2*(z*x)+3*(z*x)^2-6*(z*x)^3+(z*x)^4)*pderiv ℚ false G
           +x*(-2+6*(z*x)-18*(z*x)^2+4*(z*x)^3)*G =
           x*(x*pderiv ℚ true E-z*pderiv ℚ false E)) :
    let z : MvPowerSeries Bool ℚ := X false
    let x : MvPowerSeries Bool ℚ := X true
    (2-2*(z*x)+2*(z*x)^2-6*(z*x)^3-10*(z*x)^4+2*(z*x)^5)*pderiv ℚ false G
      +x*(-2+4*(z*x)-12*(z*x)^2-14*(z*x)^3+4*(z*x)^4)*G =
    x*(x*pderiv ℚ true ((1+z*x)*E)-z*pderiv ℚ false ((1+z*x)*E)) := by
  dsimp only at h ⊢
  simp only [Derivation.leibniz, map_add, pderiv_one, pderiv_X_self,
    pderiv_X_of_ne (by decide : true ≠ false),
    pderiv_X_of_ne (by decide : false ≠ true), smul_eq_mul]
  linear_combination (1+X false*X true)*h

lemma bivariate_scaled (G : MvPowerSeries Bool ℚ)
    (hQ : (1-X false*X true*(1+X true)-(X false)^2*X true*(1-X true))*G=1) :
    ∃ E : MvPowerSeries Bool ℚ,
    let z : MvPowerSeries Bool ℚ := X false
    let x : MvPowerSeries Bool ℚ := X true
    (2-2*(z*x)+2*(z*x)^2-6*(z*x)^3-10*(z*x)^4+2*(z*x)^5)*pderiv ℚ false G
      +x*(-2+4*(z*x)-12*(z*x)^2-14*(z*x)^3+4*(z*x)^4)*G =
    x*(x*pderiv ℚ true E-z*pderiv ℚ false E) := by
  have h := bivariate_certificate G hQ
  dsimp only at h
  exact ⟨_, scaled_certificate G _ h⟩

end OMA.T099038

namespace OMA.T099038
open MvPowerSeries

lemma coeff_diagonal_shift (H : MvPowerSeries Bool ℚ) (n j : ℕ) (hj : j ≤ n) :
    coeff (idx n n) ((Z*Y)^j*H) = coeff (idx (n-j) (n-j)) H := by
  rw [mul_pow, coeff_ZY_mul, if_pos ⟨hj,hj⟩]

lemma idx_succ_false (n m : ℕ) :
    idx n m + Finsupp.single false 1 = idx (n+1) m := by
  ext i
  cases i <;> simp [idx]

lemma idx_succ_true (n m : ℕ) :
    idx n m + Finsupp.single true 1 = idx n (m+1) := by
  ext i
  cases i <;> simp [idx]

lemma coeff_euler_Z (H : MvPowerSeries Bool ℚ) (n m : ℕ) :
    coeff (idx n m) (Z*pderiv ℚ false H) = (n:ℚ)*coeff (idx n m) H := by
  have he : Z*pderiv ℚ false H = (Z^1*Y^0)*pderiv ℚ false H := by simp
  rw [he, coeff_ZY_mul]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.zero_le, and_true,
      show 1 ≤ n+1 by omega, if_true, Nat.add_sub_cancel, Nat.sub_zero]
    rw [coeff_pderiv, idx_succ_false]
    simp only [idx_false, Nat.cast_add, Nat.cast_one]
    ring

lemma coeff_euler_Y (H : MvPowerSeries Bool ℚ) (n m : ℕ) :
    coeff (idx n m) (Y*pderiv ℚ true H) = (m:ℚ)*coeff (idx n m) H := by
  have he : Y*pderiv ℚ true H = (Z^0*Y^1)*pderiv ℚ true H := by simp
  rw [he, coeff_ZY_mul]
  cases m with
  | zero => simp
  | succ m =>
    simp only [Nat.zero_le, true_and,
      show 1 ≤ m+1 by omega, if_true, Nat.add_sub_cancel, Nat.sub_zero]
    rw [coeff_pderiv, idx_succ_true]
    simp only [idx_true, Nat.cast_add, Nat.cast_one]
    ring

lemma coeff_diagonal_euler_difference (H : MvPowerSeries Bool ℚ) (n : ℕ) :
    coeff (idx n n) (Y*pderiv ℚ true H - Z*pderiv ℚ false H) = 0 := by
  rw [map_sub, coeff_euler_Y, coeff_euler_Z, sub_self]

lemma diagonal_recurrence_of_certificate (H E : MvPowerSeries Bool ℚ)
    (hc : 2*(1-2*(Z*Y)+3*(Z*Y)^2-6*(Z*Y)^3+(Z*Y)^4)*pderiv ℚ false H
      +Y*(-2+6*(Z*Y)-18*(Z*Y)^2+4*(Z*Y)^3)*H =
      Y*(Y*pderiv ℚ true E-Z*pderiv ℚ false E))
    (n : ℕ) (hn : 5 ≤ n) :
    (n:ℚ)*coeff (idx n n) H - (n:ℚ)*coeff (idx (n-1) (n-1)) H
      +(n:ℚ)*coeff (idx (n-2) (n-2)) H
      +3*(-(n:ℚ)+1)*coeff (idx (n-3) (n-3)) H
      +(-5*(n:ℚ)+13)*coeff (idx (n-4) (n-4)) H
      +((n:ℚ)-3)*coeff (idx (n-5) (n-5)) H = 0 := by
  let U := Z*pderiv ℚ false H
  let L := Y*pderiv ℚ true E-Z*pderiv ℚ false E
  have he : 2*U-2*((Z*Y)^1*U)+2*((Z*Y)^2*U)-6*((Z*Y)^3*U)
      -10*((Z*Y)^4*U)+2*((Z*Y)^5*U)
      -2*((Z*Y)^1*H)+4*((Z*Y)^2*H)-12*((Z*Y)^3*H)
      -14*((Z*Y)^4*H)+4*((Z*Y)^5*H) = (Z*Y)^1*L+(Z*Y)^2*L := by
    dsimp [U,L]
    linear_combination (Z*(1+Z*Y))*hc
  have h := congrArg (coeff (idx n n)) he
  have h1 : 1 ≤ n := by omega
  have h2 : 2 ≤ n := by omega
  have h3 : 3 ≤ n := by omega
  have h4 : 4 ≤ n := by omega
  have hs (j : ℕ) (hj : j ≤ n) : ∀ K : MvPowerSeries Bool ℚ,
      coeff (idx n n) ((Z*Y)^j*K) = coeff (idx (n-j) (n-j)) K := by
    intro K
    exact coeff_diagonal_shift K n j hj
  simp only [map_add, map_sub] at h
  simp only [show (2 : MvPowerSeries Bool ℚ) = C 2 by exact (map_natCast (C (σ := Bool) (R := ℚ)) 2).symm,
    show (6 : MvPowerSeries Bool ℚ) = C 6 by exact (map_natCast (C (σ := Bool) (R := ℚ)) 6).symm,
    show (10 : MvPowerSeries Bool ℚ) = C 10 by exact (map_natCast (C (σ := Bool) (R := ℚ)) 10).symm,
    show (4 : MvPowerSeries Bool ℚ) = C 4 by exact (map_natCast (C (σ := Bool) (R := ℚ)) 4).symm,
    show (12 : MvPowerSeries Bool ℚ) = C 12 by exact (map_natCast (C (σ := Bool) (R := ℚ)) 12).symm,
    show (14 : MvPowerSeries Bool ℚ) = C 14 by exact (map_natCast (C (σ := Bool) (R := ℚ)) 14).symm,
    coeff_C_mul] at h
  simp only [hs 1 h1, hs 2 h2, hs 3 h3, hs 4 h4, hs 5 hn] at h
  dsimp [U,L] at h
  simp only [coeff_euler_Z, coeff_diagonal_euler_difference,
    Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3, Nat.cast_sub h4,
    Nat.cast_sub hn] at h
  norm_num at h
  linear_combination (1/2:ℚ)*h

end OMA.T099038

open OMA.T099038

theorem OMA.solution : type_of% @OMA.S_oeis_a099038.main := by
  intro n hn
  have h := diagonal_recurrence_of_certificate G
    ((2*Y-2*Z^2*Y^3+4*Z^2*Y^2-4*Z+2*Z^2*Y)*G)
    (by
      simpa only [Z,Y] using bivariate_certificate G
        (by simpa only [Z,Y] using G_eq)) n hn
  simp only [G_diagonal] at h
  exact_mod_cast h
