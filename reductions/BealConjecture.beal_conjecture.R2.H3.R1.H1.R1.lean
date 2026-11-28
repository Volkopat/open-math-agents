import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1
import Mathlib

-- Credit: @ubuwaits

/-!
# The cubic case of the square-plus-power equation

The pure cubic square-root statement H1 implies the complete odd-base
classification u²+d³=2ᵏ for k>2. When 3 does not divide k, the square
root yields integers A,B with A>0, B dividing A², and B²=A³+2ᵏ.
It follows that B is a signed power of two and 3 divides k. For k=3t,
the factors 2ᵗ−d and 2²ᵗ+2ᵗd+d² are squares after their common divisor
is removed. This divisor divides three, and the first factor is one
modulo eight. The square second factor then forces t<5. The unique
solution is 13²+7³=2⁹.

For a square plus a fifth power, only the exponent classes 1, 3, and 9
modulo 10 remain. The three resulting rational-point conditions also
follow from Mulholland (2006), Theorem 5.1 and Table 5.1. For a prime
p dividing k, the square geometric factor gives an explicit bound for
2^(k/p), unless the common factor is p and p is 1 modulo 8. The finite
certificates cover all primes from 5 through 31 outside that exceptional
case. The full odd-prime classification is Bennett and Skinner (2004),
Theorem 8.4.
-/

namespace OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H1_R1

/-- The linear cubic-field factor of this square has an integral square root.
The variables a,b,c are its coordinates in the basis 1, ∛2, ∛4. -/
def H1 : Prop :=
  ∀ {d u q j : ℕ}, d%2=1 → u%2=1 → d.Coprime u → 0<q → (j=1 ∨ j=2) →
    d^3+u^2=2^(3*q+j) → ∃ a b c : ℤ, a^2+4*b*c= -(d:ℤ) ∧
      2*a*b+2*c^2=(if j=1 then (2:ℤ)^q else 0) ∧
      2*a*c+b^2=(if j=2 then (2:ℤ)^q else 0)

/-- The remaining quintic case, with its necessary residue and coprimality conditions. -/
def H2 : Prop :=
  ∀ {u d k : ℕ}, u%2=1 → d%8=7 → 1<d → u.Coprime d → 2<k → k%2=1 →
    (k%10=1 ∨ k%10=3 ∨ k%10=9) → u^2+d^5≠2^k

/-- The remaining odd prime exponents in the specialization of
Bennett and Skinner's Theorem 1.2. -/
def H3 : Prop :=
  ∀ {u d p k : ℕ}, u%2=1 → d%8=7 → 1<d → u.Coprime d → p.Prime → 7≤p →
    2<k → k%2=1 →
    (∀ t : ℕ, k=p*t →
      (31<p ∧ ∃ a : ℕ, d+a^2=2^t ∧ 2^t<((p-1).sqrt+1)*4^(p/2+1)) ∨
        (p%8=1 ∧ ∃ a z : ℕ, d+p*a^2=2^t ∧ u=p*a*z)) → u^2+d^p≠2^k

namespace BealMordell

/-- A positive cube equal to a difference of distinct powers of two has
its lower exponent divisible by three. -/
private theorem cube_gap_valuation {a k h : ℕ} (ha : 0<a) (gap : a^3+2^k=2^h) : 3∣k := by
  have less : k<h := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by
    have := Nat.pow_pos (n:=3) ha
    omega)
  let z := 2^(h-k)-1
  have big : 1 < 2^(h-k) := Nat.one_lt_two_pow (by omega)
  have pe : 2∣2^(h-k) := dvd_pow_self _ (by omega)
  have oz : ¬2∣z := by dsimp [z]; omega
  have nz : z≠0 := by dsimp [z]; omega
  have f : a^3=2^k*z := by
    have ep : 2^h=2^k*2^(h-k) := by rw [←pow_add]; congr 1; omega
    have ez : 2^(h-k)=z+1 := by dsimp [z]; omega
    rw [ep,ez,Nat.mul_add,Nat.mul_one] at gap
    omega
  have val := congrArg (fun n : ℕ => n.factorization 2) f
  rw [Nat.factorization_mul (by positivity) nz,Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,Nat.factorization_eq_zero_of_not_dvd oz,
    Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul] at val
  exact ⟨a.factorization 2,by omega⟩

/-- The symmetric functions of a square root in the pure cubic field
give integral coordinates A,B with B dividing A² and B²=A³+2ᵏ.
Positivity of A then forces three to divide k. -/
theorem square_coordinates_force_three {d k : ℕ} (hd : 0<d)
    {a b c P Q : ℤ} (ha : a^2+4*b*c= -(d:ℤ))
    (hb : 2*a*b+2*c^2=P) (hc : 2*a*c+b^2=Q) (pq : P*Q=0)
    (power : 2*P^3+4*Q^3=(2:ℤ)^k) : 3∣k := by
  let T := 3*a
  let S := 3*(a^2-2*b*c)
  let N := a^3+2*b^3+4*c^3-6*a*b*c
  have ht : T^2=2*S-3*(d:ℤ) := by dsimp [T,S]; linear_combination 3*ha
  have hs : S^2-2*T*N=3*(d:ℤ)^2 := by
    have e : S^2-2*T*N=3*((a^2+4*b*c)^2-2*(2*a*b+2*c^2)*(2*a*c+b^2)) := by
      dsimp [S,T,N]; ring
    rw [e,ha,hb,hc]
    linear_combination -6*pq
  have hn : N^2+(d:ℤ)^3=(2:ℤ)^k := by
    have e : N^2=(a^2+4*b*c)^3+2*(2*a*b+2*c^2)^3+4*(2*a*c+b^2)^3-
        6*(a^2+4*b*c)*(2*a*b+2*c^2)*(2*a*c+b^2) := by dsimp [N]; ring
    rw [e,ha,hb,hc]
    linear_combination power+6*(d:ℤ)*pq
  let A := S-(d:ℤ)
  let B := T*S-N
  have apos : 0<A := by dsimp [A]; nlinarith [sq_nonneg T]
  have eA : 2*T*B=3*A^2 := by
    dsimp [A,B]
    linear_combination 2*S*ht+hs
  have eB : B^2=A^3+(2:ℤ)^k := by
    dsimp [A,B]
    linear_combination S^2*ht+S*hs+hn
  have dvdA : B∣A^2 := ⟨2*a,by dsimp [T] at eA; linarith only [eA]⟩
  have dvdA' : B∣A^3 := dvdA.trans (pow_dvd_pow A (by decide : 2≤3))
  have dvdB : B∣(2:ℤ)^k := by
    rw [show (2:ℤ)^k=B^2-A^3 by omega]
    exact dvd_sub (dvd_pow_self _ (by decide : 2≠0)) dvdA'
  have nd : B.natAbs∣(2:ℕ)^k := by
    simpa only [Int.natAbs_pow,show (2:ℤ).natAbs=2 by decide] using (Int.natAbs_dvd_natAbs.mpr dvdB)
  obtain ⟨h,_,bh⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp nd
  have b2 : B^2=(2:ℤ)^(2*h) := by
    have n : (B.natAbs:ℤ)^2=B^2 := by rw [Int.natCast_natAbs,sq_abs]
    rw [←n,bh]
    push_cast
    rw [←pow_mul,Nat.mul_comm]
  have aeq : (A.toNat:ℤ)=A := Int.toNat_of_nonneg apos.le
  have agap : A.toNat^3+2^k=2^(2*h) := by
    exact_mod_cast (show (A.toNat:ℤ)^3+(2:ℤ)^k=(2:ℤ)^(2*h) by rw [aeq,←eB,b2])
  exact cube_gap_valuation (by omega) agap

end BealMordell

namespace BealMordell

private theorem square_parts {A B u : ℕ} (ha : 0<A) (h : A*B=u^2) :
    ∃ a b : ℕ, A=A.gcd B*a^2 ∧ B=A.gcd B*b^2 := by
  let g := A.gcd B
  let x := A/g
  let y := B/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left B ha
  have cx : g*x=A := Nat.mul_div_cancel' (Nat.gcd_dvd_left A B)
  have cy : g*y=B := Nat.mul_div_cancel' (Nat.gcd_dvd_right A B)
  have cp : x.Coprime y := Nat.coprime_div_gcd_div_gcd gp
  have du : g^2∣u^2 := ⟨x*y,by rw [←h,←cx,←cy]; ring⟩
  obtain ⟨v,hv⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp du
  have hxy : x*y=v^2 := by
    apply Nat.mul_left_cancel (Nat.pow_pos (n:=2) gp)
    rw [←cx,←cy,hv] at h
    linear_combination h
  obtain ⟨a,ea⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp cp)) hxy
  obtain ⟨b,eb⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp cp.symm)) ((Nat.mul_comm _ _).trans hxy)
  exact ⟨a,b,by rw [←ea]; exact cx.symm,by rw [←eb]; exact cy.symm⟩

private theorem base_seven {u d k : ℕ} (hu : u%2=1) (hk : 2<k)
    (eqn : u^2+d^3=2^k) : d%8=7 := by
  obtain ⟨v,hv⟩ := Nat.odd_iff.mpr hu
  have zero : ((2^k:ℕ):ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 (by omega : 3≤k))
  have h := congrArg (fun w : ℕ => (w:ZMod 8)) eqn
  rw [zero,hv] at h
  push_cast at h
  have tab : ∀ a b : ZMod 8, (2*a+1)^2+b^3=0 → b=7 := by decide +kernel
  have result := congrArg ZMod.val (tab _ _ h)
  simpa only [ZMod.val_natCast,show (7:ZMod 8).val=7 by decide] using result

private theorem cubic_cofactor_square {d t u : ℕ} (ht : 3≤t) (hd : d%8=7)
    (hlt : d<2^t) (eqn : u^2+d^3=(2^t)^3) :
    ∃ z : ℕ, (2^t)^2+2^t*d+d^2=z^2 := by
  let W := 2^t
  let A := W-d
  let B := W^2+W*d+d^2
  let g := A.gcd B
  have WA : W=A+d := by dsimp [A,W]; omega
  have pos : 0<A := by dsimp [A,W]; omega
  have product : A*B=u^2 := by
    change u^2+d^3=W^3 at eqn
    dsimp [B]
    rw [WA] at eqn ⊢
    linear_combination -eqn
  have wd : W.Coprime d := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left t
  have cp : A.Coprime d := Nat.coprime_add_self_left.mp (WA ▸ wd)
  have ga : g∣A := Nat.gcd_dvd_left _ _
  have gb : g∣B := Nat.gcd_dvd_right _ _
  have identity : B=A*(W+2*d)+3*d^2 := by dsimp [B]; rw [WA]; ring
  have g3d : g∣3*d^2 := (Nat.dvd_add_iff_right (ga.trans (dvd_mul_right _ _))).mpr (identity ▸ gb)
  have g3 : g∣3 := ((Nat.Coprime.coprime_dvd_left ga cp).pow_right 2).dvd_of_dvd_mul_right g3d
  obtain ⟨a,b,eqA,eqB⟩ := square_parts pos product
  change A=g*a^2 at eqA
  change B=g*b^2 at eqB
  rcases (Nat.dvd_prime Nat.prime_three).mp g3 with one|three
  · exact ⟨b,by simpa [one] using eqB⟩
  have wz : (W:ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 ht)
  have dz : (d:ZMod 8)=7 := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast,show (7:ZMod 8).val=7 by decide] using hd
  have eq := congrArg (fun v : ℕ => (v:ZMod 8)) (WA.trans (by rw [eqA,three]))
  push_cast at eq
  rw [wz,dz] at eq
  exact ((by decide +kernel : ∀ a : ZMod 8, 0≠3*a^2+7) _ eq).elim

private theorem square_cofactor_small {d z t : ℕ} (hd : d%2=1)
    (hlt : d<2^t) (he : (2^t)^2+2^t*d+d^2=z^2) : t<5 := by
  by_contra! ht
  let L := 2^(t-2)
  let W := 2^t
  let S := d+2*L
  have lp : 0<L := Nat.two_pow_pos _
  have wL : W=4*L := by
    change 2^t=4*2^(t-2)
    calc
      2^t=2^(2+(t-2)) := by congr 1; omega
      _=4*2^(t-2) := by rw [pow_add]; rfl
  change W^2+W*d+d^2=z^2 at he
  change d<W at hlt
  have diff : z^2=S^2+12*L^2 := by dsimp [S]; rw [wL] at he; linear_combination -he
  have gt : S<z := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (by nlinarith [Nat.pow_pos (n:=2) lp])
  have zlt : z<2*W := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    rw [←he]
    nlinarith [Nat.pow_lt_pow_left hlt (by decide : 2≠0),Nat.mul_lt_mul_of_pos_left hlt (Nat.two_pow_pos t)]
  have oddS : S%2=1 := by dsimp [S]; omega
  have oddZ : z%2=1 := by
    have e := congrArg (fun n : ℕ => n%2) diff
    change z^2%2=(S^2+12*L^2)%2 at e
    have ev : (12*L^2)%2=0 := Nat.mod_eq_zero_of_dvd ((by decide : 2∣12).trans (dvd_mul_right _ _))
    rw [Nat.pow_mod z,Nat.add_mod (S^2),Nat.pow_mod S,oddS,ev] at e
    by_contra hn
    have e0 : z%2=0 := by omega
    simp [e0] at e
  let r := (z-S)/2
  let v := r+S
  have zr : z=2*r+S := by dsimp [r]; omega
  have prod : r*v=3*L^2 := by
    dsimp [v]; rw [zr] at diff; nlinarith only [diff]
  let e := 2*(t-2)
  have dv : 2^e∣r*v := by rw [prod]; dsimp [e,L]; rw [Nat.mul_comm 2 (t-2),pow_mul]; exact dvd_mul_left _ _
  have vt : v≤z := by dsimp [v]; omega
  have rt : r≤z := by omega
  have bound : 2^e≤z := by
    by_cases oddr : r%2=1
    · have cp := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬2∣r)).pow_left e
      exact (Nat.le_of_dvd (by dsimp [v]; omega) (cp.dvd_of_dvd_mul_left dv)).trans vt
    · have oddv : v%2=1 := by dsimp [v]; omega
      have cp := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬2∣v)).pow_left e
      exact (Nat.le_of_dvd (by dsimp [r]; omega) (cp.dvd_of_dvd_mul_right dv)).trans rt
  have grow : 2*W≤2^e := by
    change 2*2^t≤2^e
    rw [Nat.mul_comm,←pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by dsimp [e]; omega)
  omega

/-- When the exponent of two is a positive multiple of three, the
difference of cubes has only the solution 13²+7³=2⁹ for k>2. -/
theorem triple_shift {u d k : ℕ} (hu : u%2=1)
    (hk : 2<k) (divides : 3∣k) (eqn : u^2+d^3=2^k) :
    u=13 ∧ d=7 ∧ k=9 := by
  obtain ⟨t,et⟩ := divides
  have e : u^2+d^3=(2^t)^3 := by rw [←pow_mul,Nat.mul_comm t 3,←et]; exact eqn
  have lt : d<2^t := (Nat.pow_lt_pow_iff_left (by decide : 3≠0)).mp (by have := Nat.pow_pos (n:=2) (show 0<u by omega); omega)
  have seven := base_seven hu hk eqn
  have th : 3≤t := by
    by_contra! h
    have bound := Nat.pow_le_pow_right (n:=2) (by decide) (show t≤2 by omega)
    norm_num at bound
    omega
  obtain ⟨z,hz⟩ := cubic_cofactor_square th seven lt e
  have small := square_cofactor_small (by omega) lt hz
  have eqt : t=3 := by
    by_contra neq
    have t4 : t=4 := by omega
    rw [t4] at lt
    norm_num at lt
    have choices : d=7 ∨ d=15 := by omega
    have ek : k=12 := by omega
    have e11 := congrArg (fun v : ℕ => (v:ZMod 11)) eqn
    have tab : ∀ x : ZMod 11, x^2+7^3≠2^12 ∧ x^2+15^3≠2^12 := by decide +kernel
    rw [ek] at e11
    rcases choices with rfl|rfl
    · exact (tab u).1 (by exact_mod_cast e11)
    · exact (tab u).2 (by exact_mod_cast e11)
  have eqk : k=9 := by omega
  rw [eqt] at lt
  have eqd : d=7 := by norm_num at lt; omega
  rw [eqk,eqd] at eqn
  norm_num at eqn
  exact ⟨by nlinarith,eqd,eqk⟩

end BealMordell

namespace BealMordell

private theorem coprime_bases {u d k : ℕ} (hu : u%2=1) (eqn : u^2+d^3=2^k) :
    d.Coprime u := by
  apply Nat.coprime_of_dvd
  intro l lp ld lu
  have dv : l∣2^k := eqn ▸ dvd_add (lu.trans (dvd_pow_self _ (by decide : 2≠0)))
    (ld.trans (dvd_pow_self _ (by decide : 3≠0)))
  have p2 := (Nat.prime_dvd_prime_iff_eq lp Nat.prime_two).mp (lp.dvd_of_dvd_pow dv)
  subst l
  omega

/-- The pure cubic square descent is the only number-field input to the
complete classification with odd bases. -/
theorem cubic_from_coordinates
    (roots : ∀ {d u q j : ℕ}, d%2=1 → u%2=1 → d.Coprime u → 0<q → (j=1 ∨ j=2) →
      d^3+u^2=2^(3*q+j) → ∃ a b c : ℤ, a^2+4*b*c= -(d:ℤ) ∧
        2*a*b+2*c^2=(if j=1 then (2:ℤ)^q else 0) ∧
        2*a*c+b^2=(if j=2 then (2:ℤ)^q else 0))
    {u d k : ℕ} (hu : u%2=1) (hd : d%2=1) (hk : 2<k) (eqn : u^2+d^3=2^k) :
    u=13 ∧ d=7 ∧ k=9 := by
  apply triple_shift hu hk _ eqn
  by_contra bad
  let q := k/3
  let j := k%3
  have sj : j=1 ∨ j=2 := by dsimp [j]; omega
  have kk : k=3*q+j := by dsimp [q,j]; omega
  have h : d^3+u^2=2^(3*q+j) := by rw [←kk,Nat.add_comm]; exact eqn
  obtain ⟨a,b,c,ha,hb,hc⟩ := roots hd hu (coprime_bases hu eqn) (by dsimp [q]; omega) sj h
  apply bad (square_coordinates_force_three (by omega : 0<d) ha hb hc _ _)
  · rcases sj with e|e <;> simp [e]
  · rw [kk]
    have p : ((2:ℤ)^q)^3=(2:ℤ)^(3*q) := by rw [←pow_mul,Nat.mul_comm]
    rcases sj with e|e <;> simp [e,p,pow_add] <;> ring

end BealMordell

namespace BealMordell

/-- The sole positive odd-base solution for k above two. -/
theorem classify_odd (roots : H1) {u d k : ℕ} (hu : u%2=1) (hd : d%2=1) (hk : 2<k)
    (eqn : u^2+d^3=2^k) : u=13 ∧ d=7 ∧ k=9 :=
  cubic_from_coordinates roots hu hd hk eqn

private theorem equal_two_orders {p q k a b : ℕ} (ha : a%2=1) (hb : b%2=1)
    (eqn : 2^p*a+2^q*b=2^k) : p=q := by
  have exclude {p q a b : ℕ} (lt : p<q) (oa : a%2=1) (ob : b%2=1)
      (h : 2^p*a+2^q*b=2^k) : False := by
    have qsplit : 2^q=2^p*2^(q-p) := by rw [←pow_add]; congr 1; omega
    let z := a+2^(q-p)*b
    have f : 2^p*z=2^k := by dsimp [z]; rw [qsplit] at h; linear_combination h
    have g : 1<z := by
      dsimp [z]
      have pos := Nat.mul_pos (Nat.two_pow_pos (q-p)) (show 0<b by omega)
      omega
    have pk : p<k := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by
      rw [←f]; simpa using Nat.mul_lt_mul_of_pos_left g (Nat.two_pow_pos p))
    have ksplit : 2^k=2^p*2^(k-p) := by rw [←pow_add]; congr 1; omega
    rw [ksplit] at f
    have ez := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos p) f
    have dv : 2∣z := ez ▸ dvd_pow_self 2 (by omega)
    have ev : 2∣2^(q-p)*b := (dvd_pow_self 2 (by omega : q-p≠0)).trans (dvd_mul_right _ _)
    dsimp [z] at dv
    omega
  rcases lt_trichotomy p q with lt|eq|lt
  · exact (exclude lt ha hb eqn).elim
  · exact eq
  · exact (exclude lt hb ha ((Nat.add_comm _ _).trans eqn)).elim

/-- Every positive solution is a weighted power-of-two multiple of
(1,1,1) or (13,7,9). -/
theorem classify_positive (roots : H1) {u d k : ℕ} (hu : 0<u) (hd : 0<d) :
    u^2+d^3=2^k ↔ ∃ t : ℕ,
      (u=2^(3*t) ∧ d=2^(2*t) ∧ k=6*t+1) ∨
      (u=13*2^(3*t) ∧ d=7*2^(2*t) ∧ k=6*t+9) := by
  constructor
  · intro h
    obtain ⟨i,a,oa,eu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu.ne' 2 (by decide)
    obtain ⟨j,b,ob,ed⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' 2 (by decide)
    have opa : a^2%2=1 := by rw [Nat.pow_mod,show a%2=1 by omega]
    have opb : b^3%2=1 := by rw [Nat.pow_mod,show b%2=1 by omega]
    have f : 2^(i*2)*a^2+2^(j*3)*b^3=2^k := by simpa only [eu,ed,mul_pow,←pow_mul] using h
    have same := equal_two_orders opa opb f
    let t := i/3
    have ei : i=3*t := by dsimp [t]; omega
    have ej : j=2*t := by dsimp [t]; omega
    have fact : 2^(6*t)*(a^2+b^3)=2^k := by
      rw [show i*2=6*t by omega,show j*3=6*t by omega,←Nat.mul_add] at f
      exact f
    have sum : 1<a^2+b^3 := by omega
    have kk : 6*t<k := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by
      rw [←fact]; simpa using Nat.mul_lt_mul_of_pos_left sum (Nat.two_pow_pos (6*t)))
    let l := k-6*t
    have kl : k=6*t+l := by dsimp [l]; omega
    have red : a^2+b^3=2^l := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos (6*t))
      rw [fact,←pow_add,←kl]
    refine ⟨t,?_⟩
    by_cases large : 2<l
    · obtain ⟨ea,eb,el⟩ := classify_odd roots (by omega) (by omega) large red
      right
      exact ⟨by rw [eu,ei,ea,Nat.mul_comm],by rw [ed,ej,eb,Nat.mul_comm],by omega⟩
    · have bound : 2^l≤4 := Nat.pow_le_pow_right (by decide : 0<2) (by omega : l≤2)
      have ea : a=1 := by
        by_contra n
        have := Nat.pow_le_pow_left (show 2≤a by omega) 2
        norm_num at this; omega
      have eb : b=1 := by
        by_contra n
        have := Nat.pow_le_pow_left (show 2≤b by omega) 3
        norm_num at this; omega
      have el : l=1 := by
        rw [ea,eb] at red
        have e : (2:ℕ)^1=2^l := by simpa using red
        exact ((Nat.pow_right_inj (by decide : 1<2)).mp e).symm
      left
      exact ⟨by rw [eu,ei,ea,Nat.mul_one],by rw [ed,ej,eb,Nat.mul_one],by omega⟩
  · rintro ⟨t,h|h⟩ <;> obtain ⟨rfl,rfl,rfl⟩ := h <;>
      simp only [mul_pow,←pow_mul,pow_add,show 3*t*2=6*t by omega,
        show 2*t*3=6*t by omega] <;> ring

/-- If one summand has an even exponent above two and the other has
exponent divisible by three, a power-of-two output forces two even bases. -/
theorem even_bases_of_dyadic_result (roots : H1) {a b x y k : ℕ} (hx : 2<x) (hy : 0<y) (hk : 2<k)
    (dx : 2∣x) (dy : 3∣y) (h : a^x+b^y=2^k) : 2∣a ∧ 2∣b := by
  obtain ⟨r,er⟩ := dx
  obtain ⟨s,es⟩ := dy
  have hr : 1<r := by omega
  have hs : 0<s := by omega
  have e : (a^r)^2+(b^s)^3=2^k := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm r 2,Nat.mul_comm s 3,←er,←es]; exact h
  have parity (A n : ℕ) (hn : 0<n) : A^n%2=A%2 := by
    rw [Nat.pow_mod]
    rcases Nat.mod_two_eq_zero_or_one A with he|he <;> rw [he] <;> simp [hn.ne']
  have even : (2^k)%2=0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega))
  have pe := congrArg (fun n : ℕ => n%2) h
  change (a^x+b^y)%2=(2^k)%2 at pe
  rw [Nat.add_mod,parity a x (by omega),parity b y hy,even] at pe
  by_contra! no
  have oa : a%2=1 := by omega
  have ob : b%2=1 := by omega
  have az : a^r%2=1 := (parity a r (by omega)).trans oa
  have bz : b^s%2=1 := (parity b s hs).trans ob
  have sol := (classify_odd roots az bz hk e).1
  have unit := (Nat.Prime.pow_eq_iff (by decide : Nat.Prime 13)).mp sol
  omega

/-- Beal's stated common-divisor conclusion for either order of an even
exponent and a multiple of three when the output base is a power of two. -/
theorem beal_even_cube_dyadic (roots : H1) {a b c x y z : ℕ} (ha : a≠0) (hx : 2<x) (hy : 2<y) (hz : 2<z)
    (output : ∃ t : ℕ, 0<t ∧ c=2^t)
    (exponents : (2∣x ∧ 3∣y) ∨ (3∣x ∧ 2∣y)) (h : a^x+b^y=c^z) :
    1 < Finset.gcd {a,b,c} id := by
  obtain ⟨t,ht,ec⟩ := output
  have kt : 2<t*z := by nlinarith
  rw [ec,←pow_mul] at h
  have bases : 2∣a ∧ 2∣b := by
    rcases exponents with ⟨dx,dy⟩|⟨dx,dy⟩
    · exact even_bases_of_dyadic_result roots hx (by omega) kt dx dy h
    · exact (even_bases_of_dyadic_result roots hy (by omega) kt dy dx ((Nat.add_comm _ _).trans h)).symm
  have dc : 2∣c := ec ▸ dvd_pow_self _ ht.ne'
  have dv : 2 ∣ Finset.gcd {a,b,c} id := by
    apply Finset.dvd_gcd
    intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl|rfl
    · exact bases.1
    · exact bases.2
    · exact dc
  have pos : Finset.gcd {a,b,c} id ≠ 0 := Finset.gcd_ne_zero_iff.mpr ⟨a,Finset.mem_insert_self _ _,ha⟩
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero pos) dv

end BealMordell

namespace BealMordell
open Finset

theorem central_convolution (n : ℕ) :
    ∑ ij ∈ antidiagonal n, ij.1.centralBinom*ij.2.centralBinom=4^n := by
  let C := Nat.centralBinom
  let S := fun j : ℕ => ∑ v ∈ antidiagonal j, C v.1*C v.2
  let T := fun j : ℕ => ∑ v ∈ antidiagonal j, v.1*(C v.1*C v.2)
  have weighted (j : ℕ) : 2*T j=j*S j := by
    have swap : (∑ v ∈ antidiagonal j, v.2*(C v.1*C v.2))=T j := by
      convert Finset.Nat.sum_antidiagonal_swap (n:=j) (f:=fun v => v.1*(C v.1*C v.2)) using 1
      simp only [Prod.fst_swap,Prod.snd_swap,mul_comm]
    change 2*T j=j*(∑ v ∈ antidiagonal j, C v.1*C v.2)
    rw [two_mul]
    conv_lhs => rhs; rw [←swap]
    dsimp [T]; rw [←sum_add_distrib,mul_sum]
    apply sum_congr rfl
    intro v hv
    rw [←add_mul,mem_antidiagonal.mp hv]
  have step (j : ℕ) : T (j+1)=4*T j+2*S j := by
    dsimp [T,S]
    rw [Finset.Nat.sum_antidiagonal_succ (f:=fun v => v.1*(C v.1*C v.2)),zero_mul,zero_add,
      mul_sum,mul_sum,←sum_add_distrib]
    apply sum_congr rfl
    intro v _
    change (v.1+1)*(C (v.1+1)*C v.2)=_
    rw [←mul_assoc,Nat.succ_mul_centralBinom_succ]
    dsimp [C]; ring
  change S n=4^n
  induction n with
  | zero => simp [S,C]
  | succ j ih =>
    have hh := weighted (j+1)
    rw [step j] at hh
    have aux : (j+1)*S (j+1)=(j+1)*(4*S j) := by nlinarith only [hh,weighted j]
    have eq := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos j) aux
    rw [eq,ih,pow_succ,Nat.mul_comm]

/-- For a difference of prime powers that is an odd square, the common
factor of its linear and geometric factors divides the prime exponent.
At a dyadic argument the exceptional common factor is 1 modulo 8. -/
theorem prime_cofactor_cases {p d t u : ℕ} (hp : p.Prime) (ht : 3≤t) (hd : d%8=7)
    (hlt : d<2^t) (eqn : u^2+d^p=(2^t)^p) :
    (¬p∣2^t-d ∧ ∃ a z : ℕ, 2^t-d=a^2 ∧ (∑ i ∈ range p, (2^t)^i*d^(p-1-i))=z^2) ∨
      (p%8=1 ∧ ∃ a z : ℕ, d+p*a^2=2^t ∧ u=p*a*z ∧
        (∑ i ∈ range p, (2^t)^i*d^(p-1-i))=p*z^2) := by
  let W := 2^t
  let A := W-d
  let B := ∑ i ∈ range p, W^i*d^(p-1-i)
  let g := A.gcd B
  have WA : W=A+d := by dsimp [A,W]; omega
  have ap : 0<A := by dsimp [A,W]; omega
  have product : A*B=u^2 := by
    change u^2+d^p=W^p at eqn
    change (W-d)*(∑ i ∈ range p,W^i*d^(p-1-i))=u^2
    rw [Nat.mul_comm,geom_sum₂_mul_of_ge (show d≤W from hlt.le),←eqn,Nat.add_sub_cancel]
  have wd : W.Coprime d := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left t
  have cp : A.Coprime d := Nat.coprime_add_self_left.mp (WA ▸ wd)
  have ga : g∣A := Nat.gcd_dvd_left _ _
  have gb : g∣B := Nat.gcd_dvd_right _ _
  have wdmod : (W:ZMod g)=(d:ZMod g) := by
    rw [WA,Nat.cast_add,(ZMod.natCast_eq_zero_iff ..).mpr ga,zero_add]
  have modB : (B:ZMod g)=(p:ZMod g)*(d:ZMod g)^(p-1) := by
    dsimp [B]
    push_cast
    rw [wdmod,geom_sum₂_self]
  have gpd : g∣p*d^(p-1) := (ZMod.natCast_eq_zero_iff ..).mp (by
    push_cast
    rw [←modB]
    exact (ZMod.natCast_eq_zero_iff ..).mpr gb)
  have gp : g∣p := ((Nat.Coprime.coprime_dvd_left ga cp).pow_right (p-1)).dvd_of_dvd_mul_right gpd
  obtain ⟨a,b,eqA,eqB⟩ := square_parts ap product
  change A=g*a^2 at eqA
  change B=g*b^2 at eqB
  rcases (Nat.dvd_prime hp).mp gp with one|prime
  · refine Or.inl ⟨?_,a,b,by simpa [one] using eqA,by simpa [one] using eqB⟩
    intro pa
    have wp : (W:ZMod p)=(d:ZMod p) := by
      rw [WA,Nat.cast_add,(ZMod.natCast_eq_zero_iff ..).mpr pa,zero_add]
    have pb : p∣B := (ZMod.natCast_eq_zero_iff ..).mp (by
      dsimp [B]; push_cast; rw [wp,geom_sum₂_self,ZMod.natCast_self,zero_mul])
    have pg : p∣g := Nat.dvd_gcd pa pb
    rw [one] at pg
    exact hp.not_dvd_one pg
  have wz : (W:ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 ht)
  have dz : (d:ZMod 8)=7 := by
    apply ZMod.val_injective
    simpa only [ZMod.val_natCast,show (7:ZMod 8).val=7 by decide] using hd
  have eq := congrArg (fun v : ℕ => (v:ZMod 8)) (WA.trans (by rw [eqA,prime]))
  push_cast at eq
  rw [wz,dz] at eq
  have modp := (by decide +kernel : ∀ v a : ZMod 8, 0=v*a^2+7 → v=1) _ _ eq
  have p1 : p%8=1 := by
    simpa only [ZMod.val_natCast,show (1:ZMod 8).val=1 by decide] using congrArg ZMod.val modp
  rw [prime] at eqA eqB
  refine Or.inr ⟨p1,a,b,by omega,?_,eqB⟩
  apply (Nat.pow_left_inj (by decide : 2≠0)).mp
  rw [←product,eqA,eqB]
  ring

theorem exceptional_prime_shape {p d t u : ℕ} (hp : p.Prime) (ht : 3≤t) (hd : d%8=7)
    (lt : d<2^t) (eqn : u^2+d^p=(2^t)^p) (pa : p∣2^t-d) :
    p%8=1 ∧ ∃ a z : ℕ, d+p*a^2=2^t ∧ u=p*a*z ∧
      (∑ i ∈ range p, (2^t)^i*d^(p-1-i))=p*z^2 := by
  rcases prime_cofactor_cases hp ht hd lt eqn with ⟨bad,_⟩|exception
  · exact (bad pa).elim
  · exact exception

/-- Outside the exceptional common prime, both factors are squares. -/
theorem prime_cofactor_square {p d t u : ℕ} (hp : p.Prime) (ht : 3≤t) (hd : d%8=7)
    (cut : p%8≠1 ∨ ¬p∣2^t-d) (hlt : d<2^t) (eqn : u^2+d^p=(2^t)^p) :
    ∃ a z : ℕ, 2^t-d=a^2 ∧ (∑ i ∈ range p, (2^t)^i*d^(p-1-i))=z^2 := by
  rcases prime_cofactor_cases hp ht hd hlt eqn with ⟨_,sol⟩|⟨res,a,z,linear,_,_⟩
  · exact sol
  · have dv : p∣2^t-d := ⟨a^2,by omega⟩
    exact (cut.elim (fun no => no res) (fun no => no dv)).elim

/-- An odd square just below another square cannot have a small positive
sum of square roots if their difference is divisible by a high power of two. -/
theorem dyadic_square_separation {z S e f : ℕ} (oddS : S%2=1) (fp : 0<f)
    (gap : z^2=S^2+4*2^e*f) : 2*2^e≤z+S := by
  have gt : S<z := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (by
    rw [gap]; exact Nat.lt_add_of_pos_right (by positivity))
  have oddZ : z%2=1 := by
    have v := congrArg (fun n : ℕ => (n:ZMod 2)) gap
    push_cast at v
    have s1 : (S:ZMod 2)=1 := by
      apply ZMod.val_injective
      simpa only [ZMod.val_natCast,show (1:ZMod 2).val=1 by decide] using oddS
    rw [s1,show (4:ZMod 2)=0 by decide] at v
    have tab : ∀ a : ZMod 2, a^2=1 → a=1 := by decide +kernel
    have eq := tab (z:ZMod 2) (by simpa using v)
    simpa only [ZMod.val_natCast,show (1:ZMod 2).val=1 by decide] using congrArg ZMod.val eq
  let a := (z-S)/2
  let b := a+S
  have za : z=2*a+S := by dsimp [a]; omega
  have prod : a*b=2^e*f := by
    dsimp [b]; rw [za] at gap; nlinarith only [gap]
  have dv : 2^e∣a*b := ⟨f,prod⟩
  have bound : 2^e≤b := by
    by_cases oa : a%2=1
    · have cp := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬2∣a)).pow_left e
      exact Nat.le_of_dvd (by dsimp [b]; omega) (cp.dvd_of_dvd_mul_left dv)
    · have ob : b%2=1 := by dsimp [b]; omega
      have cp := (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega : ¬2∣b)).pow_left e
      exact (Nat.le_of_dvd (by dsimp [a]; omega) (cp.dvd_of_dvd_mul_right dv)).trans (by dsimp [b]; omega)
  dsimp [b] at bound
  omega

/-- The first m+1 terms of the square-root series give a square whose
positive error is divisible by 2*D*L^(m+1), where D divides both L
and the first omitted central binomial coefficient. -/
theorem geometric_square_precision {m d L D : ℕ} (hm : 0 < m) (hd : d % 2 = 1)
    (hL : 0 < L) (even : 2 ∣ L) (dl : D∣L) (dc : D∣(m+1).centralBinom) :
    ∃ R F : ℕ, R % 2 = 1 ∧ 0 < F ∧
    (∑ i ∈ range (2*m+1), (4*L)^i*d^(2*m-i))=R^2+2*D*L^(m+1)*F := by
  let s := range (m+1)
  let c := fun i : ℕ => i.centralBinom*L^i*d^(m-i)
  let R := ∑ i ∈ s, c i
  let f := fun v : ℕ × ℕ => v.1.centralBinom*v.2.centralBinom*
    L^(v.1+v.2)*d^(2*m-(v.1+v.2))
  let T := range (2*m+1)
  let E := fun j : ℕ => ∑ v ∈ (antidiagonal j).filter (fun v => v∉s ×ˢ s), f v
  have dp : 0<d := by omega
  have oddR : R%2=1 := by
    have div : 2∣∑ i ∈ range m, c (i+1) := by
      apply dvd_sum
      intro i _
      dsimp [c]
      exact ((even.trans (dvd_pow_self L (by omega : i+1≠0))).trans (dvd_mul_left _ _)).trans (dvd_mul_right _ _)
    have base : c 0=d^m := by simp [c]
    have od : d^m%2=1 := by rw [Nat.pow_mod,hd,one_pow]; decide
    have h : R=(∑ i ∈ range m, c (i+1))+c 0 := Finset.sum_range_succ' c m
    omega
  have square : R^2=∑ v ∈ s ×ˢ s, f v := by
    change (∑ i ∈ s, c i)^2=_
    rw [pow_two,sum_mul_sum,←sum_product' s s (fun i j => c i*c j)]
    apply sum_congr rfl
    intro v hv
    obtain ⟨i,j⟩ := v
    have hi : i ≤ m := by have := mem_product.mp hv |>.1; simpa [s,Nat.lt_succ_iff] using this
    have hj : j ≤ m := by have := mem_product.mp hv |>.2; simpa [s,Nat.lt_succ_iff] using this
    dsimp [c,f]
    rw [pow_add,show 2*m-(i+j)=(m-i)+(m-j) by omega,pow_add]
    ring
  have maps (v : ℕ × ℕ) (hv : v∈s ×ˢ s) : v.1+v.2∈T := by
    obtain ⟨h1,h2⟩ := mem_product.mp hv
    dsimp [T,s] at *
    simp only [mem_range] at *
    omega
  have fiber (j : ℕ) : (s ×ˢ s).filter (fun v => v.1+v.2=j)=
      (antidiagonal j).filter (fun v => v∈s ×ˢ s) := by
    ext v
    simp only [mem_filter,HasAntidiagonal.mem_antidiagonal,and_comm]
  have grouped := sum_fiberwise_of_maps_to (g:=fun v : ℕ × ℕ => v.1+v.2) maps f
  simp_rw [fiber] at grouped
  have total (j : ℕ) : (∑ v ∈ antidiagonal j, f v)=(4*L)^j*d^(2*m-j) := by
    calc
      _ = (∑ v ∈ antidiagonal j, v.1.centralBinom*v.2.centralBinom)*(L^j*d^(2*m-j)) := by
        rw [sum_mul]; apply sum_congr rfl
        intro v hv
        dsimp [f]; rw [mem_antidiagonal.mp hv]; ring
      _ = _ := by rw [central_convolution,mul_pow]; ring
  have combine : (∑ j ∈ T, (4*L)^j*d^(2*m-j))=R^2+∑ j ∈ T, E j := by
    rw [square,←grouped,←sum_add_distrib]
    apply sum_congr rfl
    intro j _
    exact (total j).symm.trans (sum_filter_add_sum_filter_not (antidiagonal j) (fun v => v∈s ×ˢ s) f).symm
  let left := fun j : ℕ => ∑ v ∈ antidiagonal j, if m < v.1 then f v else 0
  have flip (v : ℕ × ℕ) : f v.swap=f v := by
    dsimp [f]
    rw [Nat.add_comm v.2 v.1,Nat.mul_comm v.2.centralBinom v.1.centralBinom]
  have split (j : ℕ) (hj : j∈T) : E j=2*left j := by
    have sw := Finset.Nat.sum_antidiagonal_swap (n:=j) (f:=fun v => if m < v.1 then f v else 0)
    simp only [Prod.fst_swap,flip] at sw
    rw [two_mul]
    change E j=left j+(∑ v ∈ antidiagonal j, if m < v.1 then f v else 0)
    rw [←sw]
    dsimp [left,E]
    rw [sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    have hj' := mem_range.mp hj
    have ve := HasAntidiagonal.mem_antidiagonal.mp hv
    by_cases h1 : m < v.1 <;> by_cases h2 : m < v.2
    · omega
    · simp [s,mem_product,h1,h2,Nat.not_lt.mp h2,show ¬v.1 < m+1 by omega]
    · simp [s,mem_product,h1,h2,Nat.not_lt.mp h1,show ¬v.2 < m+1 by omega]
    · simp [s,mem_product,h1,h2,show v.1 < m+1 by omega,show v.2 < m+1 by omega]
  have div : D*L^(m+1)∣∑ j ∈ T, left j := by
    apply dvd_sum
    intro j _
    dsimp [left]; apply dvd_sum
    intro v _
    split_ifs with above
    · dsimp [f]
      by_cases minimal : v.1+v.2=m+1
      · have fi : v.1=m+1 := by omega
        have dv := mul_dvd_mul dc (dvd_refl (L^(m+1)))
        rw [minimal,fi]
        convert (dv.trans (dvd_mul_right _ (v.2.centralBinom*d^(2*m-(m+1))))) using 1; ring
      · have dv₀ : D*L^(m+1)∣L^(m+2) := by
          rw [pow_succ L (m+1),Nat.mul_comm (L^(m+1)) L]
          exact mul_dvd_mul dl (dvd_refl _)
        have dv := dv₀.trans (pow_dvd_pow L (show m+2≤v.1+v.2 by omega))
        exact (dv.trans (dvd_mul_left _ _)).trans (dvd_mul_right _ _)
    · exact dvd_zero _
  have eLeft : (∑ j ∈ T, E j)=2*(∑ j ∈ T, left j) := by
    rw [mul_sum]
    exact sum_congr rfl split
  have epos : 0<∑ j ∈ T, E j := by
    apply sum_pos' (fun _ _ => Nat.zero_le _)
    refine ⟨m+1,mem_range.mpr (by omega),?_⟩
    apply sum_pos' (fun _ _ => Nat.zero_le _)
    refine ⟨(m+1,0),?_,?_⟩
    · simp [s]
    · dsimp [f]
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.centralBinom_pos _) (Nat.centralBinom_pos _))
        (Nat.pow_pos hL)) (Nat.pow_pos dp)
  obtain ⟨F,hF⟩ := div
  rw [eLeft,hF] at combine epos
  refine ⟨R,F,oddR,?_,by linear_combination combine⟩
  by_contra! zero
  rw [show F=0 by omega] at epos
  simp at epos

/-- Each common power of two in L and the first omitted central binomial
coefficient improves the bound on the dyadic argument. -/
theorem geometric_square_bound_precise {m d z t b r : ℕ} (hm : 0 < m) (hd : d%2=1)
    (lt : d<2^t) (hb : 2*m+1≤b^2) (rp : 0<r) (rt : r+2≤t)
    (coeff : 2^r∣(m+1).centralBinom)
    (he : (∑ i ∈ range (2*m+1), (2^t)^i*d^(2*m-i))=z^2) :
    2^(r-1)*2^t < b*4^(m+1) := by
  let W := 2^t
  let L := 2^(t-2)
  have lp : 0<L := Nat.two_pow_pos _
  have wL : W=4*L := by
    change 2^t=4*2^(t-2)
    calc
      2^t=2^(2+(t-2)) := by congr 1; omega
      _=4*2^(t-2) := by rw [pow_add]; rfl
  have dl : 2^r∣L := pow_dvd_pow 2 (by omega : r≤t-2)
  have ev : 2∣L := (dvd_pow_self 2 rp.ne').trans dl
  obtain ⟨R,F,oddR,fp,approx⟩ := geometric_square_precision hm hd lp ev dl coeff
  change (∑ i ∈ range (2*m+1), W^i*d^(2*m-i))=z^2 at he
  change d<W at lt
  rw [←wL,he] at approx
  let e := (r-1)+(t-2)*(m+1)
  have en : 2^e=2^(r-1)*L^(m+1) := by dsimp [e,L]; rw [pow_add,pow_mul]
  have pr : 2^r=2*2^(r-1) := by
    calc
      2^r=2^(1+(r-1)) := by congr 1; omega
      _=2*2^(r-1) := by rw [pow_add,pow_one]
  have se : z^2=R^2+4*2^e*F := by rw [en]; rw [pr] at approx; linear_combination approx
  have sep := dyadic_square_separation oddR fp se
  have rz : R<z := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp (by
    rw [approx]; exact Nat.lt_add_of_pos_right (by positivity))
  have bound : z≤b*W^m := by
    apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
    calc
      z^2=∑ i ∈ range (2*m+1), W^i*d^(2*m-i) := he.symm
      _ ≤ ∑ _i ∈ range (2*m+1), W^(2*m) := by
        apply sum_le_sum
        intro i hi
        have hi' := mem_range.mp hi
        calc
          W^i*d^(2*m-i)≤W^i*W^(2*m-i) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left lt.le _)
          _=W^(2*m) := by rw [←pow_add]; congr 1; omega
      _ = (2*m+1)*W^(2*m) := by simp
      _ ≤ b^2*W^(2*m) := Nat.mul_le_mul_right _ hb
      _ = (b*W^m)^2 := by rw [mul_pow,←pow_mul W m 2,Nat.mul_comm m 2]
  have first : 2^(r-1)*L^(m+1)<b*W^m := by rw [en] at sep; omega
  have finalBound := Nat.mul_lt_mul_of_pos_right first (Nat.pow_pos (n:=m+1) (by decide : 0<4))
  have prod : L^(m+1)*4^(m+1)=W^m*W := by rw [←mul_pow,Nat.mul_comm L 4,←wL,pow_succ]
  have reduce : W^m*(2^(r-1)*W)<W^m*(b*4^(m+1)) := by
    calc
      _ = (2^(r-1)*L^(m+1))*4^(m+1) := by rw [Nat.mul_assoc,prod]; ring
      _ < _ := finalBound
      _ = _ := by ring
  exact Nat.lt_of_mul_lt_mul_left reduce

theorem geometric_square_bound {m d z t b : ℕ} (hm : 0 < m) (hd : d%2=1) (lt : d<2^t)
    (hb : 2*m+1≤b^2)
    (he : (∑ i ∈ range (2*m+1), (2^t)^i*d^(2*m-i))=z^2) :
    2^t<b*4^(m+1) := by
  by_cases high : 3≤t
  · simpa using geometric_square_bound_precise hm hd lt hb (by decide : 0<1) high
      (by simpa using Nat.two_dvd_centralBinom_succ m) he
  have bp : 0<b := by
    by_contra! zero
    have bz : b=0 := by omega
    simp [bz] at hb
  have hz : 2^t≤4 := Nat.pow_le_pow_right (by decide : 0<2) (by omega : t≤2)
  have mon : 16≤4^(m+1) := Nat.pow_le_pow_right (by decide : 0<4) (by omega : 2 ≤ m+1)
  nlinarith only [hz,mon,Nat.mul_le_mul_right (4^(m+1)) (show 1≤b by omega)]

/-- If the prime exponent divides the exponent of two, a solution either
has a bounded dyadic root or has the exceptional common factor at a prime
congruent to one modulo eight. -/
theorem prime_dividing_dyadic_exponent {m d u t b : ℕ} (hm : 0 < m) (hp : (2*m+1).Prime)
    (ht : 3≤t) (hd : d%8=7) (hu : 0<u) (hb : 2*m+1≤b^2)
    (eqn : u^2+d^(2*m+1)=(2^t)^(2*m+1)) :
    (∃ a : ℕ, d+a^2=2^t ∧ 2^t<b*4^(m+1)) ∨
      ((2*m+1)%8=1 ∧ (2*m+1)∣2^t-d) := by
  by_cases other : (2*m+1)%8=1 ∧ (2*m+1)∣2^t-d
  · exact Or.inr other
  have positive := Nat.pow_pos (n:=2) hu
  have lt : d<2^t := (Nat.pow_lt_pow_iff_left (by omega : 2*m+1≠0)).mp (by omega)
  obtain ⟨a,z,ha,he⟩ := prime_cofactor_square hp ht hd (by tauto) lt eqn
  exact Or.inl ⟨a,by omega,geometric_square_bound hm (by omega) lt hb (by simpa using he)⟩

/-- It suffices to check a single finite range of the exponent t and the
square root a of the smaller factor, with d=2^t−a². -/
theorem exclude_repeated_prime_finite {p m b T A r : ℕ} (ep : p=2*m+1)
    (hm : 0 < m) (prime : p.Prime) (hb : p≤b^2) (rp : 0<r) (rt : r+2≤T)
    (coeff : 2^r∣(m+1).centralBinom) (hT : b*4^(m+1)≤2^(r-1)*2^T)
    (hA : 2^(T-1)≤A^2)
    (check : ∀ t : Fin T, ∀ a : Fin A, 3≤t.val → a.val^2<2^t.val →
      let d := 2^t.val-a.val^2
      d%8=7 → let N := (2^t.val)^p-d^p
              (Nat.sqrt N)^2≠N)
    {u d t : ℕ} (hu : 0<u) (hd : d%8=7)
    (cut : p%8≠1 ∨ ¬p∣2^t-d) (eqn : u^2+d^p=(2^t)^p) : False := by
  subst p
  have dp : 0<d := by omega
  have up := Nat.pow_pos (n:=2) hu
  have lt : d<2^t := (Nat.pow_lt_pow_iff_left (by omega : 2*m+1≠0)).mp (by omega)
  have th : 3≤t := by
    by_contra! n
    have low : 2^t≤4 := Nat.pow_le_pow_right (by decide : 0<2) (by omega : t≤2)
    omega
  obtain ⟨a,z,square,geom⟩ := prime_cofactor_square prime th hd cut lt eqn
  have da : d+a^2=2^t := by omega
  have small : t<T := by
    by_contra! large
    have bound := geometric_square_bound_precise hm (by omega : d%2=1) lt hb rp
      (rt.trans large) coeff (by simpa using geom)
    have lower := Nat.mul_le_mul_left (2^(r-1)) (Nat.pow_le_pow_right (n:=2) (by decide) large)
    omega
  have less : a^2<2^t := by omega
  have upper := Nat.pow_le_pow_right (n:=2) (by decide) (by omega : t≤T-1)
  have slim := (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp ((less.trans_le upper).trans_le hA)
  have base : 2^t-a^2=d := by omega
  have eval := check ⟨t,small⟩ ⟨a,slim⟩ th less
  change (2^t-a^2)%8=7 → (Nat.sqrt ((2^t)^(2*m+1)-(2^t-a^2)^(2*m+1)))^2≠
    (2^t)^(2*m+1)-(2^t-a^2)^(2*m+1) at eval
  rw [base,←eqn,Nat.add_sub_cancel] at eval
  exact eval hd (by rw [show u^2=u*u by ring,Nat.sqrt_eq,pow_two])

/-- The three masks include every square residue modulo 105, 143 and 323. -/
private theorem bits_of_square {N : ℕ} (h : (Nat.sqrt N)^2=N) : (1904012832374999573601999487507:ℕ).testBit (N%105)=true ∧ (12337925766874303876000583143494390993435:ℕ).testBit (N%143)=true ∧ (4341437005659545356311106875435249476073376895144305954155417450284306736590537326127758294319635:ℕ).testBit (N%323)=true := by
  have valid (q mask : ℕ) (hq : 0<q)
      (tab : ∀ x : Fin q, mask.testBit (x.val^2%q)=true) : mask.testBit (N%q)=true := by
    let x := Nat.sqrt N
    have sq : x^2=N := h
    have md : N%q=(x%q)^2%q := by rw [←sq,Nat.pow_mod]
    rw [md]
    exact tab ⟨x%q,Nat.mod_lt _ hq⟩
  exact ⟨valid _ _ (by decide) (by decide +kernel),valid _ _ (by decide) (by decide +kernel),
    valid _ _ (by decide) (by decide +kernel)⟩

theorem repeated_check_blocks {T A p : ℕ} (w : ℕ) (wp : 0<w)
    (test : ∀ t : Fin T, ∀ i : Fin (Nat.sqrt (2^t.val)/w+1), ∀ j : Fin w,
      let a := i.val*w+j.val
      3≤t.val → a^2<2^t.val → let d := 2^t.val-a^2
      d%8=7 → let N := (2^t.val)^p-d^p
              ¬ ((1904012832374999573601999487507:ℕ).testBit (N%105)=true ∧ (12337925766874303876000583143494390993435:ℕ).testBit (N%143)=true ∧ (4341437005659545356311106875435249476073376895144305954155417450284306736590537326127758294319635:ℕ).testBit (N%323)=true ∧ (Nat.sqrt N)^2=N)) :
    ∀ t : Fin T, ∀ a : Fin A, 3≤t.val → a.val^2<2^t.val →
      let d := 2^t.val-a.val^2
      d%8=7 → let N := (2^t.val)^p-d^p
              (Nat.sqrt N)^2≠N := by
  intro t a ht ha
  dsimp only
  intro hd eq
  have less : a.val≤Nat.sqrt (2^t.val) := Nat.le_sqrt.mpr (by simpa [pow_two] using ha.le)
  have row : a.val/w≤Nat.sqrt (2^t.val)/w := Nat.div_le_div_right less
  let i : Fin (Nat.sqrt (2^t.val)/w+1) := ⟨a.val/w,by omega⟩
  let j : Fin w := ⟨a.val%w,Nat.mod_lt _ wp⟩
  have id : i.val*w+j.val=a.val := by
    dsimp [i,j]
    rw [Nat.mul_comm,Nat.div_add_mod]
  have pred := test t i j
  dsimp only at pred
  rw [id] at pred
  obtain ⟨x,y,z⟩ := bits_of_square eq
  exact pred ht ha hd ⟨x,y,z,eq⟩

private theorem lifted_residue_bit {q B a : ℕ} (large : 64≤q)
    (allowed : B.testBit (a%q)=true) :
    ((B ||| (B <<< q)) >>> ((64*(a/64))%q)).testBit (a%64)=true := by
  let v := (64*(a/64))%q
  let j := a%64
  have qp : 0<q := by omega
  have vq : v<q := Nat.mod_lt _ qp
  have jl : j<64 := Nat.mod_lt _ (by decide)
  have eq : (v+j)%q=a%q := by
    dsimp [v,j]; rw [Nat.mod_add_mod,Nat.div_add_mod]
  change ((B ||| (B <<< q)) >>> v).testBit j=true
  rw [Nat.testBit_shiftRight,Nat.testBit_or,Nat.testBit_shiftLeft]
  by_cases low : v+j<q
  · rw [Nat.mod_eq_of_lt low] at eq
    simp [eq,allowed]
  · have ge : q≤v+j := by omega
    have second : v+j-q<q := by omega
    rw [Nat.mod_eq_sub_mod ge,Nat.mod_eq_of_lt second] at eq
    simp [ge,eq,allowed]

/-- Each triple contains a modulus, a bit mask for squares, and a bit
mask for the possible residues of the linear-factor square root.
Shifting two copies of each mask tests a whole block of 64 roots at once. -/
theorem repeated_residue_layers {p T A : ℕ} (rows : List (List (ℕ × ℕ × ℕ)))
    (cert : (List.range T).all (fun t =>
      decide (t<3) ||
      let w := 2^t
      let layer := rows.getD t []
      layer.all (fun v =>
        let q := v.1
        let S := v.2.1
        let B := v.2.2
        decide (64≤q) &&
        ((List.range q).all (fun y => S.testBit (((y:ZMod q)^2).val)) &&
         (List.range q).all (fun a =>
           decide (S.testBit (((w:ZMod q)^p-((w:ZMod q)-(a:ZMod q)^2)^p).val)=true →
             B.testBit a=true)))) &&
      (List.range (Nat.sqrt w /64+1)).all (fun i =>
        decide (layer.foldr (fun v mask =>
          mask &&& ((v.2.2 ||| (v.2.2 <<< v.1)) >>> ((64*i)%v.1))) 12297829382473034410 = 0)))=true) :
    ∀ t : Fin T, ∀ a : Fin A, 3≤t.val → a.val^2<2^t.val →
      let d := 2^t.val-a.val^2
      d%8=7 → let N := (2^t.val)^p-d^p
              (Nat.sqrt N)^2≠N := by
  intro t a ht ha
  dsimp only
  intro hd bad
  let w := 2^t.val
  let d := w-a.val^2
  let u := Nat.sqrt (w^p-d^p)
  have da : d+a.val^2=w := by dsimp [d,w]; omega
  have eqn : u^2+d^p=w^p := by
    have dle : d≤w := by omega
    have ple := Nat.pow_le_pow_left dle p
    change u^2=w^p-d^p at bad
    omega
  let layer := rows.getD t.val []
  have checks := List.all_eq_true.mp cert t.val (List.mem_range.mpr t.isLt)
  simp only [show decide (t.val<3)=false by simp [show ¬t.val<3 by omega],Bool.false_or] at checks
  obtain ⟨valid,layers⟩ := Bool.and_eq_true_iff.mp checks
  have good (v : ℕ × ℕ × ℕ) (hv : v∈layer) :
      ((v.2.2 ||| (v.2.2 <<< v.1)) >>> ((64*(a.val/64))%v.1)).testBit (a.val%64)=true := by
    obtain ⟨big,ch⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp valid v hv)
    obtain ⟨squares,table⟩ := Bool.and_eq_true_iff.mp ch
    have bq : 64≤v.1 := of_decide_eq_true big
    have qp : 0<v.1 := by omega
    apply lifted_residue_bit bq
    have sq := List.all_eq_true.mp squares (u%v.1) (List.mem_range.mpr (Nat.mod_lt _ qp))
    have tab := of_decide_eq_true (List.all_eq_true.mp table (a.val%v.1) (List.mem_range.mpr (Nat.mod_lt _ qp)))
    simp only [ZMod.natCast_mod] at sq tab
    apply tab
    have e1 := congrArg (fun n : ℕ => (n:ZMod v.1)) eqn
    have e2 := congrArg (fun n : ℕ => (n:ZMod v.1)) da
    push_cast at e1 e2
    have dd : (w:ZMod v.1)-(a.val:ZMod v.1)^2=(d:ZMod v.1) := by linear_combination -e2
    have value : (w:ZMod v.1)^p-((w:ZMod v.1)-(a.val:ZMod v.1)^2)^p=(u:ZMod v.1)^2 := by
      rw [dd]; linear_combination -e1
    change v.2.1.testBit (((w:ZMod v.1)^p-((w:ZMod v.1)-(a.val:ZMod v.1)^2)^p).val)=true
    rw [value]; exact sq
  have ao : a.val%2=1 := by
    have wz : w%2=0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : t.val≠0))
    have d7 : d%8=7 := hd
    by_contra! n
    have a0 : a.val^2%2=0 := by rw [Nat.pow_mod,show a.val%2=0 by omega]
    omega
  have bitOdd : (12297829382473034410:ℕ).testBit (a.val%64)=true := by
    have tab : ∀ j : Fin 64, j.val%2=1 → (12297829382473034410:ℕ).testBit j.val=true := by decide +kernel
    exact tab ⟨a.val%64,Nat.mod_lt _ (by decide)⟩ ((Nat.mod_mod_of_dvd a.val (by decide : 2∣64)).trans ao)
  let fold := fun (v : ℕ × ℕ × ℕ) (mask : ℕ) =>
    mask &&& ((v.2.2 ||| (v.2.2 <<< v.1)) >>> ((64*(a.val/64))%v.1))
  have bit (L : List (ℕ × ℕ × ℕ)) (hl : ∀ v∈L, v∈layer) :
      (L.foldr fold 12297829382473034410).testBit (a.val%64)=true := by
    induction L with
    | nil => exact bitOdd
    | cons v l ih =>
      rw [List.foldr_cons]
      dsimp only [fold]
      rw [Nat.testBit_and,good v (hl v (by simp)),ih (fun x hx => hl x (by simp [hx]))]
      rfl
  have root : a.val≤Nat.sqrt w := Nat.le_sqrt.mpr (by simpa [pow_two] using ha.le)
  have row : a.val/64≤Nat.sqrt w/64 := Nat.div_le_div_right root
  have zero := of_decide_eq_true (List.all_eq_true.mp layers (a.val/64) (List.mem_range.mpr (Nat.lt_succ_of_le row)))
  change layer.foldr fold 12297829382473034410=0 at zero
  have impossible := bit layer (fun _ h => h)
  rw [zero,Nat.zero_testBit] at impossible
  contradiction

set_option maxHeartbeats 8000000 in
theorem fast_repeated_31 :
    ∀ t : Fin 35, ∀ a : Fin 131072, 3≤t.val → a.val^2<2^t.val →
      let d := 2^t.val-a.val^2
      d%8=7 → let N := (2^t.val)^31-d^31
              (Nat.sqrt N)^2≠N := by
  let layers : List (List (ℕ × ℕ × ℕ)) := [[],
      [],
      [],
      [(83, 2911111237809585785085595, 873070762930370586898897), (163, 4897055654650805677578640992142773019711325193811, 11473446681616343579165614293308215960778012809663), (79, 89932533647391829339959, 67702110045857573530225)],
      [(83, 2911111237809585785085595, 2229765758889015298048441), (113, 8586949319576899938239170417650583, 829339535088128003701952520592465), (67, 61808106872519771731, 141187571994130886239)],
      [(251, 980841963289099760117707917989875854385982037078632413407484287068694360763, 1008011337166495795174004380547597220324117958285025622952059502031026263493), (101, 1550432784880709368503235994227, 525837998973905660186775925081), (67, 61808106872519771731, 71046560001225259453)],
      [(83, 2911111237809585785085595, 274639776280781281904065), (149, 441852139177177952668163358831104772057793267, 438755583891732272167099623183060445552790899), (79, 89932533647391829339959, 575263444736925501000607)],
      [(163, 4897055654650805677578640992142773019711325193811, 963390012792205925062032164559925262507921363281), (263, 594840964307296816185063038393585183677063853173192926460230716038812197665631, 9127903541547153272214049125677025375164805746942882007945998046849471971666803), (79, 89932533647391829339959, 157109455636932431651461)],
      [(79, 89932533647391829339959, 597432827384860464595327), (107, 50079290986288516948354744811035, 12166237828200317872662886947217), (97, 152076272278209298711361952607, 116297265315402927645748203451)],
      [(269, 580539669191279374314387280562189650426427849693336474503682780225423163520019059, 307556198759997443568936543459120714035742653956922476487770048013694277044797845), (197, 118293807873742757827437296739134280345237452048103702628051, 170637884026519489903586097639947410272658113179185946639671), (71, 20052041432995567487, 511128433945700117977)],
      [(167, 6058870142380879454330449817022811454536025988063, 2938540697726171014955915440712453127233804779585), (179, 213639904063009026037015904849907732195616726489756219, 692407916981724526332151481678166050790859268773008847), (73, 9059857384996697084767, 3903271581874347861805)],
      [(83, 2911111237809585785085595, 5479734942494137069887763), (101, 1550432784880709368503235994227, 1251200334124195092963374060797), (79, 89932533647391829339959, 311517110606324482633603)],
      [(83, 2911111237809585785085595, 4309178281673310169731229), (211, 1276851644109113882183330310376468972669945505335701621656087155, 2877969412161044878096186968723796082769138863531994763027216375), (109, 473022961816146413042658758988475, 565403223935438622265023469814263), (89, 526807005835216593886842679, 236908427869755913483829005)],
      [(83, 2911111237809585785085595, 7386298234139114291299207), (139, 264983527547230301571683161851591864167155, 131991354896677796014336657501262390787097), (269, 580539669191279374314387280562189650426427849693336474503682780225423163520019059, 295660786456735496039804633018197612351023121690261107478588524961707864216414181)],
      [(79, 89932533647391829339959, 116502899241703539332377), (83, 2911111237809585785085595, 1177645709276125675416049), (73, 9059857384996697084767, 6090450849997837455691), (89, 526807005835216593886842679, 48767871651277309606733905)],
      [(83, 2911111237809585785085595, 3098725682199371390075029), (137, 144045494737659012533968429665233398647703, 85026352298709320509949377145037649211005), (107, 50079290986288516948354744811035, 126927871289861563255359814435879), (79, 89932533647391829339959, 42834861073723902412945)],
      [(83, 2911111237809585785085595, 125957162181073601516929), (139, 264983527547230301571683161851591864167155, 370317260385312580065668459351306923679779), (109, 473022961816146413042658758988475, 79880061825788453297682973656049), (73, 9059857384996697084767, 8507552590368839119567), (89, 526807005835216593886842679, 394658088889784047042083211)],
      [(83, 2911111237809585785085595, 643225628949448439283985), (167, 6058870142380879454330449817022811454536025988063, 11470290200404038539427511834224950210600721751009), (197, 118293807873742757827437296739134280345237452048103702628051, 194939084870973398455112351511150902204794289456888998730815), (149, 441852139177177952668163358831104772057793267, 702791347462250625823223836195062130308378751), (73, 9059857384996697084767, 5702529143591216419507)],
      [(83, 2911111237809585785085595, 4837705731430457606889475), (103, 1760368345969468176824550810519, 8970772253847650877367245888655), (227, 64921184177694085253139702133910157218476815637784532535037175340699, 57012351615897663065938569287670674585657933172922113854524535581573), (109, 473022961816146413042658758988475, 3722505618066917215706276683009), (139, 264983527547230301571683161851591864167155, 176271948160382656034098029639767962027525)],
      [(83, 2911111237809585785085595, 4878666152531592351418627), (79, 89932533647391829339959, 246275647697052869420077), (269, 580539669191279374314387280562189650426427849693336474503682780225423163520019059, 551077096799618774454883296138618848179600551302263813367101259612874356725856851), (113, 8586949319576899938239170417650583, 4005972825544167689281934798161549), (167, 6058870142380879454330449817022811454536025988063, 95271427806257444266474956030311850743449999373443), (67, 61808106872519771731, 106181190184036407355)],
      [(83, 2911111237809585785085595, 2720475361892545302528037), (139, 264983527547230301571683161851591864167155, 415254481322872962754050168832689857405491), (79, 89932533647391829339959, 415926850424603904231451), (163, 4897055654650805677578640992142773019711325193811, 3790985592704250851100962149716922629320345190805), (113, 8586949319576899938239170417650583, 6639999377914236794984186035575691), (67, 61808106872519771731, 136383474096162001519)],
      [(83, 2911111237809585785085595, 7348522317436111055716999), (79, 89932533647391829339959, 67959910820356195624561), (163, 4897055654650805677578640992142773019711325193811, 9547159657255540851051656833160459863885559308567), (127, 30790515292689894969866990722818747159, 136093086041022914436980237107315951207), (67, 61808106872519771731, 115239633798059143111), (239, 7065734077645836540429506696338911894775431419613439055992324412120959, 598410565294175817157155815181426425761388613916047666989382739562737003), (73, 9059857384996697084767, 2025026086330116706009)],
      [(83, 2911111237809585785085595, 1824401828052143325226009), (79, 89932533647391829339959, 238868207204324713474381), (127, 30790515292689894969866990722818747159, 53443187779780373439360339592365681685), (139, 264983527547230301571683161851591864167155, 206320558355330622265896248769565105104805), (167, 6058870142380879454330449817022811454536025988063, 16289249556520034869198705853162104065222076703953), (89, 526807005835216593886842679, 511245673426018413818977687), (67, 61808106872519771731, 71685797414897103997)],
      [(83, 2911111237809585785085595, 3098593306858261475901589), (79, 89932533647391829339959, 7916639173210577089921), (127, 30790515292689894969866990722818747159, 74645379380503911852644951428875686941), (181, 2211898081514375631961044640985059119846564062529976891, 2107442333032374901818616453627154579809277790542577691), (239, 7065734077645836540429506696338911894775431419613439055992324412120959, 824564323680824444452442244644903201629658431523389923983303049108201199), (101, 1550432784880709368503235994227, 1954435644444323882583354914119), (107, 50079290986288516948354744811035, 1023468649339167819825261933313)],
      [(83, 2911111237809585785085595, 5100466398475454667325891), (79, 89932533647391829339959, 127961831763742705785049), (107, 50079290986288516948354744811035, 67685844059669832420324287751853), (113, 8586949319576899938239170417650583, 6017657772791955921364139943277651), (239, 7065734077645836540429506696338911894775431419613439055992324412120959, 123376714918981401150251053606422969107509953420454242324810037481047945), (127, 30790515292689894969866990722818747159, 11402901316766437514027888556551710993), (167, 6058870142380879454330449817022811454536025988063, 25999377380115412768696581484383464874888132055945), (67, 61808106872519771731, 18412345263574884337)],
      [(83, 2911111237809585785085595, 964268132081344751125297), (79, 89932533647391829339959, 396799334182019161743403), (113, 8586949319576899938239170417650583, 335777126423644820118727754368033), (163, 4897055654650805677578640992142773019711325193811, 982646647808654816271610486942646328966742246225), (167, 6058870142380879454330449817022811454536025988063, 112461438565276533612032828268090843541480690208563), (107, 50079290986288516948354744811035, 87812696145630059880841505776291), (191, 26252236807386378396776436556232156846523662924177192831, 541314912185092364247499710319074642854031424133859493993), (71, 20052041432995567487, 488725268532401962585)],
      [(83, 2911111237809585785085595, 2496878946716620326948997), (79, 89932533647391829339959, 88730465060429698192201), (139, 264983527547230301571683161851591864167155, 564876397048615537500495193161995105469415), (107, 50079290986288516948354744811035, 33470961446438029251933801735769), (113, 8586949319576899938239170417650583, 2963882179325283436289535514382629), (181, 2211898081514375631961044640985059119846564062529976891, 2803292007854005495910445435153169917619171641544427695), (127, 30790515292689894969866990722818747159, 113755889625496939537130617163378928043), (73, 9059857384996697084767, 5702529143591216419507)],
      [(83, 2911111237809585785085595, 146946881616636006600577), (79, 89932533647391829339959, 468179841069395508470983), (113, 8586949319576899938239170417650583, 6506885346016997697072406224972811), (197, 118293807873742757827437296739134280345237452048103702628051, 167039818178755529373544270918618480793700625366872456793687), (167, 6058870142380879454330449817022811454536025988063, 148535058301872278656740099345851336321978060342695), (139, 264983527547230301571683161851591864167155, 75152896080906270568219345404895511819185), (103, 1760368345969468176824550810519, 6489721897382168606716527548299), (163, 4897055654650805677578640992142773019711325193811, 6290109273186454966929637046274140965016820857635), (73, 9059857384996697084767, 9378855297755969935615)],
      [(83, 2911111237809585785085595, 6668651946714051488399899), (79, 89932533647391829339959, 86729729706663388494409), (113, 8586949319576899938239170417650583, 7494832531689416389319079527286331), (167, 6058870142380879454330449817022811454536025988063, 436029716875557832924556876036250249033756848641), (269, 580539669191279374314387280562189650426427849693336474503682780225423163520019059, 89589016025909349853900772966662911367817658514437208521460421536112207559616561), (251, 980841963289099760117707917989875854385982037078632413407484287068694360763, 988219935771300550830395958593167082163859604562377769361048487290818572101), (197, 118293807873742757827437296739134280345237452048103702628051, 35899319946495977313052273106968623556668673454715306641257), (149, 441852139177177952668163358831104772057793267, 282457336021568943165002494943780746873247053), (73, 9059857384996697084767, 3903271581874347861805), (71, 20052041432995567487, 2286925736290436423647)],
      [(83, 2911111237809585785085595, 95308664056105229828737), (79, 89932533647391829339959, 491334609496102296277015), (139, 264983527547230301571683161851591864167155, 352255108937157185427417104531420410236163), (127, 30790515292689894969866990722818747159, 53443187779780373439360339592365681685), (163, 4897055654650805677578640992142773019711325193811, 3306178433256600839054191982604160102683415907365), (269, 580539669191279374314387280562189650426427849693336474503682780225423163520019059, 26446012619608777495609768277031203413971917485927568237790347974012210172758465), (107, 50079290986288516948354744811035, 158858271734563594210761845803711), (103, 1760368345969468176824550810519, 3092292720653612113286718677221), (109, 473022961816146413042658758988475, 102315765806204343797655817008169), (137, 144045494737659012533968429665233398647703, 143697466669221046278715154683663218526615)],
      [(83, 2911111237809585785085595, 2626061301518693856871237), (79, 89932533647391829339959, 105227409054180598747753), (139, 264983527547230301571683161851591864167155, 504687752621568761995825795065339691814203), (113, 8586949319576899938239170417650583, 4458457182261911454688938063966061), (109, 473022961816146413042658758988475, 550305165879708379960200389648695), (107, 50079290986288516948354744811035, 61385131908960484381133891778061), (167, 6058870142380879454330449817022811454536025988063, 95004490778548034142569771160009684992115321110659), (223, 2341578194317687999480691957418079046404556494213344638229394998167, 13425771364436497596634908534919450860009611839765457858828823183103), (173, 6959499201072490563778903106400207980707536372360787, 9749797700268990440103423217402915940981044192885783), (101, 1550432784880709368503235994227, 793506302182081747809934766101)],
      [(83, 2911111237809585785085595, 5664648679827146852353), (79, 89932533647391829339959, 285703523043200221577533), (139, 264983527547230301571683161851591864167155, 180020943761424352281162239439042606336133), (113, 8586949319576899938239170417650583, 10159902747133451624259003621629119), (109, 473022961816146413042658758988475, 423158618066669771046600894852811), (103, 1760368345969468176824550810519, 5717524220416557791947017311251), (197, 118293807873742757827437296739134280345237452048103702628051, 189697726537126533709931440854871558460982408812864064685855), (149, 441852139177177952668163358831104772057793267, 139522572640051523827111052695326189853696153), (229, 622496887405363581323637999554697472253602734436003095745513373030971, 472947138155794593865897004558982286268664520350598722379355044566115), (157, 126304807362733370595828809000324029340048915995, 45310569964649763249272386006468098054614744569)],
      [(83, 2911111237809585785085595, 5463077144294310870888979), (79, 89932533647391829339959, 14931815582483595826369), (139, 264983527547230301571683161851591864167155, 624180132347841500248495010842088733615439), (113, 8586949319576899938239170417650583, 829339535088128003701952520592465), (167, 6058870142380879454330449817022811454536025988063, 169546082417723348177633888501291500834549611905071), (127, 30790515292689894969866990722818747159, 104345001395729992605540597677392658803), (103, 1760368345969468176824550810519, 7745297960137364043660663341959), (137, 144045494737659012533968429665233398647703, 77621804609560931125781221296552140660893), (163, 4897055654650805677578640992142773019711325193811, 2251683651015869696527793410209094775418985211161), (89, 526807005835216593886842679, 380165884977901629701077363), (157, 126304807362733370595828809000324029340048915995, 15446797595878455893715821969456555604738132817)],
      [(83, 2911111237809585785085595, 1535085414121545086306857), (79, 89932533647391829339959, 371675755604923304717683), (139, 264983527547230301571683161851591864167155, 71184667569651491125608026210578515675313), (113, 8586949319576899938239170417650583, 4778422372448941881395165002753885), (127, 30790515292689894969866990722818747159, 113755889625496939537130617163378928043), (149, 441852139177177952668163358831104772057793267, 370887461641086735717327995577077245860798787), (163, 4897055654650805677578640992142773019711325193811, 3346666386730469375159704918989286386277983896869), (251, 980841963289099760117707917989875854385982037078632413407484287068694360763, 3394056549091306860753776132403431854719572981043540783780478900769373745183), (197, 118293807873742757827437296739134280345237452048103702628051, 192632584454351304391390438385331764475159973945972513637215), (71, 20052041432995567487, 880288612650771684853), (101, 1550432784880709368503235994227, 1945794261404971716197655723079), (67, 61808106872519771731, 109098236352648250747)],
      [(83, 2911111237809585785085595, 2555134499767835787824005), (79, 89932533647391829339959, 6461603511268556307073), (139, 264983527547230301571683161851591864167155, 251059947652316362437542347138253859272821), (113, 8586949319576899938239170417650583, 1427729250380393053635663017580937), (127, 30790515292689894969866990722818747159, 133803306206401932749905213073484518695), (239, 7065734077645836540429506696338911894775431419613439055992324412120959, 114094365947749069198033571832540952975654748670374487243036886254477577), (197, 118293807873742757827437296739134280345237452048103702628051, 121259753568481896514040466040701256216358172722916809417395), (199, 113609121299519182719251449131805282219309388139817713625015, 99761296631232334520195878910135060245884914356965939423217), (149, 441852139177177952668163358831104772057793267, 236005270528075691667034754522965126188575317), (163, 4897055654650805677578640992142773019711325193811, 1782851785109707669903689810302544499200990192073), (179, 213639904063009026037015904849907732195616726489756219, 566235879894455526385355849784752921064583909540718971), (67, 61808106872519771731, 44882507408975837029)]]
  exact repeated_residue_layers layers (by decide +kernel)

theorem exclude_repeated_five {u d t : ℕ} (hu : 0<u) (hd : d%8=7) :
    u^2+d^5≠(2^t)^5 := by
  intro eqn
  exact exclude_repeated_prime_finite (p:=5) (m:=2) (b:=3) (r:=2) (T:=7) (A:=8)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel) hu hd (Or.inl (by decide)) eqn

theorem exclude_repeated_seven {u d t : ℕ} (hu : 0<u) (hd : d%8=7) :
    u^2+d^7≠(2^t)^7 := by
  intro eqn
  exact exclude_repeated_prime_finite (p:=7) (m:=3) (b:=3) (r:=1) (T:=10) (A:=23)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel) hu hd (Or.inl (by decide)) eqn

theorem exclude_repeated_eleven {u d t : ℕ} (hu : 0<u) (hd : d%8=7) :
    u^2+d^11≠(2^t)^11 := by
  intro eqn
  exact exclude_repeated_prime_finite (p:=11) (m:=5) (b:=4) (r:=2) (T:=13) (A:=64)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel) hu hd (Or.inl (by decide)) eqn

theorem exclude_repeated_thirteen {u d t : ℕ} (hu : 0<u) (hd : d%8=7) :
    u^2+d^13≠(2^t)^13 := by
  intro eqn
  exact exclude_repeated_prime_finite (p:=13) (m:=6) (b:=4) (r:=3) (T:=14) (A:=91)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide +kernel) hu hd (Or.inl (by decide)) eqn

set_option maxHeartbeats 8000000 in
theorem exclude_repeated_seventeen {u d t : ℕ} (hu : 0<u) (hd : d%8=7) (cut : ¬17∣2^t-d) :
    u^2+d^17≠(2^t)^17 := by
  intro eqn
  exact exclude_repeated_prime_finite (p:=17) (m:=8) (b:=5) (r:=2) (T:=20) (A:=725)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (repeated_check_blocks 32 (by decide) (by decide +kernel)) hu hd (Or.inr cut) eqn

set_option maxHeartbeats 8000000 in
theorem exclude_repeated_nineteen {u d t : ℕ} (hu : 0<u) (hd : d%8=7) :
    u^2+d^19≠(2^t)^19 := by
  intro eqn
  exact exclude_repeated_prime_finite (p:=19) (m:=9) (b:=5) (r:=2) (T:=22) (A:=1449)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (repeated_check_blocks 32 (by decide) (by decide +kernel)) hu hd (Or.inl (by decide)) eqn

set_option maxHeartbeats 8000000 in
theorem exclude_repeated_twentythree {u d t : ℕ} (hu : 0<u) (hd : d%8=7) :
    u^2+d^23≠(2^t)^23 := by
  intro eqn
  exact exclude_repeated_prime_finite (p:=23) (m:=11) (b:=5) (r:=2) (T:=26) (A:=5793)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (repeated_check_blocks 64 (by decide) (by decide +kernel)) hu hd (Or.inl (by decide)) eqn

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
theorem exclude_repeated_twentynine {u d t : ℕ} (hu : 0<u) (hd : d%8=7) :
    u^2+d^29≠(2^t)^29 := by
  intro eqn
  exact exclude_repeated_prime_finite (p:=29) (m:=14) (b:=6) (r:=4) (T:=30) (A:=23171)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (repeated_check_blocks 128 (by decide) (by decide +kernel)) hu hd (Or.inl (by decide)) eqn

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
theorem exclude_repeated_thirtyone {u d t : ℕ} (hu : 0<u) (hd : d%8=7) :
    u^2+d^31≠(2^t)^31 := by
  intro eqn
  exact exclude_repeated_prime_finite (p:=31) (m:=15) (b:=6) (r:=1) (T:=35) (A:=131072)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (fast_repeated_31) hu hd (Or.inl (by decide)) eqn

private theorem fifth_residue {u d k : ℕ} (hu : u%2=1) (hk : 2<k)
    (eqn : u^2+d^5=2^k) : d%8=7 := by
  obtain ⟨v,hv⟩ := Nat.odd_iff.mpr hu
  have zero : ((2^k:ℕ):ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 (by omega : 3≤k))
  have h := congrArg (fun w : ℕ => (w:ZMod 8)) eqn
  rw [zero,hv] at h
  push_cast at h
  have tab : ∀ a b : ZMod 8, (2*a+1)^2+b^5=0 → b=7 := by decide +kernel
  simpa only [ZMod.val_natCast,show (7:ZMod 8).val=7 by decide] using congrArg ZMod.val (tab _ _ h)

/-- An odd square plus a fifth power cannot be two to an exponent divisible by five. -/
theorem fifth_multiple_impossible {u d k : ℕ} (hu : u%2=1) (hk : 2<k)
    (divides : 5∣k) (eqn : u^2+d^5=2^k) : False := by
  obtain ⟨t,et⟩ := divides
  have e : u^2+d^5=(2^t)^5 := by rw [←pow_mul,Nat.mul_comm t 5,←et]; exact eqn
  exact exclude_repeated_five (by omega) (fifth_residue hu hk eqn) e

/-- The seventh exponent class modulo ten is impossible already modulo eleven. -/
theorem fifth_seven_mod_ten {u d k : ℕ} (h : k%10=7) : u^2+d^5≠2^k := by
  intro eqn
  have ek : k=10*(k/10)+7 := by omega
  have e := congrArg (fun n : ℕ => (n:ZMod 11)) eqn
  push_cast at e
  rw [ek,pow_add,pow_mul,show (2:ZMod 11)^10=1 by decide,one_pow,one_mul] at e
  exact (by decide +kernel : ∀ a b : ZMod 11, a^2+b^5≠2^7) _ _ e

/-- Removing the powers of two from a positive solution preserves the exponent
of two modulo twice the odd exponent. -/
theorem normalize_square_odd_power {u d k p : ℕ} (hu : 0<u) (hd : 0<d) (hp : Odd p)
    (h : u^2+d^p=2^k) : ∃ a b t l : ℕ, a%2=1 ∧ b%2=1 ∧
      u=2^(p*t)*a ∧ d=2^(2*t)*b ∧ k=(2*p)*t+l ∧ 0<l ∧ a^2+b^p=2^l := by
  obtain ⟨i,a,oa,eu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hu.ne' 2 (by decide)
  obtain ⟨j,b,ob,ed⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' 2 (by decide)
  have opa : a^2%2=1 := by rw [Nat.pow_mod,show a%2=1 by omega]
  have opb : b^p%2=1 := by rw [Nat.pow_mod,show b%2=1 by omega,one_pow]; decide
  have f : 2^(i*2)*a^2+2^(j*p)*b^p=2^k := by simpa only [eu,ed,mul_pow,←pow_mul] using h
  have same := equal_two_orders opa opb f
  have even : j%2=0 := by
    have m := congrArg (fun z : ℕ => z%2) same
    change i*2%2=j*p%2 at m
    rw [Nat.mul_mod j,Nat.odd_iff.mp hp,mul_one,Nat.mod_mod] at m
    omega
  let t := j/2
  have ej : j=2*t := by dsimp [t]; omega
  have ei : i=p*t := by rw [ej] at same; nlinarith only [same]
  have fact : 2^((2*p)*t)*(a^2+b^p)=2^k := by
    rw [show i*2=(2*p)*t by rw [ei]; ring,show j*p=(2*p)*t by rw [ej]; ring,←Nat.mul_add] at f
    exact f
  have sum : 1<a^2+b^p := by omega
  have kk : (2*p)*t<k := (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mp (by
    rw [←fact]; simpa using Nat.mul_lt_mul_of_pos_left sum (Nat.two_pow_pos ((2*p)*t)))
  let l := k-(2*p)*t
  have kl : k=(2*p)*t+l := by dsimp [l]; omega
  refine ⟨a,b,t,l,by omega,by omega,by rw [eu,ei],by rw [ed,ej],kl,by omega,?_⟩
  apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos ((2*p)*t))
  rw [fact,←pow_add,←kl]

/-- The exponent of two in any sum of a positive square and a positive fifth
power belongs to one of three residue classes modulo ten. -/
theorem fifth_exponent_classes {u d k : ℕ} (hu : 0<u) (hd : 0<d) (h : u^2+d^5=2^k) :
    k%10=1 ∨ k%10=3 ∨ k%10=9 := by
  obtain ⟨a,b,t,l,oa,ob,_,_,kl,lp,eqn⟩ := normalize_square_odd_power hu hd (by decide : Odd 5) h
  have odd : l%2=1 := by
    by_contra! n
    have r := OMA.R_BealConjecture_beal_conjecture_R2_H3_R1.BealParity.odd_exponents_of_even_power_of_two
      oa ob (by decide : 1<2) (by decide : 1<5) lp (by omega) eqn
    omega
  have rem : k%10=l%10 := by rw [kl]; change (10*t+l)%10=l%10; simp
  rw [rem]
  by_cases hl : 2<l
  · have no5 : l%10≠5 := fun five => fifth_multiple_impossible oa hl
      ⟨2*(l/10)+1,by omega⟩ eqn
    have no7 : l%10≠7 := fun seven => fifth_seven_mod_ten seven eqn
    have oddrem := (Nat.mod_mod_of_dvd l (by decide : 2∣10)).trans odd
    omega
  · omega

/-- Negative rational abscissas on the curves with shifts 2, 8 and 512
suffice for the remaining primitive fifth-power case. -/
theorem fifth_from_three_curves
    (one : ∀ X Y : ℚ, X<0 → Y^2=X^5+2 → X= -1)
    (three : ∀ X Y : ℚ, X<0 → Y^2≠X^5+8)
    (nine : ∀ X Y : ℚ, X<0 → Y^2≠X^5+512)
    {d u k : ℕ} (du : 0<u) (hd : d%2=1) (big : 1<d) : u^2+d^5≠2^k := by
  intro h
  let q := k/10
  let s := (2:ℚ)^q
  let X := -(d:ℚ)/s^2
  let Y := (u:ℚ)/s^5
  have sp : 0<s := by dsimp [s]; positivity
  have xn : X<0 := by dsimp [X]; exact div_neg_of_neg_of_pos (by exact_mod_cast (show -(d:ℤ)<0 by omega)) (by positivity)
  have orig : (u:ℚ)^2+(d:ℚ)^5=(2:ℚ)^k := by exact_mod_cast h
  have split : (u:ℚ)^2+(d:ℚ)^5=s^10*(2:ℚ)^(k%10) := by
    rw [orig]; dsimp [s,q]; rw [←pow_mul,←pow_add]; congr 1; omega
  have point : Y^2=X^5+(2:ℚ)^(k%10) := by
    have x5 : X^5= -(d:ℚ)^5/s^10 := by
      dsimp only [X]; rw [div_pow,←pow_mul s 2 5]; ring
    have y2 : Y^2=(u:ℚ)^2/s^10 := by
      dsimp only [Y]; rw [div_pow,←pow_mul s 5 2]
    rw [x5,y2,div_eq_iff (pow_ne_zero 10 sp.ne'),add_mul,div_mul_cancel₀ _ (pow_ne_zero 10 sp.ne')]
    linear_combination split
  rcases fifth_exponent_classes du (by omega) h with r|r|r
  · rw [r,pow_one] at point
    have ex := one X Y xn point
    have dn : d=(2^q)^2 := by
      have eq : (d:ℚ)=s^2 := by
        dsimp [X] at ex
        have v := (div_eq_iff (pow_ne_zero 2 sp.ne')).mp ex
        linarith
      dsimp [s] at eq
      exact_mod_cast eq
    by_cases q0 : q=0
    · simp [q0] at dn; omega
    · have ed : 2∣d := dn ▸ (dvd_pow_self 2 q0).trans (dvd_pow_self _ (by decide : 2≠0))
      omega
  · exact three X Y xn (by rw [r] at point; norm_num at point; exact point)
  · exact nine X Y xn (by rw [r] at point; norm_num at point; exact point)

/-- The three rational-point statements imply the complete positive
classification, including every imprimitive scaling. -/
theorem fifth_positive_from_three_curves
    (one : ∀ X Y : ℚ, X<0 → Y^2=X^5+2 → X= -1)
    (three : ∀ X Y : ℚ, X<0 → Y^2≠X^5+8)
    (nine : ∀ X Y : ℚ, X<0 → Y^2≠X^5+512)
    {u d k : ℕ} (hu : 0<u) (hd : 0<d) :
    u^2+d^5=2^k ↔ ∃ t : ℕ, u=2^(5*t) ∧ d=2^(2*t) ∧ k=10*t+1 := by
  constructor
  · intro h
    obtain ⟨a,b,t,l,oa,ob,eu,ed,ek,lp,e⟩ := normalize_square_odd_power hu hd (by decide : Odd 5) h
    have b1 : b=1 := by
      by_contra no
      exact fifth_from_three_curves one three nine (by omega) ob (by omega) e
    have small : l≤2 := by
      by_contra! large
      have r := fifth_residue oa large e
      omega
    have l1 : l=1 := by
      have := fifth_exponent_classes (by omega) (by omega) e
      omega
    rw [b1,l1] at e
    norm_num at e
    have a1 : a=1 := by nlinarith
    exact ⟨t,by simpa [a1] using eu,by simpa [b1] using ed,by omega⟩
  · rintro ⟨t,rfl,rfl,rfl⟩
    rw [←pow_mul,←pow_mul,pow_succ]
    have e1 : 5*t*2=10*t := by omega
    have e2 : 2*t*5=10*t := by omega
    rw [e1,e2]; ring

/-- At repeated prime exponents up to 31, the only surviving possibility
has exponent 17 and the linear factor divisible by 17. -/
theorem small_repeated_prime {u d t p : ℕ} (prime : p.Prime) (lo : 5≤p) (hi : p≤31)
    (hu : 0<u) (hd : d%8=7) (eqn : u^2+d^p=(2^t)^p) :
    p=17 ∧ 17∣2^t-d := by
  have tab : ∀ i : Fin 32, i.val.Prime → 5 ≤ i.val →
      i.val=5 ∨ i.val=7 ∨ i.val=11 ∨ i.val=13 ∨ i.val=17 ∨ i.val=19 ∨ i.val=23 ∨ i.val=29 ∨ i.val=31 := by decide +kernel
  rcases tab ⟨p,by omega⟩ prime lo with e|e|e|e|e|e|e|e|e <;> change p=_ at e <;> subst p
  · exact (exclude_repeated_five hu hd eqn).elim
  · exact (exclude_repeated_seven hu hd eqn).elim
  · exact (exclude_repeated_eleven hu hd eqn).elim
  · exact (exclude_repeated_thirteen hu hd eqn).elim
  · exact ⟨rfl,by by_contra no; exact exclude_repeated_seventeen hu hd no eqn⟩
  · exact (exclude_repeated_nineteen hu hd eqn).elim
  · exact (exclude_repeated_twentythree hu hd eqn).elim
  · exact (exclude_repeated_twentynine hu hd eqn).elim
  · exact (exclude_repeated_thirtyone hu hd eqn).elim

/-- A necessary condition for every odd prime exponent at least five
that divides the exponent of two in the primitive equation. -/
theorem repeated_prime_profile {p d u t : ℕ} (prime : p.Prime) (lo : 5≤p) (hu : 0<u)
    (hd : d%8=7) (eqn : u^2+d^p=(2^t)^p) :
    (31<p ∧ ∃ a : ℕ, d+a^2=2^t ∧ 2^t<((p-1).sqrt+1)*4^(p/2+1)) ∨
      (p%8=1 ∧ ∃ a z : ℕ, d+p*a^2=2^t ∧ u=p*a*z) := by
  have dlt : d<2^t := (Nat.pow_lt_pow_iff_left prime.ne_zero).mp (by
    have := Nat.pow_pos (n:=2) hu; omega)
  have ht : 3≤t := by
    by_contra! bad
    have low : 2^t≤4 := Nat.pow_le_pow_right (by decide : 0<2) (by omega : t≤2)
    omega
  have shaped (pa : p∣2^t-d) : p%8=1 ∧ ∃ a z : ℕ, d+p*a^2=2^t ∧ u=p*a*z := by
    obtain ⟨res,a,z,linear,root,_⟩ := exceptional_prime_shape prime ht hd dlt eqn pa
    exact ⟨res,a,z,linear,root⟩
  by_cases small : p≤31
  · obtain ⟨rfl,h⟩ := small_repeated_prime prime lo small hu hd eqn
    exact Or.inr (shaped h)
  let m := p/2
  have po := Nat.odd_iff.mp (prime.odd_of_ne_two (by omega))
  have ep : p=2*m+1 := by dsimp [m]; omega
  have hm : 0 < m := by omega
  let b := (p-1).sqrt+1
  have hb : p≤b^2 := by
    have sq := Nat.lt_succ_sqrt' (p-1)
    change p-1<b^2 at sq
    omega
  have result := prime_dividing_dyadic_exponent hm (ep ▸ prime) ht hd hu (ep ▸ hb) (ep ▸ eqn)
  rw [←ep] at result
  exact result.elim (fun h => Or.inl ⟨by omega,h⟩) (fun e => Or.inr (shaped e.2))

/-- All positive inputs are covered, including those with a common factor
of two. -/
theorem no_positive_small_repeated_prime {u d k p : ℕ} (hu : 0<u) (hd : 0<d) (prime : p.Prime)
    (lo : 5≤p) (hi : p≤31) (hne : p≠17) (dv : p∣k) : u^2+d^p≠2^k := by
  intro h
  have odd := prime.odd_of_ne_two (by omega)
  obtain ⟨a,b,t,l,oa,ob,_,_,kl,lp,e⟩ := normalize_square_odd_power hu hd odd h
  have dw : p∣(2*p)*t := ⟨2*t,by ring⟩
  have dl : p∣l := (Nat.dvd_add_iff_right dw).mpr (kl ▸ dv)
  have big := Nat.le_of_dvd lp dl
  have mod8 : (2^l:ℕ)%8=0 := Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 (by omega : 3≤l))
  have a2 : a^2%8=1 := by
    rw [Nat.pow_mod]
    rcases (show a%8=1 ∨ a%8=3 ∨ a%8=5 ∨ a%8=7 by omega) with q|q|q|q <;> rw [q]
  have bm := OMA.R_BealConjecture_beal_conjecture_R2_H3_R1.odd_exponent_mod_eight ob (Nat.odd_iff.mp odd)
  have residues := congrArg (fun x : ℕ => x%8) e
  change (a^2+b^p)%8=2^l%8 at residues
  rw [Nat.add_mod,a2,bm,mod8] at residues
  obtain ⟨s,es⟩ := dl
  have fixed : a^2+b^p=(2^s)^p := by rw [←pow_mul,Nat.mul_comm s p,←es]; exact e
  exact hne (small_repeated_prime prime lo hi (by omega) (by omega) fixed).1

/-- In Beal's equation with dyadic output, these repeated primes exclude
the equality for positive bases and either order of the two summands. -/
theorem beal_dyadic_even_repeated_prime {a b x y z t p : ℕ} (ha : 0<a) (hb : 0<b)
    (prime : p.Prime) (lo : 5≤p) (hi : p≤31) (hne : p≠17) (dk : p∣t*z)
    (exps : (2∣x ∧ p∣y) ∨ (p∣x ∧ 2∣y)) : a^x+b^y≠(2^t)^z := by
  have exclude {A B i j : ℕ} (ap : 0<A) (bp : 0<B) (di : 2∣i) (dj : p∣j)
      (h : A^i+B^j=(2^t)^z) : False := by
    obtain ⟨v,ev⟩ := di
    obtain ⟨w,ew⟩ := dj
    apply no_positive_small_repeated_prime (Nat.pow_pos (n:=v) ap) (Nat.pow_pos (n:=w) bp) prime lo hi hne dk
    rw [←pow_mul,←pow_mul,Nat.mul_comm v 2,Nat.mul_comm w p,←ev,←ew,pow_mul]
    exact h
  intro h
  rcases exps with ⟨dx,dy⟩|⟨dx,dy⟩
  · exact exclude ha hb dx dy h
  · exact exclude hb ha dy dx ((Nat.add_comm _ _).trans h)

end BealMordell

/-- An odd square and a power summing to a multiple of eight force the
power to have odd exponent and base seven modulo eight. -/
private theorem residues {u d p k : ℕ} (hu : u%2=1) (hd : d%2=1) (hk : 2<k)
    (h : u^2+d^p=2^k) : p%2=1 ∧ d%8=7 := by
  have square {a : ℕ} (odd : a%2=1) : (a:ZMod 8)^2=1 := by
    obtain ⟨v,ev⟩ := Nat.odd_iff.mpr odd
    rw [ev]; push_cast
    exact (by decide +kernel : ∀ v : ZMod 8, (2*v+1)^2=1) _
  have eqn := congrArg (fun a : ℕ => (a:ZMod 8)) h
  have zero : ((2^k:ℕ):ZMod 8)=0 := (ZMod.natCast_eq_zero_iff ..).mpr (pow_dvd_pow 2 (by omega : 3≤k))
  rw [zero] at eqn
  push_cast at eqn
  rw [square hu] at eqn
  rcases Nat.even_or_odd p with ⟨j,ej⟩|⟨j,ej⟩
  · rw [show p=2*j by omega,pow_mul,square hd,one_pow] at eqn
    exact (by decide : (1:ZMod 8)+1≠0) eqn |>.elim
  · rw [ej,pow_succ,pow_mul,square hd,one_pow,one_mul] at eqn
    have ed : (d:ZMod 8)=7 := (by decide +kernel : ∀ a : ZMod 8, 1+a=0 → a=7) _ eqn
    refine ⟨by omega,?_⟩
    simpa only [ZMod.val_natCast,show (7:ZMod 8).val=7 by decide] using congrArg ZMod.val ed

private theorem prime_power_coprime {u d p k : ℕ} (hu : u%2=1) (hp : 0<p)
    (eqn : u^2+d^p=2^k) : u.Coprime d := by
  apply Nat.coprime_of_dvd
  intro l lp lu ld
  have dv : l∣2^k := eqn ▸ dvd_add (lu.trans (dvd_pow_self _ (by decide : 2≠0)))
    (ld.trans (dvd_pow_self _ hp.ne'))
  have p2 := (Nat.prime_dvd_prime_iff_eq lp Nat.prime_two).mp (lp.dvd_of_dvd_pow dv)
  subst l
  omega

theorem main : H1 → H2 → H3 → OMA.R_BealConjecture_beal_conjecture_R2_H3_R1.H1 := by
  intro roots fifth large u d m k hu hd big hm hk ko eqn
  let p := m.minFac
  have prime : p.Prime := Nat.minFac_prime (by omega)
  obtain ⟨j,ej⟩ := Nat.minFac_dvd m
  change m=p*j at ej
  have jp : 0<j := by
    by_contra! zero
    have j0 : j=0 := by omega
    rw [j0,Nat.mul_zero] at ej
    omega
  let D := d^j
  have dp : 1<D := Nat.one_lt_pow jp.ne' big
  have od : D%2=1 := by dsimp [D]; rw [Nat.pow_mod,hd,one_pow]; decide
  have e : u^2+D^p=2^k := by dsimp [D]; rw [←pow_mul,Nat.mul_comm j p,←ej]; exact eqn
  obtain ⟨po,seven⟩ := residues hu od hk e
  have cop := prime_power_coprime hu prime.pos e
  have p2 := prime.two_le
  by_cases p3 : p=3
  · rw [p3] at e
    exact (BealMordell.cubic_from_coordinates roots hu od hk e).1
  by_cases p5 : p=5
  · rw [p5] at e
    exact (fifth hu seven dp cop hk ko (BealMordell.fifth_exponent_classes (by omega) (by omega) e) e).elim
  apply (large hu seven dp cop prime (by omega) hk ko ?_ e).elim
  intro t et
  have fixed : u^2+D^p=(2^t)^p := e.trans (by rw [et,Nat.mul_comm p t,pow_mul])
  exact BealMordell.repeated_prime_profile prime (by omega) (by omega) seven fixed

end OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H1_R1
