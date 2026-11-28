import OMAStatements.S_oeis_a330382

/-!
Amiram Eldar and Thomas Ordowski's conjecture on Mersenne cubes (OEIS A330382).

For n>2, put t=2^n−2 and c=1+t(t/3+1), with integer division.
The cube condition is equivalent to n odd and n(n−1) dividing t*c.
In the odd case t and c are coprime. An exceptional prime dividing c
and n(n−1) therefore characterizes a counterexample exactly.

This proves the forward construction from n(n−1) dividing t for every n,
the full equivalence for prime n, and the equivalence through 131074.
The two residual problems test prime divisors of n and n−1 separately.
They use the smaller cofactor in the cyclotomic divisibility test.
The families n = 38·174763^b+1 and n = 7·5419^(2b) show why each
period on its own allows infinitely many failures of Fermat divisibility.
The right-hand test is invariant under n ↦ 2^n−1. Iteration starting
at the composite 2^43−1 supplies arbitrarily large positive examples
with composite exponent.
-/

namespace OMA.R_oeis_a330382_R1

theorem two_pow_modulus {m e : ℕ} : (2 : ZMod m)^e=1 ↔ m ∣ 2^e-1 := by
  have h := Nat.modEq_iff_dvd' (n:=m) (Nat.one_le_two_pow (n:=e))
  constructor
  · intro eq
    apply h.mp
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa using eq.symm
  · intro hd
    have he := (ZMod.natCast_eq_natCast_iff _ _ _).mpr (h.mpr hd).symm
    simpa using he

theorem order_mersenne (m : ℕ) (hm : 1 < m) : orderOf (2 : ZMod (2^m-1))=m := by
  apply (orderOf_eq_iff (by omega : 0 < m)).mpr
  refine ⟨two_pow_modulus.mpr dvd_rfl,?_⟩
  intro e el ep he
  have lo := Nat.pow_lt_pow_right (by decide : 1<2) el
  have eu := Nat.pow_lt_pow_right (by decide : 1<2) ep
  simp only [pow_zero] at eu
  exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) (two_pow_modulus.mp he)

theorem order_cyclo_six (n : ℕ) (hn : 1<n) :
    orderOf (2 : ZMod ((2^n)^2-2^n+1))=6*n := by
  let x := 2^n
  let B := x^2-x+1
  change orderOf (2 : ZMod B)=6*n
  have x4 : 4≤x := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2≤n)
  have x2 : 2^(2*n)=x^2 := by rw [Nat.mul_comm 2 n, pow_mul]
  have x3 : 2^(3*n)=x^3 := by rw [Nat.mul_comm 3 n, pow_mul]
  have lx : 2*x≤x^2 := by
    simpa only [pow_two] using Nat.mul_le_mul_right x (by omega : 2≤x)
  have bx : B+x=x^2+1 := by dsimp only [B]; omega
  have bb : 2<B := by omega
  have bc : B*(x+1)=x^3+1 := by
    have h := congrArg (·*(x+1)) bx
    nlinarith only [h]
  have hp : B ∣ 2^(3*n)+1 := ⟨x+1,by rw [x3]; exact bc.symm⟩
  have hz := (ZMod.natCast_eq_zero_iff _ _).mpr hp
  push_cast at hz
  have hs : (2 : ZMod B)^(3*n) = -1 := by linear_combination hz
  have hfull : (2 : ZMod B)^(6*n)=1 := by
    rw [show 6*n=(3*n)*2 by omega,pow_mul,hs]; ring
  let o := orderOf (2 : ZMod B)
  have pord : o∣6*n := orderOf_dvd_of_pow_eq_one hfull
  have op : 0<o := Nat.pos_of_dvd_of_pos pord (by omega)
  have om : B ∣ 2^o-1 := two_pow_modulus.mp (pow_orderOf_eq_one _)
  have o3 : o ≠ 3*n := by
    intro eq
    rw [eq] at om
    have hpn : 1≤2^(3*n) := Nat.one_le_two_pow
    rw [show 2^(3*n)+1=(2^(3*n)-1)+2 by omega] at hp
    exact Nat.not_dvd_of_pos_of_lt (by decide) bb ((Nat.dvd_add_right om).mp hp)
  have o2 : o ≠ 2*n := by
    intro eq
    rw [eq,x2,show x^2-1=B+(x-2) by omega] at om
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) ((Nat.dvd_add_right (dvd_refl B)).mp om)
  have lower : 2*n≤o := by
    by_contra! small
    have pv := Nat.pow_le_pow_right (by decide : 0<2) (by omega : o+1≤2*n)
    rw [pow_succ,x2] at pv
    have pos := Nat.pow_lt_pow_right (by decide : 1<2) op
    simp only [pow_zero] at pos
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega) om
  obtain ⟨k,hk⟩ := pord
  change o=6*n
  by_contra ne
  have hk0 : k≠0 := by intro z; simp [z] at hk; omega
  have hk1 : k≠1 := by intro z; simp [z] at hk; omega
  have hk2 : k≠2 := by intro z; rw [z] at hk; omega
  have ho := Nat.mul_le_mul_left o (by omega : 3≤k)
  omega

theorem necessary_cube_periods (n : ℕ) (hn : 2<n)
    (h : (2^n-1)^3-1 ∣ 2^((2^n-1)^3)-2) :
    n-1 ∣ (2^n-1)^3-1 ∧ 6*n ∣ (2^n-1)^3-1 := by
  let A := 2^(n-1)-1
  let B := (2^n)^2-2^n+1
  let K := (2^n-1)^3
  have xm : 2^n=2^(n-1)*2 := by conv_lhs => rw [show n=n-1+1 by omega,pow_succ]
  have xp : 1≤2^(n-1) := Nat.one_le_two_pow
  have x2 : 2≤2^n := by omega
  have fac : K-1=2*(A*B) := by
    have xf : (2^n-1)^3-1=(2^n-2)*((2^n)^2-2^n+1) := by
      generalize 2^n=x at *
      obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le x2
      simp only [Nat.add_sub_cancel_left]
      grind +ring
    have e : 2^n-2=2*A := by dsimp only [A]; omega
    change (2^n-1)^3-1=2*(A*B)
    rw [xf,e]
    exact mul_assoc _ _ _
  have K1 : 0<K := pow_pos (by omega) _
  have em : 2^K = 2^(K-1)*2 := by conv_lhs => rw [show K=K-1+1 by omega,pow_succ]
  have eh : 2^K-2=2*(2^(K-1)-1) := by have t : 1≤2^(K-1) := Nat.one_le_two_pow; omega
  change K-1 ∣ 2^K-2 at h
  rw [fac,eh] at h
  have both := (Nat.mul_dvd_mul_iff_left (by decide : 0<2)).mp h
  have aO : orderOf (2:ZMod A)=n-1 := order_mersenne _ (by omega)
  have bO : orderOf (2:ZMod B)=6*n := order_cyclo_six n (by omega)
  rw [←aO,←bO]
  exact ⟨orderOf_dvd_of_pow_eq_one (two_pow_modulus.mpr ((dvd_mul_right A B).trans both)),
         orderOf_dvd_of_pow_eq_one (two_pow_modulus.mpr ((dvd_mul_left B A).trans both))⟩

/-- A congruence witnessed by a product at the period propagates to each multiple. -/
private theorem lift_period {p d e k c : ℕ} (base : p^e = d*k+1) (period : e ∣ c) :
    d ∣ p^c-1 := by
  obtain ⟨j,rfl⟩ := period
  have h : 1 ≡ p^e [MOD d] := by
    rw [base]
    exact Nat.ModEq.modulus_mul_add.symm
  have h' : 1 ≡ p^(e*j) [MOD d] := by simpa [pow_mul] using h.pow j
  exact h'.dvd'

/-- The two cyclotomic factors may share 3. In that case we cover an extra
factor of 3 on the Mersenne side and cancel it before using coprimality. -/
private theorem combine_mersenne_factors {a w : ℕ} (ha : a ∣ w)
    (hb : 3+6*a+4*a^2 ∣ w) (hshared : 3 ∣ a → 3*a ∣ w) :
    a*(3+6*a+4*a^2) ∣ w := by
  by_cases h : 3 ∣ a
  · obtain ⟨u,hu⟩ := h
    let b := 1+a*(2+4*u)
    have bf : 3+6*a+4*a^2 = 3*b := by dsimp [b]; rw [hu]; ring
    have cop : a.Coprime b := (Nat.coprime_add_mul_left_right a 1 _).mpr (Nat.coprime_one_right a)
    obtain ⟨k,hk⟩ := hb
    have hd : 3*a ∣ 3*(b*k) := by simpa only [hk,bf,mul_assoc] using hshared ⟨u,hu⟩
    have hd' : a ∣ k := cop.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 3) hd)
    obtain ⟨j,hj⟩ := hd'
    exact ⟨j,by rw [hk,hj]; ring⟩
  · have cop3 : a.Coprime 3 := ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr h).symm
    have cop : a.Coprime (3+6*a+4*a^2) := by
      rw [show 3+6*a+4*a^2=3+a*(6+4*a) by ring]
      exact (Nat.coprime_add_mul_left_right _ _ _).mpr cop3
    exact cop.mul_dvd_of_dvd_of_dvd ha hb

/-- A period certificate for the full pseudoprime divisibility with no
materialization of the power whose exponent is the cube. -/
theorem lhs_of_periods {n : ℕ} (hn : 0 < n)
    (hA : n-1 ∣ (2^n-1)^3-1)
    (hB : 6*n ∣ (2^n-1)^3-1)
    (h3 : 3 ∣ 2^(n-1)-1 → 3*(n-1) ∣ (2^n-1)^3-1) :
    (2^n-1)^3-1 ∣ 2^((2^n-1)^3)-2 := by
  let a := 2^(n-1)-1
  let c := (2^n-1)^3-1
  have hsm : 2^(n-1) = a+1 := by dsimp [a]; have := Nat.one_le_two_pow (n := n-1); omega
  have ht : 2^n = 2*a+2 := by
    calc 2^n = 2^(n-1+1) := by congr 1; omega
         _ = 2*a+2 := by rw [pow_succ,hsm]; ring
  have hc : c = 2*(a*(3+6*a+4*a^2)) := by
    dsimp [c]; rw [ht,show 2*a+2-1 = 2*a+1 by omega]
    have h : (2*a+1)^3 = 2*(a*(3+6*a+4*a^2))+1 := by ring
    omega
  have hsmall : a ∣ 2^c-1 := lift_period (p:=2) (d:=a) (e:=n-1) (k:=1) (by simpa using hsm) hA
  have hlarge : 3+6*a+4*a^2 ∣ 2^c-1 := by
    apply lift_period (e:=6*n) (k:=(2*a+3)*(8*a^3+24*a^2+24*a+7)) _ hB
    rw [mul_comm 6,pow_mul,ht]; ring
  have hboth := combine_mersenne_factors hsmall hlarge (by
    intro ha
    obtain ⟨u,hu⟩ := ha
    apply lift_period (e:=3*(n-1)) (k:=1+a+a*u) _ (h3 ⟨u,hu⟩)
    rw [mul_comm 3,pow_mul,hsm,hu]; ring)
  have hk : (2^n-1)^3 = c+1 := by
    dsimp [c]; rw [ht,show 2*a+2-1=2*a+1 by omega]
    have h : 0 < (2*a+1)^3 := by positivity
    omega
  change c ∣ 2^((2^n-1)^3)-2
  rw [hk,pow_succ,show 2^c*2-2=2*(2^c-1) by have := Nat.one_le_two_pow (n:=c); omega]
  conv_lhs => rw [hc]
  exact Nat.mul_dvd_mul_left 2 hboth

theorem lhs_of_two_periods {n : ℕ} (hn : 0 < n)
    (hA : 3*(n-1) ∣ (2^n-1)^3-1) (hB : 6*n ∣ (2^n-1)^3-1) :
    (2^n-1)^3-1 ∣ 2^((2^n-1)^3)-2 :=
  lhs_of_periods hn ((dvd_mul_left _ _).trans hA) hB (fun _ => hA)

private theorem not_self_dvd_two_pow_sub {m : ℕ} (hm : 1 < m) : ¬ m ∣ 2^m-1 := by
  intro hd
  let p := m.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have : Fact p.Prime := ⟨hp⟩
  have hp' : 2 ≤ p := hp.two_le
  have hmd := (Nat.minFac_dvd m).trans hd
  have hmz : (2 : ZMod p)^m = 1 := by
    have hx : 1 ≡ 2^m [MOD p] := (Nat.modEq_iff_dvd' (Nat.one_le_two_pow (n := m))).mpr hmd
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hx.symm
  have hne : (2:ZMod p) ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : m ≠ 0)] at hmz
    exact zero_ne_one hmz
  let o := orderOf (2 : ZMod p)
  have ho : o ∣ m := orderOf_dvd_of_pow_eq_one hmz
  have ho' : o ∣ p-1 := ZMod.orderOf_dvd_card_sub_one hne
  have key : o = 1 := Nat.dvd_one.mp <| (Nat.coprime_of_lt_minFac (by omega : p-1 ≠ 0)
    (by change p-1 < p; omega)).gcd_eq_one ▸ Nat.dvd_gcd ho ho'
  have he : (2:ZMod p) = 1 := orderOf_eq_one_iff.mp key
  have hdv : p ∣ 2-1 := (Nat.modEq_iff_dvd' (by decide : 1 ≤ 2)).mp <|
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using he.symm)
  have : p = 1 := Nat.dvd_one.mp hdv
  omega

private theorem rhs_odd {n : ℕ} (hn : 2 < n) (hr : n*(n-1) ∣ 2^n-2) : Odd n := by
  by_contra h
  have he : Even n := Nat.not_odd_iff_even.mp h
  have hm : Odd (n-1) := by obtain ⟨j,hj⟩ := he; exact ⟨j-1, by omega⟩
  have hsub : 2^n-2 = 2*(2^(n-1)-1) := by
    have hpos : 0 < 2^(n-1) := by positivity
    have hx : 2^n = 2^(n-1)*2 := by conv_lhs => rw [show n = n-1+1 by omega, pow_succ]
    omega
  have hd := (dvd_mul_left (n-1) n).trans hr
  rw [hsub] at hd
  exact not_self_dvd_two_pow_sub (by omega : 1 < n-1) (hm.coprime_two_right.dvd_of_dvd_mul_left hd)

private theorem cube_exp_factor {n : ℕ} (hn : 0 < n) :
    (2^n-1)^3-1 = (2^n-2) * ((2^n)^2-2^n+1) := by
  have hx : 2 ≤ 2^n := Nat.le_self_pow (by omega : n ≠ 0) 2
  generalize 2^n = x at *
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hx
  simp only [Nat.add_sub_cancel_left]
  grind +ring

private theorem rhs_periods {n : ℕ} (hn : 2 < n) (hr : n*(n-1) ∣ 2^n-2) :
    3*(n-1) ∣ (2^n-1)^3-1 ∧ 6*n ∣ (2^n-1)^3-1 := by
  have ho := rhs_odd hn hr
  have hb : 3 ∣ (2^n)^2-2^n+1 := by
    obtain ⟨k,hk⟩ := ho
    have hx : 2^n ≡ 2 [MOD 3] := by
      rw [hk, pow_succ, pow_mul]
      have hc : 2^2 ≡ 1 [MOD 3] := by decide
      simpa using (hc.pow k).mul_right 2
    have hx1 : 2^n ≤ (2^n)^2 := by
      have : 1 ≤ 2^n := Nat.one_le_two_pow
      nlinarith [Nat.mul_le_mul_left (2^n) this]
    have hz : (2^n)^2-2^n+1 ≡ 0 [MOD 3] := by
      have hz0 : (2^n)^2-2^n+1 + 2^n ≡ 0+2 [MOD 3] := by
        rw [show (2^n)^2-2^n+1+2^n = (2^n)^2+1 by omega]
        exact ((hx.pow 2).add_right 1).trans (by decide)
      exact hx.add_right_cancel hz0
    exact Nat.modEq_zero_iff_dvd.mp hz
  rw [cube_exp_factor (by omega : 0 < n)]
  have hm := (dvd_mul_left (n-1) n).trans hr
  have h2m : 2*n ∣ 2^n-2 := by
    apply dvd_trans _ hr
    rw [mul_comm 2]
    obtain ⟨k,hk⟩ := ho
    exact Nat.mul_dvd_mul_left n ⟨k, by omega⟩
  constructor
  · simpa only [mul_comm 3] using Nat.mul_dvd_mul hm hb
  · convert Nat.mul_dvd_mul h2m hb using 1
    ring

private theorem seven_cube : (2 : ZMod 7)^3=1 := by decide
private theorem seven_sign : (1 : ZMod 7) ≠ -1 := by decide

private theorem B_prime {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hcop : n.Coprime (p-1))
    (hB : p ∣ (2^n)^2-2^n+1) : p = 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hg : 2^n ≤ (2^n)^2 := by
    have ha : 1 ≤ 2^n := Nat.one_le_two_pow
    nlinarith [Nat.mul_le_mul_left (2^n) ha]
  have hcast := (ZMod.natCast_eq_zero_iff _ _).mpr hB
  push_cast [Nat.cast_sub hg] at hcast
  let z : ZMod p := 2
  have hpoly : (z^n)^2-z^n+1 = 0 := by simpa only [z] using hcast
  have hc : z^(3*n) = -1 := by
    rw [mul_comm, pow_mul]
    linear_combination (z ^ n + 1) * hpoly
  have h6 : z^(6*n)=1 := by
    rw [show 6*n = (3*n)*2 by omega, pow_mul, hc]; ring
  have hne : z ≠ 0 := by
    intro he
    rw [he, zero_pow (by omega : 6*n ≠ 0)] at h6
    exact zero_ne_one h6
  have ho := ZMod.orderOf_dvd_card_sub_one hne
  have hd : orderOf z ∣ 6 := (hcop.symm.coprime_dvd_left ho).dvd_of_dvd_mul_right
    (orderOf_dvd_of_pow_eq_one h6)
  have hh : z^6 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
  have h63 : p ∣ 63 := by
    apply (Nat.modEq_iff_dvd' (by decide : 1 ≤ 64)).mp
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    norm_num [z] at hh ⊢
    exact hh.symm
  have hfac : p ∣ 3 ∨ p ∣ 7 := by
    rcases hp.dvd_mul.mp (show p ∣ 3*3*7 from h63) with h|h
    · exact Or.inl ((hp.dvd_mul.mp h).elim id id)
    · exact Or.inr h
  rcases hfac with h|h
  · exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp h
  · have he := (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h
    subst p
    have hs : z^3=1 := seven_cube
    rw [pow_mul, hs, one_pow] at hc
    exact False.elim (seven_sign hc)

private theorem three_pow_pred {n e : ℕ} (ho : Odd n) (hd : 3^e ∣ n-1) :
    3^e ∣ 2^n-2 := by
  obtain ⟨t,ht⟩ := ho
  have ht' : 3^e ∣ t := by
    have hc : (3^e).Coprime 2 := (by decide : Nat.Coprime 3 2).pow_left e
    apply hc.dvd_of_dvd_mul_left
    simpa [ht] using hd
  obtain ⟨u, hu⟩ := ht'
  have hm : 4^(3^e) ≡ 1 [MOD 3^e] := pow_pow_modEq_one 3 e 1
  have hz : 2^n ≡ 2 [MOD 3^e] := by
    rw [ht, hu, pow_succ, pow_mul, pow_mul]
    simpa using (hm.pow u).mul_right 2
  exact hz.symm.dvd'

private theorem pred_of_compatible {n : ℕ} (hn : 2 < n) (ho : Odd n)
    (hm : n-1 ∣ (2^n-2)*((2^n)^2-2^n+1))
    (hc : ∀ p : ℕ, p.Prime → p ∣ n-1 → n.Coprime (p-1)) : n-1 ∣ 2^n-2 := by
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e hp hpe
  rcases e with _ | a
  · simp
  have hpm : p ∣ n-1 := (dvd_pow_self p (by omega : a+1 ≠ 0)).trans hpe
  by_cases hb : p ∣ (2^n)^2-2^n+1
  · have he := B_prime (by omega : 0 < n) hp (hc p hp hpm) hb
    subst p
    exact three_pow_pred ho hpe
  · have hcp := (hp.coprime_iff_not_dvd.mpr hb).pow_left (a+1)
    exact hcp.dvd_of_dvd_mul_right (hpe.trans hm)

private theorem prime_rhs_of_first_period {n : ℕ} (hn : 2 < n) (hp : n.Prime)
    (hm : n-1 ∣ (2^n-2)*((2^n)^2-2^n+1)) : n*(n-1) ∣ 2^n-2 := by
  have : Fact n.Prime := ⟨hp⟩
  have ho := hp.odd_of_ne_two (by omega)
  have hc : ∀ p : ℕ, p.Prime → p ∣ n-1 → n.Coprime (p-1) := by
    intro p hpr hpd
    have hle := Nat.le_of_dvd (by omega : 0 < n-1) hpd
    apply hp.coprime_iff_not_dvd.mpr
    have := hpr.two_le
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hpred := pred_of_compatible hn ho hm hc
  have hself : n ∣ 2^n-2 := by
    apply Nat.ModEq.dvd'
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simp
  exact (Nat.coprime_self_sub_right (by omega : 1 ≤ n)).mpr (by simp) |>.mul_dvd_of_dvd_of_dvd hself hpred

/-- Any possible power of three discarded by taking the lcm of the separate
periods is already supplied by the Mersenne factor in the cube exponent. -/
theorem period_triple_automatic {n : ℕ} (hn : 2<n)
    (hper : n-1 ∣ (2^n-1)^3-1) (hs : 3∣2^(n-1)-1) :
    3*(n-1)∣(2^n-1)^3-1 := by
  have per : orderOf (2 : ZMod 3) ∣ n-1 := orderOf_dvd_of_pow_eq_one (two_pow_modulus.mpr hs)
  have two : orderOf (2 : ZMod 3)=2 := order_mersenne 2 (by decide)
  obtain ⟨t,ht⟩ := two ▸ per
  obtain ⟨k,hk⟩ := hs
  have xn : 2^n=6*k+2 := by
    have xp : 1≤2^(n-1) := Nat.one_le_two_pow
    have xm : 2^n=2^(n-1)*2 := by conv_lhs => rw [show n=n-1+1 by omega,pow_succ]
    omega
  let b := 12*k^2+6*k+1
  have cf : (2^n-1)^3-1=3*((2^n-2)*b) := by
    rw [xn,show 6*k+2-1=6*k+1 by omega,show 6*k+2-2=6*k by omega]
    have z : (6*k+1)^3=3*((6*k)*b)+1 := by dsimp only [b]; ring
    omega
  rw [cf] at hper ⊢
  apply Nat.mul_dvd_mul_left
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e pr d
  by_cases h : p=3
  · subst p
    apply dvd_mul_of_dvd_left _ _
    have cp : (3^e).Coprime 2 := (by decide : Nat.Coprime 3 2).pow_left _
    have dt : 3^e ∣ t := cp.dvd_of_dvd_mul_left (ht ▸ d)
    obtain ⟨z,hz⟩ := dt
    have ref : 4^(3^e) ≡ 1 [MOD 3^e] := pow_pow_modEq_one 3 e 1
    have d2 : 2^n ≡ 2 [MOD 3^e] := by
      rw [show n=2*t+1 by omega,hz,pow_succ,pow_mul,pow_mul]
      simpa using (ref.pow z).mul_right 2
    exact d2.symm.dvd'
  · have cp : (p^e).Coprime 3 := ((Nat.coprime_primes pr (by decide : Nat.Prime 3)).mpr h).pow_left _
    exact cp.dvd_of_dvd_mul_left (d.trans hper)

theorem cube_iff_two_periods (n : ℕ) (hn : 2<n) :
    ((2^n-1)^3-1 ∣ 2^((2^n-1)^3)-2 ↔
      n-1∣(2^n-1)^3-1 ∧ 6*n∣(2^n-1)^3-1) :=
  ⟨necessary_cube_periods n hn, fun h =>
    lhs_of_periods (by omega) h.1 h.2 (period_triple_automatic hn h.1)⟩

theorem odd_of_six_period {n : ℕ} (hn : 1<n) (h : 6*n ∣ (2^n-1)^3-1) : Odd n := by
  by_contra hO
  obtain ⟨t,ht⟩ := Nat.not_odd_iff_even.mp hO
  have d : 4∣(2^n-1)^3-1 := (show 4∣6*n from ⟨3*t,by omega⟩).trans h
  have d0 : 4∣2^n := pow_dvd_pow 2 (by omega : 2≤n)
  have per0 := Nat.modEq_zero_iff_dvd.mpr d0
  have x := Nat.one_le_two_pow (n:=n)
  have plus : 2^n-1+1 ≡ 3+1 [MOD 4] := by
    rw [Nat.sub_add_cancel x]
    exact per0.trans (by decide)
  have pred : 2^n-1 ≡ 3 [MOD 4] := Nat.ModEq.add_right_cancel' 1 plus
  have cube : (2^n-1)^3 ≡ 3 [MOD 4] := (pred.pow 3).trans (by decide)
  have x2 := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤n)
  have cp : 1≤(2^n-1)^3 := Nat.one_le_pow _ _ (by omega)
  have wrong := (Nat.modEq_zero_iff_dvd.mpr d).add_right 1
  rw [Nat.sub_add_cancel cp] at wrong
  exact (by decide : ¬ (0+1 ≡ 3 [MOD 4])) (wrong.symm.trans cube)

theorem cube_odd_factors {n : ℕ} (hn : 2 < n) (ho : Odd n) :
    let t := 2^n-2
    let c := 1+t*(t/3+1)
    (2^n)^2-2^n+1 = 3*c ∧ t.Coprime c ∧ ¬ 3∣c ∧ ¬ 2∣c ∧ 3∣2^(n-1)-1 := by
  dsimp only
  obtain ⟨j,hj⟩ := ho
  have h4 : 4 ≡ 1 [MOD 3] := by decide
  have ha : 2^(n-1) ≡ 1 [MOD 3] := by
    rw [show n-1=2*j by omega,pow_mul]
    simpa using h4.pow j
  have hh := ha.symm.dvd'
  obtain ⟨k,hk⟩ := hh
  have hx : 2^n=6*k+2 := by
    have hy : 1 ≤ 2^(n-1) := Nat.one_le_two_pow
    have hv : 2^n = 2^(n-1)*2 := by conv_lhs => rw [show n=n-1+1 by omega,pow_succ]
    omega
  refine ⟨?_,(Nat.coprime_add_mul_left_right _ _ _).mpr (Nat.coprime_one_right _),?_,?_,⟨k,hk⟩⟩
  all_goals rw [hx,show 6*k+2-2=6*k by omega,show 6*k/3=2*k by omega]
  · have h : (6*k+2)^2 + 1 = 3*(1+6*k*(2*k+1)) + (6*k+2) := by ring
    omega
  · rw [show 6*k*(2*k+1)=3*(2*k*(2*k+1)) by ring]
    omega
  · rw [show 6*k*(2*k+1)=2*(3*k*(2*k+1)) by ring]
    omega

theorem cube_iff_single_product {n : ℕ} (hn : 2 < n) :
    let t := 2^n-2
    let c := 1+t*(t/3+1)
    ((2^n-1)^3-1 ∣ 2^((2^n-1)^3)-2 ↔ Odd n ∧ n*(n-1) ∣ t*c) := by
  dsimp only
  rw [cube_iff_two_periods n hn]
  let t := 2^n-2
  let c := 1+t*(t/3+1)
  have fac (ho : Odd n) : (2^n-1)^3-1 = 3*(t*c) := by
    rw [cube_exp_factor (by omega : 0<n), (cube_odd_factors hn ho).1]
    change t*(3*c)=3*(t*c)
    ring
  have cop : n.Coprime (n-1) := (Nat.coprime_self_sub_right (by omega : 1≤n)).mpr (by simp)
  constructor
  · rintro ⟨ha,hb⟩
    have ho := odd_of_six_period (by omega) hb
    obtain ⟨_,_,_,_,h3⟩ := cube_odd_factors hn ho
    have h1 := period_triple_automatic hn ha h3
    rw [fac ho] at hb h1
    have h2 : 3*n ∣ 3*(t*c) := (show 3*n ∣ 6*n from ⟨2,by ring⟩).trans hb
    exact ⟨ho,cop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mul_dvd_mul_left (by decide : 0<3) h2)
      (Nat.dvd_of_mul_dvd_mul_left (by decide : 0<3) h1)⟩
  · rintro ⟨ho,hp⟩
    rw [fac ho]
    have hn' : n ∣ t*c := (dvd_mul_right n (n-1)).trans hp
    have hm' : n-1 ∣ t*c := (dvd_mul_left (n-1) n).trans hp
    have he : 2 ∣ t := by
      have hh : 2 ∣ 2^n := dvd_pow_self _ (by omega)
      exact Nat.dvd_sub hh dvd_rfl
    have tw : 2*n ∣ t*c := ho.coprime_two_left.mul_dvd_of_dvd_of_dvd (dvd_mul_of_dvd_left he _) hn'
    exact ⟨dvd_mul_of_dvd_right hm' _,by convert Nat.mul_dvd_mul_left 3 tw using 1; ring⟩

theorem cube_exception {n : ℕ} (hn : 2<n) (hl : (2^n-1)^3-1 ∣ 2^((2^n-1)^3)-2)
    (hr : ¬ n*(n-1) ∣ 2^n-2) :
    let t := 2^n-2
    let c := 1+t*(t/3+1)
    ∃ p : ℕ, p.Prime ∧ 3<p ∧ p ∣ n*(n-1) ∧ p∣c ∧ p∣(2^n)^2-2^n+1 := by
  obtain ⟨ho,hprod⟩ := (cube_iff_single_product hn).mp hl
  let t := 2^n-2
  let c := 1+t*(t/3+1)
  obtain ⟨hfac,_,h3,h2,_⟩ := cube_odd_factors hn ho
  have hc : ¬ (n*(n-1)).Coprime c := fun h => hr (h.dvd_of_dvd_mul_right hprod)
  obtain ⟨p,hp,hm,hpc⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hbig : 3<p := by
    have hp2 := hp.two_le
    by_contra! h
    obtain hp'|hp' : p=2 ∨ p=3 := by omega
    · subst p; exact h2 hpc
    · subst p; exact h3 hpc
  exact ⟨p,hp,hbig,hm,hpc,hfac ▸ dvd_mul_of_dvd_right hpc 3⟩

theorem counterexample_iff {n : ℕ} (hn : 2<n) :
    let t := 2^n-2
    let c := 1+t*(t/3+1)
    (((2^n-1)^3-1 ∣ 2^((2^n-1)^3)-2) ∧ ¬n*(n-1)∣t ↔
      Odd n ∧ n*(n-1)∣t*c ∧ ∃ p : ℕ, p.Prime ∧ 3<p ∧ p∣n*(n-1) ∧ p∣c) := by
  dsimp only
  constructor
  · rintro ⟨hl,hr⟩
    obtain ⟨ho,hdiv⟩ := (cube_iff_single_product hn).mp hl
    obtain ⟨p,hp,hbig,hprod,hc,_⟩ := cube_exception hn hl hr
    exact ⟨ho,hdiv,p,hp,hbig,hprod,hc⟩
  · rintro ⟨ho,hdiv,p,hp,_,hprod,hc⟩
    refine ⟨(cube_iff_single_product hn).mpr ⟨ho,hdiv⟩,?_⟩
    intro h
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes (cube_odd_factors hn ho).2.1 (hprod.trans h) hc)

private theorem seven_period_certificate : (2 : ZMod 7)^3=1 := by decide

theorem cyclo_prime_orders {p n : ℕ} (hn : 0<n) (hp : p.Prime) (big : 3<p)
    (hB : p ∣ (2^n)^2-2^n+1) :
    orderOf ((2 : ZMod p)^n)=6 ∧
    ∃ d : ℕ, 1<d ∧ d∣n ∧ orderOf (2 : ZMod p)=6*d ∧ (n/d).Coprime 6 := by
  have : Fact p.Prime := ⟨hp⟩
  let z : ZMod p := 2
  let x := z^n
  have nz (u : ℕ) (up : 0<u) (ult : u<p) : (u:ZMod p)≠0 :=
    fun h => Nat.not_dvd_of_pos_of_lt up ult ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have nz2 : (2:ZMod p)≠0 := nz 2 (by decide) (by omega)
  have nz3 : (3:ZMod p)≠0 := nz 3 (by decide) big
  have xl : 2^n≤(2^n)^2 := by
    have j := Nat.mul_le_mul_left (2^n) (Nat.one_le_two_pow (n:=n))
    simpa only [mul_one,pow_two] using j
  have poly := (ZMod.natCast_eq_zero_iff _ _).mpr hB
  push_cast [Nat.cast_sub xl] at poly
  change x^2-x+1=0 at poly
  have sign : x^3 = -1 := by linear_combination (x+1)*poly
  have six : x^6=1 := by rw [show 6=3*2 by decide,pow_mul,sign]; ring
  have non3 : x^3≠1 := by
    intro h
    apply nz2
    linear_combination sign-h
  have non2 : x^2≠1 := by
    intro h
    have z2 : x=2 := by linear_combination h-poly
    rw [z2] at h
    apply nz3
    linear_combination h
  have hx : orderOf x=6 := by
    apply orderOf_eq_of_pow_and_pow_div_prime (by decide) six
    intro q hq hd
    rcases hq.dvd_mul.mp (show q∣2*3 from hd) with h|h
    · have := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 2)).mp h
      subst q
      exact non3
    · have := (Nat.prime_dvd_prime_iff_eq hq (by decide : Nat.Prime 3)).mp h
      subst q
      exact non2
  let o := orderOf z
  let d := o.gcd n
  have dp : 0<d := Nat.gcd_pos_of_pos_right _ hn
  have od : o/d=6 := (orderOf_pow' z hn.ne').symm.trans hx
  have eq : o=6*d := by rw [←od]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left o n)).symm
  have ex : d≠1 := by
    intro one
    have o6 : o=6 := by simpa [one] using eq
    have hh := pow_orderOf_eq_one z
    change z^o=1 at hh
    rw [o6] at hh
    have dv : p ∣ 63 := by
      apply (Nat.modEq_iff_dvd' (by decide : 1≤64)).mp
      apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
      norm_num [z] at hh ⊢
      exact hh.symm
    have p7 : p=7 := by
      rcases hp.dvd_mul.mp (show p∣9*7 from dv) with h|h
      · rcases hp.dvd_mul.mp (show p∣3*3 from h) with h|h <;>
          exact False.elim (Nat.not_dvd_of_pos_of_lt (by decide) big h)
      · exact (Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7)).mp h
    subst p
    have h3 : (2:ZMod 7)^3=1 := seven_period_certificate
    have d3 := orderOf_dvd_of_pow_eq_one h3
    change o∣3 at d3
    rw [o6] at d3
    exact (by decide : ¬ 6∣3) d3
  refine ⟨hx,d,by omega,Nat.gcd_dvd_right _ _,eq,?_⟩
  rw [←od]
  exact (Nat.coprime_div_gcd_div_gcd dp).symm

theorem cyclo_prime_forces_smaller {p n : ℕ} (hn : 0<n) (hp : p.Prime) (big : 3<p)
    (hB : p ∣ (2^n)^2-2^n+1) : ∃ q : ℕ, q.Prime ∧ q∣n ∧ 6*q∣p-1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨_,d,dl,dn,od,_⟩ := cyclo_prime_orders hn hp big hB
  obtain ⟨q,qp,qd⟩ := Nat.exists_prime_and_dvd (by omega : d≠1)
  have nz : (2:ZMod p)≠0 := fun h => Nat.not_dvd_of_pos_of_lt (by decide : 0<2)
    (by omega : 2<p) ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have hd := ZMod.orderOf_dvd_card_sub_one nz
  rw [od] at hd
  exact ⟨q,qp,qd.trans dn,(Nat.mul_dvd_mul_left 6 qd).trans hd⟩

/-- Over the prime field, a block of length p in the exponent reduces to one.
The shift is arbitrary, covering both prime divisors of n and of n−1. -/
theorem cyclo_prime_cofactor {p : ℕ} (hp : p.Prime) (r j : ℕ) :
    p ∣ (2^(p*r+j))^2-2^(p*r+j)+1 ↔ p ∣ (2^(r+j))^2-2^(r+j)+1 := by
  have : Fact p.Prime := ⟨hp⟩
  have cast_test (k : ℕ) : p ∣ (2^k)^2-2^k+1 ↔ ((2:ZMod p)^k)^2-(2:ZMod p)^k+1=0 := by
    have le : 2^k≤(2^k)^2 := by
      simpa only [pow_two,mul_one] using Nat.mul_le_mul_left (2^k) (Nat.one_le_two_pow (n:=k))
    rw [←ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub le]
    rfl
  have power : (2:ZMod p)^(p*r+j)=(2:ZMod p)^(r+j) := by
    rw [pow_add,pow_add,pow_mul,ZMod.pow_card]
  rw [cast_test,cast_test,power]

theorem not_nine_of_six_period {n : ℕ} (hn : 1<n) (h : 6*n ∣ (2^n-1)^3-1) : ¬9∣n := by
  intro d9
  obtain ⟨u,hu⟩ := d9
  obtain ⟨v,hv⟩ := odd_of_six_period hn h
  have en : n=18*(u/2)+9 := by omega
  have eq : 2^n ≡ 26 [MOD 27] := by
    rw [en,pow_add,pow_mul]
    have a : 2^18 ≡ 1 [MOD 27] := by decide
    have b : 2^9 ≡ 26 [MOD 27] := by decide
    simpa using (a.pow (u/2)).mul b
  have xp := Nat.one_le_two_pow (n:=n)
  have ce := Nat.ModEq.add_right_cancel' 1 (show 2^n-1+1 ≡ 25+1 [MOD 27] by
    rw [Nat.sub_add_cancel xp]
    exact eq)
  have cu : (2^n-1)^3 ≡ 19 [MOD 27] := (ce.pow 3).trans (by decide)
  have dv : 27∣(2^n-1)^3-1 := (show 27∣6*n from ⟨2*u,by omega⟩).trans h
  have x2 := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤n)
  have cp : 1≤(2^n-1)^3 := Nat.one_le_pow _ _ (by omega)
  have wrong := (Nat.modEq_zero_iff_dvd.mpr dv).add_right 1
  rw [Nat.sub_add_cancel cp] at wrong
  exact (by decide : ¬ (0+1 ≡ 19 [MOD 27])) (wrong.symm.trans cu)

theorem cyclo_prime_mod_twentyfour {n p : ℕ} (odd : Odd n) (hp : p.Prime) (big : 3<p)
    (hB : p∣(2^n)^2-2^n+1) : p%24=1 ∨ p%24=19 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k,hk⟩ := odd
  have hn : 0<n := by omega
  obtain ⟨q,_,_,div⟩ := cyclo_prime_forces_smaller hn hp big hB
  have d6 : 6∣p-1 := (dvd_mul_right 6 q).trans div
  have xl : 2^n≤(2^n)^2 := by
    simpa only [pow_two,mul_one] using Nat.mul_le_mul_left (2^n) (Nat.one_le_two_pow (n:=n))
  have poly := (ZMod.natCast_eq_zero_iff _ _).mpr hB
  push_cast [Nat.cast_sub xl] at poly
  have sign : (2:ZMod p)^(3*n) = -1 := by
    rw [mul_comm 3 n,pow_mul]
    linear_combination ((2:ZMod p)^n+1)*poly
  have square : IsSquare (-2:ZMod p) := by
    refine ⟨(2:ZMod p)^(3*k+2),?_⟩
    rw [←pow_add,show 3*k+2+(3*k+2)=3*n+1 by omega,pow_succ,sign]
    ring
  have classes := (ZMod.exists_sq_eq_neg_two_iff (by omega : p≠2)).mp square
  omega

/-- Both periods force n≡3 mod 4: the cube predecessor is 2 modulo 4. -/
private theorem candidate_mod_four {n : ℕ} (hn : 2 < n)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) : n % 4 = 3 := by
  have hd : 4 ∣ 2^n := pow_dvd_pow 2 (by omega : 2≤n)
  have x := Nat.one_le_two_pow (n:=n)
  have step : 2^n-1+1 ≡ 3+1 [MOD 4] := by
    rw [Nat.sub_add_cancel x]
    exact (Nat.modEq_zero_iff_dvd.mpr hd).trans (by decide)
  have three := ((step.add_right_cancel' 1).pow 3).trans (by decide : 3^3 ≡ 3 [MOD 4])
  have hlarge : 1 ≤ (2^n-1)^3 := by
    have := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤n)
    exact Nat.one_le_pow _ _ (by omega)
  have nofour : ¬4 ∣ (2^n-1)^3-1 := fun h =>
    (by decide : ¬(1 ≡ 3 [MOD 4])) (((Nat.modEq_iff_dvd' hlarge).mpr h).trans three)
  have h1 : ¬4 ∣ n-1 := fun h => nofour (h.trans hm)
  have h2 : ¬4 ∣ 6*n := fun h => nofour (h.trans h6)
  omega

/-- A balanced traversal checks every leaf in the indicated dyadic interval. -/
private theorem checked_leaf (f : ℕ → Bool) (k a i : ℕ)
    (h : (Nat.rec (motive := fun _ => ℕ → Bool) f
      (fun _ child j => child (2*j) && child (2*j+1)) k a) = true)
    (lo : a*2^k ≤ i) (hi : i < (a+1)*2^k) : f i = true := by
  induction k generalizing a with
  | zero =>
    simp only [pow_zero, mul_one] at lo hi
    have eq : i=a := by omega
    rw [eq]
    exact h
  | succ k ih =>
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp h
    rw [pow_succ] at lo hi
    by_cases side : i < (2*a+1)*2^k
    · exact ih (2*a) left (by nlinarith only [lo]) side
    · exact ih (2*a+1) right (by omega) (by nlinarith only [hi])

/-- The two checked residues of the cube and the checked ordinary residue give
an implication that Lean can evaluate without expanding a power to the cube. -/
private theorem period_block_sound (k a : ℕ) :
    let f := fun i : ℕ =>
      let n := 4*i+3
      let v := (1 <<< n : ℕ)-1
      let test (m : ℕ) := (v%m)^3%m == 1%m
      !(test (n-1)) || !(test (6*n)) || ((v-1)%(n*(n-1)) == 0)
    (Nat.rec (motive := fun _ => ℕ → Bool) f
      (fun _ child j => child (2*j) && child (2*j+1)) k a) = true →
    ∀ n : ℕ, 2<n → 4*a*2^k ≤ n → n < 4*((a+1)*2^k)+3 → n-1 ∣ (2^n-1)^3-1 → 6*n ∣ (2^n-1)^3-1 →
      n*(n-1) ∣ 2^n-2 := by
  intro f cert n hn lower bound hm h6
  let i := n/4
  have res := candidate_mod_four hn hm h6
  have eqn : 4*i+3=n := by dsimp [i]; omega
  have leaf := checked_leaf f k a i cert (by nlinarith only [eqn,lower]) (by omega)
  dsimp only [f] at leaf
  rw [eqn, Nat.shiftLeft_eq_mul_pow, one_mul] at leaf
  have hb := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤n)
  have vpos : 1 ≤ (2^n-1)^3 := Nat.one_le_pow _ _ (by omega)
  have residue (m : ℕ) (h : m ∣ (2^n-1)^3-1) : (((2^n-1)%m)^3%m == 1%m) = true := by
    apply beq_iff_eq.mpr
    exact ((Nat.mod_modEq (2^n-1) m).pow 3).trans ((Nat.modEq_iff_dvd' vpos).mpr h).symm
  rw [residue _ hm,residue _ h6] at leaf
  have done : (2^n-1-1)%(n*(n-1)) = 0 := beq_iff_eq.mp leaf
  exact Nat.dvd_of_mod_eq_zero (by simpa only [Nat.sub_sub] using done)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3200000 in
private theorem finite_range_0 {n : ℕ} (hn : 2<n) (lo : 0≤n) (hi : n≤16386)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) : n*(n-1) ∣ 2^n-2 :=
  period_block_sound 12 0 (by decide +kernel) n hn lo (by omega) hm h6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3200000 in
private theorem finite_range_1 {n : ℕ} (hn : 2<n) (lo : 16384≤n) (hi : n≤32770)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) : n*(n-1) ∣ 2^n-2 :=
  period_block_sound 12 1 (by decide +kernel) n hn lo (by omega) hm h6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3200000 in
private theorem finite_range_2 {n : ℕ} (hn : 2<n) (lo : 32768≤n) (hi : n≤49154)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) : n*(n-1) ∣ 2^n-2 :=
  period_block_sound 12 2 (by decide +kernel) n hn lo (by omega) hm h6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3200000 in
private theorem finite_range_3 {n : ℕ} (hn : 2<n) (lo : 49152≤n) (hi : n≤65538)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) : n*(n-1) ∣ 2^n-2 :=
  period_block_sound 12 3 (by decide +kernel) n hn lo (by omega) hm h6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3200000 in
private theorem finite_range_4 {n : ℕ} (hn : 2<n) (lo : 65536≤n) (hi : n≤81922)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) : n*(n-1) ∣ 2^n-2 :=
  period_block_sound 12 4 (by decide +kernel) n hn lo (by omega) hm h6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3200000 in
private theorem finite_range_5 {n : ℕ} (hn : 2<n) (lo : 81920≤n) (hi : n≤98306)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) : n*(n-1) ∣ 2^n-2 :=
  period_block_sound 12 5 (by decide +kernel) n hn lo (by omega) hm h6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3200000 in
private theorem finite_range_6 {n : ℕ} (hn : 2<n) (lo : 98304≤n) (hi : n≤114690)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) : n*(n-1) ∣ 2^n-2 :=
  period_block_sound 12 6 (by decide +kernel) n hn lo (by omega) hm h6

set_option maxRecDepth 12000 in
set_option maxHeartbeats 3200000 in
private theorem finite_range_7 {n : ℕ} (hn : 2<n) (lo : 114688≤n) (hi : n≤131074)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) : n*(n-1) ∣ 2^n-2 :=
  period_block_sound 12 7 (by decide +kernel) n hn lo (by omega) hm h6

/-- Complete finite check of the two-period implication through 131,074. -/
theorem finite_periods {n : ℕ} (hn : 2<n) (bound : n ≤ 131074)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) : n*(n-1) ∣ 2^n-2 := by
  by_cases within0 : n ≤ 16386
  · exact finite_range_0 hn (by omega) within0 hm h6
  by_cases within1 : n ≤ 32770
  · exact finite_range_1 hn (by omega) within1 hm h6
  by_cases within2 : n ≤ 49154
  · exact finite_range_2 hn (by omega) within2 hm h6
  by_cases within3 : n ≤ 65538
  · exact finite_range_3 hn (by omega) within3 hm h6
  by_cases within4 : n ≤ 81922
  · exact finite_range_4 hn (by omega) within4 hm h6
  by_cases within5 : n ≤ 98306
  · exact finite_range_5 hn (by omega) within5 hm h6
  by_cases within6 : n ≤ 114690
  · exact finite_range_6 hn (by omega) within6 hm h6
  exact finite_range_7 hn (by omega) bound hm h6

theorem near_predecessor_family (b : ℕ) :
    let n := 2*19*174763^b+1
    n-1 ∣ (2^n-1)^3-1 ∧ ¬ n-1 ∣ 2^n-2 := by
  let t := 174763^b
  let n := 2*19*t+1
  change n-1 ∣ (2^n-1)^3-1 ∧ ¬ n-1 ∣ 2^n-2
  have h9 : t ≡ 1 [MOD 9] := by
    have h : 174763 ≡ 1 [MOD 9] := by decide
    simpa only [one_pow] using h.pow b
  have en : n=18*(n/18)+3 := by
    change t%9=1 at h9
    dsimp only [n]
    omega
  have h19 : 2^n ≡ 8 [MOD 19] := by
    rw [en,pow_add,pow_mul]
    have h : 2^18 ≡ 1 [MOD 19] := by decide
    simpa only [one_pow,one_mul] using (h.pow (n/18)).mul (show 2^3 ≡ 8 [MOD 19] by decide)
  have x2 : 2≤2^n := Nat.le_self_pow (by dsimp [n]; omega : n≠0) 2
  have xl : 2^n≤(2^n)^2 := by
    simpa only [pow_two,mul_one] using Nat.mul_le_mul_left (2^n) (Nat.one_le_two_pow (n:=n))
  have div19 : 19 ∣ (2^n)^2-2^n+1 := by
    apply Nat.modEq_zero_iff_dvd.mp
    apply h19.add_right_cancel
    rw [show (2^n)^2-2^n+1+2^n=(2^n)^2+1 by omega]
    exact ((h19.pow 2).add_right 1).trans (by decide)
  have hl := pow_pow_modEq_one 174763 b 1572861
  change (4^19)^t ≡ 1 [MOD t] at hl
  have dl : t ∣ (4^19)^t-1 := hl.symm.dvd'
  have xn : 2^n = 2*((4^19)^t) := by
    change 2^(2*19*t+1)=_
    rw [pow_succ,pow_mul,pow_mul]
    ring
  have diff : 2^n-2=2*((4^19)^t-1) := by
    have hpos := Nat.one_le_pow t (4^19) (by decide)
    omega
  have d2 : 2*t∣2^n-2 := diff ▸ Nat.mul_dvd_mul_left 2 dl
  have fact : (2^n-1)^3-1=(2^n-2)*((2^n)^2-2^n+1) := by
    generalize 2^n=x at *
    obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le x2
    simp only [Nat.add_sub_cancel_left]
    grind +ring
  have pred : n-1=(2*t)*19 := by dsimp [n]; omega
  refine ⟨by rw [pred,fact]; exact Nat.mul_dvd_mul d2 div19,?_⟩
  intro no
  have bad := (show 19∣n-1 by rw [pred]; exact dvd_mul_left _ _).trans no
  have contra := ((Nat.modEq_iff_dvd' x2).mpr bad).trans h19
  exact (by decide : ¬(2 ≡ 8 [MOD 19])) contra

theorem second_period_family (e : ℕ) (he : 0<e) :
    let n := 7*5419^e
    6*n ∣ (2^n-1)^3-1 ∧ ¬ n ∣ 2^n-2 := by
  intro n
  let Q := 5419^e
  let t := 2^n-2
  let B := t^2+3*t+3
  let C := (t+1)*(t+3)*(t^2+5*t+7)
  have pos : 0 < n := by dsimp [n]; positivity
  have hx : 2^n = t+2 := (Nat.sub_add_cancel (Nat.le_self_pow pos.ne' 2)).symm
  have hp : Nat.Prime 5419 := by norm_num
  have qmod : Q ≡ 1 [MOD 42] := by
    simpa only [Q, one_pow] using (show 5419 ≡ 1 [MOD 42] by decide).pow e
  have qpos : 1 ≤ Q := Nat.one_le_pow _ _ (by decide)
  obtain ⟨j,hj⟩ := (Nat.modEq_iff_dvd' qpos).mp qmod.symm
  have hn : n=7+42*(7*j) := by change 7*Q=_; omega
  have periodic (i : ℕ) : 2^(7+42*i) ≡ 128 [MOD 42*5419] := by
    induction i with
    | zero => decide
    | succ i ih =>
      rw [show 7+42*(i+1)=(7+42*i)+42 by omega, pow_add]
      exact (ih.mul_right (2^42)).trans (by decide)
  have residue : t ≡ 126 [MOD 42*5419] := by
    apply Nat.ModEq.add_right_cancel' 2
    change t+2 ≡ 128 [MOD 42*5419]
    rw [←hx,hn]
    exact periodic _
  have s42 : t ≡ 126 [MOD 42] := residue.of_dvd (by decide)
  have d42 : 42∣t := Nat.modEq_zero_iff_dvd.mp (s42.trans (by decide))
  have sr : t ≡ 126 [MOD 5419] := residue.of_dvd (by decide)
  have cmod : C ≡ 5161 [MOD 5419] := by
    refine (((sr.add_right 1).mul (sr.add_right 3)).mul
      (((sr.pow 2).add (sr.mul_left 5)).add_right 7)).trans ?_
    decide
  have cop : Q.Coprime C := by
    apply Nat.Coprime.pow_left _ (hp.coprime_iff_not_dvd.mpr ?_)
    intro hd
    have h := cmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd)
    exact (by decide : ¬ 5161 ≡ 0 [MOD 5419]) h
  have lift : 2^(6*n) ≡ 1 [MOD Q] := by
    rw [show 6*n=42*Q by dsimp [Q,n]; ring,pow_mul]
    exact (by decide : 2^42 = 1+5419*811597437) ▸ pow_pow_modEq_one 5419 e 811597437
  have x6 : 2^(6*n) = B*C+1 := by rw [Nat.mul_comm 6 n,pow_mul,hx]; dsimp [B,C]; ring
  have hb : Q∣B := by
    apply cop.dvd_of_dvd_mul_right
    apply Nat.modEq_zero_iff_dvd.mp
    apply Nat.ModEq.add_right_cancel' 1
    simpa only [← x6, zero_add] using lift
  have target : (2^n-1)^3-1=t*B := by
    rw [hx,show t+2-1=t+1 by omega]
    have hh : (t+1)^3=t*B+1 := by dsimp [B]; ring
    omega
  refine ⟨?_,?_⟩
  · rw [target,show 6*n=42*Q by dsimp [Q,n]; ring]
    exact Nat.mul_dvd_mul d42 hb
  · intro h
    have dr : 5419∣t := (dvd_pow_self 5419 he.ne').trans ((dvd_mul_left Q 7).trans h)
    have hmod := sr.symm.trans (Nat.modEq_zero_iff_dvd.mpr dr)
    exact (by decide : ¬126 ≡ 0 [MOD 5419]) hmod

theorem even_exponent_second_period_family (b : ℕ) (hb : 1≤b) :
    let n := 7*5419^(2*b)
    n % 4 = 3 ∧ 6*n ∣ (2^n-1)^3-1 ∧ ¬ n ∣ 2^n-2 := by
  intro n
  refine ⟨?_,second_period_family (2*b) (by omega)⟩
  have h : 5419^(2*b) ≡ 1 [MOD 4] := by
    rw [pow_mul]
    simpa only [one_pow] using (show 5419^2 ≡ 1 [MOD 4] by decide).pow b
  exact (h.mul_left 7).trans (by decide : 7*1 ≡ 3 [MOD 4])

private theorem excluded_cube_residue {n m r : ℕ} (hn : 1 < n)
    (hr : 2^n ≡ r+1 [MOD m]) (bad : ¬(1 ≡ r^3 [MOD m])) :
    ¬m ∣ (2^n-1)^3-1 := by
  have ht : 2^n-1+1 ≡ r+1 [MOD m] := by simpa only [Nat.sub_add_cancel (Nat.one_le_two_pow (n:=n))] using hr
  have vpos := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤n)
  have hi : 1 ≤ (2^n-1)^3 := Nat.one_le_pow _ _ (by omega)
  exact fun h => bad (((Nat.modEq_iff_dvd' hi).mpr h).trans ((ht.add_right_cancel' 1).pow 3))

/-- Modulo 5, the cube predecessor is 2 for every remaining exponent. -/
theorem period_mod_twenty {n : ℕ} (hn : 2 < n) (h4 : n%4 = 3)
    (hm : n-1 ∣ (2^n-1)^3-1) (h6 : 6*n ∣ (2^n-1)^3-1) :
    n%20=3 ∨ n%20=7 ∨ n%20=19 := by
  have hx5 : 2^n ≡ 2+1 [MOD 5] := by
    conv_lhs => rw [show n = 4*(n/4)+3 by omega, pow_add,pow_mul]
    have h : 2^4 ≡ 1 [MOD 5] := by decide
    have H := (h.pow (n/4)).mul_right (2^3)
    simp only [one_pow, one_mul] at H
    exact H.trans (by decide)
  have he5 := excluded_cube_residue (by omega : 1<n) hx5 (by decide)
  have h5m : ¬5 ∣ n-1 := fun h => he5 (h.trans hm)
  have h5n : ¬5 ∣ 6*n := fun h => he5 (h.trans h6)
  have h5n' : ¬5 ∣ n := fun h => h5n (dvd_mul_of_dvd_right h 6)
  have h4' : (n%20)%4 = 3 := by rwa [Nat.mod_mod_of_dvd _ (by decide : 4 ∣ 20)]
  have h5' : (n%20)%5 ≠ 0 ∧ (n%20)%5 ≠ 1 := by
    rw [Nat.mod_mod_of_dvd _ (by decide : 5 ∣ 20)]
    omega
  have small := Nat.mod_lt n (by decide : 0 < 20)
  generalize n%20=r at h4' h5' small ⊢
  interval_cases r <;> norm_num at *

theorem cube_pred_not_four {n : ℕ} (hn : 1<n) : ¬4∣(2^n-1)^3-1 := by
  have d0 : 4∣2^n := pow_dvd_pow 2 (by omega : 2≤n)
  have one := Nat.one_le_two_pow (n:=n)
  have cp : 1≤(2^n-1)^3 := Nat.one_le_pow _ _ (by
    have h := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 1≤n)
    omega)
  have e : 2^n-1 ≡ 3 [MOD 4] := by
    apply Nat.ModEq.add_right_cancel' 1
    rw [Nat.sub_add_cancel one]
    exact (Nat.modEq_zero_iff_dvd.mpr d0).trans (by decide)
  intro bad
  have v := (Nat.modEq_zero_iff_dvd.mpr bad).add_right 1
  rw [Nat.sub_add_cancel cp] at v
  exact (by decide : ¬(0+1 ≡ 3^3 [MOD 4])) (v.symm.trans (e.pow 3))

theorem period_prime_order_not_four {n p : ℕ} (hn : 2<n) (hp : p.Prime) (p2 : 2<p)
    (div : p∣n*(n-1)) (pre : n-1∣(2^n-1)^3-1) (six : 6*n∣(2^n-1)^3-1) :
    ¬4∣orderOf (2:ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  have dp : p∣(2^n-1)^3-1 :=
    (hp.dvd_mul.mp div).elim (fun h => (h.trans (dvd_mul_left n 6)).trans six) (·.trans pre)
  have x2 : 2≤2^n := Nat.le_self_pow (by omega : n≠0) 2
  have fac : (2^n-1)^3-1=(2^n-2)*((2^n)^2-2^n+1) := by
    generalize 2^n=x at *
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le x2
    simp only [Nat.add_sub_cancel_left]
    grind +ring
  rw [fac] at dp
  rcases hp.dvd_mul.mp dp with simple|exceptional
  · have h : 2^n-2=2*(2^(n-1)-1) := by
      have t := Nat.one_le_two_pow (n:=n-1)
      have y : 2^n=2^(n-1)*2 := by conv_lhs => rw [show n=n-1+1 by omega,pow_succ]
      omega
    rw [h] at simple
    have s : p∣2^(n-1)-1 := (hp.dvd_mul.mp simple).resolve_left (Nat.not_dvd_of_pos_of_lt (by decide) p2)
    have per := orderOf_dvd_of_pow_eq_one (two_pow_modulus.mpr s)
    exact fun bad => cube_pred_not_four (by omega : 1<n) ((bad.trans per).trans pre)
  · by_cases e : p=3
    · subst p
      have nz : (2:ZMod 3)≠0 := fun h => Nat.not_dvd_of_pos_of_lt (by decide : 0<2) (by decide : 2<3)
        ((ZMod.natCast_eq_zero_iff 2 3).mp h)
      have dv := ZMod.orderOf_dvd_card_sub_one nz
      exact fun bad => (by decide : ¬4∣3-1) (bad.trans dv)
    · obtain ⟨_,d,_,dn,eq,_⟩ := cyclo_prime_orders (by omega : 0<n) hp (by omega) exceptional
      obtain ⟨u,hu⟩ := (odd_of_six_period (by omega : 1<n) six).of_dvd_nat dn
      rw [eq]
      omega

theorem period_prime_not_five_mod_eight {n p : ℕ} (hn : 2<n) (hp : p.Prime) (p2 : 2<p)
    (div : p∣n*(n-1)) (pre : n-1∣(2^n-1)^3-1) (six : 6*n∣(2^n-1)^3-1) :
    p%8≠5 := by
  have : Fact p.Prime := ⟨hp⟩
  let o := orderOf (2:ZMod p)
  have not4 : ¬4∣o := period_prime_order_not_four hn hp p2 div pre six
  have nz : (2:ZMod p)≠0 := fun h => Nat.not_dvd_of_pos_of_lt (by decide : 0<2) p2
    ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  obtain ⟨k,hk⟩ := ZMod.orderOf_dvd_card_sub_one nz
  change p-1=o*k at hk
  intro bad
  have four : 4∣p-1 := by omega
  have ek : Even k := by
    by_contra h
    have odd := Nat.not_even_iff_odd.mp h
    have cp : Nat.Coprime 4 k := odd.coprime_two_left.pow_left 2
    rw [hk] at four
    exact not4 (cp.dvd_of_dvd_mul_right four)
  obtain ⟨j,hj⟩ := ek
  have rel : p-1=2*(o*j) := by rw [hk,hj]; ring
  have oh : o∣p/2 := ⟨j, by omega⟩
  have sq := (ZMod.euler_criterion p nz).mpr (orderOf_dvd_iff_pow_eq_one.mp oh)
  have z := (ZMod.exists_sq_eq_two_iff (by omega : p≠2)).mp sq
  omega

/-- The adjacent Mersenne factors have orders n and n−1. They are coprime
because the larger is twice the smaller plus one. -/
theorem mersenne_tower_iff {n : ℕ} (hn : 2 < n) :
    ((2^n-1)*((2^n-1)-1) ∣ 2^(2^n-1)-2) ↔ n*(n-1) ∣ 2^n-2 := by
  let m := 2^n-1
  let a := 2^(n-1)-1
  have small := Nat.one_le_two_pow (n:=n-1)
  have eq : m=2*a+1 := by
    have h : 2^n=2^(n-1)*2 := by conv_lhs => rw [show n=n-1+1 by omega, pow_succ]
    dsimp [m,a]; omega
  have cop : m.Coprime a := by
    rw [eq]
    exact ((Nat.coprime_mul_right_add_right a 1 2).mpr (Nat.coprime_one_right a)).symm
  have cn : n.Coprime (n-1) := (Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_one_right n)
  have divs (x y z : ℕ) (hc : x.Coprime y) : x*y ∣ z ↔ x∣z ∧ y∣z :=
    ⟨fun d => ⟨(dvd_mul_right _ _).trans d,(dvd_mul_left _ _).trans d⟩,
      fun d => hc.mul_dvd_of_dvd_of_dvd d.1 d.2⟩
  have factors (t : ℕ) (ht : 1 < t) : 2^t-1 ∣ 2^(m-1)-1 ↔ t ∣ m-1 := by
    rw [← two_pow_modulus, ← orderOf_dvd_iff_pow_eq_one, order_mersenne t ht]
  have numerator : 2^m-2=2*(2^(m-1)-1) := by
    have h : 2^m=2^(m-1)*2 := by conv_lhs => rw [show m=m-1+1 by omega, pow_succ]
    have := Nat.one_le_two_pow (n:=m-1)
    omega
  have denominator : m*(m-1)=2*(m*a) := by rw [show m-1=2*a by omega]; ring
  change m*(m-1) ∣ 2^m-2 ↔ n*(n-1) ∣ m-1
  rw [denominator,numerator,Nat.mul_dvd_mul_iff_left (by decide : 0<2), divs _ _ _ cop, divs _ _ _ cn]
  exact and_congr (factors n (by omega)) (factors (n-1) (by omega))

/-- There are arbitrarily large composite exponents for which both sides hold. -/
private theorem unbounded_from {s : ℕ} (hs : 2<s) (hsn : ¬s.Prime)
    (hsr : s*(s-1)∣2^s-2) (N : ℕ) :
    ∃ n : ℕ, N<n ∧ 2<n ∧ ¬n.Prime ∧ n*(n-1)∣2^n-2 ∧
      (2^n-1)^3-1 ∣ 2^((2^n-1)^3)-2 := by
  have grow {n : ℕ} (hn : 2<n) : n < mersenne n := by
    have hh := (n-1).lt_two_pow_self
    have hv : 2^n=2^(n-1)*2 := by conv_lhs => rw [show n=n-1+1 by omega,pow_succ]
    dsimp [mersenne]
    omega
  have help {n : ℕ} (hn : 2<n) (hr : n*(n-1)∣2^n-2) := by
    obtain ⟨ha,hb⟩ := rhs_periods hn hr
    exact lhs_of_two_periods (by omega : 0<n) ha hb
  induction N with
  | zero =>
    exact ⟨s,lt_trans (by decide : 0<2) hs,hs,hsn,hsr,help hs hsr⟩
  | succ N ih =>
    obtain ⟨n,hN,hn,hp,hr,_⟩ := ih
    have gr := grow hn
    have hr' := (mersenne_tower_iff hn).mpr hr
    exact ⟨mersenne n,by omega,by omega,fun h => hp h.of_mersenne,hr',help (by omega : 2 < mersenne n) hr'⟩

theorem unbounded_composite_examples (N : ℕ) :
    ∃ n : ℕ, N<n ∧ 2<n ∧ ¬n.Prime ∧ n*(n-1)∣2^n-2 ∧
      (2^n-1)^3-1 ∣ 2^((2^n-1)^3)-2 := by
  have lift {m : ℕ} (hm : 2 < m) (hm' : 2 < mersenne m) (hc : ¬(mersenne m).Prime)
      (hr : m*(m-1)∣2^m-2) := unbounded_from (s := mersenne m) hm' hc ((mersenne_tower_iff hm).mpr hr) N
  have hnp : ¬(mersenne 43).Prime := by
    intro hp
    have hd : 431∣mersenne 43 := by decide
    rcases (Nat.dvd_prime hp).mp hd with h|h <;> norm_num [mersenne] at h
  exact lift (m := 43) (by decide) (by decide) hnp (by decide)

/-- Exclude an exceptional prime factor of the exponent itself. -/
def H1 : Prop :=
  ∀ p r q : ℕ, let n := p*r
    let t := 2^n-2
    let c := 1+t*(t/3+1)
    131074<n → (n%20=3 ∨ n%20=7 ∨ n%20=19) → ¬9∣n → ¬n.Prime →
    (∀ l : ℕ, l.Prime → l∣n*(n-1) → l%8≠5) → p.Prime → (p%24=1 ∨ p%24=19) →
    q.Prime → q∣r → 6*q∣p-1 → p∣(2^r)^2-2^r+1 → ¬n*(n-1)∣t*c

/-- Exclude an exceptional prime factor of the exponent's predecessor. -/
def H2 : Prop :=
  ∀ p r q : ℕ, let n := p*r+1
    let t := 2^n-2
    let c := 1+t*(t/3+1)
    131074<n → (n%20=3 ∨ n%20=7 ∨ n%20=19) → ¬9∣n → ¬n.Prime →
    (∀ l : ℕ, l.Prime → l∣n*(n-1) → l%8≠5) → p.Prime → (p%24=1 ∨ p%24=19) →
    q.Prime → q∣r+1 → 6*q∣p-1 → p∣(2^(r+1))^2-2^(r+1)+1 → ¬n*(n-1)∣t*c

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a330382.main := by
  intro h1 h2 n hn
  constructor
  · intro hl
    obtain ⟨ha,hb⟩ := (cube_iff_two_periods n hn).mp hl
    by_contra hr
    have hg : 131074 < n := by
      by_contra! h
      exact hr (finite_periods hn h ha hb)
    have hmod := candidate_mod_four hn ha hb
    have h20 := period_mod_twenty hn hmod ha hb
    have hall : ∀ l : ℕ, l.Prime → l∣n*(n-1) → l%8≠5 := by
      intro l hlp hld
      by_cases ht : 2<l
      · exact period_prime_not_five_mod_eight hn hlp ht hld ha hb
      · omega
    have h9 := not_nine_of_six_period (by omega) hb
    have hcomp : ¬n.Prime := by
      intro hp
      rw [cube_exp_factor (by omega : 0<n)] at ha
      exact hr (prime_rhs_of_first_period hn hp ha)
    obtain ⟨ho,hprod⟩ := (cube_iff_single_product hn).mp hl
    obtain ⟨p,hp,hbig,hm,_,hB⟩ := cube_exception hn hl hr
    have h24 := cyclo_prime_mod_twentyfour ho hp hbig hB
    rcases hp.dvd_mul.mp hm with hd|hd
    · obtain ⟨r,hr'⟩ := hd
      subst n
      have hsmall : p ∣ (2^r)^2-2^r+1 := by
        simpa using (cyclo_prime_cofactor hp r 0).mp (by simpa using hB)
      have hpos : 0<r := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hn
      obtain ⟨q,hq,hqr,hqp⟩ := cyclo_prime_forces_smaller hpos hp hbig hsmall
      exact h1 p r q hg h20 h9 hcomp hall hp h24 hq hqr hqp hsmall hprod
    · obtain ⟨r,hr'⟩ := hd
      have he : n=p*r+1 := by omega
      subst n
      have hsmall := (cyclo_prime_cofactor hp r 1).mp hB
      obtain ⟨q,hq,hqr,hqp⟩ := cyclo_prime_forces_smaller (by omega : 0<r+1) hp hbig hsmall
      exact h2 p r q hg h20 h9 hcomp hall hp h24 hq hqr hqp hsmall hprod
  · intro hr
    obtain ⟨ha,hb⟩ := rhs_periods hn hr
    exact lhs_of_two_periods (by omega) ha hb

end OMA.R_oeis_a330382_R1
