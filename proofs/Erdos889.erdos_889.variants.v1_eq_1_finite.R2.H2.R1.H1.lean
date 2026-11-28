import OMAReductions.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1

/-! The two square steps of the second reduction follow from the effective upper bound.
For the first step we also classify the solutions away from multiples of thirty.
The second and third offsets supply the new divisibility by five. -/
namespace Erdos889.FiveMissingSeven
private theorem cycle {x t m : ℕ} (h : Nat.ModEq m (x^t) 1) (b : ℕ) :
    Nat.ModEq m (x^b) (x^(b%t)) := by
  calc
    x^b = x^(b%t)*(x^t)^(b/t) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
    _ ≡ x^(b%t)*1^(b/t) [MOD m] := (h.pow _).mul_left _
    _ = _ := by simp
private theorem large_neighbour {z : ℕ} (large : 4375 < z) (smooth : ∀ p : ℕ, p.Prime → p∣z → p≤7) :
    (∃ p : ℕ, p.Prime ∧ 7<p ∧ p∣z-1) ∧ (∃ p : ℕ, p.Prime ∧ 7<p ∧ p∣z+1) := by
  constructor
  · by_contra missing
    have bound := Erdos889.SevenSmooth.consecutive_smooth_seven (z-1) (by
      intro p pp d
      rcases pp.dvd_mul.mp d with dv|dv
      · by_contra! high
        exact missing ⟨p,pp,high,dv⟩
      · exact smooth p pp (by rwa [show z-1+1=z by omega] at dv))
    omega
  · by_contra missing
    have bound := Erdos889.SevenSmooth.consecutive_smooth_seven z (by
      intro p pp d
      rcases pp.dvd_mul.mp d with dv|dv
      · exact smooth p pp dv
      · by_contra! high
        exact missing ⟨p,pp,high,dv⟩)
    omega
private theorem five_scaled_cube {n z : ℕ} (sparse : (∀ k p q : ℕ, 0<k → p.Prime → q.Prime → p≠q → k<p → k<q → p∣n+k → q∣n+k → False)) (large : 1000000000000<n)
    (three : 3∣n) (shape : n+2=5*z^3) (div : 4∣z ∨ 5∣z)
    (smooth : ∀ p : ℕ, p.Prime → p∣z → p≤7) : False := by
  have huge : 4375 < z := by
    by_contra! low
    have := Nat.pow_le_pow_left low 3
    omega
  let u := z-1
  have eu : z=u+1 := by dsimp only [u]; omega
  let R := u^2+u+1
  have identity : z^2+1=R+z := by rw [eu]; dsimp only [R]; ring
  have z3 : z%3=1 := by
    have m := ((Nat.mod_modEq z 3).pow 3).mul_left 5
    change 5*(z%3)^3%3=5*z^3%3 at m
    rw [←shape] at m
    have low := Nat.mod_lt z (by decide : 0<3)
    interval_cases z%3 <;> norm_num at m <;> omega
  have r3 : ¬3∣R := by
    have dip : 3∣u := by dsimp only [u]; omega
    have dd : 3∣u^2+u := dvd_add (dip.trans (dvd_pow_self u (by decide : 2≠0))) dip
    intro dr
    have d1 := (Nat.dvd_add_iff_right dd).mpr dr
    exact (by decide : ¬3∣1) d1
  have notSmall (p : ℕ) (pp : p=2 ∨ p=5) : ¬p∣R := by
    have pos : 0<p := by omega
    have tab : ∀ v : Fin p, ¬p∣v.val^2+v.val+1 := by rcases pp with rfl|rfl <;> decide +kernel
    have mod := (((Nat.mod_modEq u p).pow 2).add (Nat.mod_modEq u p)).add_right 1
    exact fun d => tab ⟨u%p,Nat.mod_lt _ pos⟩ (Nat.modEq_zero_iff_dvd.mp (mod.trans (Nat.modEq_zero_iff_dvd.mpr d)))
  have rLarge : ∃ p : ℕ, p.Prime ∧ 7<p ∧ p∣R := by
    by_contra missing
    have eq : R=7^R.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by dsimp [R]; omega) (by
      intro p pp dp
      have small : p≤7 := by by_contra! h; exact missing ⟨p,pp,h,dp⟩
      have opts : ∀ k : Fin 8, k.val.Prime → k.val=2 ∨ k.val=3 ∨ k.val=5 ∨ k.val=7 := by decide +kernel
      rcases opts ⟨p,by omega⟩ pp with e|e|e|e <;> change p=_ at e <;> subst p
      · exact (notSmall 2 (Or.inl rfl) dp).elim
      · exact (r3 dp).elim
      · exact (notSmall 5 (Or.inr rfl) dp).elim
      · rfl)
    let e := R.primeFactorsList.length
    change R=7^e at eq
    have zmod {p : ℕ} (dm : p∣z) : Nat.ModEq p R 1 := by
      have dv : p∣z^2 := dm.trans (dvd_pow_self z (by decide : 2≠0))
      have hh := (Nat.modEq_zero_iff_dvd.mpr dv).add_right 1
      rw [identity,zero_add] at hh
      exact (show Nat.ModEq p R (R+z) by simpa only [add_zero] using ((Nat.ModEq.refl R).add (Nat.modEq_zero_iff_dvd.mpr dm)).symm).trans hh
    have even : e%2=0 := by
      rcases div with d4|d5
      · have m := (cycle (by decide : Nat.ModEq 4 (7^2) 1) e).symm.trans (eq ▸ zmod d4)
        change 7^(e%2)%4=1 at m
        have rem := Nat.mod_lt e (by decide : 0<2)
        have tab : ∀ t : Fin 2, 7^t.val%4=1 → t.val=0 := by decide +kernel
        exact tab ⟨e%2,rem⟩ m
      · have m := (cycle (by decide : Nat.ModEq 5 (7^4) 1) e).symm.trans (eq ▸ zmod d5)
        change 7^(e%4)%5=1 at m
        have rem := Nat.mod_lt e (by decide : 0<4)
        have tab : ∀ t : Fin 4, 7^t.val%5=1 → t.val=0 := by decide +kernel
        have zero := tab ⟨e%4,rem⟩ m
        change e%4=0 at zero
        omega
    let t := 7^(e/2)
    have sq : R=t^2 := by dsimp [t]; rw [eq,←pow_mul]; congr 1; omega
    have lo : u<t := by
      by_contra! h
      have bound := Nat.pow_le_pow_left h 2
      dsimp [R] at sq
      omega
    have hi : t<u+1 := by
      by_contra! big
      have bad := Nat.pow_le_pow_left big 2
      dsimp [R] at sq
      nlinarith
    omega
  obtain ⟨p,pp,lp,dp⟩ := (large_neighbour huge smooth).2
  obtain ⟨q,pq,lq,dq⟩ := rLarge
  have ne : p≠q := by
    rintro rfl
    have de : p∣u+2 := by rwa [show u+2=z+1 by omega]
    have mult : p∣(u-1)*(u+2) := dvd_mul_of_dvd_right de (u-1)
    have fac : R=(u-1)*(u+2)+3 := by
      have up : u-1+1=u := by omega
      dsimp [R]; nlinarith [congrArg (fun t : ℕ => t*(u+2)) up]
    rw [fac] at dq
    have d3 := (Nat.dvd_add_iff_right mult).mpr dq
    have := Nat.le_of_dvd (by decide : 0<3) d3
    omega
  have off : n+7=5*((z+1)*R) := by
    have ident : (z+1)*R=z^3+1 := by rw [eu]; dsimp only [R]; ring
    rw [ident,Nat.mul_add,mul_one]
    omega
  exact sparse 7 p q (by decide) pp pq ne lp lq (off ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_left dp _) _)
    (off ▸ dvd_mul_of_dvd_right (dvd_mul_of_dvd_right dq _) _)

/-- For the shift two, the exponent of five is two modulo three. -/
theorem two_shift_mod_three {n a b : ℕ} (sparse : (∀ k p q : ℕ, 0<k → p.Prime → q.Prime → p≠q → k<p → k<q → p∣n+k → q∣n+k → False)) (large : 1000000000000<n)
    (two : 2∣n) (three : 3∣n) (bp : 0<b) (eq : n+2=2^a*5^b) : b%3=2 := by
  have nd := no_cube_at_five_shift sparse large two three (Or.inl rfl) bp eq
  by_contra bad
  have b1 : b%3=1 := by omega
  have dj : 5∣n+2 := eq ▸ dvd_mul_of_dvd_right (dvd_pow_self _ bp.ne') _
  have seven := seven_divides_of_five_shift sparse (by omega) two three (by decide : 2≤2) (by decide) dj
  have residue := (cycle (by decide : Nat.ModEq 7 (2^6) 1) a).mul (cycle (by decide : Nat.ModEq 7 (5^6) 1) b)
  change (2^a*5^b)%7=(2^(a%6)*5^(b%6))%7 at residue
  rw [←eq] at residue
  have target : (2^(a%6)*5^(b%6))%7=2 := by omega
  have tab : ∀ i j : Fin 6, (2^i.val*5^j.val)%7=2 → j.val%3=1 → i.val%3=0 := by decide +kernel
  have as := tab ⟨a%6,Nat.mod_lt _ (by decide)⟩ ⟨b%6,Nat.mod_lt _ (by decide)⟩ target (by change b%6%3=1; omega)
  change a%6%3=0 at as
  let z := 2^(a/3)*5^(b/3)
  have shape : n+2=5*z^3 := by
    rw [eq]
    dsimp only [z]
    rw [mul_pow,←pow_mul,←pow_mul]
    have ae : a=(a/3)*3 := by omega
    have be : b=1+(b/3)*3 := by omega
    calc
      _ = 2^((a/3)*3)*5^(1+(b/3)*3) := by rw [←ae,←be]
      _ = _ := by rw [pow_add,pow_one]; ring
  have div : 4∣z ∨ 5∣z := by
    by_cases b3 : 0 < b/3
    · exact Or.inr (dvd_mul_of_dvd_right (dvd_pow_self 5 b3.ne') _)
    · have zb : b/3=0 := by omega
      have a3 : 2≤a/3 := by
        by_contra! low
        have small := Nat.pow_le_pow_right (by decide : 0<2) (show a/3≤1 by omega)
        have smallz : z≤2 := by dsimp only [z]; rw [zb,pow_zero,mul_one]; exact small
        have := Nat.pow_le_pow_left smallz 3
        omega
      exact Or.inl (dvd_mul_of_dvd_left (pow_dvd_pow 2 a3) _)
  apply five_scaled_cube sparse large three shape div
  intro p pp d
  dsimp only [z] at d
  rcases pp.dvd_mul.mp d with h|h
  · have := Nat.le_of_dvd (by decide : 0<2) (pp.dvd_of_dvd_pow h); omega
  · have := Nat.le_of_dvd (by decide : 0<5) (pp.dvd_of_dvd_pow h); omega


private theorem support_at {n k p q : ℕ} (sparse : (∀ k p q : ℕ, 0<k → p.Prime → q.Prime → p≠q → k<p → k<q → p∣n+k → q∣n+k → False)) (kp : 0<k) (pp : p.Prime)
    (eligible : k<p) (dp : p∣n+k) (pq : q.Prime) (dq : q∣n+k) : q=p ∨ q≤k := by
  by_contra! h
  exact sparse k p q kp pp pq h.1.symm eligible h.2 dp dq

private theorem two_factor_support {m p q : ℕ} (mp : 0 < m) (pp : p.Prime)
    (pool : ∀ r : ℕ, r.Prime → r∣m → r=p ∨ r=q) :
    ∃ a b : ℕ, m=p^a*q^b := by
  let k := m/p^m.factorization p
  have pos : 0<k := Nat.ordCompl_pos p mp.ne'
  have no : ¬p∣k := Nat.not_dvd_ordCompl pp mp.ne'
  have form : p^m.factorization p*k=m := Nat.ordProj_mul_ordCompl_eq_self _ _
  have pure : k=q^k.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd pos.ne' (by
    intro r pr dr
    exact (pool r pr (dr.trans (Nat.ordCompl_dvd m p))).resolve_left (by rintro rfl; exact no dr))
  exact ⟨_,_,by rw [←pure]; exact form.symm⟩

set_option maxHeartbeats 600000 in
private theorem reject_at_eight {n : ℕ} (sparse : (∀ k p q : ℕ, 0<k → p.Prime → q.Prime → p≠q → k<p → k<q → p∣n+k → q∣n+k → False)) (dj : 5∣n+2) (d32 : 32∣n+2)
    (three : 3∣n) (seven : 7∣n) (at8 : 13∣n+8) : False := by
  have pick : ∀ i : Fin 10, i.val.Prime → i.val=2 ∨ i.val=3 ∨ i.val=5 ∨ i.val=7 := by decide +kernel
  obtain ⟨t,ht⟩ := d32
  let m := 16*t+3
  have form : n+8=2*m := by dsimp only [m]; omega
  have m8 : m%8=3 := by dsimp only [m]; omega
  have pure : m=13^m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by omega) (by
    intro p pp dp
    have dn : p∣n+8 := form ▸ dvd_mul_of_dvd_right dp 2
    rcases support_at sparse (by decide) (by decide : Nat.Prime 13) (by decide) at8 pp dn with e|h
    · exact e
    · rcases pick ⟨p,by omega⟩ pp with z|z|z|z <;> change p=_ at z <;> subst p <;> omega)
  let e := m.primeFactorsList.length
  change m=13^e at pure
  have orbit := cycle (by decide : Nat.ModEq 8 (13^2) 1) e
  change 13^e%8=13^(e%2)%8 at orbit
  rw [←pure,m8] at orbit
  have no : ∀ t : Fin 2, 13^t.val%8≠3 := by decide +kernel
  exact no ⟨e%2,Nat.mod_lt _ (by decide)⟩ orbit.symm

private theorem res40_from_dvd {N : ℕ} (d : 40∣N+2) : (N+9)%40=7 := by
  obtain ⟨k,hk⟩ := d
  have e : N+9=40*k+7 := by omega
  omega

private theorem thirteen_branches {N : ℕ} (h : (N+2)%13=6 ∨ (N+2)%13=7) :
    13∣N+8 ∨ 13∣N+9 := by omega

private theorem avoid_two {n : ℕ} (two : 2∣n) : ¬2∣n+9 := by omega

private theorem avoid_five {n : ℕ} (five : 5∣n+2) : ¬5∣n+9 := by omega

private theorem avoid_seven {n : ℕ} (seven : 7∣n) : ¬7∣n+9 := by omega

private theorem allowed_nine {n p : ℕ} (sparse : (∀ k p q : ℕ, 0<k → p.Prime → q.Prime → p≠q → k<p → k<q → p∣n+k → q∣n+k → False)) (dj : 5∣n+2)
    (two : 2∣n) (seven : 7∣n) (at9 : 13∣n+9) (pp : p.Prime) (dp : p∣n+9) : p=3 ∨ p=13 := by
  rcases support_at sparse (by decide) (by decide : Nat.Prime 13) (by decide) at9 pp dp with h|low
  · exact Or.inr h
  · have pick : ∀ i : Fin 10, i.val.Prime → i.val=2 ∨ i.val=3 ∨ i.val=5 ∨ i.val=7 := by decide +kernel
    rcases pick ⟨p,Nat.lt_succ_of_le low⟩ pp with e|e|e|e
    · change p=2 at e
      exact (avoid_two two (e ▸ dp)).elim
    · exact Or.inl e
    · change p=5 at e
      exact (avoid_five dj (e ▸ dp)).elim
    · change p=7 at e
      exact (avoid_seven seven (e ▸ dp)).elim

private theorem nine_congruence (u v : ℕ) : (3^u*13^v)%40≠7 := by
  have orbit := (cycle (by decide : Nat.ModEq 40 (3^4) 1) u).mul (cycle (by decide : Nat.ModEq 40 (13^4) 1) v)
  change (3^u*13^v)%40=(3^(u%4)*13^(v%4))%40 at orbit
  have no : ∀ i j : Fin 4, (3^i.val*13^j.val)%40≠7 := by decide +kernel
  exact fun e => no ⟨u%4,Nat.mod_lt _ (by decide)⟩ ⟨v%4,Nat.mod_lt _ (by decide)⟩ (Eq.trans orbit.symm e)

private theorem nine_products {m : ℕ} (mp : 0 < m)
    (pool : ∀ p : ℕ, p.Prime → p∣m → p=3 ∨ p=13) (rem : m%40=7) : False := by
  obtain ⟨u,v,form⟩ := @two_factor_support m 3 13 mp Nat.prime_three pool
  have equality : (3^u*13^v)%40=7 := Eq.trans (congrArg (fun y : ℕ => y%40) form).symm rem
  exact nine_congruence u v equality

private theorem multiple_forty {m : ℕ} (d32 : 32∣m) (dj : 5∣m) : 40∣m :=
  (by decide : Nat.Coprime 8 5).mul_dvd_of_dvd_of_dvd ((by decide : 8∣32).trans d32) dj

private theorem nine_primes_only {n : ℕ} (sparse : (∀ k p q : ℕ, 0<k → p.Prime → q.Prime → p≠q → k<p → k<q → p∣n+k → q∣n+k → False)) (dj : 5∣n+2)
    (two : 2∣n) (seven : 7∣n) (at9 : 13∣n+9) :
    ∀ p : ℕ, p.Prime → p∣n+9 → p=3 ∨ p=13 :=
  fun p pp dp => @allowed_nine n p sparse dj two seven at9 pp dp

private theorem reject_at_nine {n : ℕ} (sparse : (∀ k p q : ℕ, 0<k → p.Prime → q.Prime → p≠q → k<p → k<q → p∣n+k → q∣n+k → False)) (dj : 5∣n+2) (d32 : 32∣n+2)
    (two : 2∣n) (seven : 7∣n) (at9 : 13∣n+9) : False :=
  @nine_products (n+9) (Nat.add_pos_right n (by decide : 0<9))
    (@nine_primes_only n sparse dj two seven at9)
    (@res40_from_dvd n (@multiple_forty (n+2) d32 dj))

/-- No exceptional multiple of six above the finite search can have five
at its second offset. At offsets eight and nine, thirteen yields the last
two incompatible congruences. -/
theorem no_five_at_two {n : ℕ} (sparse : (∀ k p q : ℕ, 0<k → p.Prime → q.Prime → p≠q → k<p → k<q → p∣n+k → q∣n+k → False)) (large : 1000000000000<n)
    (two : 2∣n) (three : 3∣n) (dj : 5∣n+2) : False := by
  obtain ⟨a,b,eq⟩ := two_factor_support (by omega : 0<n+2) Nat.prime_two (q:=5) (by
    intro p pp dp
    rcases support_at sparse (by decide) (by decide : Nat.Prime 5) (by decide) dj pp dp with e|h
    · exact Or.inr e
    · exact Or.inl (by have := pp.two_le; omega))
  have bp : 0<b := by
    by_contra! small
    have zero : b=0 := by omega
    rw [eq,zero,pow_zero,mul_one] at dj
    exact (by decide : ¬5∣2) ((by decide : Nat.Prime 5).dvd_of_dvd_pow dj)
  have mod3 := two_shift_mod_three sparse large two three bp eq
  have seven := seven_divides_of_five_shift sparse (by omega) two three (by decide : 2≤2) (by decide) dj
  have full : 21∣n := (by decide : Nat.Coprime 3 7).mul_dvd_of_dvd_of_dvd three seven
  have cres := (cycle (by decide : Nat.ModEq 21 (2^6) 1) a).mul (cycle (by decide : Nat.ModEq 21 (5^6) 1) b)
  change (2^a*5^b)%21=(2^(a%6)*5^(b%6))%21 at cres
  rw [←eq] at cres
  have tab : ∀ i j : Fin 6, (2^i.val*5^j.val)%21=2 → j.val%3=2 → i.val=5 ∧ j.val=2 := by decide +kernel
  have exp := tab ⟨a%6,Nat.mod_lt _ (by decide)⟩ ⟨b%6,Nat.mod_lt _ (by decide)⟩ (by change (2^(a%6)*5^(b%6))%21=2; omega) (by change b%6%3=2; omega)
  change a%6=5 ∧ b%6=2 at exp
  have d32 : 32∣n+2 := eq ▸ dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega : 5≤a)) _
  have cr := (cycle (by decide : Nat.ModEq 13 (2^12) 1) a).mul (cycle (by decide : Nat.ModEq 13 (5^12) 1) b)
  change (2^a*5^b)%13=(2^(a%12)*5^(b%12))%13 at cr
  rw [←eq] at cr
  have cover : ∀ i j : Fin 12, i.val%6=5 → j.val%6=2 →
      (2^i.val*5^j.val)%13=6 ∨ (2^i.val*5^j.val)%13=7 := by decide +kernel
  have choose := cover ⟨a%12,Nat.mod_lt _ (by decide)⟩ ⟨b%12,Nat.mod_lt _ (by decide)⟩
    (by change a%12%6=5; omega) (by change b%12%6=2; omega)
  change (2^(a%12)*5^(b%12))%13=6 ∨ (2^(a%12)*5^(b%12))%13=7 at choose
  have rem : (n+2)%13=6 ∨ (n+2)%13=7 := cr ▸ choose
  have branches := thirteen_branches rem
  rcases branches with at8|at9
  · exact reject_at_eight sparse dj d32 three seven at8
  · exact reject_at_nine sparse dj d32 two seven at9

end Erdos889.FiveMissingSeven
namespace Erdos889.SmallMissing
private theorem offset_of_missing {p n : ℕ} (hp : 0 < p) (miss : ¬p∣n) :
    ∃ k : ℕ, 0 < k ∧ k < p ∧ p∣n+k := by
  have nonzero : n%p≠0 := fun eq => miss (Nat.dvd_of_mod_eq_zero eq)
  have low := Nat.mod_lt n hp
  refine ⟨p-n%p,by omega,by omega,n/p+1,?_⟩
  rw [Nat.mul_add,mul_one]
  have eq := Nat.mod_add_div n p
  omega
end Erdos889.SmallMissing
namespace Erdos889.PellFiftyFive

private theorem pell_growth {D : ℤ} (eps : Pell.Solution₁ D) (hx : 1 < eps.x)
    (hy : 0 < eps.y) (n : ℕ) : (2:ℤ)^n*eps.y ≤ (eps^(n+1)).y := by
  induction n with
  | zero => simp
  | succ n ih =>
    have sx := Pell.Solution₁.x_pow_pos (show 0 < eps.x by omega) (n+1)
    have sy := Pell.Solution₁.y_pow_succ_pos (show 0 < eps.x by omega) hy n
    have grow := mul_le_mul_of_nonneg_left (show (2:ℤ) ≤ eps.x by omega) sy.le
    rw [pow_succ, show n+1+1=(n+1)+1 by rfl, pow_succ eps (n+1),Pell.Solution₁.y_mul]
    nlinarith [mul_pos sx hy]


private structure Row where
  d : ℕ
  a : ℕ
  b : ℕ
  deriving DecidableEq

private def rows : List Row := [⟨55,89,12⟩]
private def factors : List (ℕ × ℕ) := [(2,2),(3,1),(5,1),(11,1)]

private def coord (r : Row) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | k+1 =>
    let v := coord r k
    (v.1*r.a+r.d*v.2*r.b,v.1*r.b+v.2*r.a)

private theorem row_ok : ∀ r ∈ rows, 1<r.a ∧ 0<r.b ∧ r.a^2=r.d*r.b^2+1 := by decide +kernel

private theorem row_min : ∀ r ∈ rows, ∀ a ∈ List.range (r.a+1), ∀ b ∈ List.range (r.b+1),
    1<a → 0<b → a^2=r.d*b^2+1 → a=r.a ∧ b=r.b := by decide +kernel

private theorem row_hit : ∀ r ∈ rows, ∀ v ∈ factors, ∃ h : Fin 12, 0 < h.val ∧
    v.1∣(coord r h.val).2 ∧ ¬v.1^(v.2+1)∣(coord r h.val).2 := by decide +kernel

private theorem index_check : ∀ r ∈ rows, ∀ k : Fin 33, (coord r k.val).2∣k.val*660 →
    (coord r k.val).1≤89 := by decide +kernel

private theorem row_unit {r : Row} (hr : r∈rows) :
    ∃ g : Pell.Solution₁ (r.d:ℤ), Pell.IsFundamental g ∧ g.x=(r.a:ℤ) ∧ g.y=(r.b:ℤ) := by
  obtain ⟨ha,hb,eq⟩ := row_ok r hr
  have e : (r.a:ℤ)^2=(r.d:ℤ)*(r.b:ℤ)^2+1 := by exact_mod_cast eq
  let u : Pell.Solution₁ (r.d:ℤ) := Pell.Solution₁.mk r.a r.b (by linarith)
  have ux : 1<u.x := by change 1<(r.a:ℤ); exact_mod_cast ha
  have uy : 0<u.y := by change 0<(r.b:ℤ); exact_mod_cast hb
  obtain ⟨g,hg⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (Pell.Solution₁.d_pos_of_one_lt_x ux) (Pell.Solution₁.d_nonsquare_of_one_lt_x ux)
  have gx := hg.1
  have gy := hg.2.1
  have leA := hg.x_le_x ux
  have leB := hg.y_le_y ux uy
  change g.x≤(r.a:ℤ) at leA
  change g.y≤(r.b:ℤ) at leB
  have norm : g.x.toNat^2=r.d*g.y.toNat^2+1 := by
    zify
    rw [Int.toNat_of_nonneg (by omega),Int.toNat_of_nonneg (by omega)]
    linarith [g.prop]
  have hit := row_min r hr g.x.toNat (List.mem_range.mpr (by omega)) g.y.toNat
    (List.mem_range.mpr (by omega)) (by omega) (by omega) norm
  exact ⟨g,hg,by omega,by omega⟩

private theorem coord_eq {r : Row} (g : Pell.Solution₁ (r.d:ℤ)) (ga : g.x=(r.a:ℤ))
    (gb : g.y=(r.b:ℤ)) (i : ℕ) :
    (g^i).x=((coord r i).1:ℤ) ∧ (g^i).y=((coord r i).2:ℤ) := by
  induction i with
  | zero => simp [coord]
  | succ i ih =>
    rw [pow_succ]
    simp only [Pell.Solution₁.x_mul,Pell.Solution₁.y_mul,ih.1,ih.2,ga,gb,coord,Nat.cast_add,Nat.cast_mul]
    simp [mul_assoc]

private theorem smooth_y_dvd {r : Row} (hr : r∈rows) (g : Pell.Solution₁ (r.d:ℤ))
    (hg : Pell.IsFundamental g) (ga : g.x=(r.a:ℤ)) (gb : g.y=(r.b:ℤ)) (i : ℕ) (hi : 0 < i)
    (smooth : ∀ p : ℕ, p.Prime → p∣(g^i).y.natAbs → p=2 ∨ p=3 ∨ p=5 ∨ p=11) : (g^i).y.natAbs∣i*660 := by
  have nonzero (k : ℕ) (hk : 0<k) : (g^k).y.natAbs≠0 := by
    obtain ⟨t,ht⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    exact Int.natAbs_ne_zero.mpr (ht ▸ (Pell.Solution₁.y_pow_succ_pos hg.x_pos hg.2.1 t).ne')
  apply (Nat.factorization_le_iff_dvd (nonzero i hi) (Nat.mul_pos hi (by decide)).ne').mp
  intro p
  by_cases yes : p.Prime ∧ p∣(g^i).y.natAbs
  · obtain ⟨pp,dp⟩ := yes
    have small := smooth p pp dp
    have pick : p∈factors.map Prod.fst := by rcases small with rfl|rfl|rfl|rfl <;> decide
    obtain ⟨⟨q,e⟩,row,same⟩ := List.mem_map.mp pick
    change q=p at same
    subst q
    obtain ⟨h,hh,dv,nd⟩ := row_hit r hr (p,e) row
    have Y : (g^h.val).y.natAbs=(coord r h.val).2 := by rw [(coord_eq g ga gb h.val).2]; rfl
    change p ∣ (coord r h.val).2 at dv
    change ¬p^(e+1)∣(coord r h.val).2 at nd
    rw [←Y] at dv nd
    have le := Erdos889.PellValuation.pell_factorization_y_le g pp hi hh hg.x_pos hg.2.1 dv
    have ee : ((g^h.val).y.natAbs).factorization p ≤ e := by
      rw [pp.pow_dvd_iff_le_factorization (nonzero h.val hh)] at nd
      omega
    have power : ∀ v ∈ factors, v.1^v.2∣660 := by decide +kernel
    have EC := (pp.pow_dvd_iff_le_factorization (by decide : (660:ℕ)≠0)).mp (power (p,e) row)
    rw [Nat.factorization_mul hi.ne' (nonzero h.val hh),Finsupp.add_apply] at le
    rw [Nat.factorization_mul hi.ne' (by decide),Finsupp.add_apply]
    omega
  · by_cases pp : p.Prime
    · have nd : ¬p∣(g^i).y.natAbs := fun d => yes ⟨pp,d⟩
      simp [Nat.factorization_eq_zero_of_not_dvd nd]
    · simp [Nat.factorization_eq_zero_of_not_prime _ pp]

private theorem linear_exp (k : ℕ) : 660*(k+33) < 2^(k+32) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k+1+32=(k+32)+1 by omega,pow_succ]
    omega

private theorem seven_pell {r : Row} (hr : r∈rows) {x y : ℕ} (hx : 1 < x) (hy : 0 < y)
    (eq : x^2=r.d*y^2+1) (smooth : ∀ p : ℕ, p.Prime → p∣y → p=2 ∨ p=3 ∨ p=5 ∨ p=11) : x≤89 := by
  obtain ⟨g,hg,ga,gb⟩ := row_unit hr
  have e : (x:ℤ)^2=(r.d:ℤ)*(y:ℤ)^2+1 := by exact_mod_cast eq
  let w : Pell.Solution₁ (r.d:ℤ) := Pell.Solution₁.mk x y (by linarith)
  obtain ⟨i,hi⟩ := hg.eq_pow_of_nonneg (a:=w) (by change 0<(x:ℤ); omega) (by change 0≤(y:ℤ); positivity)
  have xx : (g^i).x=(x:ℤ) := by rw [←hi]; rfl
  have yy : (g^i).y=(y:ℤ) := by rw [←hi]; rfl
  have yi : (g^i).y.natAbs=y := by rw [yy]; rfl
  have ip : 0 < i := by
    by_contra! low
    have zi : i=0 := by omega
    rw [zi,pow_zero,Pell.Solution₁.y_one] at yy
    omega
  have dv := smooth_y_dvd hr g hg ga gb i ip (by rwa [yi])
  have le := Nat.le_of_dvd (Nat.mul_pos ip (by decide)) dv
  rw [yi] at le
  have i32 : i≤32 := by
    by_contra! high
    obtain ⟨k,ek⟩ := Nat.exists_eq_add_of_le (show 33 ≤ i by omega)
    have growth := pell_growth g hg.1 hg.2.1 (k+32)
    rw [show k+32+1=i by omega,yy,gb] at growth
    have gN : 2^(k+32)*r.b≤y := by exact_mod_cast growth
    have bb := (row_ok r hr).2.1
    have small := linear_exp k
    have lower := Nat.le_mul_of_pos_right (2^(k+32)) bb
    rw [Nat.mul_comm i 660] at le
    omega
  have coords := coord_eq g ga gb i
  have xc : (coord r i).1=x := by omega
  have yc : (coord r i).2=(g^i).y.natAbs := by rw [coords.2]; rfl
  have bound := index_check r hr ⟨i,by omega⟩ (yc ▸ dv)
  simpa only [xc] using bound



theorem pell_fifty_five_bound {x y : ℕ} (hx : 1<x) (hy : 0<y) (eq : x^2=55*y^2+1)
    (smooth : ∀ p : ℕ, p.Prime → p∣y → p=2 ∨ p=3 ∨ p=5 ∨ p=11) : x≤89 :=
  seven_pell (r:=⟨55,89,12⟩) (by decide) hx hy eq smooth

end Erdos889.PellFiftyFive

namespace Erdos889.PellFiftyFive

private theorem cycle {x t m : ℕ} (h : Nat.ModEq m (x^t) 1) (b : ℕ) :
    Nat.ModEq m (x^b) (x^(b%t)) := by
  calc
    x^b = x^(b%t)*(x^t)^(b/t) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
    _ ≡ x^(b%t)*1^(b/t) [MOD m] := (h.pow _).mul_left _
    _ = _ := by simp

/-- The unique remaining class of the exponent sieve has no starting value above 42. -/
theorem third_shift_survivor {n a b : ℕ}
    (sparse : ∀ k p q : ℕ, 0<k → p.Prime → q.Prime → p≠q → k<p → k<q → p∣n+k → q∣n+k → False)
    (shape : n+3=3^a*5^b) (pa : a%120=2) (pb : b%120=1) : n≤42 := by
  have bounds := (cycle (by decide : Nat.ModEq 88 (3^120) 1) a).mul
    (cycle (by decide : Nat.ModEq 88 (5^120) 1) b)
  change (3^a*5^b)%88=(3^(a%120)*5^(b%120))%88 at bounds
  rw [←shape,pa,pb] at bounds
  change (n+3)%88=45 at bounds
  let t := (n+3)/88
  have lift : 45+88*t=n+3 := by simpa only [t,bounds] using Nat.mod_add_div (n+3) 88
  let m := 22*t+11
  have form : n+2=4*m := by dsimp only [m]; omega
  have d11 : 11∣n+2 := by dsimp only [m] at form; omega
  have pure : m=11^m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd (by dsimp only [m]; omega) (by
    intro p pp d
    have d2 : p∣n+2 := form ▸ dvd_mul_of_dvd_right d 4
    by_contra ne
    have high : 2<p := by
      have := pp.two_le
      by_contra! h
      have e : p=2 := by omega
      subst p
      dsimp only [m] at d
      omega
    exact sparse 2 p 11 (by decide) pp (by decide) ne high (by decide) d2 d11)
  let e := m.primeFactorsList.length
  change m=11^e at pure
  have powN : n+2=4*11^e := by rw [←pure,←form]
  have d3 : 3∣n+3 := shape ▸ dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega : a≠0)) _
  have ep : e%2=1 := by
    have orbit := (cycle (by decide : Nat.ModEq 3 (11^2) 1) e).mul_left 4
    change (4*11^e)%3=(4*11^(e%2))%3 at orbit
    rw [←powN] at orbit
    by_contra h
    have rem := Nat.mod_lt e (by decide : 0<2)
    have ez : e%2=0 := by omega
    rw [ez,pow_zero,mul_one] at orbit
    omega
  let y := 4*3^(a/2)*5^(b/2)*11^(e/2)
  have f (p l : ℕ) : p^l=p^(l%2)*(p^(l/2))^2 := by
    rw [←pow_mul,←pow_add,Nat.mul_comm (l/2) 2,Nat.mod_add_div]
  have norm : (2*n+5)^2=55*y^2+1 := by
    calc
      _ = 4*(n+2)*(n+3)+1 := by ring
      _ = _ := by
        rw [powN,shape,f 11 e,f 3 a,f 5 b,ep,show a%2=0 by omega,show b%2=1 by omega]
        dsimp only [y]
        ring
  have smooth (p : ℕ) (pp : p.Prime) (d : p∣y) : p=2 ∨ p=3 ∨ p=5 ∨ p=11 := by
    dsimp only [y] at d
    rcases pp.dvd_mul.mp d with h|h
    · rcases pp.dvd_mul.mp h with h|h
      · rcases pp.dvd_mul.mp h with h|h
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp
            (pp.dvd_of_dvd_pow (show p∣(2:ℕ)^2 from h)))
        · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_three).mp (pp.dvd_of_dvd_pow h)))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 5)).mp (pp.dvd_of_dvd_pow h))))
    · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq pp (by decide : Nat.Prime 11)).mp (pp.dvd_of_dvd_pow h))))
  have hx := pell_fifty_five_bound (x:=2*n+5) (y:=y) (by omega) (by dsimp only [y]; positivity) norm smooth
  omega

end Erdos889.PellFiftyFive

namespace Erdos889.ThirdShift

private structure Row where
  q : ℕ
  k : ℕ
  pool : List ℕ
  m : ℕ
  mask : ℕ
  deriving Inhabited

private abbrev Stable (m : ℕ) := 0 < m ∧ 3^121%m=3%m ∧ 5^121%m=5%m

private theorem cycle {p m : ℕ} (one : Nat.ModEq m (p^121) p) (e : ℕ) (he : 0<e) :
    Nat.ModEq m (p^e) (p^(120+e%120)) := by
  have step (v : ℕ) (hv : 0<v) : Nat.ModEq m (p^(v+120)) (p^v) := by
    have one' := one.mul_right (p^(v-1))
    rw [←pow_add,show 121+(v-1)=v+120 by omega] at one'
    simpa only [←pow_succ',Nat.sub_add_cancel hv] using one'
  have steps (v : ℕ) (hv : 0<v) (j : ℕ) : Nat.ModEq m (p^(v+120*j)) (p^v) := by
    induction j with
    | zero => simp only [Nat.mul_zero,Nat.add_zero]; rfl
    | succ j ih =>
      rw [Nat.mul_succ,←Nat.add_assoc]
      exact (step _ (by omega)).trans ih
  calc
    p^e ≡ p^(e+120) [MOD m] := (step e he).symm
    _ = p^((120+e%120)+120*(e/120)) := by rw [Nat.add_assoc,Nat.mod_add_div,Nat.add_comm]
    _ ≡ _ [MOD m] := steps _ (by omega) _

private def residue (m k a b : ℕ) := (3^(120+a)*5^(120+b)+k+3*m-3)%m

private theorem residue_eq {n a b : ℕ} (eq : n+3=3^a*5^b) (ha : 0<a) (hb : 0<b)
    {m : ℕ} (stable : Stable m) (k : ℕ) :
    (n+k)%m=residue m k (a%120) (b%120) := by
  obtain ⟨mp,c3,c5⟩ := stable
  let w := 3^(120+a%120)*5^(120+b%120)+k
  have d : Nat.ModEq m (n+k+3) w := by
    rw [show n+k+3=(n+3)+k by omega,eq]
    exact ((cycle c3 a ha).mul (cycle c5 b hb)).add_right k
  have add : Nat.ModEq m w (w+3*m) := by
    change w%m=(w+3*m)%m
    rw [Nat.mul_comm 3 m,Nat.add_mul_mod_self_left]
  have strong := Nat.ModEq.add_right_cancel' 3
    (show Nat.ModEq m (n+k+3) (w+3*m-3+3) by rw [Nat.sub_add_cancel (by omega)]; exact d.trans add)
  exact strong

private abbrev RowOK (r : Row) :=
  r.q.Prime ∧ 0<r.k ∧ r.k<r.q ∧ r.q∈r.pool ∧ Stable r.q ∧ Stable r.m ∧
  r.mask.testBit (1%r.m)=true ∧
  ∀ i : Fin r.m, r.mask.testBit i.val=true → ∀ p∈r.pool, r.mask.testBit (i.val*p%r.m)=true

private abbrev CellOK (r : Row) (i j : ℕ) :=
  residue r.q r.k i j=0 ∧ r.mask.testBit (residue r.m r.k i j)=false ∧
  ∀ p : Fin (r.k+1), p.val.Prime → p.val∉r.pool → Stable p.val ∧ residue p.val r.k i j≠0

private theorem smooth {r : Row} (h : RowOK r) (t : ℕ) :
    0<t → (∀ p : ℕ, p.Prime → p∣t → p∈r.pool) → r.mask.testBit (t%r.m)=true := by
  induction t using induction_on_primes with
  | zero => omega
  | one => exact fun _ _ => h.2.2.2.2.2.2.1
  | prime_mul p t pp ih =>
    intro pos sup
    have tt : 0<t := Nat.pos_of_mul_pos_left pos
    have pt := sup p pp (dvd_mul_right p t)
    have good := ih tt (fun q pq d => sup q pq (dvd_mul_of_dvd_right d p))
    have final := h.2.2.2.2.2.2.2 ⟨t%r.m,Nat.mod_lt _ h.2.2.2.2.2.1.1⟩ good p pt
    simpa only [Nat.mod_mul_mod,Nat.mul_comm t p] using final

private theorem exclude {n a b : ℕ} (eq : n+3=3^a*5^b) (ha : 0<a) (hb : 0<b)
    (sol : Erdos889.v_l 1 n=1) {r : Row} (h : RowOK r) (cell : CellOK r (a%120) (b%120)) : False := by
  have qd := Nat.dvd_of_mod_eq_zero ((residue_eq eq ha hb h.2.2.2.2.1 r.k).trans cell.1)
  have support (p : ℕ) (pp : p.Prime) (dp : p∣n+r.k) : p∈r.pool := by
    by_contra outside
    have ne : r.q≠p := by intro e; exact outside (e ▸ h.2.2.2.1)
    by_cases early : p≤r.k
    · obtain ⟨st,nd⟩ := cell.2.2 ⟨p,by omega⟩ pp outside
      exact nd ((residue_eq eq ha hb st r.k).symm.trans (Nat.mod_eq_zero_of_dvd dp))
    · exact OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2.two_primes h.2.1 h.1 pp ne h.2.2.1 (by omega) qd dp sol
  have prop := smooth h (n+r.k) (by have := h.2.1; omega) support
  rw [residue_eq eq ha hb h.2.2.2.2.2.1,cell.2.1] at prop
  contradiction

private def rows : List Row := [
  ⟨11,2,[2, 11],13,0x1ffe⟩,
  ⟨11,2,[2, 11],16,0x1b5f⟩,
  ⟨11,2,[2, 11],20,0x11916⟩,
  ⟨11,2,[2, 11],32,0xb4f1b5f⟩,
  ⟨11,2,[2, 11],39,0x102510d36⟩,
  ⟨11,2,[2, 11],41,0x1fffffffffe⟩,
  ⟨11,2,[2, 11],48,0x110902410916⟩,
  ⟨11,2,[2, 11],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  ⟨11,2,[2, 11],241,0x1a246480a08200027002003000005430a8000030010039000104140498916⟩,
  ⟨11,2,[2, 11],615,0x500026110410086902020124030114c029821108041801025825144a01125324a4100c86900c02524090012116810502410c36814d22422420c841161309261b08208965125001b4c16996⟩,
  ⟨11,2,[2, 11],728,0x41001000101040040110001001000081100010100000001000001000000114001010000000100010110000001020101020850000001010000100100050110000001400101000c0001004103000008010201090000101100450b16⟩,
  ⟨11,5,[11],5,0x2⟩,
  ⟨11,9,[3, 11],13,0x1ffe⟩,
  ⟨11,9,[3, 11],31,0x7ffffffe⟩,
  ⟨11,9,[3, 11],41,0x1fffffffffe⟩,
  ⟨11,9,[3, 11],61,0x1434026619900b0a⟩,
  ⟨11,9,[3, 11],91,0x50f01092600000649080f0a⟩,
  ⟨11,9,[3, 11],164,0x8820a0220282088002aa88a282a02a0a288aaa⟩,
  ⟨11,10,[2, 11],7,0x16⟩,
  ⟨13,2,[2, 13],55,0x12081594076396⟩,
  ⟨13,4,[2, 13],16,0x2737⟩,
  ⟨13,4,[2, 13],160,0x11010100210101220205010011003104052316⟩,
  ⟨13,4,[2, 13],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  ⟨13,4,[2, 13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  ⟨13,4,[2, 13],287,0x4310a07408c043e714195a511241aac3b5325038226d97352425d3102ddc8f50f8f335e⟩,
  ⟨13,4,[2, 13],451,0x688580269400082c82200000008448a0800c0810005000001001903060c09800800000a00081030010512210000000441341000296401a116⟩,
  ⟨13,7,[7, 13],40,0x2000882a82⟩,
  ⟨13,8,[2, 5, 13],41,0x1fffffffffe⟩,
  ⟨13,8,[2, 5, 13],112,0x131050301332215211107152736⟩,
  ⟨13,8,[2, 5, 13],244,0x7553717517135511113571575331533373117551773131357335157153776⟩,
  ⟨13,8,[2, 5, 13],732,0x514110510110510110114110132110114110510112110110130514114110014132110110114110114114510110132130134512510112530110110112502110512516130110112130134110530130110110512130114130116112536⟩,
  ⟨13,9,[3, 13],31,0x7ffffffe⟩,
  ⟨13,9,[3, 13],40,0xa08800220a⟩,
  ⟨13,10,[2, 13],16,0x2737⟩,
  ⟨13,10,[2, 13],160,0x11010100210101220205010011003104052316⟩,
  ⟨13,10,[2, 13],183,0x522080904d101825025b6130012d10c36504d26cb2916⟩,
  ⟨13,10,[2, 13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  ⟨13,10,[2, 13],451,0x688580269400082c82200000008448a0800c0810005000001001903060c09800800000a00081030010512210000000441341000296401a116⟩,
  ⟨13,10,[2, 13],488,0x1010101010101010121010101010101010105010101010101010101030121010101010101110103010101010101010101010101010111010105012116⟩,
  ⟨13,11,[11, 13],12,0x802⟩,
  ⟨13,12,[2, 3, 13],160,0x1111010110a19901230a4501415100b18d05335e⟩,
  ⟨13,12,[2, 3, 13],217,0x1eb3383c2a402ec12674941062a7951820a4b9920dd00950f07335e⟩,
  ⟨13,12,[2, 3, 13],224,0x121850bc9b32a4571c14f8da76e1131950bd9a33a5561d14f9db77e⟩,
  ⟨31,6,[2, 3, 31],352,0x20ca85966e031cb94967e030da95867e130cb95977e020da85966e131ca94977e030da95867e131cb95977e⟩,
  ⟨31,6,[2, 3, 31],455,0x100300401b04042540128a54344021583625010308859823214e313041085223840e681c631103411a5490c1228695194e490275a90f135e⟩]
set_option maxHeartbeats 3000000 in
private theorem good : ∀ r∈rows, RowOK r := by decide +kernel
private def packed : ℕ → ℕ
  | 0 => 0x2c00000004800000007400000003400000001c00000002c00000004800000009c00000003400000001000000002c00000004800000007400000003400000000c00000002c00000004800000009c00000003400000000c0000000
  | 2 => 0x2c00000004800000008000000003c00000001800000002c00000004800000008c00000003000000000c00000002c00000004800000008000000003c00000000c00000002c0000000480000000880000000300000000000
  | 3 => 0x1300000000f00000000000000000b00000001200000001500000000f00000000200000000b00000001200000001300000000f00000000000000000b00000001200000001800000000f00000000200000000b000000012000
  | 5 => 0x1200000001a00000001000000000200000000b00000001200000002a00000001000000000100000000b00000001200000001a00000001000000000200000000b00000001200000002800000001000000000100000000b000000
  | 6 => 0x3c00000000c00000002c00000004800000007000000003c00000000c00000002c00000004800000009c00000003c00000001000000002c00000004800000007000000003c00000001800000002c00000004800000009c0000000
  | 8 => 0x3000000000c00000002c00000004800000008000000004000000002000000002c00000004800000008400000003000000001800000002c00000004800000008000000004000000000c00000002c0000000480000000840
  | 9 => 0xb00000001200000001300000001000000000000000000b00000001200000001400000001100000000100000000b00000001200000001300000001000000000000000000b000000012000000014000000011000000001000
  | 11 => 0x200000000b00000001200000001a00000000f00000000100000000b00000001200000002a00000000f00000000200000000b00000001200000001a00000000f00000000100000000b00000001200000002800000000f000000
  | 12 => 0x4800000009c00000003c00000001000000002c00000004800000007800000003c00000000c00000002c00000004800000009c00000003c00000000c00000002c00000004800000007800000003c00000002000000002c0000000
  | 14 => 0x4800000009400000003000000000c00000002c00000004800000008000000003c00000000c00000002c00000004800000008800000003000000001c00000002c00000004800000008000000003c00000001800000002c0
  | 15 => 0xf00000000200000000b00000001200000001300000000f00000000000000000b00000001200000001600000000f00000000200000000b00000001200000001300000000f00000000000000000b000000012000000015000
  | 17 => 0x2a00000000f00000000100000000b00000001200000001a00000000f00000000200000000b00000001200000002800000000f00000000100000000b00000001200000001a00000000f00000000200000000b000000012000000
  | 18 => 0xc00000002c00000004800000009c00000003c00000001000000002c00000004800000007000000003c00000001800000002c00000004800000009c00000003c00000000c00000002c00000004800000007000000003c0000000
  | 20 => 0x1c00000002c00000004800000008400000003000000001800000002c00000004800000007c00000003400000000c00000002c00000004800000008400000003000000000c00000002c00000004800000007c0000000340
  | 21 => 0x1200000001400000000f00000000100000000b00000001200000001300000000f00000000000000000b00000001200000001400000000f00000000100000000b00000001200000001300000000f00000000000000000b000
  | 23 => 0xb00000001200000002900000001000000000200000000b00000001200000001a00000001000000000100000000b00000001200000002800000001000000000200000000b00000001200000001a000000010000000001000000
  | 24 => 0x7400000004000000000c00000002c00000004800000009c00000004000000000c00000002c00000004800000007400000004000000001c00000002c00000004800000009c00000004000000001000000002c0000000480000000
  | 26 => 0x8000000003c00000000c00000002c00000004800000008800000003000000001c00000002c00000004800000008000000003c00000001800000002c00000004800000009000000003000000000c00000002c0000000480
  | 27 => 0xb00000001200000001600000000f00000000200000000b00000001200000001300000000f00000000000000000b00000001200000001500000000f00000000200000000b00000001200000001300000000f000
  | 29 => 0xf00000000200000000b00000001200000002800000000f00000000100000000b00000001200000001a00000000f00000000200000000b00000001200000002a00000000f00000000100000000b00000001200000001a000000
  | 30 => 0x2c00000004800000007000000003400000001800000002c00000004800000009c00000003400000000c00000002c00000004800000007000000003400000000c00000002c00000004800000009c0000000340000000100000000
  | 32 => 0x2c00000004800000008000000003c00000000c00000002c00000004800000008400000003000000000c00000002c00000004800000008000000003c00000002800000002c0000000480000000840000000300000000180
  | 33 => 0x1300000000f00000000000000000b00000001200000001400000000f00000000100000000b00000001200000001300000000f00000000000000000b00000001200000001400000000f00000000100000000b000000012000
  | 35 => 0x1200000001a00000001000000000100000000b00000001200000002800000001000000000200000000b00000001200000001a00000001000000000100000000b00000001200000002a00000001000000000200000000b000000
  | 36 => 0x3c00000000c00000002c0000000480000000b000000003c00000001c00000002c00000004800000009c00000003c00000001000000002c0000000480000000ac00000003c00000000c00000002c00000004800000009c0000000
  | 38 => 0x3000000002000000002c00000004800000008000000004000000001800000002c00000004800000008c00000003000000000c00000002c00000004800000008000000004000000000c00000002c0000000480000000880
  | 39 => 0xb00000001200000001300000000e00000000000000000b00000001200000001500000001100000000200000000b00000001200000001300000000e00000000000000000b000000012000000017000000011000000002000
  | 41 => 0x100000000b00000001200000001a00000000f00000000200000000b00000001200000002a00000000f00000000100000000b00000001200000001a00000000f00000000200000000b00000001200000002800000000f000000
  | 42 => 0x4800000009c00000003c00000000c00000002c00000004800000007000000003c00000000c00000002c00000004800000009c00000003c00000001000000002c00000004800000007000000003c00000001800000002c0000000
  | 44 => 0x4800000008400000003000000000c00000002c00000004800000008000000003c00000001c00000002c00000004800000008400000003000000001800000002c00000004800000008000000003c00000000c00000002c0
  | 45 => 0xf00000000100000000b00000001200000001300000000f00000000000000000b00000001200000001400000000f00000000100000000b00000001200000001300000000f00000000000000000b000000012000000014000
  | 47 => 0x2800000000f00000000200000000b00000001200000001a00000000f00000000100000000b00000001200000002a00000000f00000000200000000b00000001200000001a00000000f00000000100000000b000000012000000
  | 48 => 0x2000000002c00000004800000009c00000003c00000001000000002c00000004800000006c00000003c00000000c00000002c00000004800000009c00000003c00000000c00000002c00000004800000006c00000003c0000000
  | 50 => 0x1400000002c00000004800000009000000003000000000c00000002c00000004800000007c00000003400000000c00000002c00000004800000008800000003000000001c00000002c00000004800000007c0000000340
  | 51 => 0x1200000001500000000f00000000200000000b00000001200000001300000000f00000000000000000b00000001200000001800000000f00000000200000000b00000001200000001300000000f00000000000000000b000
  | 53 => 0xb00000001200000002900000001000000000100000000b00000001200000001a00000001000000000200000000b00000001200000002800000001000000000100000000b00000001200000001a000000010000000002000000
  | 54 => 0x7000000004000000000c00000002c00000004800000009c00000004000000001000000002c00000004800000007000000004000000001800000002c00000004800000009c00000004000000000c00000002c0000000480000000
  | 56 => 0x8000000003c00000001c00000002c00000004800000008400000003000000001800000002c00000004800000008000000003c00000000c00000002c00000004800000008400000003000000000c00000002c0000000480
  | 57 => 0xb00000001200000001400000000f00000000100000000b00000001200000001300000000f00000000000000000b00000001200000001400000000f00000000100000000b00000001200000001300000000f000
  | 59 => 0xf00000000100000000b00000001200000002a00000000e00000000200000000b00000001200000001a00000000f00000000100000000b00000001200000002800000000e00000000200000000b00000001200000001a000000
  | 60 => 0x2c00000004800000007400000003400000000c00000002c00000004800000009c00000003400000000c00000002c00000004800000007400000003400000001c00000002c00000004800000009c0000000340000000100000000
  | 62 => 0x2c00000004800000008000000003c00000000c00000002c00000004800000008800000003000000002400000002c00000004800000008000000003c00000001800000002c00000004800000008c00000003000000000c0
  | 63 => 0x1300000000f00000000000000000b00000001200000001900000000f00000000200000000b00000001200000001300000000f00000000000000000b00000001200000001500000000f00000000200000000b000000012000
  | 65 => 0x1200000001a00000001000000000200000000b00000001200000002800000001000000000100000000b00000001200000001a00000001000000000200000000b00000001200000002a00000001000000000100000000b000000
  | 66 => 0x3c00000001000000002c00000004800000007000000003c00000001800000002c00000004800000009c00000003c00000000c00000002c00000004800000007000000003c00000000c00000002c00000004800000009c0000000
  | 68 => 0x3000000001800000002c00000004800000008000000004000000000c00000002c00000004800000008400000003000000000c00000002c00000004800000008000000004000000002000000002c0000000480000000840
  | 69 => 0xb00000001200000001300000001000000000000000000b00000001200000001400000001100000000100000000b00000001200000001300000001000000000000000000b000000012000000014000000011000000001000
  | 71 => 0x200000000b00000001200000001a00000000f00000000100000000b00000001200000002800000000f00000000200000000b00000001200000001a00000000f00000000100000000b00000001200000002a00000000f000000
  | 72 => 0x4800000009c00000003c00000000c00000002c00000004800000007800000003c00000002000000002c00000004800000009c00000003c00000001000000002c00000004800000007800000003c00000000c00000002c0000000
  | 74 => 0x4800000008800000003000000001c00000002c00000004800000008000000003c00000001800000002c00000004800000009800000003000000000c00000002c00000004800000008000000003c00000000c00000002c0
  | 75 => 0xf00000000200000000b00000001200000001300000000f00000000000000000b00000001200000001500000000f00000000200000000b00000001200000001300000000f00000000000000000b000000012000000016000
  | 77 => 0x2800000000f00000000100000000b00000001200000001a00000000f00000000200000000b00000001200000002a00000000f00000000100000000b00000001200000001a00000000f00000000200000000b000000012000000
  | 78 => 0x1800000002c00000004800000009c00000003c00000000c00000002c00000004800000007000000003c00000000c00000002c00000004800000009c00000003c00000001000000002c00000004800000007000000003c0000000
  | 80 => 0xc00000002c00000004800000008400000003000000000c00000002c00000004800000007c00000003400000001c00000002c00000004800000008400000003000000001800000002c00000004800000007c0000000340
  | 81 => 0x1200000001400000000f00000000100000000b00000001200000001300000000f00000000000000000b00000001200000001400000000f00000000100000000b00000001200000001300000000f00000000000000000b000
  | 83 => 0xb00000001200000002800000001000000000200000000b00000001200000001a00000001000000000100000000b00000001200000002900000001000000000200000000b00000001200000001a000000010000000001000000
  | 84 => 0x7400000004000000001c00000002c00000004800000009c00000004000000001000000002c00000004800000007400000004000000000c00000002c00000004800000009c00000004000000000c00000002c0000000480000000
  | 86 => 0x8000000003c00000001800000002c00000004800000009000000003000000000c00000002c00000004800000008000000003c00000000c00000002c00000004800000008800000003000000001c00000002c0000000480
  | 87 => 0xb00000001200000001500000000f00000000200000000b00000001200000001300000000f00000000000000000b00000001200000001600000000f00000000200000000b00000001200000001300000000f000
  | 89 => 0xf00000000200000000b00000001200000002a00000000f00000000100000000b00000001200000001a00000000f00000000200000000b00000001200000002800000000f00000000100000000b00000001200000001a000000
  | 90 => 0x2c00000004800000007000000003400000000c00000002c00000004800000009c00000003400000001000000002c00000004800000007000000003400000001400000002c00000004800000009c00000003400000000c0000000
  | 92 => 0x2c00000004800000008000000003c00000002400000002c00000004800000008400000003000000001800000002c00000004800000008000000003c00000000c00000002c00000004800000008400000003000000000c0
  | 93 => 0x1300000000f00000000000000000b00000001200000001400000000f00000000100000000b00000001200000001300000000f00000000000000000b00000001200000001400000000f00000000100000000b000000012000
  | 95 => 0x1200000001a00000001000000000100000000b00000001200000002a00000001000000000200000000b00000001200000001a00000001000000000100000000b00000001200000002800000001000000000200000000b000000
  | 96 => 0x3c00000001000000002c0000000480000000ac00000003c00000000c00000002c00000004800000009c00000003c00000000c00000002c0000000480000000b000000003c00000001c00000002c00000004800000009c0000000
  | 98 => 0x3000000000c00000002c00000004800000008000000004000000000c00000002c00000004800000008800000003000000002000000002c00000004800000008000000004000000001800000002c00000004800000008c0
  | 99 => 0xb00000001200000001300000001000000000000000000b00000001200000001700000000e00000000200000000b00000001200000001300000001000000000000000000b00000001200000001500000000e000000002000
  | 101 => 0x100000000b00000001200000001a00000000f00000000200000000b00000001200000002800000000f00000000100000000b00000001200000001a00000000f00000000200000000b00000001200000002a00000000f000000
  | 102 => 0x4800000009c00000003c00000001000000002c00000004800000007000000003c00000001800000002c00000004800000009c00000003c00000000c00000002c00000004800000007000000003c00000000c00000002c0000000
  | 104 => 0x4800000008400000003000000001800000002c00000004800000008000000003c00000000c00000002c00000004800000008400000003000000000c00000002c00000004800000008000000003c00000001c00000002c0
  | 105 => 0xf00000000100000000b00000001200000001300000000f00000000000000000b00000001200000001400000000f00000000100000000b00000001200000001300000000f00000000000000000b000000012000000014000
  | 107 => 0x2a00000000f00000000200000000b00000001200000001a00000000f00000000100000000b00000001200000002800000000f00000000200000000b00000001200000001a00000000f00000000100000000b000000012000000
  | 108 => 0xc00000002c00000004800000009c00000003c00000000c00000002c00000004800000007400000003c00000002000000002c00000004800000009c00000003c00000001000000002c00000004800000007400000003c0000000
  | 110 => 0xc00000002c00000004800000008800000003000000001400000002c00000004800000007c00000003400000001800000002c00000004800000009000000003000000000c00000002c00000004800000007c0000000340
  | 111 => 0x1200000001800000000f00000000200000000b00000001200000001300000000f00000000000000000b00000001200000001500000000f00000000200000000b00000001200000001300000000f00000000000000000b000
  | 113 => 0xb00000001200000002800000001000000000100000000b00000001200000001a00000001000000000200000000b00000001200000002900000001000000000100000000b00000001200000001a000000010000000002000000
  | 114 => 0x7000000004000000001800000002c00000004800000009c00000004000000000c00000002c00000004800000007000000004000000000c00000002c00000004800000009c00000004000000001000000002c0000000480000000
  | 116 => 0x8000000003c00000000c00000002c00000004800000008400000003000000000c00000002c00000004800000008000000003c00000001c00000002c00000004800000008400000003000000001800000002c0000000480
  | 117 => 0xb00000001200000001400000000f00000000100000000b00000001200000001300000000f00000000000000000b00000001200000001400000000f00000000100000000b00000001200000001300000000f000
  | 119 => 0xe00000000100000000b00000001200000002800000000f00000000200000000b00000001200000001a00000000e00000000100000000b00000001200000002a00000000f00000000200000000b00000001200000001a000000
  | _ => 0
private def idx (i j : ℕ) := ((packed i) >>> (j*6))%64
private def rowFor (i j : ℕ) : Row := rows[idx i j]?.getD default
private abbrev Test (i j : ℕ) := i%6=(j+1)%6 → j%3≠0 → (i≠2 ∨ j≠1) → idx i j < rows.length ∧ CellOK (rowFor i j) i j
set_option maxHeartbeats 3000000 in
private theorem block0 : ∀ i ∈ List.range' 0 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block1 : ∀ i ∈ List.range' 10 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block2 : ∀ i ∈ List.range' 20 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block3 : ∀ i ∈ List.range' 30 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block4 : ∀ i ∈ List.range' 40 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block5 : ∀ i ∈ List.range' 50 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block6 : ∀ i ∈ List.range' 60 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block7 : ∀ i ∈ List.range' 70 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block8 : ∀ i ∈ List.range' 80 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block9 : ∀ i ∈ List.range' 90 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block10 : ∀ i ∈ List.range' 100 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
set_option maxHeartbeats 3000000 in
private theorem block11 : ∀ i ∈ List.range' 110 10, ∀ j : Fin 120, Test i j.val := by decide +kernel
private theorem cover {i j : ℕ} (hi : i<120) (hj : j<120) : Test i j := by
  by_cases lt0 : i<10
  · exact block0 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases lt1 : i<20
  · exact block1 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases lt2 : i<30
  · exact block2 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases lt3 : i<40
  · exact block3 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases lt4 : i<50
  · exact block4 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases lt5 : i<60
  · exact block5 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases lt6 : i<70
  · exact block6 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases lt7 : i<80
  · exact block7 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases lt8 : i<90
  · exact block8 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases lt9 : i<100
  · exact block9 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  by_cases lt10 : i<110
  · exact block10 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩
  exact block11 i (by simp only [List.mem_range'_1]; omega) ⟨j,hj⟩

theorem third_shift_residues {n a b : ℕ} (eq : n+3=3^a*5^b) (ha : 0<a) (hb : 0<b)
    (sol : Erdos889.v_l 1 n=1) (mod6 : a%6=(b+1)%6) (nd : ¬3∣b) : a%120=2 ∧ b%120=1 := by
  by_contra bad
  have cell := cover (show a%120<120 by omega) (show b%120<120 by omega)
  obtain ⟨ix,ok⟩ := cell (by omega) (by omega) (by omega)
  have mem : rowFor (a%120) (b%120) ∈ rows := by
    simp only [rowFor,List.getElem?_eq_getElem ix,Option.getD_some]
    exact List.getElem_mem _
  exact exclude eq ha hb sol (good _ mem) ok
end Erdos889.ThirdShift
namespace Erdos889.ThirdShiftApplication

private theorem cycle {x t m : ℕ} (h : Nat.ModEq m (x^t) 1) (b : ℕ) :
    Nat.ModEq m (x^b) (x^(b%t)) := by
  calc
    x^b = x^(b%t)*(x^t)^(b/t) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
    _ ≡ x^(b%t)*1^(b/t) [MOD m] := (h.pow _).mul_left _
    _ = _ := by simp

theorem no_third_from_sieve {n : ℕ}
    (sparse : ∀ k p q : ℕ, 0<k → p.Prime → q.Prime → p≠q → k<p → k<q → p∣n+k → q∣n+k → False)
    (modular : ∀ {a b : ℕ}, n+3=3^a*5^b → 0<a → 0<b → a%6=(b+1)%6 → ¬3∣b →
      a%120=2 ∧ b%120=1)
    (large : 1000000000000<n) (two : 2∣n) (three : 3∣n) (dj : 5∣n+3) : False := by
  let a := (n+3).factorization 3
  let m := (n+3)/3^a
  let b := m.primeFactorsList.length
  have pos : 0 < m := Nat.ordCompl_pos 3 (by omega : n+3≠0)
  have fac : 3^a*m=n+3 := Nat.ordProj_mul_ordCompl_eq_self _ _
  have pure : m=5^b := Nat.eq_prime_pow_of_unique_prime_dvd pos.ne' (by
    intro p pp dv
    have d : p∣n+3 := fac ▸ dvd_mul_of_dvd_right dv _
    by_contra ne
    have gt : 3<p := by
      by_contra! low
      have opts : p=2 ∨ p=3 := by have := pp.two_le; omega
      rcases opts with rfl|rfl
      · omega
      · exact Nat.not_dvd_ordCompl Nat.prime_three (by omega : n+3≠0) dv
    exact sparse 3 p 5 (by decide) pp (by decide) ne gt (by decide) d dj)
  have shape : n+3=3^a*5^b := by rw [←pure,fac]
  have apos : 0<a := by
    by_contra! low
    have zero : a=0 := by omega
    have d3 := dvd_add three (dvd_refl 3)
    rw [shape,zero,pow_zero,one_mul] at d3
    exact (by decide : ¬3∣5) (Nat.prime_three.dvd_of_dvd_pow d3)
  have bpos : 0<b := by
    by_contra! low
    have zero : b=0 := by omega
    rw [shape,zero,pow_zero,mul_one] at dj
    exact (by decide : ¬5∣3) ((by decide : Nat.Prime 5).dvd_of_dvd_pow dj)
  have seven := Erdos889.FiveMissingSeven.seven_divides_of_five_shift sparse (by omega) two three
    (by decide : 2≤3) (by decide) dj
  have mod7 := (cycle (by decide : Nat.ModEq 7 (3^6) 1) a).mul (cycle (by decide : Nat.ModEq 7 (5^6) 1) b)
  change (3^a*5^b)%7=(3^(a%6)*5^(b%6))%7 at mod7
  rw [←shape] at mod7
  have row : ∀ i j : Fin 6, (3^i.val*5^j.val)%7=3 → i.val=(j.val+1)%6 := by decide +kernel
  have lift := row ⟨a%6,Nat.mod_lt _ (by decide)⟩ ⟨b%6,Nat.mod_lt _ (by decide)⟩ (by
    change (3^(a%6)*5^(b%6))%7=3
    exact mod7.symm.trans (by have e := (Nat.modEq_zero_iff_dvd.mpr seven).add_right 3; exact e))
  change a%6=(b%6+1)%6 at lift
  have alignment : a%6=(b+1)%6 := by omega
  have nd := Erdos889.FiveMissingSeven.no_cube_at_five_shift sparse large two three (Or.inr rfl) bpos shape
  obtain ⟨pa,pb⟩ := modular shape apos bpos alignment nd
  exact (Nat.not_lt_of_ge (Erdos889.PellFiftyFive.third_shift_survivor sparse shape pa pb)) (by omega)

end Erdos889.ThirdShiftApplication

namespace Erdos889.SmallMissing

open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

theorem no_five_at_three
    (modular : ∀ {n a b : ℕ}, n+3=3^a*5^b → 0<a → 0<b → Erdos889.v_l 1 n=1 →
      a%6=(b+1)%6 → ¬3∣b → a%120=2 ∧ b%120=1)
    {n : ℕ} (large : 1000000000000<n) (sol : Erdos889.v_l 1 n=1) (dj : 5∣n+3) : False := by
  have two : 2∣n := by
    by_contra nd
    have odd : Odd n := by rw [Nat.odd_iff]; omega
    rcases (odd_classification odd).mp sol with h|h|h|h <;> omega
  exact Erdos889.ThirdShiftApplication.no_third_from_sieve
    (fun _ _ _ hk hp hq ne lp lq dp dq => two_primes hk hp hq ne lp lq dp dq sol)
    (fun eq ha hb => modular eq ha hb sol) large two (three_dvd_of_large_solution large sol) dj

end Erdos889.SmallMissing


namespace Erdos889.SmallMissing
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

/-- Every exceptional starting value beyond the finite search is divisible by thirty. -/
theorem thirty_dvd_of_large_solution {n : ℕ} (big : 1000000000000<n) (sol : Erdos889.v_l 1 n=1) : 30∣n := by
  have three := three_dvd_of_large_solution big sol
  have two : 2∣n := by
    by_contra missing
    have odd : Odd n := by rw [Nat.odd_iff]; omega
    rcases (odd_classification odd).mp sol with h|h|h|h <;> omega
  have sparse (k p q : ℕ) (hk : 0<k) (pp : p.Prime) (pq : q.Prime) (ne : p≠q)
      (lp : k<p) (lq : k<q) (dp : p∣n+k) (dq : q∣n+k) : False := two_primes hk pp pq ne lp lq dp dq sol
  have five : 5∣n := by
    by_contra no
    obtain ⟨k,hk,hi,d⟩ := offset_of_missing (by decide : 0<5) no
    interval_cases k
    · have eq : n%5=4 := by omega
      rcases (Erdos889.FiveSuccessor.four_mod_five eq).mp sol with h|h <;> omega
    · exact Erdos889.FiveMissingSeven.no_five_at_two sparse big two three d
    · exact no_five_at_three Erdos889.ThirdShift.third_shift_residues big sol d
    · exact Erdos889.FiveMissingSeven.no_five_at_four sparse (by omega) two three d
  omega
end Erdos889.SmallMissing

namespace Erdos889.MissingPrimeSieve
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2
/-- Bounds and divisibility of any solution beyond the list through 330. -/
theorem further_solution_bounds_thirty {n : ℕ} (big : 330<n) (sol : v_l 1 n=1) :
    1000000000000000000<n ∧ n<2^(2^21) ∧ 30∣n := by
  have lower : 1000000000000000000<n := by by_contra! low; exact no_new_solutions big low sol
  exact ⟨lower,Erdos889.effective_binary_cutoff sol,
    Erdos889.SmallMissing.thirty_dvd_of_large_solution (by omega) sol⟩

/-- Complete positive classification away from multiples of thirty. -/
theorem solutions_missing_thirty {n : ℕ} (pos : 0<n) (miss : ¬30∣n) :
    v_l 1 n=1 ↔ n ∈ [1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,36,42,46,48,70,78,80,96,190,222] := by
  by_cases small : n≤330
  · rw [solutions_through_330 pos small]
    let xs : List ℕ := [1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,48,60,70,78,80,96,120,190,222,330]
    change n ∈ xs ↔ _
    have keep : xs.filter (fun x => decide (¬30∣x)) =
        [1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,36,42,46,48,70,78,80,96,190,222] := by decide
    rw [←keep,List.mem_filter]
    simp [miss]
  constructor
  · intro sol
    exact (miss (further_solution_bounds_thirty (by omega) sol).2.2).elim
  · intro mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    omega


private theorem round_bound {N cap : ℕ} (hi : N-1 < cap) (nd : 30∣N-1) :
    N ≤ 1+30*((cap-1)/30) := by omega

/-- Exactly four prime-square predecessors outside the multiples of thirty are solutions. -/
theorem prime_square_missing_thirty {n p : ℕ} (hp : p.Prime) (shape : n+1=p^2)
    (miss : ¬30∣n) : v_l 1 n=1 ↔ n ∈ [3,8,24,48] := by
  have hp2 : 4≤p^2 := Nat.pow_le_pow_left hp.two_le 2
  have pos : 0<n := by omega
  constructor
  · intro sol
    have mem := (solutions_missing_thirty pos miss).mp sol
    have size : n≤222 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      omega
    have bound : p<15 := by
      by_contra! ge
      have low : 225≤p^2 := Nat.pow_le_pow_left ge 2
      omega
    have table : ∀ u : Fin 15, u.val.Prime →
        u.val^2-1 ∈ ([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,36,42,46,48,70,78,80,96,190,222] : List ℕ) →
        u.val^2-1 ∈ ([3,8,24,48] : List ℕ) := by decide +kernel
    have eq : p^2-1=n := by omega
    have known : p^2-1 ∈ ([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,36,42,46,48,70,78,80,96,190,222] : List ℕ) := eq.symm ▸ mem
    simpa only [eq] using table ⟨p,bound⟩ hp known
  · intro mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl <;>
      apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide

/-- For N above 223, a predecessor outside the multiples of thirty always supplies
a pair of fresh primes. Beyond the rounded upper bound the same holds for every N. -/
theorem witness_after_classification {N : ℕ} (big : 223<N)
    (h : 1+30*((2^(2^21)-1)/30)<N ∨ ¬30∣N-1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣N+d ∧ s∣N+d := by
  by_contra miss
  have sol := Erdos889.Missing.predecessor_solution_of_missing (by omega : 1<N) miss
  by_cases div : 30∣N-1
  · have nr := round_bound (Erdos889.effective_binary_cutoff sol) div
    exact h.elim (Nat.not_lt_of_ge nr) (fun hd => hd div)
  · have mem := (solutions_missing_thirty (n:=N-1) (by omega) div).mp sol
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    omega

end Erdos889.MissingPrimeSieve




/- The sixth-offset constraint for a prime-square successor away from multiples of seven. -/
namespace Erdos889.SquareSeven
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

/-- For a large square successor missing seven at the starting value, only the
sixth offset remains. Every prime divisor there is two, three, or seven. -/
theorem sixth_offset {n p : ℕ} (big : 330 < n) (div : 30 ∣ n)
    (miss : ¬7 ∣ n) (pp : p.Prime) (shape : n+1=p^2) (sol : v_l 1 n=1) :
    n%7=1 ∧ ∀ q : ℕ, q.Prime → q∣n+6 → q=2 ∨ q=3 ∨ q=7 := by
  have hp : 7<p := by
    by_contra! small
    have := Nat.pow_le_pow_left small 2
    omega
  have none : ¬∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧
      q∣p^2+d ∧ s∣p^2+d := by
    rintro ⟨d,q,s,pq,ps,ne,lq,ls,dq,ds⟩
    have h : n+(d+1)=p^2+d := by omega
    exact two_primes (by omega : 0<d+1) pq ps ne lq ls (h ▸ dq) (h ▸ ds) sol
  obtain ⟨_,r,_,b,_,pr,_,_,rr,_,_,_,ob,_,f3⟩ :=
    square_survivor pp (pp.odd_of_ne_two (by omega)) (by omega) none
  have skip : ¬7∣n+4 := by
    intro d
    have seven : Nat.Prime 7 := by decide
    have dp : 7∣r^b := by omega
    have eq := (Nat.prime_dvd_prime_iff_eq seven pr).mp (seven.dvd_of_dvd_pow dp)
    subst r
    have cycle : Nat.ModEq 5 (7^b) (7^(b%4)) := by
      calc
        7^b = 7^(b%4)*(7^4)^(b/4) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
        _ ≡ 7^(b%4)*1^(b/4) [MOD 5] :=
          ((by decide : Nat.ModEq 5 (7^4) 1).pow _).mul_left _
        _ = _ := by simp
    change 7^b%5=7^(b%4)%5 at cycle
    obtain ⟨k,hk⟩ := ob
    have rem : b%4=1 ∨ b%4=3 := by omega
    rcases rem with h|h <;> rw [h] at cycle <;> norm_num at cycle <;> omega
  have pd : ¬7∣p := by
    intro d
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 7) pp).mp d
    omega
  have res : n%7=1 := by
    have sq := Nat.pow_mod p 2 7
    have small := Nat.mod_lt p (by decide : 0<7)
    interval_cases t : p%7 <;> norm_num at sq <;> omega
  refine ⟨res,?_⟩
  intro q pq dq
  by_cases hi : 6<q
  · by_contra no
    exact two_primes (by decide : 0<6) pq (by decide : Nat.Prime 7)
      (by tauto) hi (by decide) dq (by omega) sol
  · have nd5 : ¬5∣n+6 := by omega
    interval_cases q <;> tauto

end Erdos889.SquareSeven


/- Reduction of the sixth offset to the two smooth Pell equations. -/
namespace Erdos889.SquareSeven

private theorem two_prime_shape {z : ℕ} (pos : 0 < z)
    (sup : ∀ q : ℕ, q.Prime → q∣z → q=3 ∨ q=7) : ∃ a b : ℕ, z=3^a*7^b := by
  let a := z.factorization 3
  let m := z/3^a
  have mp : 0 < m := Nat.ordCompl_pos 3 pos.ne'
  have fac : 3^a*m=z := Nat.ordProj_mul_ordCompl_eq_self _ _
  have pure : m=7^m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd mp.ne' (by
    intro q pq dv
    rcases sup q pq (fac ▸ dvd_mul_of_dvd_right dv _) with rfl|h
    · exact (Nat.not_dvd_ordCompl Nat.prime_three pos.ne' dv).elim
    · exact h)
  exact ⟨a,_,by rw [←pure,fac]⟩

private theorem peel (p e : ℕ) : p^e = p^(e%2)*(p^(e/2))^2 := by
  rw [←pow_mul,←pow_add]
  congr 1
  omega

/-- Removing a square from the part supported at three and seven leaves
coefficient six or fourteen. -/
theorem pell_shape {n p : ℕ} (large : 330<n) (div : 30∣n) (hp : p.Prime)
    (shape : n+1=p^2) (sup : ∀ q : ℕ, q.Prime → q∣n+6 → q=2 ∨ q=3 ∨ q=7) :
    ∃ u v : ℕ, (p^2+5=6*(3^u*7^v)^2 ∨ p^2+5=14*(3^u*7^v)^2) := by
  have mod8 : p^2%8=1 := by
    have pp : p≠2 := by rintro rfl; norm_num at shape; omega
    obtain ⟨j,hj⟩ := hp.odd_of_ne_two pp
    have sq := Nat.pow_mod p 2 8
    have lt := Nat.mod_lt p (by decide : 0<8)
    interval_cases t : p%8 <;> norm_num at sq <;> omega
  let z := (n+6)/2
  have zeq : 2*z=n+6 := by dsimp [z]; omega
  obtain ⟨a,b,h⟩ := two_prime_shape (z:=z) (by omega) (by
    intro q pq dv
    rcases sup q pq (zeq ▸ dvd_mul_of_dvd_right dv 2) with rfl|h|h
    · omega
    · exact Or.inl h
    · exact Or.inr h)
  let y := 3^(a/2)*7^(b/2)
  have fac : p^2+5=(2*3^(a%2)*7^(b%2))*y^2 := by
    calc
      p^2+5 = 2*z := by omega
      _ = 2*(3^a*7^b) := by rw [h]
      _ = _ := by rw [peel 3 a,peel 7 b]; dsimp only [y]; ring
  have oddY : Odd y := (Odd.pow (by decide : Odd 3)).mul (Odd.pow (by decide : Odd 7))
  obtain ⟨j,hj⟩ := oddY
  have y8 : y^2%8=1 := by
    have sq := Nat.pow_mod y 2 8
    have lt := Nat.mod_lt y (by decide : 0<8)
    interval_cases t : y%8 <;> norm_num at sq <;> omega
  refine ⟨a/2,b/2,?_⟩
  change p^2+5=6*y^2 ∨ p^2+5=14*y^2
  have ar := Nat.mod_lt a (by decide : 0<2)
  have br := Nat.mod_lt b (by decide : 0<2)
  interval_cases i : a%2 <;> interval_cases j : b%2 <;> norm_num at fac <;> omega

theorem smooth_powers (u v : ℕ) :
    ∀ q : ℕ, q.Prime → q∣3^u*7^v → q=3 ∨ q=7 := by
  intro q pq dv
  rcases pq.dvd_mul.mp dv with d|d
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pq Nat.prime_three).mp (pq.dvd_of_dvd_pow d))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq pq (by decide : Nat.Prime 7)).mp (pq.dvd_of_dvd_pow d))

theorem pell_size {p y D : ℕ} (hp : 7<p) (cap : p^2≤2^2097152) (d : 2≤D)
    (eq : p^2+5=D*y^2) : y<2^2097152 := by
  have small : y≤p := by
    by_contra! notsmall
    have h := Nat.pow_le_pow_left notsmall.le 2
    have h2 := Nat.mul_le_mul_right (y^2) d
    nlinarith
  have : p<p^2 := by nlinarith
  exact lt_of_lt_of_le (lt_of_le_of_lt small this) cap

end Erdos889.SquareSeven

namespace Erdos889.SquareSeven
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

/-- Every further solution with a prime-square successor is a multiple of 210. -/
theorem multiple_of_210_from_pell
    (six : ∀ {p u v : ℕ}, p^2+5=6*(3^u*7^v)^2 → 3^u*7^v<2^2097152 → p≤101)
    (fourteen : ∀ {p u v : ℕ}, p^2+5=14*(3^u*7^v)^2 → 3^u*7^v<2^2097152 → p≤101)
    {n p : ℕ} (big : 330<n) (pp : p.Prime) (shape : n+1=p^2) (sol : v_l 1 n=1) :
    210∣n := by
  obtain ⟨lower,upper,div⟩ := Erdos889.MissingPrimeSieve.further_solution_bounds_thirty big sol
  by_contra missing
  have miss : ¬7∣n := by omega
  have hp : 7<p := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have cap : p^2≤2^2097152 := by
    rw [←shape]
    rw [show (2:ℕ)^21=2097152 by decide] at upper
    exact Nat.succ_le_of_lt upper
  have sf := (sixth_offset big div miss pp shape sol).2
  obtain ⟨u,v,h|h⟩ := pell_shape big div pp shape sf
  · have b := six h (pell_size hp cap (by decide) h)
    have := Nat.pow_le_pow_left b 2
    omega
  · have b := fourteen h (pell_size hp cap (by decide) h)
    have := Nat.pow_le_pow_left b 2
    omega

theorem outside_210_from_divisibility
    (necessary : ∀ {n p : ℕ}, 330<n → p.Prime → n+1=p^2 → v_l 1 n=1 → 210∣n)
    {n p : ℕ} (pp : p.Prime) (shape : n+1=p^2) (miss : ¬210∣n) :
    v_l 1 n=1 ↔ n ∈ [3,8,24,48,120] := by
  have pos : 0<n := by have := Nat.pow_le_pow_left pp.two_le 2; omega
  constructor
  · intro sol
    have low : n≤330 := by by_contra! hi; exact miss (necessary hi pp shape sol)
    have bound : p<19 := by
      by_contra! hi
      have := Nat.pow_le_pow_left hi 2
      omega
    have known := (solutions_through_330 pos low).mp sol
    have tab : ∀ q : Fin 19, q.val.Prime →
        q.val^2-1 ∈ ([1,2,3,4,6,7,8,10,12,15,16,18,22,24,26,30,36,42,46,48,60,70,78,80,96,120,190,222,330] : List ℕ) →
        q.val^2-1 ∈ ([3,8,24,48,120] : List ℕ) := by decide +kernel
    have eq : p^2-1=n := by omega
    have mem := tab ⟨p,bound⟩ pp (eq.symm ▸ known)
    simpa only [eq] using mem
  · intro mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl <;>
      apply (solutions_through_330 (by decide) (by decide)).mpr <;> decide

end Erdos889.SquareSeven


/- Modular period lifting for two quadratic Pell orbits. -/
namespace Erdos889.PellSixSieve

def mul (d : ℕ) (a b : ℕ × ℕ) : ℕ × ℕ :=
  (a.1*b.1+d*a.2*b.2,a.1*b.2+a.2*b.1)

private def norm (m : ℕ) (a : ℕ × ℕ) := (a.1%m,a.2%m)

private theorem assoc (d : ℕ) (a b c : ℕ × ℕ) :
    mul d (mul d a b) c=mul d a (mul d b c) := by
  ext <;> simp only [mul] <;> ring

private theorem comm (d : ℕ) (a b : ℕ × ℕ) : mul d a b=mul d b a := by
  ext <;> simp only [mul] <;> ring

private theorem one_mul (d : ℕ) (a : ℕ × ℕ) : mul d (1,0) a=a := by simp [mul]

private theorem norm_mul (d m : ℕ) (a b : ℕ × ℕ) :
    norm m (mul d (norm m a) (norm m b))=norm m (mul d a b) := by
  ext <;> simp only [mul,norm] <;> simp [Nat.add_mod,Nat.mul_mod]

def power (d : ℕ) (unit : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | n+1 => mul d (power d unit n) unit

private theorem power_add (d : ℕ) (unit : ℕ × ℕ) (i j : ℕ) :
    power d unit (i+j)=mul d (power d unit i) (power d unit j) := by
  induction j with
  | zero => simp only [Nat.add_zero,power,comm d _ (1,0),one_mul]
  | succ j ih => rw [Nat.add_succ,power,ih,assoc,power]

def orbit (d : ℕ) (unit seed : ℕ × ℕ) (n : ℕ) := mul d (power d unit n) seed

theorem orbit_zero (d : ℕ) (unit seed : ℕ × ℕ) : orbit d unit seed 0=seed := one_mul d seed

theorem orbit_succ (d : ℕ) (unit seed : ℕ × ℕ) (n : ℕ) :
    orbit d unit seed (n+1)=mul d unit (orbit d unit seed n) := by
  simp only [orbit,power,comm d (power d unit n) unit,assoc]

private def fastAux (d m : ℕ) (unit : ℕ × ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0,_ => norm m (1,0)
  | k+1,n =>
      let a := fastAux d m unit k (n/2)
      let b := norm m (mul d a a)
      if n%2=0 then b else norm m (mul d b (norm m unit))

private def fast (d m : ℕ) (unit : ℕ × ℕ) (n : ℕ) :=
  fastAux d m unit (n.log2+1) n

private theorem fast_eq (d m : ℕ) (unit : ℕ × ℕ) (n : ℕ) :
    fast d m unit n=norm m (power d unit n) := by
  have sound (k e : ℕ) (he : e<2^k) : fastAux d m unit k e=norm m (power d unit e) := by
    induction k generalizing e with
    | zero =>
      have h : e=0 := by simpa using he
      subst e
      rfl
    | succ k ih =>
      rw [pow_succ] at he
      have h : e/2<2^k := by omega
      rw [fastAux,ih (e/2) h,norm_mul,←power_add]
      split_ifs with ev
      · congr 2
        omega
      · rw [norm_mul,←power]
        congr 2
        omega
  exact sound _ _ Nat.lt_log2_self

private def atMod (d m : ℕ) (unit seed : ℕ × ℕ) (n : ℕ) :=
  (norm m (mul d (fast d m unit n) (norm m seed))).2

private theorem atMod_eq (d m : ℕ) (unit seed : ℕ × ℕ) (n : ℕ) :
    atMod d m unit seed n=(orbit d unit seed n).2%m := by
  rw [atMod,fast_eq,norm_mul]
  rfl

private theorem reduced {d m t : ℕ} {unit seed : ℕ × ℕ}
    (per : fast d m unit t=norm m (1,0)) (n : ℕ) :
    atMod d m unit seed (n%t)=(orbit d unit seed n).2%m := by
  rw [fast_eq] at per
  have step (i : ℕ) : norm m (power d unit (i+t))=norm m (power d unit i) := by
    rw [power_add,←norm_mul,per,norm_mul,comm d _ (1,0),one_mul]
  have steps (i j : ℕ) : norm m (power d unit (i+t*j))=norm m (power d unit i) := by
    induction j with
    | zero => simp
    | succ j ih => rw [Nat.mul_succ,←Nat.add_assoc,step,ih]
  have en := steps (n%t) (n/t)
  rw [Nat.mod_add_div] at en
  rw [atMod,fast_eq,←en,norm_mul]
  rfl

private def Good (d m t : ℕ) (unit seed : ℕ × ℕ) (roots : List ℕ) :=
  ∀ n : ℕ, m∣(orbit d unit seed n).2 → n%t∈roots

private theorem good_one (d : ℕ) (unit seed : ℕ × ℕ) : Good d 1 1 unit seed [0] := by
  intro n _
  simp [Nat.mod_one]

private theorem lift {d m m' t s : ℕ} {unit seed : ℕ × ℕ} {rr next : List ℕ}
    (old : Good d m t unit seed rr) (dvd : m∣m') (ht : 0<t) (hs : 0<s)
    (per : fast d m' unit (t*s)=norm m' (1,0))
    (cells : ∀ r∈rr, ∀ i : Fin s, atMod d m' unit seed (r+t*i.val)=0 → r+t*i.val∈next) :
    Good d m' (t*s) unit seed next := by
  intro n hit
  let a := n%(t*s)
  have small : a<t*s := Nat.mod_lt _ (Nat.mul_pos ht hs)
  have ai : a/t<s := (Nat.div_lt_iff_lt_mul ht).mpr (by simpa only [Nat.mul_comm t s] using small)
  have split := Nat.mod_add_div a t
  have rmem : a%t∈rr := by
    dsimp [a]
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right t s)]
    exact old n (dvd.trans hit)
  have h := cells (a%t) rmem ⟨a/t,ai⟩
  rw [split] at h
  exact h ((reduced per n).trans (Nat.mod_eq_zero_of_dvd hit))

/-- The modular orbit avoids zero up to the effective index cutoff. -/
theorem avoid_6_1_3 {n : ℕ} :
    ¬3^2∣(orbit 6 (5,2) (1,1) n).2 := by
  have h0 : Good 6 3 6 (5,2) (1,1) [2, 5] :=
    lift (t:=1) (s:=6) (good_one 6 (5,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 9 6 (5,2) (1,1) [] :=
    lift (t:=6) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h1 n dvd
  exact List.not_mem_nil mem

/-- The modular orbit avoids zero up to the effective index cutoff. -/
theorem avoid_6_1_7 {n : ℕ} :
    ¬7^2∣(orbit 6 (5,2) (1,1) n).2 := by
  have h0 : Good 6 7 8 (5,2) (1,1) [1, 5] :=
    lift (t:=1) (s:=8) (good_one 6 (5,2) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 49 8 (5,2) (1,1) [] :=
    lift (t:=8) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h1 n dvd
  exact List.not_mem_nil mem

/-- The modular orbit avoids zero up to the effective index cutoff. -/
theorem avoid_6_7_3 {n : ℕ} :
    ¬3^2∣(orbit 6 (5,2) (7,3) n).2 := by
  have h0 : Good 6 3 6 (5,2) (7,3) [0, 3] :=
    lift (t:=1) (s:=6) (good_one 6 (5,2) (7,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 9 6 (5,2) (7,3) [] :=
    lift (t:=6) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h1 n dvd
  exact List.not_mem_nil mem

/-- The modular orbit avoids zero up to the effective index cutoff. -/
theorem avoid_6_7_7 {n : ℕ} :
    ¬7^2∣(orbit 6 (5,2) (7,3) n).2 := by
  have h0 : Good 6 7 8 (5,2) (7,3) [2, 6] :=
    lift (t:=1) (s:=8) (good_one 6 (5,2) (7,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 6 49 8 (5,2) (7,3) [] :=
    lift (t:=8) (s:=1) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h1 n dvd
  exact List.not_mem_nil mem

/-- The modular orbit avoids zero up to the effective index cutoff. -/
theorem avoid_14_3_3 {n : ℕ} (hn : n<2097152) :
    ¬3^15∣(orbit 14 (15,4) (3,1) n).2 := by
  have h0 : Good 14 3 4 (15,4) (3,1) [1, 3] :=
    lift (t:=1) (s:=4) (good_one 14 (15,4) (3,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 14 9 12 (15,4) (3,1) [1, 7] :=
    lift (t:=4) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 14 27 36 (15,4) (3,1) [1, 19] :=
    lift (t:=12) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 14 81 108 (15,4) (3,1) [37, 91] :=
    lift (t:=36) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 14 243 324 (15,4) (3,1) [91, 253] :=
    lift (t:=108) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 14 729 972 (15,4) (3,1) [253, 739] :=
    lift (t:=324) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 14 2187 2916 (15,4) (3,1) [739, 2197] :=
    lift (t:=972) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 14 6561 8748 (15,4) (3,1) [739, 5113] :=
    lift (t:=2916) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 14 19683 26244 (15,4) (3,1) [9487, 22609] :=
    lift (t:=8748) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 14 59049 78732 (15,4) (3,1) [22609, 61975] :=
    lift (t:=26244) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 14 177147 236196 (15,4) (3,1) [22609, 140707] :=
    lift (t:=78732) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 14 531441 708588 (15,4) (3,1) [258805, 613099] :=
    lift (t:=236196) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 14 1594323 2125764 (15,4) (3,1) [613099, 1675981] :=
    lift (t:=708588) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 14 4782969 6377292 (15,4) (3,1) [1675981, 4864627] :=
    lift (t:=2125764) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 14 14348907 19131876 (15,4) (3,1) [4864627, 14430565] :=
    lift (t:=6377292) (s:=3) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h14 n dvd
  rw [Nat.mod_eq_of_lt (by omega)] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  omega

/-- The modular orbit avoids zero up to the effective index cutoff. -/
theorem avoid_14_3_7 {n : ℕ} (hn : n<2097152) :
    ¬7^9∣(orbit 14 (15,4) (3,1) n).2 := by
  have h0 : Good 14 7 7 (15,4) (3,1) [4] :=
    lift (t:=1) (s:=7) (good_one 14 (15,4) (3,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 14 49 49 (15,4) (3,1) [32] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 14 343 343 (15,4) (3,1) [32] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 14 2401 2401 (15,4) (3,1) [1747] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 14 16807 16807 (15,4) (3,1) [1747] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 14 117649 117649 (15,4) (3,1) [18554] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 14 823543 823543 (15,4) (3,1) [724448] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 14 5764801 5764801 (15,4) (3,1) [724448] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 14 40353607 40353607 (15,4) (3,1) [6489249] :=
    lift (t:=5764801) (s:=7) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h8 n dvd
  rw [Nat.mod_eq_of_lt (by omega)] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  omega

/-- The modular orbit avoids zero up to the effective index cutoff. -/
theorem avoid_14_11_3 {n : ℕ} (hn : n<2097152) :
    ¬3^15∣(orbit 14 (15,4) (11,3) n).2 := by
  have h0 : Good 14 3 4 (15,4) (11,3) [0, 2] :=
    lift (t:=1) (s:=4) (good_one 14 (15,4) (11,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 14 9 12 (15,4) (11,3) [4, 10] :=
    lift (t:=4) (s:=3) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 14 27 36 (15,4) (11,3) [16, 34] :=
    lift (t:=12) (s:=3) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 14 81 108 (15,4) (11,3) [16, 70] :=
    lift (t:=36) (s:=3) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 14 243 324 (15,4) (11,3) [70, 232] :=
    lift (t:=108) (s:=3) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 14 729 972 (15,4) (11,3) [232, 718] :=
    lift (t:=324) (s:=3) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 14 2187 2916 (15,4) (11,3) [718, 2176] :=
    lift (t:=972) (s:=3) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 14 6561 8748 (15,4) (11,3) [3634, 8008] :=
    lift (t:=2916) (s:=3) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 14 19683 26244 (15,4) (11,3) [3634, 16756] :=
    lift (t:=8748) (s:=3) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 14 59049 78732 (15,4) (11,3) [16756, 56122] :=
    lift (t:=26244) (s:=3) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 14 177147 236196 (15,4) (11,3) [95488, 213586] :=
    lift (t:=78732) (s:=3) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 14 531441 708588 (15,4) (11,3) [95488, 449782] :=
    lift (t:=236196) (s:=3) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 14 1594323 2125764 (15,4) (11,3) [449782, 1512664] :=
    lift (t:=708588) (s:=3) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 14 4782969 6377292 (15,4) (11,3) [1512664, 4701310] :=
    lift (t:=2125764) (s:=3) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 14 14348907 19131876 (15,4) (11,3) [4701310, 14267248] :=
    lift (t:=6377292) (s:=3) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h14 n dvd
  rw [Nat.mod_eq_of_lt (by omega)] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  omega

/-- The modular orbit avoids zero up to the effective index cutoff. -/
theorem avoid_14_11_7 {n : ℕ} (hn : n<2097152) :
    ¬7^8∣(orbit 14 (15,4) (11,3) n).2 := by
  have h0 : Good 14 7 7 (15,4) (11,3) [2] :=
    lift (t:=1) (s:=7) (good_one 14 (15,4) (11,3)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 14 49 49 (15,4) (11,3) [16] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 14 343 343 (15,4) (11,3) [310] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 14 2401 2401 (15,4) (11,3) [653] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 14 16807 16807 (15,4) (11,3) [15059] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 14 117649 117649 (15,4) (11,3) [99094] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 14 823543 823543 (15,4) (11,3) [99094] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 14 5764801 5764801 (15,4) (11,3) [5040352] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h7 n dvd
  rw [Nat.mod_eq_of_lt (by omega)] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  omega

end Erdos889.PellSixSieve

namespace Erdos889.PellSixSieve

private theorem six_orbits (x y : ℕ) (normEq : x^2+5=6*y^2) :
    ∃ n, orbit 6 (5,2) (1,1) n=(x,y) ∨ orbit 6 (5,2) (7,3) n=(x,y) := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<5
    · have xl : x<12 := by
        by_contra! hx
        nlinarith [Nat.pow_le_pow_left hx 2,Nat.pow_le_pow_left (show y≤4 by omega) 2]
      have tab : ∀ a : Fin 12, ∀ b : Fin 5, a.val^2+5=6*b.val^2 →
          (1,1)=(a.val,b.val) ∨ (7,3)=(a.val,b.val) := by decide +kernel
      exact ⟨0,by simpa only [orbit_zero] using tab ⟨x,xl⟩ ⟨y,small⟩ normEq⟩
    have hy : 5≤y := by omega
    have leA : 12*y≤5*x := by
      by_contra! bad
      nlinarith [Nat.pow_le_pow_left bad.le 2,Nat.pow_le_pow_left hy 2]
    have leB : 2*x≤5*y := by
      by_contra! bad
      nlinarith [Nat.pow_le_pow_left bad.le 2]
    have bound : 4*y<2*x := by
      by_contra! bad
      nlinarith [Nat.pow_le_pow_left bad 2,Nat.pow_le_pow_left hy 2]
    let a := 5*x-12*y
    let b := 5*y-2*x
    have ea : a+12*y=5*x := Nat.sub_add_cancel leA
    have eb : b+2*x=5*y := Nat.sub_add_cancel leB
    have smallB : b<y := by omega
    have rx : x=5*a+12*b := by omega
    have ry : y=2*a+5*b := by omega
    have eq : a^2+5=6*b^2 := by
      rw [rx,ry] at normEq
      nlinarith [normEq]
    obtain ⟨n,hn|hn⟩ := ih b smallB a eq
    · refine ⟨n+1,Or.inl ?_⟩
      rw [orbit_succ,hn]
      ext <;> simp only [mul] <;> omega
    · refine ⟨n+1,Or.inr ?_⟩
      rw [orbit_succ,hn]
      ext <;> simp only [mul] <;> omega

private theorem smooth_small (y : ℕ) (smooth : ∀ p : ℕ, p.Prime → p∣y → p=3 ∨ p=7)
    (a : ¬9∣y) (b : ¬49∣y) : y=1 ∨ y=3 ∨ y=7 ∨ y=21 := by
  induction y using induction_on_primes with
  | zero => omega
  | one => tauto
  | prime_mul p t pp ih =>
    have t := ih (fun q pq dq => smooth q pq (dvd_mul_of_dvd_right dq p))
      (fun h => a (dvd_mul_of_dvd_right h p)) (fun h => b (dvd_mul_of_dvd_right h p))
    rcases smooth p pp (dvd_mul_right p _) with rfl|rfl <;> omega

/-- The complete x-coordinate list for the negative norm with smooth y, without an index cutoff. -/
theorem pell_six_smooth {x y : ℕ} (eq : x^2+5=6*y^2)
    (smooth : ∀ p : ℕ, p.Prime → p∣y → p=3 ∨ p=7) : x=1 ∨ x=7 ∨ x=17 := by
  obtain ⟨n,hn|hn⟩ := six_orbits x y eq
  all_goals
    have divs : ¬9∣y ∧ ¬49∣y := by
      first
      | simpa only [hn,Nat.reducePow] using And.intro (avoid_6_1_3 (n:=n)) (avoid_6_1_7 (n:=n))
      | simpa only [hn,Nat.reducePow] using And.intro (avoid_6_7_3 (n:=n)) (avoid_6_7_7 (n:=n))
    have cases := smooth_small y smooth divs.1 divs.2
    have bound : x≤52 := by
      by_contra! bad
      have sy : y≤21 := by omega
      nlinarith [Nat.pow_le_pow_left sy 2,Nat.pow_le_pow_left bad.le 2]
    have tab : ∀ a : Fin 53, ∀ b : Fin 22, a.val^2+5=6*b.val^2 →
        (b.val=1 ∨ b.val=3 ∨ b.val=7 ∨ b.val=21) →
        a.val=1 ∨ a.val=7 ∨ a.val=17 := by decide +kernel
    exact tab ⟨x,by omega⟩ ⟨y,by omega⟩ eq cases

end Erdos889.PellSixSieve


/- Descent and bounded smooth coordinates on the positive Pell conic of norm minus five. -/

namespace Erdos889.PellFourteen

def term (s : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => s
  | k+1 => let z := term s k; (15*z.1+56*z.2,4*z.1+15*z.2)

theorem descent {x y : ℕ} (eqn : x^2+5=14*y^2) :
    ∃ s : ℕ × ℕ, (s=(3,1) ∨ s=(11,3)) ∧
      ∃ k : ℕ, term s k=(x,y) ∧ 8^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<9
    · have hx : x<30 := by
        by_contra! ge
        have := Nat.pow_le_pow_left ge 2
        have := Nat.pow_le_pow_left (show y≤8 by omega) 2
        nlinarith
      have cases' : ∀ i : Fin 30, ∀ j : Fin 9, i.val^2+5=14*j.val^2 →
          (i.val=3 ∧ j.val=1) ∨ (i.val=11 ∧ j.val=3) := by decide +kernel
      rcases cases' ⟨x,hx⟩ ⟨y,small⟩ eqn with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨(3,1),Or.inl rfl,0,rfl,by decide⟩
      · exact ⟨(11,3),Or.inr rfl,0,rfl,by decide⟩
    have low : 9^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 56*y≤15*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 4*x≤15*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 14*y<4*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 15*x-56*y
    let v := 15*y-4*x
    have hu : u+56*y=15*x := Nat.sub_add_cancel ax
    have hv : v+4*x=15*y := Nat.sub_add_cancel ay
    have ev : u^2+5=14*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    have smaller : v<y := by omega
    obtain ⟨s,hs,k,hk,lim⟩ := ih v smaller ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · simp only [term,hk]
      exact Prod.ext (by dsimp; omega) (by dsimp; omega)
    · rw [pow_succ]
      omega

/-- Once the two modular valuation bounds hold on the orbit, only three smooth
solutions remain. Both the descent and the finite prefix are checked in the kernel. -/
theorem smooth_from_orbit_bounds
    (v3 : ∀ s : ℕ × ℕ, (s=(3,1) ∨ s=(11,3)) → ∀ k : ℕ, k<2097152 → ¬3^40∣(term s k).2)
    (v7 : ∀ s : ℕ × ℕ, (s=(3,1) ∨ s=(11,3)) → ∀ k : ℕ, k<2097152 → ¬7^40∣(term s k).2)
    {x y a b : ℕ} (eqn : x^2+5=14*y^2) (size : y<2^2097152) (form : y=3^a*7^b) :
    (x=3 ∧ y=1) ∨ (x=11 ∧ y=3) ∨ (x=101 ∧ y=27) := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent eqn
  have small : k<2097152 := by
    by_contra! le
    have h := Nat.pow_le_pow_right (by decide : 0<2) le
    have h' := Nat.pow_le_pow_left (by decide : 2≤8) k
    omega
  have no3 := v3 s hs k small
  have no7 := v7 s hs k small
  rw [hk] at no3 no7
  change ¬3^40∣y at no3
  change ¬7^40∣y at no7
  have ha : a≤40 := by
    by_contra! big
    exact no3 (form ▸ dvd_mul_of_dvd_left (pow_dvd_pow 3 big.le) _)
  have hb : b≤40 := by
    by_contra! big
    exact no7 (form ▸ dvd_mul_of_dvd_right (pow_dvd_pow 7 big.le) _)
  have yd : y∣21^40 := by
    rw [form,show (21:ℕ)=3*7 by decide,mul_pow]
    exact Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow 7 hb)
  have lk : k<64 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<8) ge
    have := Nat.le_of_dvd (by decide : 0<21^40) yd
    have : 21^40<8^64 := by decide
    omega
  have tab : ∀ e : Bool, ∀ i : Fin 64,
      let z := term (if e then (3,1) else (11,3)) i.val
      z.2∣21^40 → (z.1=3 ∧ z.2=1) ∨ (z.1=11 ∧ z.2=3) ∨ (z.1=101 ∧ z.2=27) := by
    decide +kernel
  rcases hs with rfl|rfl
  · have t := tab true ⟨k,lk⟩
    simp only [if_true,hk] at t
    exact t yd
  · have t := tab false ⟨k,lk⟩
    simp only [Bool.false_eq_true,if_false,hk] at t
    exact t yd

end Erdos889.PellFourteen


namespace Erdos889.PellFourteen
open Erdos889.PellSixSieve

private theorem term_eq_orbit (s : ℕ × ℕ) (k : ℕ) :
    term s k = orbit 14 (15,4) s k := by
  induction k with
  | zero => exact (orbit_zero 14 (15,4) s).symm
  | succ k ih =>
    rw [term,ih,orbit_succ]
    apply Prod.ext
    · rfl
    · exact Nat.add_comm _ _

/-- The exact positive smooth-coordinate solutions up to the effective binary
bound for exceptional starting values. No upper bound on the exponents is necessary. -/
theorem smooth_coordinates {x y a b : ℕ} (eqn : x^2+5=14*y^2)
    (size : y<2^2097152) (form : y=3^a*7^b) :
    (x=3 ∧ y=1) ∨ (x=11 ∧ y=3) ∨ (x=101 ∧ y=27) := by
  apply smooth_from_orbit_bounds _ _ eqn size form
  · intro s hs k hk
    rw [term_eq_orbit]
    rcases hs with rfl|rfl
    · exact fun h => avoid_14_3_3 hk ((pow_dvd_pow 3 (by decide : 15≤40)).trans h)
    · exact fun h => avoid_14_11_3 hk ((pow_dvd_pow 3 (by decide : 15≤40)).trans h)
  · intro s hs k hk
    rw [term_eq_orbit]
    rcases hs with rfl|rfl
    · exact fun h => avoid_14_3_7 hk ((pow_dvd_pow 7 (by decide : 9≤40)).trans h)
    · exact fun h => avoid_14_11_7 hk ((pow_dvd_pow 7 (by decide : 8≤40)).trans h)

end Erdos889.PellFourteen


namespace Erdos889.SquareSeven
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

/-- The prime-square branch above the known list requires every prime through seven. -/
theorem square_multiple_of_210 {n p : ℕ} (big : 330<n)
    (pp : p.Prime) (shape : n+1=p^2) (sol : v_l 1 n=1) : 210∣n := by
  refine multiple_of_210_from_pell ?_ ?_ big pp shape sol
  · intro p u v eq _
    rcases Erdos889.PellSixSieve.pell_six_smooth eq (smooth_powers u v) with h|h|h <;> rw [h] <;> decide
  · intro p u v eq size
    rcases Erdos889.PellFourteen.smooth_coordinates eq size (a:=u) (b:=v) rfl with
      ⟨h,_⟩|⟨h,_⟩|⟨h,_⟩ <;> rw [h] <;> decide

/-- Exact positive solutions with a prime-square successor outside multiples of 210. -/
theorem prime_square_outside_210 {n p : ℕ} (pp : p.Prime) (shape : n+1=p^2) (miss : ¬210∣n) :
    v_l 1 n=1 ↔ n ∈ [3,8,24,48,120] :=
  outside_210_from_divisibility (fun hi pr eq sol => square_multiple_of_210 hi pr eq sol) pp shape miss

private theorem round_square {N cap : ℕ} (hi : N-1<cap) (dv : 210∣N-1) :
    N≤1+210*((cap-1)/210) := by omega

/-- A square above the rounded cutoff, or with a predecessor outside 210ℕ
above the last known such predecessor, has a two-prime witness. -/
theorem square_witness {p : ℕ} (pp : p.Prime) (big : 121<p^2)
    (bound : 1+210*((2^(2^21)-1)/210)<p^2 ∨ ¬210∣p^2-1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p^2+d ∧ s∣p^2+d := by
  by_contra none
  have sol := Erdos889.Missing.predecessor_solution_of_missing (by omega : 1<p^2) none
  by_cases div : 210∣p^2-1
  · have lim := round_square (Erdos889.effective_binary_cutoff sol) div
    exact bound.elim (Nat.not_lt_of_ge lim) (fun missing => missing div)
  · have eq : p^2-1+1=p^2 := by omega
    have mem := (prime_square_outside_210 pp eq div).mp sol
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    omega

end Erdos889.SquareSeven




/- Third and ninth offsets for a prime square with eleven missing. -/
namespace Erdos889.ElevenSmall
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private def unit : Pell.Solution₁ (3:ℤ) := Pell.Solution₁.mk 2 1 (by decide)

private theorem fundamental : Pell.IsFundamental unit := by
  refine ⟨by decide,by decide,?_⟩
  intro b hb
  change 2≤b.x
  omega

private theorem unit_growth (i : ℕ) : (2:ℤ)^i≤(unit^i).x := by
  induction i with
  | zero => simp
  | succ i ih =>
    have nonneg : 0≤(unit^i).y := by
      cases i with
      | zero => simp
      | succ i => exact (Pell.Solution₁.y_pow_succ_pos fundamental.x_pos fundamental.2.1 i).le
    rw [pow_succ (2:ℤ),pow_succ unit,Pell.Solution₁.x_mul]
    change _≤(unit^i).x*2+3*((unit^i).y*1)
    omega

private theorem exp_large (i : ℕ) (hi : 40 ≤ i) : 3*(i*3135)^2 < 2^i := by
  induction i,hi using Nat.le_induction with
  | base => decide
  | succ i hi ih =>
    rw [pow_succ 2 i]
    nlinarith [Nat.mul_le_mul_left i hi]

/-- For norm -2 and support {3,11}, the original coordinate is small with no height assumption. -/
theorem third_pell {x y : ℕ} (hx : 0<x) (hy : 0<y) (eqn : x^2+2=3*y^2)
    (sup : ∀ q : ℕ, q.Prime → q∣y → q=3 ∨ q=11) : x≤250800 := by
  have e : (x:ℤ)^2+2=3*(y:ℤ)^2 := by exact_mod_cast eqn
  let z : Pell.Solution₁ (3:ℤ) := Pell.Solution₁.mk ((x:ℤ)^2+1) ((x:ℤ)*y)
    (by linear_combination (x:ℤ)^2*e)
  have sx : z.x=(x:ℤ)^2+1 := rfl
  have sy : z.y=(x:ℤ)*y := rfl
  obtain ⟨i, powz⟩ := fundamental.eq_pow_of_nonneg (a:=z) (by rw [sx]; positivity) (by rw [sy]; positivity)
  have imag : (unit^i).y.natAbs=x*y := by rw [←powz,sy,Int.natAbs_mul]; rfl
  have ip : 0 < i := by
    by_contra! low
    have zero : i=0 := by omega
    rw [zero,pow_zero,Pell.Solution₁.y_one] at imag
    simp [hx.ne',hy.ne'] at imag
  have h3 : (unit^3).y.natAbs=15 := by decide +kernel
  have h5 : (unit^5).y.natAbs=209 := by decide +kernel
  have divy : y∣i*3135 := by
    apply (Nat.factorization_le_iff_dvd hy.ne' (Nat.mul_pos ip (by decide)).ne').mp
    intro q
    by_cases pq : q.Prime
    · by_cases dy : q∣y
      · have dv : y∣(unit^i).y.natAbs := by rw [imag]; exact dvd_mul_left _ _
        have nz : (unit^i).y.natAbs≠0 := by rw [imag]; positivity
        have sub := (Nat.factorization_le_iff_dvd hy.ne' nz).mpr dv q
        obtain ⟨h,hh,hd,hm⟩ : ∃ h : ℕ, 0<h ∧ q∣(unit^h).y.natAbs ∧ (unit^h).y.natAbs∣3135 := by
          rcases sup q pq dy with rfl|rfl
          · exact ⟨3,by decide,by rw [h3]; decide,by rw [h3]; decide⟩
          · exact ⟨5,by decide,by rw [h5]; decide,by rw [h5]; decide⟩
        have le := Erdos889.PellValuation.pell_factorization_y_le (D:=3) unit pq ip hh fundamental.x_pos fundamental.2.1 hd
        have nh : (unit^h).y.natAbs≠0 := by intro z; rw [z] at hm; norm_num at hm
        have lifted := Nat.mul_dvd_mul_left i hm
        exact sub.trans (le.trans ((Nat.factorization_le_iff_dvd (Nat.mul_ne_zero ip.ne' nh)
          (Nat.mul_pos ip (by decide)).ne').mpr lifted q))
      · simp [Nat.factorization_eq_zero_of_not_dvd dy]
    · simp [Nat.factorization_eq_zero_of_not_prime _ pq]
  have small := Nat.le_of_dvd (Nat.mul_pos ip (by decide)) divy
  have growth := unit_growth i
  rw [←powz,sx] at growth
  have g : 2^i≤x^2+1 := by exact_mod_cast growth
  have il : i<40 := by
    by_contra! bad
    have := exp_large i bad
    nlinarith [Nat.pow_le_pow_left small 2]
  have small2 : y≤125400 := by omega
  nlinarith [Nat.pow_le_pow_left small2 2]

/-- The norm-minus-two equation at the third offset has exactly three possible positive first coordinates. -/
theorem third_shape_exact {x u v : ℕ} (hx : 0<x) (e : x^2+2=3*(3^u*11^v)^2) :
    x=1 ∨ x=5 ∨ x=19 := by
  have small := third_pell hx (by positivity) e (by
    intro q pq d
    rcases pq.dvd_mul.mp d with dv|dv
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pq Nat.prime_three).mp (pq.dvd_of_dvd_pow dv))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq pq (by decide : Nat.Prime 11)).mp (pq.dvd_of_dvd_pow dv)))
  have yb : 3^u*11^v≤250800 := by
    nlinarith [Nat.pow_le_pow_left small 2]
  have au : u<12 := by
    by_contra! hi
    have := Nat.pow_le_pow_right (by decide : 0<3) hi
    have := Nat.le_mul_of_pos_right (3^u) (by positivity : 0<11^v)
    omega
  have bv : v<6 := by
    by_contra! hi
    have := Nat.pow_le_pow_right (by decide : 0<11) hi
    have := Nat.le_mul_of_pos_left (11^v) (by positivity : 0<3^u)
    omega
  have table : ∀ a : Fin 12, ∀ b : Fin 6,
      let t := 3*(3^a.val*11^b.val)^2-2
      t.sqrt^2=t → t.sqrt=1 ∨ t.sqrt=5 ∨ t.sqrt=19 := by decide +kernel
  have t := table ⟨u,au⟩ ⟨v,bv⟩
  dsimp only at t
  rw [show 3*(3^u*11^v)^2-2=x^2 by omega,Nat.sqrt_eq'] at t
  exact t rfl

private theorem bare {n k : ℕ} (sol : v_l 1 n=1) (div : 210∣n)
    (kh : k=3 ∨ k=9) (hit : 11∣n+k) : ∃ a b : ℕ, n+k=3^a*11^b := by
  have pos : 0<n+k := by rcases kh with rfl|rfl <;> omega
  let z := n+k
  let a := z.factorization 3
  let m := z/3^a
  have mp : 0 < m := Nat.ordCompl_pos 3 pos.ne'
  have fac : 3^a*m=z := Nat.ordProj_mul_ordCompl_eq_self _ _
  have pure : m=11^m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd mp.ne' (by
    intro q pq dv
    have d : q∣z := fac ▸ dvd_mul_of_dvd_right dv _
    change q∣n+k at d
    by_contra ne
    have nd3 : q≠3 := by rintro rfl; exact Nat.not_dvd_ordCompl Nat.prime_three pos.ne' dv
    have high : k<q := by
      by_contra! low
      have bound : q≤9 := by rcases kh with rfl|rfl <;> omega
      have opts : q=2 ∨ q=3 ∨ q=5 ∨ q=7 := by interval_cases q <;> tauto
      rcases kh with rfl|rfl <;> rcases opts with rfl|rfl|rfl|rfl <;> omega
    exact two_primes (by omega : 0<k) pq (by decide : Nat.Prime 11) ne high (by omega) d hit sol)
  exact ⟨a,_,by change z=_; rw [←pure,fac]⟩

private theorem peel (p e : ℕ) : p^e=p^(e%2)*(p^(e/2))^2 := by
  rw [←pow_mul,←pow_add]
  congr 1
  omega

private theorem cycle {m x t : ℕ} (h : Nat.ModEq m (x^t) 1) (e : ℕ) :
    Nat.ModEq m (x^e) (x^(e%t)) := by
  calc
    x^e=x^(e%t)*(x^t)^(e/t) := by rw [←pow_mul,←pow_add,Nat.mod_add_div]
    _ ≡ x^(e%t)*1^(e/t) [MOD m] := (h.pow _).mul_left _
    _ = _ := by simp

set_option maxHeartbeats 1200000 in
private theorem shape_at {n k p : ℕ} (sol : v_l 1 n=1) (div : 210∣n)
    (kh : k=3 ∨ k=9) (hit : 11∣n+k) (shape : n+1=p^2) :
    ∃ u v : ℕ, (k=3 ∧ p^2+2=3*(3^u*11^v)^2) ∨ (k=9 ∧ p^2+8=(3^u*11^v)^2) := by
  obtain ⟨a,b,ab⟩ := bare sol div kh hit
  let y := 3^(a/2)*11^(b/2)
  have f : n+k=3^(a%2)*11^(b%2)*y^2 := by
    rw [ab,peel 3 a,peel 11 b]; dsimp only [y]; ring
  have m5 := (cycle (by decide : Nat.ModEq 5 (3^4) 1) a).mul (cycle (by decide : Nat.ModEq 5 (11^1) 1) b)
  change (3^a*11^b)%5=(3^(a%4)*11^(b%1))%5 at m5
  rw [←ab,Nat.mod_one,pow_zero,mul_one] at m5
  have smod : p^2%8=1 := by
    have sq := Nat.pow_mod p 2 8
    have s := Nat.mod_lt p (by decide : 0<8)
    interval_cases t : p%8 <;> norm_num at sq <;> omega
  have m8 := (cycle (by decide : Nat.ModEq 8 (3^2) 1) a).mul (cycle (by decide : Nat.ModEq 8 (11^2) 1) b)
  change (3^a*11^b)%8=(3^(a%2)*11^(b%2))%8 at m8
  rw [←ab] at m8
  have al := Nat.mod_lt a (by decide : 0<4)
  have bl := Nat.mod_lt b (by decide : 0<2)
  have ar : a%2=a%4%2 := by omega
  rw [ar] at m8 f
  refine ⟨a/2,b/2,?_⟩
  change (k=3 ∧ p^2+2=3*y^2) ∨ (k=9 ∧ p^2+8=y^2)
  rcases kh with rfl|rfl <;> interval_cases s : a%4 <;> interval_cases t : b%2 <;>
    norm_num at m5 m8 f <;> omega

/-- Neither the third nor the ninth offset can contain eleven for a remaining large square. -/
theorem no_three_nine {n p : ℕ} (huge : 1000000000000000000<n) (div : 210∣n)
    (shape : n+1=p^2) (sol : v_l 1 n=1) (k : ℕ) (kh : k=3 ∨ k=9) : ¬11∣n+k := by
  intro hit
  obtain ⟨u,v,⟨_,e⟩|⟨_,e⟩⟩ := shape_at sol div kh hit shape
  · have xp : 0<p := by
      by_contra! z
      have h : p=0 := by omega
      rw [h] at shape
      omega
    have b := third_pell xp (by positivity) e (by
      intro q pq d
      rcases pq.dvd_mul.mp d with dv|dv
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq pq Nat.prime_three).mp (pq.dvd_of_dvd_pow dv))
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq pq (by decide : Nat.Prime 11)).mp (pq.dvd_of_dvd_pow dv)))
    have := Nat.pow_le_pow_left b 2
    omega
  · let y := 3^u*11^v
    change p^2+8=y^2 at e
    have lt : p<y := by by_contra! low; have := Nat.pow_le_pow_left low 2; omega
    have next := Nat.pow_le_pow_left (show p+1≤y by omega) 2
    have pb : p≤4 := by nlinarith
    have := Nat.pow_le_pow_left pb 2
    omega
end Erdos889.ElevenSmall

namespace Erdos889.PellSixSieve
theorem seven_1_7 {n : ℕ} (hn : n<2097152) :
    ¬7^8∣(orbit 7 (8,3) (1,1) n).2 := by
  have h0 : Good 7 7 7 (8,3) (1,1) [2] :=
    lift (t:=1) (s:=7) (good_one 7 (8,3) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 49 49 (8,3) (1,1) [9] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 343 343 (8,3) (1,1) [156] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 2401 2401 (8,3) (1,1) [499] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 16807 16807 (8,3) (1,1) [499] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 117649 117649 (8,3) (1,1) [67727] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 7 823543 823543 (8,3) (1,1) [538323] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 7 5764801 5764801 (8,3) (1,1) [4656038] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h7 n dvd
  rw [Nat.mod_eq_of_lt (by omega)] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  omega

theorem seven_1_11 {n : ℕ} (hn : n<2097152) :
    ¬11^7∣(orbit 7 (8,3) (1,1) n).2 := by
  have h0 : Good 7 11 12 (8,3) (1,1) [1, 7] :=
    lift (t:=1) (s:=12) (good_one 7 (8,3) (1,1)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 121 132 (8,3) (1,1) [7, 73] :=
    lift (t:=12) (s:=11) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 1331 1452 (8,3) (1,1) [205, 931] :=
    lift (t:=132) (s:=11) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 14641 15972 (8,3) (1,1) [3109, 11095] :=
    lift (t:=1452) (s:=11) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 161051 175692 (8,3) (1,1) [82969, 170815] :=
    lift (t:=15972) (s:=11) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 1771561 1932612 (8,3) (1,1) [170815, 1137121] :=
    lift (t:=175692) (s:=11) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 7 19487171 21258732 (8,3) (1,1) [4036039, 14665405] :=
    lift (t:=1932612) (s:=11) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h6 n dvd
  rw [Nat.mod_eq_of_lt (by omega)] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  omega

theorem seven_13_7 {n : ℕ} (hn : n<2097152) :
    ¬7^9∣(orbit 7 (8,3) (13,5) n).2 := by
  have h0 : Good 7 7 7 (8,3) (13,5) [4] :=
    lift (t:=1) (s:=7) (good_one 7 (8,3) (13,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 49 49 (8,3) (13,5) [39] :=
    lift (t:=7) (s:=7) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 343 343 (8,3) (13,5) [186] :=
    lift (t:=49) (s:=7) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 2401 2401 (8,3) (13,5) [1901] :=
    lift (t:=343) (s:=7) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 16807 16807 (8,3) (13,5) [16307] :=
    lift (t:=2401) (s:=7) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 117649 117649 (8,3) (13,5) [49921] :=
    lift (t:=16807) (s:=7) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 7 823543 823543 (8,3) (13,5) [285219] :=
    lift (t:=117649) (s:=7) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 7 5764801 5764801 (8,3) (13,5) [1108762] :=
    lift (t:=823543) (s:=7) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 7 40353607 40353607 (8,3) (13,5) [6873563] :=
    lift (t:=5764801) (s:=7) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h8 n dvd
  rw [Nat.mod_eq_of_lt (by omega)] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  omega

theorem seven_13_11 {n : ℕ} (hn : n<2097152) :
    ¬11^7∣(orbit 7 (8,3) (13,5) n).2 := by
  have h0 : Good 7 11 12 (8,3) (13,5) [4, 10] :=
    lift (t:=1) (s:=12) (good_one 7 (8,3) (13,5)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 7 121 132 (8,3) (13,5) [58, 124] :=
    lift (t:=12) (s:=11) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 7 1331 1452 (8,3) (13,5) [520, 1246] :=
    lift (t:=132) (s:=11) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 7 14641 15972 (8,3) (13,5) [4876, 12862] :=
    lift (t:=1452) (s:=11) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 7 161051 175692 (8,3) (13,5) [4876, 92722] :=
    lift (t:=15972) (s:=11) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 7 1771561 1932612 (8,3) (13,5) [795490, 1761796] :=
    lift (t:=175692) (s:=11) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 7 19487171 21258732 (8,3) (13,5) [6593326, 17222692] :=
    lift (t:=1932612) (s:=11) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro dvd
  have mem := h6 n dvd
  rw [Nat.mod_eq_of_lt (by omega)] at mem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  omega

end Erdos889.PellSixSieve
namespace Erdos889.ElevenSeven


def term (s : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => s
  | k+1 => let z := term s k; (8*z.1+21*z.2,3*z.1+8*z.2)

theorem descent {x y : ℕ} (eqn : x^2+6=7*y^2) :
    ∃ s : ℕ × ℕ, (s=(1,1) ∨ s=(13,5)) ∧
      ∃ k : ℕ, term s k=(x,y) ∧ 8^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<8
    · have hx : x<30 := by
        by_contra! ge
        have := Nat.pow_le_pow_left ge 2
        have := Nat.pow_le_pow_left (show y≤7 by omega) 2
        nlinarith
      have cases' : ∀ i : Fin 30, ∀ j : Fin 8, i.val^2+6=7*j.val^2 →
          (i.val=1 ∧ j.val=1) ∨ (i.val=13 ∧ j.val=5) := by decide +kernel
      rcases cases' ⟨x,hx⟩ ⟨y,small⟩ eqn with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨(1,1),Or.inl rfl,0,rfl,by decide⟩
      · exact ⟨(13,5),Or.inr rfl,0,rfl,by decide⟩
    have low : 8^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 21*y≤8*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 3*x≤8*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : 7*y<3*x := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad 2
      nlinarith only [this,low,eqn]
    let u := 8*x-21*y
    let v := 8*y-3*x
    have hu : u+21*y=8*x := Nat.sub_add_cancel ax
    have hv : v+3*x=8*y := Nat.sub_add_cancel ay
    have ev : u^2+6=7*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    have smaller : v<y := by omega
    obtain ⟨s,hs,k,hk,lim⟩ := ih v smaller ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · simp only [term,hk]
      exact Prod.ext (by dsimp; omega) (by dsimp; omega)
    · rw [pow_succ]
      omega


open Erdos889.PellSixSieve

private theorem coords (s : ℕ × ℕ) (k : ℕ) : term s k = orbit 7 (8,3) s k := by
  induction k with
  | zero => exact (orbit_zero 7 (8,3) s).symm
  | succ k ih =>
    rw [term,ih,orbit_succ]
    apply Prod.ext
    · rfl
    · exact Nat.add_comm _ _

/-- All solutions in the effective range to the norm equation arising at the seventh offset. -/
theorem smooth {p u v : ℕ} (eq : p^2+6=7*(7^u*11^v)^2) (size : 7^u*11^v<2^2097152) :
    p=1 ∨ p=29 := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent eq
  have low : k<2097152 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<2) ge
    have := Nat.pow_le_pow_left (by decide : 2≤8) k
    omega
  have avoid : ¬7^9∣(term s k).2 ∧ ¬11^7∣(term s k).2 := by
    rw [coords]
    rcases hs with rfl|rfl
    · exact ⟨fun d => seven_1_7 low ((pow_dvd_pow 7 (by decide : 8≤9)).trans d),seven_1_11 low⟩
    · exact ⟨seven_13_7 low,seven_13_11 low⟩
  rw [hk] at avoid
  have uu : u≤9 := by
    by_contra! hi
    exact avoid.1 (dvd_mul_of_dvd_left (pow_dvd_pow 7 hi.le) _)
  have vv : v≤9 := by
    by_contra! hi
    exact avoid.2 (dvd_mul_of_dvd_right (pow_dvd_pow 11 (by omega : 7≤v)) _)
  have dv : 7^u*11^v ∣ 77^9 := by
    rw [show (77:ℕ)=7*11 by decide,mul_pow]
    exact Nat.mul_dvd_mul (pow_dvd_pow 7 uu) (pow_dvd_pow 11 vv)
  have k32 : k<32 := by
    by_contra! hi
    have := Nat.pow_le_pow_right (by decide : 0<8) hi
    have := Nat.le_of_dvd (by decide : 0<77^9) dv
    have : 77^9<8^32 := by decide
    omega
  have table : ∀ e : Bool, ∀ i : Fin 32,
      let z := term (if e then (1,1) else (13,5)) i.val
      z.2∣77^9 → z.1=1 ∨ z.1=29 := by decide +kernel
  rcases hs with rfl|rfl
  · have t := table true ⟨k,k32⟩
    simp only [if_true,hk] at t
    exact t dv
  · have t := table false ⟨k,k32⟩
    simp only [Bool.false_eq_true,if_false,hk] at t
    exact t dv
end Erdos889.ElevenSeven

namespace Erdos889.ElevenSeven
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

private theorem peel (p e : ℕ) : p^e=p^(e%2)*(p^(e/2))^2 := by
  rw [←pow_mul,←pow_add]
  congr 1
  omega

private theorem coefficient {x y a b : ℕ} (sx : x%8=1) (sy : y%8=1)
    (eq : x+6=(7^(a%2)*11^(b%2))*y) : x+6=7*y := by
  have ar := Nat.mod_lt a (by decide : 0<2)
  have br := Nat.mod_lt b (by decide : 0<2)
  interval_cases i : a%2 <;> interval_cases j : b%2 <;> norm_num at eq <;> omega

set_option maxHeartbeats 2000000 in
theorem reject_seven {n p : ℕ} (huge : 1000000000000000000<n) (div : 210∣n)
    (shape : n+1=p^2) (sol : Erdos889.v_l 1 n=1) (eleven : 11∣n+7) : False := by
  have two : ¬2∣n+7 := by omega
  have three : ¬3∣n+7 := by omega
  have five : ¬5∣n+7 := by omega
  have sup (q : ℕ) (pq : q.Prime) (dq : q∣n+7) : q=7 ∨ q=11 := by
    by_cases small : q≤7
    · interval_cases q <;> tauto
    · by_contra ne
      exact two_primes (by decide : 0<7) pq (by decide : Nat.Prime 11) (by tauto)
        (by omega) (by decide) dq eleven sol
  have pos : n+7≠0 := by omega
  let a := (n+7).factorization 7
  let m := (n+7)/7^a
  have pp : Nat.Prime 7 := by decide
  have fac : 7^a*m=n+7 := Nat.ordProj_mul_ordCompl_eq_self _ _
  have pure : m=11^m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd
    (Nat.ordCompl_pos 7 pos).ne' (by
      intro q pq dq
      exact (sup q pq (fac ▸ dvd_mul_of_dvd_right dq _)).resolve_left
        (by rintro rfl; exact Nat.not_dvd_ordCompl pp pos dq))
  let b := m.primeFactorsList.length
  have eq : p^2+6=7^a*11^b := by change p^2+6=7^a*11^m.primeFactorsList.length; rw [←pure,fac]; omega
  let y := 7^(a/2)*11^(b/2)
  have split : p^2+6=(7^(a%2)*11^(b%2))*y^2 := by
    rw [eq,peel 7 a,peel 11 b]; dsimp only [y]; ring
  have oddP : ¬2∣p := by
    intro d
    have d2 : 2∣p^2 := dvd_pow d (by decide)
    omega
  have modP : p^2%8=1 := by
    have sq := Nat.pow_mod p 2 8
    have lt := Nat.mod_lt p (by decide : 0<8)
    interval_cases t : p%8 <;> norm_num at sq <;> omega
  have oddY : Odd y := (Odd.pow (by decide : Odd 7)).mul (Odd.pow (by decide : Odd 11))
  obtain ⟨z,hz⟩ := oddY
  have modY : y^2%8=1 := by
    have sq := Nat.pow_mod y 2 8
    have lt := Nat.mod_lt y (by decide : 0<8)
    interval_cases t : y%8 <;> norm_num at sq <;> omega
  have normEq : p^2+6=7*y^2 := coefficient modP modY split
  have ysmall : y≤p := by
    by_contra! hi
    have := Nat.pow_le_pow_left hi.le 2
    nlinarith
  have hp : 30<p := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have ppow : p<p^2 := by nlinarith
  have cap := Erdos889.effective_binary_cutoff sol
  rw [show (2:ℕ)^21=2097152 by decide] at cap
  have bound : p^2≤2^2097152 := by
    rw [← shape]
    exact Nat.succ_le_of_lt cap
  have size : y<2^2097152 := (lt_of_le_of_lt ysmall ppow).trans_le bound
  rcases smooth normEq size with h|h <;> omega
end Erdos889.ElevenSeven

namespace Erdos889.PellSixSieve
theorem eight_avoid_1_2 {k : ℕ} (small : k<2097152) :
    ¬2^24∣(orbit 2 (3,2) (1,2) k).2 := by
  have h0 : Good 2 2 1 (3,2) (1,2) [0] :=
    lift (t:=1) (s:=1) (good_one 2 (3,2) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 4 2 (3,2) (1,2) [1] :=
    lift (t:=1) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 8 4 (3,2) (1,2) [1] :=
    lift (t:=2) (s:=2) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 16 8 (3,2) (1,2) [5] :=
    lift (t:=4) (s:=2) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 32 16 (3,2) (1,2) [13] :=
    lift (t:=8) (s:=2) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 64 32 (3,2) (1,2) [29] :=
    lift (t:=16) (s:=2) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 2 128 64 (3,2) (1,2) [61] :=
    lift (t:=32) (s:=2) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 2 256 128 (3,2) (1,2) [61] :=
    lift (t:=64) (s:=2) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 2 512 256 (3,2) (1,2) [189] :=
    lift (t:=128) (s:=2) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 2 1024 512 (3,2) (1,2) [445] :=
    lift (t:=256) (s:=2) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 2 2048 1024 (3,2) (1,2) [957] :=
    lift (t:=512) (s:=2) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 2 4096 2048 (3,2) (1,2) [957] :=
    lift (t:=1024) (s:=2) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 2 8192 4096 (3,2) (1,2) [3005] :=
    lift (t:=2048) (s:=2) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 2 16384 8192 (3,2) (1,2) [3005] :=
    lift (t:=4096) (s:=2) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 2 32768 16384 (3,2) (1,2) [3005] :=
    lift (t:=8192) (s:=2) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h15 : Good 2 65536 32768 (3,2) (1,2) [3005] :=
    lift (t:=16384) (s:=2) (h14) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h16 : Good 2 131072 65536 (3,2) (1,2) [35773] :=
    lift (t:=32768) (s:=2) (h15) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h17 : Good 2 262144 131072 (3,2) (1,2) [101309] :=
    lift (t:=65536) (s:=2) (h16) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h18 : Good 2 524288 262144 (3,2) (1,2) [232381] :=
    lift (t:=131072) (s:=2) (h17) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h19 : Good 2 1048576 524288 (3,2) (1,2) [232381] :=
    lift (t:=262144) (s:=2) (h18) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h20 : Good 2 2097152 1048576 (3,2) (1,2) [232381] :=
    lift (t:=524288) (s:=2) (h19) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h21 : Good 2 4194304 2097152 (3,2) (1,2) [1280957] :=
    lift (t:=1048576) (s:=2) (h20) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h22 : Good 2 8388608 4194304 (3,2) (1,2) [1280957] :=
    lift (t:=2097152) (s:=2) (h21) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h23 : Good 2 16777216 8388608 (3,2) (1,2) [5475261] :=
    lift (t:=4194304) (s:=2) (h22) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro d
  have h := h23 k d
  rw [Nat.mod_eq_of_lt (by omega)] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  omega

theorem eight_avoid_1_11 {k : ℕ} (small : k<2097152) :
    ¬11^7∣(orbit 2 (3,2) (1,2) k).2 := by
  have h0 : Good 2 11 12 (3,2) (1,2) [4, 10] :=
    lift (t:=1) (s:=12) (good_one 2 (3,2) (1,2)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 121 132 (3,2) (1,2) [10, 76] :=
    lift (t:=12) (s:=11) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 1331 1452 (3,2) (1,2) [472, 1198] :=
    lift (t:=132) (s:=11) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 14641 15972 (3,2) (1,2) [472, 8458] :=
    lift (t:=1452) (s:=11) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 161051 175692 (3,2) (1,2) [80332, 168178] :=
    lift (t:=15972) (s:=11) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 1771561 1932612 (3,2) (1,2) [783100, 1749406] :=
    lift (t:=175692) (s:=11) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 2 19487171 21258732 (3,2) (1,2) [3682018, 14311384] :=
    lift (t:=1932612) (s:=11) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro d
  have h := h6 k d
  rw [Nat.mod_eq_of_lt (by omega)] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  omega

theorem eight_avoid_5_2 {k : ℕ} (small : k<2097152) :
    ¬2^23∣(orbit 2 (3,2) (5,4) k).2 := by
  have h0 : Good 2 2 1 (3,2) (5,4) [0] :=
    lift (t:=1) (s:=1) (good_one 2 (3,2) (5,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 4 2 (3,2) (5,4) [0] :=
    lift (t:=1) (s:=2) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 8 4 (3,2) (5,4) [2] :=
    lift (t:=2) (s:=2) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 16 8 (3,2) (5,4) [2] :=
    lift (t:=4) (s:=2) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 32 16 (3,2) (5,4) [2] :=
    lift (t:=8) (s:=2) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 64 32 (3,2) (5,4) [2] :=
    lift (t:=16) (s:=2) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 2 128 64 (3,2) (5,4) [2] :=
    lift (t:=32) (s:=2) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h7 : Good 2 256 128 (3,2) (5,4) [66] :=
    lift (t:=64) (s:=2) (h6) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h8 : Good 2 512 256 (3,2) (5,4) [66] :=
    lift (t:=128) (s:=2) (h7) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h9 : Good 2 1024 512 (3,2) (5,4) [66] :=
    lift (t:=256) (s:=2) (h8) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h10 : Good 2 2048 1024 (3,2) (5,4) [66] :=
    lift (t:=512) (s:=2) (h9) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h11 : Good 2 4096 2048 (3,2) (5,4) [1090] :=
    lift (t:=1024) (s:=2) (h10) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h12 : Good 2 8192 4096 (3,2) (5,4) [1090] :=
    lift (t:=2048) (s:=2) (h11) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h13 : Good 2 16384 8192 (3,2) (5,4) [5186] :=
    lift (t:=4096) (s:=2) (h12) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h14 : Good 2 32768 16384 (3,2) (5,4) [13378] :=
    lift (t:=8192) (s:=2) (h13) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h15 : Good 2 65536 32768 (3,2) (5,4) [29762] :=
    lift (t:=16384) (s:=2) (h14) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h16 : Good 2 131072 65536 (3,2) (5,4) [29762] :=
    lift (t:=32768) (s:=2) (h15) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h17 : Good 2 262144 131072 (3,2) (5,4) [29762] :=
    lift (t:=65536) (s:=2) (h16) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h18 : Good 2 524288 262144 (3,2) (5,4) [29762] :=
    lift (t:=131072) (s:=2) (h17) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h19 : Good 2 1048576 524288 (3,2) (5,4) [291906] :=
    lift (t:=262144) (s:=2) (h18) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h20 : Good 2 2097152 1048576 (3,2) (5,4) [816194] :=
    lift (t:=524288) (s:=2) (h19) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h21 : Good 2 4194304 2097152 (3,2) (5,4) [816194] :=
    lift (t:=1048576) (s:=2) (h20) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h22 : Good 2 8388608 4194304 (3,2) (5,4) [2913346] :=
    lift (t:=2097152) (s:=2) (h21) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro d
  have h := h22 k d
  rw [Nat.mod_eq_of_lt (by omega)] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  omega

theorem eight_avoid_5_11 {k : ℕ} (small : k<2097152) :
    ¬11^7∣(orbit 2 (3,2) (5,4) k).2 := by
  have h0 : Good 2 11 12 (3,2) (5,4) [1, 7] :=
    lift (t:=1) (s:=12) (good_one 2 (3,2) (5,4)) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h1 : Good 2 121 132 (3,2) (5,4) [55, 121] :=
    lift (t:=12) (s:=11) (h0) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h2 : Good 2 1331 1452 (3,2) (5,4) [253, 979] :=
    lift (t:=132) (s:=11) (h1) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h3 : Good 2 14641 15972 (3,2) (5,4) [7513, 15499] :=
    lift (t:=1452) (s:=11) (h2) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h4 : Good 2 161051 175692 (3,2) (5,4) [7513, 95359] :=
    lift (t:=15972) (s:=11) (h3) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h5 : Good 2 1771561 1932612 (3,2) (5,4) [183205, 1149511] :=
    lift (t:=175692) (s:=11) (h4) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  have h6 : Good 2 19487171 21258732 (3,2) (5,4) [6947347, 17576713] :=
    lift (t:=1932612) (s:=11) (h5) (by decide) (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  intro d
  have h := h6 k d
  rw [Nat.mod_eq_of_lt (by omega)] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  omega

end Erdos889.PellSixSieve

namespace Erdos889.ElevenEight
open Erdos889.PellSixSieve
private def term (s : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => s
  | k+1 => let z := term s k; (3*z.1+4*z.2,2*z.1+3*z.2)

private theorem term_eq_orbit (s : ℕ × ℕ) (k : ℕ) :
    term s k=orbit 2 (3,2) s k := by
  induction k with
  | zero => exact (orbit_zero 2 (3,2) s).symm
  | succ k ih =>
    rw [term,ih,orbit_succ]
    apply Prod.ext
    · rfl
    · exact Nat.add_comm _ _

private theorem descent {x y : ℕ} (eqn : x^2+7=2*y^2) :
    ∃ s : ℕ × ℕ, (s=(1,2) ∨ s=(5,4)) ∧ ∃ k : ℕ, term s k=(x,y) ∧ 3^k≤y := by
  induction y using Nat.strong_induction_on generalizing x with
  | h y ih =>
    by_cases small : y<6
    · have hx : x<9 := by
        by_contra! ge
        have := Nat.pow_le_pow_left ge 2
        have := Nat.pow_le_pow_left (show y≤5 by omega) 2
        nlinarith
      have tab : ∀ i : Fin 9, ∀ j : Fin 6, i.val^2+7=2*j.val^2 →
          (i.val=1 ∧ j.val=2) ∨ (i.val=5 ∧ j.val=4) := by decide +kernel
      rcases tab ⟨x,hx⟩ ⟨y,small⟩ eqn with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact ⟨(1,2),Or.inl rfl,0,rfl,by decide⟩
      · exact ⟨(5,4),Or.inr rfl,0,rfl,by decide⟩
    have low : 6^2≤y^2 := Nat.pow_le_pow_left (by omega) 2
    have ax : 4*y≤3*x := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have ay : 2*x≤3*y := by
      apply (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp
      nlinarith only [low,eqn]
    have gy : y<x := by
      by_contra! h
      have := Nat.pow_le_pow_left h 2
      nlinarith only [low,eqn,this]
    let u := 3*x-4*y
    let v := 3*y-2*x
    have hu : u+4*y=3*x := Nat.sub_add_cancel ax
    have hv : v+2*x=3*y := Nat.sub_add_cancel ay
    have ev : u^2+7=2*v^2 := by
      dsimp only [u,v]
      zify [ax,ay] at eqn ⊢
      nlinarith only [eqn]
    obtain ⟨s,hs,k,hk,hlim⟩ := ih v (by omega) ev
    refine ⟨s,hs,k+1,?_,?_⟩
    · simp only [term,hk]
      exact Prod.ext (by dsimp; omega) (by dsimp; omega)
    · rw [pow_succ]
      omega

/-- Smooth coordinates in the two Pell orbits within the effective interval. -/
theorem eight_smooth_coordinates {x y a b : ℕ} (eqn : x^2+7=2*y^2)
    (size : y<2^2097152) (form : y=2^a*11^b) :
    (x=1 ∧ y=2) ∨ (x=5 ∧ y=4) ∨ (x=11 ∧ y=8) ∨ (x=31 ∧ y=22) ∨ (x=181 ∧ y=128) := by
  obtain ⟨s,hs,k,hk,lim⟩ := descent eqn
  have small : k<2097152 := by
    by_contra! ge
    have h₁ := Nat.pow_le_pow_right (by decide : 0<2) ge
    have h₂ := Nat.pow_le_pow_left (by decide : 2≤3) k
    omega
  have noTwo : ¬2^24∣y := by
    have h := congrArg Prod.snd hk
    simp only [term_eq_orbit] at h
    rcases hs with rfl|rfl
    · exact h ▸ eight_avoid_1_2 small
    · exact h ▸ (fun dv => eight_avoid_5_2 small ((pow_dvd_pow 2 (by decide : 23≤24)).trans dv))
  have noEleven : ¬11^7∣y := by
    have h := congrArg Prod.snd hk
    simp only [term_eq_orbit] at h
    rcases hs with rfl|rfl
    · exact h ▸ eight_avoid_1_11 small
    · exact h ▸ eight_avoid_5_11 small
  have ha : a≤24 := by
    by_contra! ge
    exact noTwo (form ▸ dvd_mul_of_dvd_left (pow_dvd_pow 2 ge.le) _)
  have hb : b≤7 := by
    by_contra! ge
    exact noEleven (form ▸ dvd_mul_of_dvd_right (pow_dvd_pow 11 ge.le) _)
  have bound : y∣2^24*11^7 := form ▸ Nat.mul_dvd_mul (pow_dvd_pow 2 ha) (pow_dvd_pow 11 hb)
  have lk : k<40 := by
    by_contra! ge
    have := Nat.pow_le_pow_right (by decide : 0<3) ge
    have := Nat.le_of_dvd (by decide : 0<2^24*11^7) bound
    have : 2^24*11^7<3^40 := by decide
    omega
  have tab : ∀ e : Bool, ∀ i : Fin 40,
      let z := term (if e then (1,2) else (5,4)) i.val
      z.2∣2^24*11^7 → (z.1=1 ∧ z.2=2) ∨ (z.1=5 ∧ z.2=4) ∨ (z.1=11 ∧ z.2=8) ∨
        (z.1=31 ∧ z.2=22) ∨ (z.1=181 ∧ z.2=128) := by decide +kernel
  rcases hs with rfl|rfl
  · have t := tab true ⟨k,lk⟩
    simp only [if_true,hk] at t
    exact t bound
  · have t := tab false ⟨k,lk⟩
    simp only [Bool.false_eq_true,if_false,hk] at t
    exact t bound

private theorem two_eleven_shape {z : ℕ} (pos : 0<z)
    (sup : ∀ q : ℕ, q.Prime → q∣z → q=2 ∨ q=11) : ∃ a b : ℕ, z=2^a*11^b := by
  let a := z.factorization 2
  let m := z/2^a
  have mp : 0 < m := Nat.ordCompl_pos 2 pos.ne'
  have fac : 2^a*m=z := Nat.ordProj_mul_ordCompl_eq_self _ _
  have pure : m=11^m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd mp.ne' (by
    intro q pq dv
    rcases sup q pq (fac ▸ dvd_mul_of_dvd_right dv _) with rfl|h
    · exact (Nat.not_dvd_ordCompl Nat.prime_two pos.ne' dv).elim
    · exact h)
  exact ⟨a,_,by rw [←pure,fac]⟩

private theorem split_pow (p e : ℕ) : p^e=p^(e%2)*(p^(e/2))^2 := by
  rw [←pow_mul,←pow_add]
  congr 1
  omega

open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

/-- The smooth eighth offset cannot coexist with a square successor in the effective range. -/
theorem reject_eight_shape {n p a b : ℕ} (large : 1000000000000000000<n)
    (cap : n<2^2097152) (div : 210∣n) (shape : n+1=p^2) (f : n+8=2^a*11^b) : False := by
  let y := 2^(a/2)*11^(b/2)
  have fac : n+8=(2^(a%2)*11^(b%2))*y^2 := by
    calc
      n+8=2^a*11^b := f
      _=_ := by rw [split_pow 2 a,split_pow 11 b]; dsimp only [y]; ring
  have r3 : y^2%3=0 ∨ y^2%3=1 := by
    have sq := Nat.pow_mod y 2 3
    have lt := Nat.mod_lt y (by decide : 0<3)
    interval_cases t : y%3 <;> norm_num at sq <;> omega
  have r5 : y^2%5=0 ∨ y^2%5=1 ∨ y^2%5=4 := by
    have sq := Nat.pow_mod y 2 5
    have lt := Nat.mod_lt y (by decide : 0<5)
    interval_cases t : y%5 <;> norm_num at sq <;> omega
  have eq : p^2+7=2*y^2 := by
    have ar := Nat.mod_lt a (by decide : 0<2)
    have br := Nat.mod_lt b (by decide : 0<2)
    interval_cases i : a%2 <;> interval_cases j : b%2 <;> norm_num at fac <;> omega
  have size : y<2^2097152 := by
    have yp : y≤p := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad.le 2
      nlinarith only [eq,this,shape,large]
    have pn : p≤n := by
      by_contra! bad
      have := Nat.pow_le_pow_left bad.le 2
      nlinarith only [shape,this,large]
    exact lt_of_le_of_lt (yp.trans pn) cap
  have coords := eight_smooth_coordinates eq size (a:=a/2) (b:=b/2) rfl
  rcases coords with ⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩|⟨h,_⟩ <;> rw [h] at shape <;> norm_num at shape <;> omega

/-- The eighth offset cannot be divisible by eleven in a further exceptional square predecessor. -/
theorem reject_eight {n p : ℕ} (large : 1000000000000000000<n) (div : 210∣n)
    (shape : n+1=p^2) (sol : v_l 1 n=1) (eleven : 11∣n+8) : False := by
  have sup (q : ℕ) (pq : q.Prime) (dv : q∣n+8) : q=2 ∨ q=11 := by
    by_cases big : 8<q
    · by_contra ne
      exact two_primes (by decide : 0<8) pq (by decide : Nat.Prime 11) (by tauto) big (by decide) dv eleven sol
    · have n3 : ¬3∣n+8 := by omega
      have n5 : ¬5∣n+8 := by omega
      have n7 : ¬7∣n+8 := by omega
      interval_cases q <;> tauto
  obtain ⟨a,b,f⟩ := two_eleven_shape (by omega : 0<n+8) sup
  have cap := Erdos889.effective_binary_cutoff sol
  rw [show (2:ℕ)^21=2097152 by decide] at cap
  exact reject_eight_shape large cap div shape f

end Erdos889.ElevenEight

namespace Erdos889.SquareEleven
open OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2

set_option maxHeartbeats 4000000 in
/-- Beyond 330, a prime-square successor forces divisibility by every prime through
eleven. The odd square also supplies the factor of eight. -/
theorem square_multiple_of_9240 {n p : ℕ} (big : 330<n) (pp : p.Prime)
    (shape : n+1=p^2) (sol : v_l 1 n=1) : 9240∣n := by
  have div := Erdos889.SquareSeven.square_multiple_of_210 big pp shape sol
  have huge := (Erdos889.MissingPrimeSieve.further_solution_bounds_thirty big sol).1
  have gt : 11<p := by
    by_contra! low
    have := Nat.pow_le_pow_left low 2
    omega
  have not11 : ¬11∣p := by
    intro d
    have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 11) pp).mp d
    omega
  have eleven : 11∣n := by
    by_contra missing
    have alts : 11∣n+3 ∨ 11∣n+7 ∨ 11∣n+8 ∨ 11∣n+9 := by
      have sq := Nat.pow_mod p 2 11
      have sm := Nat.mod_lt p (by decide : 0<11)
      interval_cases t : p%11 <;> norm_num at sq <;> omega
    rcases alts with h|h|h|h
    · exact Erdos889.ElevenSmall.no_three_nine huge div shape sol 3 (Or.inl rfl) h
    · exact Erdos889.ElevenSeven.reject_seven huge div shape sol h
    · exact Erdos889.ElevenEight.reject_eight huge div shape sol h
    · exact Erdos889.ElevenSmall.no_three_nine huge div shape sol 9 (Or.inr rfl) h
  have eight : 8∣n := by
    obtain ⟨j,hj⟩ := pp.odd_of_ne_two (by omega)
    have sq := Nat.pow_mod p 2 8
    have sm := Nat.mod_lt p (by decide : 0<8)
    interval_cases t : p%8 <;> norm_num at sq <;> omega
  omega

/-- All solutions with a prime-square successor outside the multiples of 9240. -/
theorem prime_square_outside_9240 {n p : ℕ} (pp : p.Prime)
    (shape : n+1=p^2) (miss : ¬9240∣n) : v_l 1 n=1 ↔ n ∈ [3,8,24,48,120] := by
  by_cases large : 330<n
  · constructor
    · intro sol
      exact (miss (square_multiple_of_9240 large pp shape sol)).elim
    · intro mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      omega
  · have old : ¬210∣n := by
      intro d
      have l : p<19 := by
        by_contra! ge
        have := Nat.pow_le_pow_left ge 2
        omega
      have pos := Nat.pow_le_pow_left pp.two_le 2
      have h : n=210 := by omega
      interval_cases p <;> norm_num at shape <;> omega
    exact Erdos889.SquareSeven.prime_square_outside_210 pp shape old

private theorem round_square {N cap : ℕ} (hi : N-1<cap) (dv : 9240∣N-1) :
    N≤1+9240*((cap-1)/9240) := by omega

theorem square_witness {p : ℕ} (pp : p.Prime) (big : 121<p^2)
    (bound : 1+9240*((2^(2^21)-1)/9240)<p^2 ∨ ¬9240∣p^2-1) :
    ∃ d q s : ℕ, q.Prime ∧ s.Prime ∧ q≠s ∧ d+1<q ∧ d+1<s ∧ q∣p^2+d ∧ s∣p^2+d := by
  by_contra none
  have sol := Erdos889.Missing.predecessor_solution_of_missing (by omega : 1<p^2) none
  by_cases div : 9240∣p^2-1
  · have lim := round_square (Erdos889.effective_binary_cutoff sol) div
    exact bound.elim (Nat.not_lt_of_ge lim) (fun missing => missing div)
  · have eq : p^2-1+1=p^2 := by omega
    have mem := (prime_square_outside_9240 pp eq div).mp sol
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    omega
end Erdos889.SquareEleven

theorem OMA.solution : OMA.R_Erdos889_erdos_889_variants_v1_eq_1_finite_R2_H2_R1.H1 := by
  refine ⟨0,max 121 (1+9240*((2^(2^21)-1)/9240)),?_⟩
  intro p pp _ high _ _ _ _
  exact Erdos889.SquareEleven.square_witness pp
    (lt_of_le_of_lt (Nat.le_max_left _ _) high)
    (Or.inl (lt_of_le_of_lt (Nat.le_max_right _ _) high))
