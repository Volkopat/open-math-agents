import OMAReductions.R_OeisA256544_conjecture_R1
import Mathlib

/-!
# A fixed ternary-form route for odd squarefree triangular floors

Credit: @MattGaiser. All proof code in this file is independently written.
The parent odd-squarefree step is @marcusbuffett's merged reduction PR #3440.
The original conjecture is Zhi-Wei Sun's OEIS A256544, April1 2015,
and Conjecture1.1(ii) of arXiv1504.01608, DOI10.48550/arXiv.1504.01608 (preprint).

H1 proves every required prime-power local congruence for the fixed form
x^2+(x+m*y)^2+(m*z)^2. local_data_proved proves H1 below, using Mathlib's
finite-field two-square theorem and elementary lifting arguments.

H2 is OPEN: a uniform local-to-global bound for the positive ternary form
x^2+(x+m*y)^2+(m*z)^2, of Gram determinant8*m^4 and level4*m^2.
It is a stronger sufficient condition than the floor conjecture. Almost all
remaining difficulty is concentrated in H2. No analytic estimate is invoked
as a proof of that bound. General theta-series estimates such as Waibel,
Uniform bounds for norms of theta series and arithmetic applications,
Math.Proc.Camb.Phil.Soc.173(2022),669-691, DOI10.1017/S0305004122000081
(refereed), do not yield the required range by the naive specialization.

The new local proof is classical mathematics; no mathematical novelty is claimed.
-/

namespace OMA.R_OeisA256544_conjecture_R1_H1_R1

lemma twice_tri (x : ℕ) : 2 * Nat.triangular x = x * (x + 1) := by
  have h : x * (x + 1) % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      simp [Nat.mul_mod, Nat.add_mod, hx]
  unfold Nat.triangular
  omega

lemma eight_tri_add_one (x : ℕ) : 8 * Nat.triangular x + 1 = (2*x+1)^2 := by
  nlinarith [twice_tri x]

lemma carry_identity (m x y z : ℕ) :
    m * (Nat.triangular x / m + Nat.triangular y / m + Nat.triangular z / m) +
      (Nat.triangular x % m + Nat.triangular y % m + Nat.triangular z % m) = Nat.triangular x + Nat.triangular y + Nat.triangular z := by
  have hx := Nat.mod_add_div (Nat.triangular x) m
  have hy := Nat.mod_add_div (Nat.triangular y) m
  have hz := Nat.mod_add_div (Nat.triangular z) m
  simp only [Nat.mul_add]
  omega

lemma floors_eq_of_residue_sum {m n r x y z : ℕ} (hm : 0 < m)
    (hsum : Nat.triangular x + Nat.triangular y + Nat.triangular z = m*n+r)
    (hres : Nat.triangular x % m + Nat.triangular y % m + Nat.triangular z % m = r) :
    n = Nat.triangular x / m + Nat.triangular y / m + Nat.triangular z / m := by
  have h := carry_identity m x y z
  rw [hres, hsum] at h
  exact Nat.eq_of_mul_eq_mul_left hm (Nat.add_right_cancel h).symm

lemma odd_int_tri (a : ℤ) (ha : Odd a) :
    ∃ x : ℕ, 2*x+1 = a.natAbs ∧ a^2 = 8*(Nat.triangular x : ℤ)+1 := by
  have habs : Odd a.natAbs := ha.natAbs
  let x := a.natAbs / 2
  have hx : 2*x+1 = a.natAbs := by
    have h := Nat.odd_iff.mp habs
    dsimp [x]
    omega
  refine ⟨x, hx, ?_⟩
  have hs : ((a.natAbs : ℤ)^2) = a^2 := by simp [sq_abs]
  have hcast : (a.natAbs : ℤ) = 2*(x : ℤ)+1 := by exact_mod_cast hx.symm
  rw [hcast] at hs
  have ht : 8*(Nat.triangular x : ℤ)+1 = (2*(x : ℤ)+1)^2 := by
    exact_mod_cast eight_tri_add_one x
  exact hs.symm.trans ht.symm

lemma odd_square_mod_eight (g : ℕ) (hg : Odd g) : g^2%8=1 := by
  obtain ⟨k,hk⟩ := hg
  rw [hk,← eight_tri_add_one]
  omega

lemma square_mod_four (a : ℤ) : a^2%4=0 ∨ a^2%4=1 := by
  have test : ∀ t : Fin 4, ((t.val : ℤ)^2)%4=0 ∨ ((t.val : ℤ)^2)%4=1 := by decide
  have h0 : 0≤a%4 := Int.emod_nonneg _ (by decide)
  have h1 : a%4<4 := Int.emod_lt_of_pos _ (by decide)
  have hcast : ((a%4).toNat : ℤ)=a%4 := by omega
  have h := test ⟨(a%4).toNat,by omega⟩
  simp only at h
  rw [hcast,(Int.mod_modEq a 4).pow 2] at h
  exact h

lemma odd_of_three_square_norm (a b c : ℤ) (hn : (a^2+b^2+c^2)%4=3) :
    Odd a ∧ Odd b ∧ Odd c := by
  have ha := square_mod_four a
  have hb := square_mod_four b
  have hc := square_mod_four c
  have hA : a^2%4=1 := by rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases hc with hc|hc <;> omega
  have hB : b^2%4=1 := by rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases hc with hc|hc <;> omega
  have hC : c^2%4=1 := by rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases hc with hc|hc <;> omega
  refine ⟨?_,?_,?_⟩
  · exact (Int.odd_pow' (by decide : (2:ℕ)≠0)).mp (Int.odd_iff.mpr (by omega))
  · exact (Int.odd_pow' (by decide : (2:ℕ)≠0)).mp (Int.odd_iff.mpr (by omega))
  · exact (Int.odd_pow' (by decide : (2:ℕ)≠0)).mp (Int.odd_iff.mpr (by omega))

lemma modEq_cancel_coprime (m c a b : ℤ) (hc : IsCoprime m c)
    (h : Int.ModEq m (c*a) (c*b)) : Int.ModEq m a b := by
  apply Int.modEq_iff_dvd.mpr
  exact hc.dvd_of_dvd_mul_left (by simpa only [mul_sub] using Int.modEq_iff_dvd.mp h)

lemma floors_from_square_residues (m n ρ : ℕ) (hm : 0< m) (ho : Odd m) (hρ : ρ< m)
    (a b c : ℤ) (hn : a^2+b^2+c^2=8*((m:ℤ)*n+ρ)+3)
    (ha : Int.ModEq m (a^2) 1) (hb : Int.ModEq m (b^2) 1)
    (hc : Int.ModEq m (c^2) (8*(ρ:ℤ)+1)) :
    ∃ x y z : ℕ, n=Nat.triangular x/m+Nat.triangular y/m+Nat.triangular z/m := by
  have h4 : (a^2+b^2+c^2)%4=3 := by rw [hn]; omega
  obtain ⟨hoa,hob,hoc⟩ := odd_of_three_square_norm a b c h4
  obtain ⟨x,hxroot,hxsq⟩ := odd_int_tri a hoa
  obtain ⟨y,hyroot,hysq⟩ := odd_int_tri b hob
  obtain ⟨z,hzroot,hzsq⟩ := odd_int_tri c hoc
  have hco2 : IsCoprime (m:ℤ) 2 := Int.isCoprime_two_right.mpr (by exact_mod_cast ho)
  have hco8 : IsCoprime (m:ℤ) 8 := by simpa using (hco2.pow_right (n:=3))
  rw [hxsq] at ha
  rw [hysq] at hb
  rw [hzsq] at hc
  have hx8 : Int.ModEq m (8*(Nat.triangular x:ℤ)) (8*0) := by
    simpa using Int.ModEq.add_right_cancel' 1 ha
  have hy8 : Int.ModEq m (8*(Nat.triangular y:ℤ)) (8*0) := by
    simpa using Int.ModEq.add_right_cancel' 1 hb
  have hz8 : Int.ModEq m (8*(Nat.triangular z:ℤ)) (8*(ρ:ℤ)) :=
    Int.ModEq.add_right_cancel' 1 hc
  have hx : Nat.ModEq m (Nat.triangular x) 0 := Int.natCast_modEq_iff.mp (modEq_cancel_coprime m 8 _ _ hco8 hx8)
  have hy : Nat.ModEq m (Nat.triangular y) 0 := Int.natCast_modEq_iff.mp (modEq_cancel_coprime m 8 _ _ hco8 hy8)
  have hz : Nat.ModEq m (Nat.triangular z) ρ := Int.natCast_modEq_iff.mp (modEq_cancel_coprime m 8 _ _ hco8 hz8)
  have hsum : Nat.triangular x+Nat.triangular y+Nat.triangular z=m*n+ρ := by
    rw [hxsq,hysq,hzsq] at hn
    have he : (Nat.triangular x:ℤ)+Nat.triangular y+Nat.triangular z=(m:ℤ)*n+ρ := by omega
    exact_mod_cast he
  apply Exists.intro x
  apply Exists.intro y
  apply Exists.intro z
  apply floors_eq_of_residue_sum hm hsum
  change Nat.triangular x%m=0%m at hx
  change Nat.triangular y%m=0%m at hy
  change Nat.triangular z%m=ρ%m at hz
  rw [hx,hy,hz,Nat.zero_mod,Nat.mod_eq_of_lt hρ]
  omega

lemma rayForm_mod (m g : ℕ) (x y z : ℤ) :
    Int.ModEq m ((x^2+(x+m*y)^2+(g*x+m*z)^2)) (((g:ℤ)^2+2)*x^2) := by
  have hb : Int.ModEq m (x+m*y) x := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-y,by ring⟩
  have hc : Int.ModEq m (g*x+m*z) (g*x) := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-z,by ring⟩
  have h := ((Int.ModEq.refl (x^2)).add (hb.pow 2)).add (hc.pow 2)
  have he : x^2+x^2+((g:ℤ)*x)^2=((g:ℤ)^2+2)*x^2 := by ring
  rw [he] at h
  exact h

lemma floors_from_rayForm (m n g ρ : ℕ) (hm : 0< m) (ho : Odd m) (hρ : ρ< m)
    (hunit : Nat.Coprime (g^2+2) m)
    (hres : Int.ModEq m (8*(ρ:ℤ)+1) ((g:ℤ)^2))
    (x y z : ℤ) (hn : (x^2+(x+m*y)^2+(g*x+m*z)^2)=8*((m:ℤ)*n+ρ)+3) :
    ∃ a b c : ℕ, n=Nat.triangular a/m+Nat.triangular b/m+Nat.triangular c/m := by
  have hN0 : Int.ModEq m (8*((m:ℤ)*n+ρ)+3) (8*(ρ:ℤ)+3) := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-8*(n:ℤ),by ring⟩
  have hN1 : Int.ModEq m (8*(ρ:ℤ)+3) ((g:ℤ)^2+2) := by
    simpa only [add_assoc,show (1:ℤ)+2=3 from rfl] using hres.add_right 2
  have hq : Int.ModEq m ((x^2+(x+m*y)^2+(g*x+m*z)^2)) ((g:ℤ)^2+2) := by
    rw [hn]
    exact hN0.trans hN1
  have hco : IsCoprime (m:ℤ) ((g^2+2:ℕ):ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using hunit.symm
  push_cast at hco
  have hxm : Int.ModEq m (x^2) 1 := by
    apply modEq_cancel_coprime m ((g:ℤ)^2+2) _ _ hco
    simpa using (rayForm_mod m g x y z).symm.trans hq
  have hbm : Int.ModEq m (x+m*y) x := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-y,by ring⟩
  have hcm : Int.ModEq m (g*x+m*z) (g*x) := by
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-z,by ring⟩
  have hgm : Int.ModEq m (((g:ℤ)*x)^2) ((g:ℤ)^2) := by
    simpa only [mul_pow,mul_one] using hxm.mul_left ((g:ℤ)^2)
  exact floors_from_square_residues m n ρ hm ho hρ x (x+m*y) (g*x+m*z) hn hxm
    ((hbm.pow 2).trans hxm) (((hcm.pow 2).trans hgm).trans hres.symm)

lemma unit_square_lifts (m C N : ℤ) (hco : IsCoprime m (2*C))
    (hbase : Int.ModEq m C N) :
    ∀ k : ℕ, ∃ x : ℤ, Int.ModEq m x 1 ∧ Int.ModEq (m^(k+1)) (C*x^2) N := by
  intro k
  induction k with
  | zero => exact ⟨1,Int.ModEq.rfl,by simpa using hbase⟩
  | succ k ih =>
    obtain ⟨x,hx,hsol⟩ := ih
    obtain ⟨d,hd⟩ := Int.modEq_iff_dvd.mp hsol
    have hcox : IsCoprime m x := by
      obtain ⟨e,he⟩ := Int.modEq_iff_dvd.mp hx
      exact ⟨e,1,by nlinarith only [he]⟩
    obtain ⟨s,t,hst⟩ := hco.mul_right hcox
    let X := x+m^(k+1)*(t*d)
    have hX : Int.ModEq m X 1 := by
      apply Int.ModEq.trans (b:=x) ?_ hx
      apply Int.modEq_iff_dvd.mpr
      refine ⟨-m^k*(t*d),?_⟩
      dsimp [X]
      rw [pow_succ]
      ring
    refine ⟨X,hX,Int.modEq_iff_dvd.mpr ?_⟩
    refine ⟨s*d-C*m^k*(t*d)^2,?_⟩
    have hst' : 1-2*C*x*t=s*m := by nlinarith only [hst]
    calc
      N-C*X^2 = (N-C*x^2)-2*C*x*m^(k+1)*(t*d)-C*(m^(k+1))^2*(t*d)^2 := by
        dsimp [X]
        ring
      _ = m^(k+1)*d*(1-2*C*x*t)-C*(m^(k+1))^2*(t*d)^2 := by rw [hd]; ring
      _ = m^(k+1)*d*(s*m)-C*(m^(k+1))^2*(t*d)^2 := by rw [hst']
      _ = m^(k+1+1)*(s*d-C*m^k*(t*d)^2) := by simp only [pow_succ]; ring

lemma rayForm_local_at_modulus_powers (m g N : ℕ) (ho : Odd m)
    (hco : Nat.Coprime (g^2+2) m) (hN : Nat.ModEq m N (g^2+2)) :
    ∀ k : ℕ, ∃ x y z : ℤ, Int.ModEq ((m:ℤ)^k) ((x^2+(x+m*y)^2+(g*x+m*z)^2)) N := by
  have hcoC : IsCoprime (m:ℤ) ((g^2+2:ℕ):ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using hco.symm
  push_cast at hcoC
  have hco2 : IsCoprime (m:ℤ) 2 := Int.isCoprime_two_right.mpr (by exact_mod_cast ho)
  have hco2C : IsCoprime (m:ℤ) (2*((g:ℤ)^2+2)) := hco2.mul_right hcoC
  have hbase : Int.ModEq m ((g:ℤ)^2+2) N := by
    exact_mod_cast Int.natCast_modEq_iff.mpr hN.symm
  intro k
  cases k with
  | zero => exact ⟨0,0,0,by simp [Int.ModEq]⟩
  | succ k =>
    obtain ⟨x,hx,hrep⟩ := unit_square_lifts m ((g:ℤ)^2+2) N hco2C hbase k
    refine ⟨x,0,0,?_⟩
    have he : (x^2+(x+m*0)^2+(g*x+m*0)^2)=((g:ℤ)^2+2)*x^2 := by simp only [mul_zero,add_zero]; ring
    rw [he]
    exact hrep

lemma odd_prime_local_three_squares (p : ℕ) (hp : p.Prime) (ho : Odd p) (N : ℤ) :
    ∀ k : ℕ, ∃ a b c : ℤ, Int.ModEq ((p:ℤ)^k) (a^2+b^2+c^2) N := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b,c,hb,hc,hbc⟩ := Nat.sq_add_sq_zmodEq p (N-1)
  have hbase : Int.ModEq p 1 (N-(b:ℤ)^2-(c:ℤ)^2) := by
    convert (hbc.add_right 1).sub_right ((b:ℤ)^2+(c:ℤ)^2) using 1 <;> ring
  have hco : IsCoprime (p:ℤ) (2*1) := by
    simpa using (Int.isCoprime_two_right.mpr (by exact_mod_cast ho) : IsCoprime (p:ℤ) 2)
  intro k
  cases k with
  | zero => exact ⟨0,0,0,by simp [Int.ModEq]⟩
  | succ k =>
    obtain ⟨a,ha,he⟩ := unit_square_lifts p 1 (N-(b:ℤ)^2-(c:ℤ)^2) hco hbase k
    refine ⟨a,b,c,?_⟩
    convert he.add_right ((b:ℤ)^2+(c:ℤ)^2) using 1 <;> ring

lemma square_lifts_two_stages (T : ℤ) (hT : T%8=1) :
    ∀ k : ℕ, ∃ x : ℤ, Odd x ∧ Int.ModEq ((2:ℤ)^(k+3)) (x^2) T := by
  intro k
  induction k with
  | zero => exact ⟨1,odd_one,by simpa [Int.ModEq] using hT.symm⟩
  | succ k ih =>
    obtain ⟨x,hx,he⟩ := ih
    obtain ⟨d,hd⟩ := Int.modEq_iff_dvd.mp he
    obtain ⟨s,hs⟩ := hx
    let X := x+(2:ℤ)^(k+2)*d
    have hX : Odd X := by
      refine ⟨s+(2:ℤ)^(k+1)*d,?_⟩
      dsimp [X]
      rw [hs]
      simp only [pow_succ]
      ring
    refine ⟨X,hX,Int.modEq_iff_dvd.mpr ?_⟩
    refine ⟨-s*d-(2:ℤ)^k*d^2,?_⟩
    calc
      T-X^2=(T-x^2)-2*x*(2:ℤ)^(k+2)*d-((2:ℤ)^(k+2))^2*d^2 := by dsimp [X]; ring
      _ = (2:ℤ)^(k+3)*d*(1-x)-((2:ℤ)^(k+2))^2*d^2 := by
        rw [hd]
        simp only [pow_add]
        norm_num
        ring
      _ = (2:ℤ)^(k+1+3)*(-s*d-(2:ℤ)^k*d^2) := by
        rw [hs]
        simp only [pow_add]
        norm_num
        ring

lemma square_lifts_two (T : ℤ) (hT : T%8=1) :
    ∀ k : ℕ, ∃ x : ℤ, Odd x ∧ Int.ModEq ((2:ℤ)^k) (x^2) T := by
  intro k
  obtain ⟨x,hx,he⟩ := square_lifts_two_stages T hT k
  refine ⟨x,hx,he.of_dvd ?_⟩
  exact ⟨8,by rw [pow_add]; norm_num⟩

lemma two_local_three_squares (N : ℤ) (hN : N%8=3) :
    ∀ k : ℕ, ∃ a b c : ℤ, Int.ModEq ((2:ℤ)^k) (a^2+b^2+c^2) N := by
  intro k
  obtain ⟨x,hx,he⟩ := square_lifts_two (N-2) (by omega) k
  refine ⟨1,1,x,?_⟩
  convert he.add_left 2 using 1 <;> ring

lemma rayForm_local_away_of_congruence (m g d : ℕ) (hco : Nat.Coprime d m) (N : ℤ)
    (hrep : ∃ a b c : ℤ, Int.ModEq d (a^2+b^2+c^2) N) :
    ∃ x y z : ℤ, Int.ModEq d ((x^2+(x+m*y)^2+(g*x+m*z)^2)) N := by
  obtain ⟨a,b,c,hn⟩ := hrep
  have hcoZ : IsCoprime (d:ℤ) (m:ℤ) := by
    apply Int.isCoprime_iff_nat_coprime.mpr
    simpa only [Int.natAbs_natCast] using hco
  obtain ⟨u,v,huv⟩ := hcoZ
  have hi : 1-(m:ℤ)*v=u*d := by nlinarith only [huv]
  have hb : Int.ModEq d (a+m*(v*(b-a))) b := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨u*(b-a),?_⟩
    calc
      b-(a+m*(v*(b-a)))=(1-(m:ℤ)*v)*(b-a) := by ring
      _ = (d:ℤ)*(u*(b-a)) := by rw [hi]; ring
  have hc : Int.ModEq d (g*a+m*(v*(c-g*a))) c := by
    apply Int.modEq_iff_dvd.mpr
    refine ⟨u*(c-g*a),?_⟩
    calc
      c-(g*a+m*(v*(c-g*a)))=(1-(m:ℤ)*v)*(c-g*a) := by ring
      _ = (d:ℤ)*(u*(c-g*a)) := by rw [hi]; ring
  refine ⟨a,v*(b-a),v*(c-g*a),?_⟩
  exact (((Int.ModEq.refl (a^2)).add (hb.pow 2)).add (hc.pow 2)).trans hn

lemma rayForm_all_local_congruences (m g N : ℕ) (ho : Odd m) (hco : Nat.Coprime (g^2+2) m)
    (hN : Nat.ModEq m N (g^2+2)) (hN8 : N%8=3) :
    ∀ p : ℕ, p.Prime → ∀ k : ℕ,
      ∃ x y z : ℤ, Int.ModEq ((p:ℤ)^k) ((x^2+(x+m*y)^2+(g*x+m*z)^2)) N := by
  intro p hp k
  by_cases hpm : p∣m
  · obtain ⟨x,y,z,hrep⟩ := rayForm_local_at_modulus_powers m g N ho hco hN k
    refine ⟨x,y,z,hrep.of_dvd ?_⟩
    apply pow_dvd_pow_of_dvd
    exact_mod_cast hpm
  · have hc : Nat.Coprime (p^k) m := (hp.coprime_iff_not_dvd.mpr hpm).pow_left k
    have hrep : ∃ a b c : ℤ, Int.ModEq ((p^k:ℕ):ℤ) (a^2+b^2+c^2) N := by
      rcases hp.eq_two_or_odd with rfl|hop
      · simpa only [Nat.cast_pow,Nat.cast_ofNat] using two_local_three_squares N (by exact_mod_cast hN8) k
      · simpa only [Nat.cast_pow] using odd_prime_local_three_squares p hp (Nat.odd_iff.mpr hop) N k
    simpa only [Nat.cast_pow] using rayForm_local_away_of_congruence m g (p^k) hc N hrep


/-- The fixed form has every required prime-power local representation. -/
def H1 : Prop := ∀ m : ℕ, 0< m → Odd m → ∀ N : ℕ,
  N%8=3 → Nat.ModEq m N 2 → ∀ p : ℕ, p.Prime → ∀ k : ℕ,
    ∃ x y z : ℤ, Int.ModEq ((p:ℤ)^k) ((x^2+(x+m*y)^2+(m*z)^2)) N

/-- Open quantitative global representation for one explicit form per modulus. -/
def H2 : Prop := ∀ m N : ℕ, 0< m → Odd m → Squarefree m →
  m ∉ ({1,3,5,13,15}:Finset ℕ) → N%8=3 → Nat.Coprime N (2*m) →
  Nat.ModEq m N 2 → m^8<16*N →
  (∀ p : ℕ, p.Prime → ∀ k : ℕ,
    ∃ x y z : ℤ, Int.ModEq ((p:ℤ)^k) ((x^2+(x+m*y)^2+(m*z)^2)) N) →
  ∃ x y z : ℤ, (x^2+(x+m*y)^2+(m*z)^2)=N

lemma odd_coprime_two (m : ℕ) (ho : Odd m) : Nat.Coprime 2 m := by
  have hm2 : Nat.ModEq 2 m 1 := by change m%2=1%2; exact Nat.odd_iff.mp ho
  change Nat.gcd 2 m=1
  rw [Nat.gcd_comm,hm2.gcd_eq]
  decide

lemma local_data_proved : H1 := by
  intro m hm ho N hN8 hNm
  simpa using rayForm_all_local_congruences m 0 N ho (by simpa using odd_coprime_two m ho) hNm hN8

theorem main : H1 → H2 → OMA.R_OeisA256544_conjecture_R1.H1 := by
  intro hlocal hglobal m ho hs hex n hn
  have hm : 0< m := by obtain ⟨k,hk⟩ := ho; omega
  have hco := odd_coprime_two m ho
  let c := m^2%(8*m)
  let ρ := c/8
  let N := 8*(m*n+ρ)+3
  have hc8 : c%8=1 := by
    dsimp [c]
    rw [Nat.mod_mod_of_dvd _ (show 8∣8*m from ⟨m,rfl⟩)]
    exact odd_square_mod_eight m ho
  have hclt : c<8*m := Nat.mod_lt _ (by omega)
  have hcρ : c=8*ρ+1 := by dsimp [ρ]; omega
  have hρ : ρ< m := by omega
  have hcmod : Nat.ModEq m (8*ρ+1) 0 := by
    rw [← hcρ]
    apply ((Nat.mod_modEq (m^2) (8*m)).of_dvd ⟨8,by ring⟩).trans
    change m^2%m=0%m
    simp [Nat.pow_mod]
  have hN8 : N%8=3 := by dsimp [N]; omega
  have hN0 : Nat.ModEq m N (8*ρ+3) := by
    have hp : Nat.ModEq m (8*m*n) 0 := by change (8*m*n)%m=0%m; simp [Nat.mul_mod]
    have he : N=8*m*n+(8*ρ+3) := by dsimp [N]; ring
    rw [he]
    simpa using hp.add (Nat.ModEq.refl (8*ρ+3))
  have hNm : Nat.ModEq m N 2 :=
    hN0.trans (by simpa only [Nat.add_assoc,zero_add,show (1:ℕ)+2=3 from rfl] using hcmod.add_right 2)
  have hcoNm : Nat.Coprime N m := by
    change Nat.gcd N m=1
    rw [hNm.gcd_eq]
    exact hco
  have hN2 : Nat.ModEq 2 N 1 := by change N%2=1%2; omega
  have hcoN2 : Nat.Coprime N 2 := by
    change Nat.gcd N 2=1
    rw [hN2.gcd_eq]
    decide
  have hcoN : Nat.Coprime N (2*m) := Nat.coprime_mul_iff_right.mpr ⟨hcoN2,hcoNm⟩
  have hbig : m^8<16*N := calc
    m^8=m*m^7 := by ring
    _ < m*(128*n) := Nat.mul_lt_mul_of_pos_left hn hm
    _ ≤ 16*N := by dsimp [N]; nlinarith
  obtain ⟨x,y,z,hrep⟩ := hglobal m N hm ho hs hex hN8 hcoN hNm hbig (hlocal m hm ho N hN8 hNm)
  have hcmodZ : Int.ModEq m (8*(ρ:ℤ)+1) ((0:ℤ)^2) := by
    simpa using Int.natCast_modEq_iff.mpr hcmod
  apply floors_from_rayForm m n 0 ρ hm ho hρ (by simpa using hco) hcmodZ x y z
  simpa [N] using hrep

end OMA.R_OeisA256544_conjecture_R1_H1_R1
