import OMAStatements.S_oeis_a193437

/-! For any period d greater than one and any prime p congruent to one
modulo d, the integral operator f ↦ f' + f/(1-X^d) gains a factor of p
every p iterations. An integrating factor over the finite prime field
conjugates the operator to ordinary differentiation.
-/

namespace PeriodicCycles193437

open PowerSeries
open scoped PowerSeries

noncomputable def op {R : Type*} [CommRing R] (g f : R⟦X⟧) := derivative R f + g*f

lemma deriv_map {R S : Type*} [CommRing R] [CommRing S] (u : R →+* S) (f : R⟦X⟧) :
    map u (derivative R f) = derivative S (map u f) := by
  ext n
  simp [coeff_derivative]

lemma op_map {R S : Type*} [CommRing R] [CommRing S] (u : R →+* S) (g f : R⟦X⟧) (n : ℕ) :
    map u ((op g)^[n] f) = (op (map u g))^[n] (map u f) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',op,map_add,map_mul,deriv_map,ih]

lemma gauge {R : Type*} [CommRing R] (h g : R⟦X⟧) (hh : derivative R h = h*g)
    (n : ℕ) (f : R⟦X⟧) : h*(op g)^[n] f = (derivative R)^[n] (h*f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',← ih,Derivation.leibniz,hh]
    simp [op,smul_eq_mul]
    ring

lemma iter_deriv_zero (p : ℕ) [Fact p.Prime] (f : (ZMod p)⟦X⟧) :
    (derivative (ZMod p))^[p] f=0 := by
  ext k
  rw [coeff_iterate_derivative,map_zero]
  have h : p ∣ (k+1).ascFactorial p :=
    (Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl).trans (Nat.factorial_dvd_ascFactorial _ _)
  rw [(ZMod.natCast_eq_zero_iff ..).mpr h,zero_mul]

lemma lift_one (p : ℕ) [Fact p.Prime] (g : ℤ⟦X⟧)
    (h : (ZMod p)⟦X⟧) (hn : h≠0) (hh : derivative (ZMod p) h = h*map (Int.castRingHom (ZMod p)) g)
    (f : ℤ⟦X⟧) : ∃ b : ℤ⟦X⟧, (op g)^[p] f = C (p:ℤ)*b := by
  let u := Int.castRingHom (ZMod p)
  have zero : map u ((op g)^[p] f)=0 := by
    rw [op_map]
    apply (mul_eq_zero.mp _).resolve_left hn
    rw [gauge h _ hh,iter_deriv_zero]
  let t := (op g)^[p] f
  have hd (n : ℕ) : (p:ℤ) ∣ coeff n t := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa [t,u] using congrArg (coeff (R:=ZMod p) n) zero
  refine ⟨mk (fun n => coeff n t / p),?_⟩
  ext n
  rw [coeff_C_mul,coeff_mk]
  simpa only [t] using (Int.mul_ediv_cancel' (hd n)).symm

lemma op_const {R : Type*} [CommRing R] (g f : R⟦X⟧) (c : R) (n : ℕ) :
    (op g)^[n] (C c*f)=C c*(op g)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply',ih,op,Derivation.leibniz,derivative_C,smul_eq_mul,mul_zero]
    ring

lemma lift_all (p : ℕ) [Fact p.Prime] (g : ℤ⟦X⟧)
    (h : (ZMod p)⟦X⟧) (hn : h≠0) (hh : derivative (ZMod p) h = h*map (Int.castRingHom (ZMod p)) g)
    (n : ℕ) : ∃ b : ℤ⟦X⟧, (op g)^[n] 1 = C ((p:ℤ)^(n/p))*b := by
  suffices aux : ∀ k : ℕ, ∀ f : ℤ⟦X⟧, ∃ b : ℤ⟦X⟧, (op g)^[p*k] f=C ((p:ℤ)^k)*b by
    obtain ⟨b,hb⟩ := aux (n/p) ((op g)^[n%p] 1)
    exact ⟨b,by rwa [← Function.iterate_add_apply,Nat.div_add_mod] at hb⟩
  intro k
  induction k with
  | zero => intro f; exact ⟨f,by simp⟩
  | succ k ih =>
    intro f
    obtain ⟨a,ha⟩ := ih f
    obtain ⟨b,hb⟩ := lift_one p g h hn hh a
    refine ⟨b,?_⟩
    rw [Nat.mul_succ,Nat.add_comm,Function.iterate_add_apply,ha,op_const,hb,pow_succ,map_mul,mul_assoc]

lemma transfer (p : ℕ) [Fact p.Prime] (g : ℤ⟦X⟧) (y : ℚ⟦X⟧)
    (yc : constantCoeff y=1) (yd : derivative ℚ y=y*map (Int.castRingHom ℚ) g)
    (h : (ZMod p)⟦X⟧) (hn : h≠0) (hh : derivative (ZMod p) h = h*map (Int.castRingHom (ZMod p)) g)
    (n : ℕ) : ∃ k : ℤ, (n.factorial:ℚ)*coeff n y=(p:ℚ)^(n/p)*k := by
  obtain ⟨b,hb⟩ := lift_all p g h hn hh n
  have he := gauge y _ yd n 1
  rw [mul_one] at he
  rw [← constantCoeff_iterate_derivative,← he,← map_one (map (Int.castRingHom ℚ)),← op_map,hb]
  refine ⟨constantCoeff b,?_⟩
  have hc : constantCoeff (map (Int.castRingHom ℚ) b)=((constantCoeff b : ℤ):ℚ) := by
    rw [← coeff_zero_eq_constantCoeff_apply,coeff_map,coeff_zero_eq_constantCoeff_apply]; rfl
  simp [yc,hc]



open PowerSeries Finset
open scoped PowerSeries

noncomputable def indicator (d : ℕ) : ℤ⟦X⟧ := mk (fun n => if d ∣ n then 1 else 0)

noncomputable def geometric {K : Type*} [Field K] (a : K) : K⟦X⟧ := mk (fun n => a^n)

lemma geometric_mul {K : Type*} [Field K] (a : K) :
    (1-C a*X)*geometric a=1 := by
  rw [sub_mul,one_mul,show C a*X*geometric a=(C a * geometric a)*X by ring]
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff_apply,geometric,constantCoeff_mk]
  | succ n => simp [coeff_succ_mul_X,coeff_C_mul,geometric,pow_succ,coeff_one]; ring

def admits {K : Type*} [Field K] (g : K⟦X⟧) : Prop :=
  ∃ h : K⟦X⟧, h≠0 ∧ derivative K h=h*g

lemma admits_add {K : Type*} [Field K] {g f : K⟦X⟧} (hg : admits g) (hf : admits f) :
    admits (g+f) := by
  obtain ⟨a,an,ad⟩ := hg
  obtain ⟨b,bn,bd⟩ := hf
  refine ⟨a*b,mul_ne_zero an bn,?_⟩
  rw [Derivation.leibniz,ad,bd]
  simp only [smul_eq_mul]; ring

lemma admits_sum {K : Type*} [Field K] (g : ℕ → K⟦X⟧) (hg : ∀ j, admits (g j)) (d : ℕ) :
    admits (∑ j ∈ range d, g j) := by
  induction d with
  | zero => exact ⟨1,one_ne_zero,by simp⟩
  | succ d ih => rw [sum_range_succ]; exact admits_add ih (hg d)

lemma admits_geom {p : ℕ} [Fact p.Prime] (a c : ZMod p) (ha : a≠0) :
    admits (C c * geometric a) := by
  let b : (ZMod p)⟦X⟧ := 1-C a*X
  let e := (-c/a).val + p
  have ep : 0 < e := by dsimp [e]; have hp := (Fact.out : p.Prime).pos; omega
  have ec : (e:ZMod p)*(-a)=c := by simp [e,ha]
  have bh : b ≠ 0 := fun h => by
    have h' := geometric_mul a
    change b * geometric a = 1 at h'
    simp [h] at h'
  refine ⟨b^e,pow_ne_zero _ bh,?_⟩
  have db : derivative (ZMod p) b = -C a := by simp [b,Derivation.leibniz,smul_eq_mul]
  have bp : b^(e-1)*b=b^e := by rw [← pow_succ,show e-1+1=e by omega]
  have cpp : (C (e:ZMod p) : (ZMod p)⟦X⟧)=(e:ℕ) := by simp
  apply mul_left_cancel₀ bh
  rw [derivative_pow,db,← cpp]
  calc
    b * (C (e:ZMod p)*b^(e-1)* -C a) = b^e*C ((e:ZMod p)*(-a)) := by
      rw [← bp,map_mul,map_neg]; ring
    _ = b*(b^e*(C c*geometric a)) := by
      rw [ec]
      have h : b*geometric a=1 := geometric_mul a
      linear_combination -(b^e*C c)*h

lemma primitive {p d : ℕ} [Fact p.Prime] (hd : d ∣ p-1) : ∃ z : ZMod p, IsPrimitiveRoot z d := by
  obtain ⟨u,hu⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,Nat.totient_prime (Fact.out : p.Prime)] at hu
  obtain ⟨k,hk⟩ := hd
  have h := IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu)
  have pos : 0 < p-1 := by have := (Fact.out : p.Prime).two_le; omega
  exact ⟨(u:ZMod p)^k, h.pow pos (by simpa [Nat.mul_comm] using hk)⟩

lemma periodic_gauge {p d : ℕ} [Fact p.Prime] (hd : 0 < d) (hdp : d ∣ p-1) :
    admits (map (Int.castRingHom (ZMod p)) (indicator d)) := by
  obtain ⟨z,hz⟩ := primitive hdp
  have nz : z≠0 := (hz.isUnit hd.ne').ne_zero
  have dlt : d < p := by
    have hp := (Fact.out : p.Prime).two_le
    have := Nat.le_of_dvd (show 0<p-1 by omega) hdp
    omega
  have dn : (d:ZMod p)≠0 := by
    rw [Ne,ZMod.natCast_eq_zero_iff]; exact Nat.not_dvd_of_pos_of_lt hd dlt
  let g := fun j : ℕ => C ((d:ZMod p)⁻¹)*geometric (z^j)
  convert admits_sum g (fun j => admits_geom _ _ (pow_ne_zero _ nz)) d using 1
  ext n
  simp only [coeff_map,indicator,coeff_mk,map_sum,g,coeff_C_mul,geometric]
  rw [← mul_sum]
  have powers (i : ℕ) : (z^i)^n = (z^n)^i := by rw [← pow_mul,← pow_mul,Nat.mul_comm]
  simp_rw [powers]
  by_cases h : d ∣ n
  · rw [if_pos h,(hz.pow_eq_one_iff_dvd n).mpr h]; simp [dn]
  · rw [if_neg h]
    have ne : z^n ≠ 1 := fun he => h ((hz.pow_eq_one_iff_dvd n).mp he)
    have hp : (z^n)^d=1 := by rw [← pow_mul,Nat.mul_comm,pow_mul,hz.pow_eq_one,one_pow]
    have hs := geom_sum_mul (z^n) d
    rw [hp,sub_self] at hs
    rw [(mul_eq_zero.mp hs).resolve_right (sub_ne_zero.mpr ne)]; simp



open PowerSeries Finset
open scoped PowerSeries

noncomputable def cycleLog (d : ℕ) : ℚ⟦X⟧ := mk fun n => if n%d=1 then 1/(n:ℚ) else 0
noncomputable def cycleExp (d : ℕ) : ℚ⟦X⟧ := (exp ℚ).subst (cycleLog d)

lemma log_zero (d : ℕ) : constantCoeff (cycleLog d)=0 := by simp [cycleLog,constantCoeff_mk]

lemma exp_zero (d : ℕ) : constantCoeff (cycleExp d)=1 := by
  let f := cycleLog d
  have h := constantCoeff_subst (HasSubst.of_constantCoeff_zero (log_zero d)) (exp ℚ)
  change constantCoeff (cycleExp d) = _ at h
  rw [h,finsum_eq_single _ 0]
  · simp
  · intro b hb
    change coeff b (exp ℚ) • constantCoeff (cycleLog d ^ b) = 0
    rw [map_pow,log_zero,zero_pow hb,smul_zero]

lemma exp_differential (d : ℕ) (hd : 1 < d) :
    derivative ℚ (cycleExp d) = cycleExp d * map (Int.castRingHom ℚ)
      (mk (fun n : ℕ => if d ∣ n then (1:ℤ) else 0)) := by
  rw [cycleExp,derivative_subst (HasSubst.of_constantCoeff_zero (log_zero d)),derivative_exp]
  congr 1
  ext n
  simp only [coeff_derivative,cycleLog,coeff_mk,coeff_map]
  have iff' : (n+1)%d=1 ↔ d∣n := by
    have hm : 1 ≡ n+1 [MOD d] ↔ d∣n := by rw [Nat.modEq_iff_dvd' (by omega)]; simp
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt hd,eq_comm] using hm
  rw [if_congr iff' rfl rfl]
  split_ifs <;> simp [show (n:ℚ)+1≠0 by positivity]


lemma cycle_divisibility (d p : ℕ) (hd : 1 < d) (hp : p.Prime) (hdp : d ∣ p-1)
    (n : ℕ) : ∃ k : ℤ, (n.factorial:ℚ)*PowerSeries.coeff n (cycleExp d) = (p:ℚ)^(n/p)*k := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨h,hn,hh⟩ := periodic_gauge (by omega : 0<d) hdp
  exact transfer p (indicator d) (cycleExp d) (exp_zero d) (exp_differential d hd) h hn hh n

end PeriodicCycles193437

open PeriodicCycles193437 in
theorem OMA.solution : type_of% @OMA.S_oeis_a193437.main := by
  constructor
  · exact fun n => cycle_divisibility 3 7 (by decide) (by decide) (by decide) n
  · intro p hp hm n
    have hp' := hp.two_le
    have hd : 3 ∣ p-1 := by omega
    exact cycle_divisibility 3 p (by decide) hp hd n
