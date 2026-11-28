import OMAStatements.S_oeis_a009003

/-! A positive integer is a hypotenuse exactly when a prime factor is one modulo four. -/

namespace HypotenuseNumbers

def Hypotenuse (m : ℕ) : Prop := ∃ a b : ℕ, 0<a ∧ 0<b ∧ a^2+b^2=m^2

def SplitFactor (m : ℕ) : Prop := ∃ p : ℕ, p.Prime ∧ p ∣ m ∧ p%4=1

private theorem reduce_square {a b : ℕ} (h : a ∣ b)
    (square : IsSquare (-1 : ZMod b)) : IsSquare (-1 : ZMod a) := by
  simpa only [map_neg, map_one] using square.map (ZMod.castHom h (ZMod a))

private theorem split_of_primitive {a b c : ℕ} (ha : 0<a) (hb : 0<b)
    (hc : a.Coprime b) (eq : a^2+b^2=c^2) : SplitFactor c := by
  have large : 1<c := by nlinarith [Nat.one_le_pow 2 a ha, Nat.one_le_pow 2 b hb]
  let p := c.minFac
  have prime : p.Prime := Nat.minFac_prime (by omega)
  let _ : Fact p.Prime := ⟨prime⟩
  have hit : p ∣ c := c.minFac_dvd
  have sq := ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime eq.symm hc
  have odd : p≠2 := by
    intro e
    have two : 2 ∣ c := e ▸ hit
    have four : 4 ∣ c^2 := pow_dvd_pow_of_dvd two 2
    exact (by decide : ¬IsSquare (-1 : ZMod 4)) (reduce_square four sq)
  have qr := ZMod.exists_sq_eq_neg_one_iff.mp
    (reduce_square (hit.trans (dvd_pow (dvd_refl c) (by decide : 2≠0))) sq)
  have parity := Nat.odd_iff.mp (prime.odd_of_ne_two odd)
  exact ⟨p,prime,hit,by omega⟩

theorem split_iff {m : ℕ} (positive : 0 < m) : Hypotenuse m ↔ SplitFactor m := by
  constructor
  · rintro ⟨a,b,ha,hb,eq⟩
    let g := a.gcd b
    have gp : 0<g := Nat.gcd_pos_of_pos_left b ha
    have ga : g ∣ a := Nat.gcd_dvd_left ..
    have gb : g ∣ b := Nat.gcd_dvd_right ..
    have gm : g ∣ m := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp (by
      rw [← eq]
      exact dvd_add (pow_dvd_pow_of_dvd ga 2) (pow_dvd_pow_of_dvd gb 2))
    have trip : (a/g)^2+(b/g)^2=(m/g)^2 := by
      apply Nat.eq_of_mul_eq_mul_right (by positivity : 0<g^2)
      rw [Nat.add_mul,← Nat.mul_pow,← Nat.mul_pow,← Nat.mul_pow,
          Nat.div_mul_cancel ga,Nat.div_mul_cancel gb,Nat.div_mul_cancel gm,eq]
    obtain ⟨p,hp,pc,mod⟩ := split_of_primitive
      (Nat.div_pos (Nat.le_of_dvd ha ga) gp) (Nat.div_pos (Nat.le_of_dvd hb gb) gp)
      (Nat.coprime_div_gcd_div_gcd gp) trip
    exact ⟨p,hp,pc.trans (Nat.div_dvd_of_dvd gm),mod⟩
  · rintro ⟨p,hp,⟨k,rfl⟩,mod⟩
    let _ : Fact p.Prime := ⟨hp⟩
    obtain ⟨a,b,eq⟩ := Nat.Prime.sq_add_sq (p:=p) (by omega)
    have nz {x y : ℕ} (id : x^2+y^2=p) : 0<x := by
      by_contra! bad
      simp [show x=0 by omega] at id
      exact (Nat.Prime.not_prime_pow (x:=y) (by decide : 2≤2)) (id ▸ hp)
    have apos := nz eq
    have bpos := nz (by rw [add_comm,eq])
    have ne : a≠b := by
      rintro rfl
      have two : 2 ∣ p := ⟨a^2,by omega⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp two
      omega
    have kp : 0<k := Nat.pos_of_mul_pos_left positive
    wlog le : b<a generalizing a b
    · exact this b a (by rwa [add_comm]) bpos apos ne.symm (by omega)
    refine ⟨k*(a^2-b^2),k*(2*a*b),mul_pos kp
      (Nat.sub_pos_of_lt (Nat.pow_lt_pow_left le (by decide))),by positivity,?_⟩
    zify [Nat.pow_le_pow_left le.le 2] at eq ⊢
    rw [← eq]
    ring

end HypotenuseNumbers

/-! The finite Möbius sum from OEIS A009003, including its real part at even inputs. -/

namespace HypotenuseNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

def divisorSum (m : ℕ) : ℂ := ∑ d ∈ m.divisors, (μ d : ℂ)*Complex.I^d

private def four : ℕ →* ℤ :=
  ZMod.χ₄.toMonoidHom.comp (Nat.castRingHom (ZMod 4)).toMonoidHom

private def parityChar : ℕ →* ℤ where
  toFun n := if Even n then 0 else 1
  map_one' := by decide
  map_mul' a b := by
    by_cases ha : Even a <;> by_cases hb : Even b <;> simp [Nat.even_mul,ha,hb]

private theorem euler {m : ℕ} (hm : m≠0) (f : ℕ →* ℤ) :
    (∑ d ∈ m.divisors, μ d*f d)=∏ p ∈ m.primeFactors, (1-f p) := by
  classical
  have restrict : (∑ d ∈ m.divisors with Squarefree d, μ d*f d)=
      ∑ d ∈ m.divisors, μ d*f d :=
    sum_subset (filter_subset ..) (by
      intro d hd h
      simp only [mem_filter,hd,true_and] at h
      simp [moebius_eq_zero_of_not_squarefree h])
  rw [←restrict,Nat.sum_divisors_filter_squarefree hm,Nat.factors_eq]
  simp_rw [sub_eq_add_neg]
  rw [prod_one_add]
  apply sum_congr rfl
  intro s hs
  have sub : s ⊆ m.primeFactors := mem_powerset.mp hs
  rw [s.prod_val,Function.id_def,isMultiplicative_moebius.map_prod_of_subset_primeFactors m s sub,
    map_prod,←prod_mul_distrib]
  apply prod_congr rfl
  intro p hp
  rw [moebius_apply_prime (Nat.prime_of_mem_primeFactors (sub hp))]
  ring

private theorem term (d : ℕ) : (μ d : ℂ)*Complex.I^d =
    ((μ d*parityChar d : ℤ):ℂ) - ((μ d : ℤ):ℂ) + ((μ d*four d : ℤ):ℂ)*Complex.I := by
  change _ = ((μ d*(if Even d then 0 else 1) : ℤ):ℂ) - _ +
    ((μ d*ZMod.χ₄ (d:ZMod 4) : ℤ):ℂ)*Complex.I
  rw [ZMod.χ₄_nat_eq_if_mod_four,Complex.I_pow_eq_pow_mod d]
  simp only [Nat.even_iff]
  rcases (show d%4=0 ∨ d%4=1 ∨ d%4=2 ∨ d%4=3 by omega) with h|h|h|h
  · have bad : ¬ Squarefree d := fun sf =>
      (by decide : ¬ Squarefree 4) (sf.squarefree_of_dvd (Nat.dvd_of_mod_eq_zero h))
    simp [moebius_eq_zero_of_not_squarefree bad]
  · simp [h,show d%2=1 by omega]
  · simp [h,show d%2=0 by omega]
  · simp [h,show d%2=1 by omega, Complex.I_pow_three]

private def product (m : ℕ) (f : ℕ →* ℤ) : ℤ := ∏ p ∈ m.primeFactors, (1-f p)

private theorem formula {m : ℕ} (hm : m≠0) : divisorSum m =
    ((product m parityChar:ℂ)-(product m 1:ℂ))+(product m four:ℂ)*Complex.I := by
  unfold divisorSum product
  rw [←euler hm,←euler hm,←euler hm]
  push_cast
  simp only [MonoidHom.one_apply,sum_mul,←sum_sub_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro d _
  push_cast at *
  simpa using term d

theorem mobius_iff {m : ℕ} (hm : 0 < m) : divisorSum m=0 ↔ SplitFactor m := by
  rw [formula hm.ne']
  constructor
  · intro eq
    have im := congrArg Complex.im eq
    have van : product m four=0 := by simpa using im
    obtain ⟨p,hp,z⟩ := Finset.prod_eq_zero_iff.mp van
    have spec := Nat.mem_primeFactors.mp hp
    change 1-ZMod.χ₄ (p:ZMod 4)=0 at z
    rw [ZMod.χ₄_nat_eq_if_mod_four] at z
    refine ⟨p,spec.1,spec.2.1,?_⟩
    split_ifs at z <;> omega
  · rintro ⟨p,prime,div,mod⟩
    have hp := Nat.mem_primeFactors.mpr ⟨prime,div,hm.ne'⟩
    have fourZero : product m four=0 :=
      Finset.prod_eq_zero hp (sub_eq_zero.mpr (ZMod.χ₄_nat_one_mod_four mod).symm)
    have twoZero : product m parityChar=0 := Finset.prod_eq_zero hp (by
      change 1-(if Even p then (0:ℤ) else 1)=0
      simp only [Nat.even_iff,if_neg (show ¬p%2=0 by omega)]; decide)
    have oneZero : product m 1=0 := Finset.prod_eq_zero hp (by simp)
    simp [fourZero,twoZero,oneZero]

end HypotenuseNumbers

theorem OMA.solution : type_of% @OMA.S_oeis_a009003.main := by
  intro m positive
  change (0 < m ∧ HypotenuseNumbers.Hypotenuse m) ↔ HypotenuseNumbers.divisorSum m = 0
  rw [and_iff_right positive]
  exact (HypotenuseNumbers.split_iff positive).trans (HypotenuseNumbers.mobius_iff positive).symm
