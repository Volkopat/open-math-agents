import OMAReductions.R_mo_296166_R1
import Mathlib

/-!
# The two signs for the inner strong probable prime

Credit: @AlfredMelson
Source: https://mathoverflow.net/questions/296166

For m = du, the positive outer congruence forces m = 3 mod 4 and forces
the complementary divisor c to be 1 mod 8 and at least 49. The inner strong
test therefore has just one odd exponent. Its sign fixes the residue classes
of every odd divisor of m. In the positive branch c is 1 mod 16 and at least
97. In the negative branch c is 9 mod 16 and at least 73. Both tests use u/2 in the exponent of c+1
via the defining factorization of the outer number.
-/

namespace OMA.R_mo_296166_R1_H1_R1
private theorem no_shared {p e d : ℕ} (hp : p.Prime) (hp2 : 2 < p) (odd : Odd d)
    (minus : (2 : ZMod p)^e = -1) (plus : (2 : ZMod p)^d = 1) : False := by
  let : Fact p.Prime := ⟨hp⟩
  have h := pow_right_comm (2 : ZMod p) e d
  rw [minus,plus,odd.neg_one_pow,one_pow] at h
  have two : (2 : ZMod p) = 0 := by linear_combination -h
  have dvd := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using two)
  have := Nat.le_of_dvd (by decide : 0<2) dvd
  omega

private theorem shape {d u c : ℕ} (hd : 1 < d) (odd : Odd d) (ou : Odd u) (hc : 3 ≤ c)
    (eqn : 2^d-1 = (2*(d*u)+1)*c) :
    d*u % 4 = 3 ∧ c % 8 = 1 ∧ 49 ≤ c := by
  let n := 2*(d*u)+1
  have hn : Odd n := ⟨d*u,rfl⟩
  have hdu := Nat.odd_iff.mp (odd.mul ou)
  have powpos : 0 < 2^d := by positivity
  have eq' : 2^d = n*c+1 := by change 2^d-1 = n*c at eqn; omega
  have modn : (2:ℤ)^d ≡ 1 [ZMOD n] := by
    have h : (2:ℕ)^d ≡ 1 [MOD n] := by rw [eq']; simp [Nat.ModEq,Nat.add_mod]
    exact_mod_cast (Int.natCast_modEq_iff.mpr h)
  have jac := jacobiSym.mod_left' modn
  rw [jacobiSym.pow_left,jacobiSym.one_left,jacobiSym.at_two hn,ZMod.χ₈_nat_eq_if_mod_eight] at jac
  have bad : n%8 ≠ 3 := by
    intro h
    simp [Nat.odd_iff.mp hn,h,odd.neg_one_pow] at jac
  have hn7 : n%8=7 := by dsimp [n] at *; omega
  have dd : 3 ≤ d := by have := Nat.odd_iff.mp odd; omega
  have p8 : 2^d%8 = 0 := Nat.mod_eq_zero_of_dvd (show 2^3 ∣ 2^d from pow_dvd_pow _ dd)
  rw [eq',Nat.add_mod,Nat.mul_mod,hn7] at p8
  have hc8 : c%8=1 := by omega
  refine ⟨by dsimp [n] at hn7; omega,hc8,?_⟩
  have elim (p e : ℕ) (hp : p.Prime) (hp2 : 2 < p) (neg : (2:ZMod p)^e = -1) (div : p ∣ c) : False := by
    have hm : (2:ℕ)^d ≡ 1 [MOD p] := by
      rw [eq']; exact Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right div n))
    apply no_shared hp hp2 odd neg
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm
  by_contra! small
  have choices : c=9 ∨ c=17 ∨ c=25 ∨ c=33 ∨ c=41 := by omega
  rcases choices with rfl|rfl|rfl|rfl|rfl
  · exact elim 3 1 (by decide) (by decide) (by decide) (by decide)
  · exact elim 17 4 (by decide) (by decide) (by decide) (by decide)
  · exact elim 5 2 (by decide) (by decide) (by decide) (by decide)
  · exact elim 3 1 (by decide) (by decide) (by decide) (by decide)
  · exact elim 41 10 (by decide) (by decide) (by decide) (by decide)

private theorem character {m e : ℕ} {a : ℤ} (odd : Odd e)
    (h : (a : ZMod m)^e = 1) (b : ℕ) (div : b ∣ m) : jacobiSym a b = 1 := by
  have eq : a^e ≡ 1 [ZMOD m] := (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa using h)
  have red := eq.of_dvd (show (b:ℤ) ∣ m by exact_mod_cast div)
  have hj := jacobiSym.mod_left' red
  rw [jacobiSym.pow_left,jacobiSym.one_left] at hj
  rcases jacobiSym.trichotomy a b with hh|hh|hh <;> simp_all [odd.neg_one_pow,zero_pow odd.pos.ne']

/-- In the positive inner branch, every odd divisor of du is 1 or 7 mod 8. -/
def H1 : Prop := ∀ d u c : ℕ, 1 < d → Odd d → 3 ≤ u → Odd u → 97 ≤ c → c % 16 = 1 →
    2^d - 1 = (2*(d*u)+1)*c →
    (∀ b : ℕ, b ∣ d*u → Odd b → b%8 = 1 ∨ b%8 = 7) →
    (2 : ZMod (d*u))^(d/2) * ((c+1 : ℕ) : ZMod (d*u))^(u/2) = 1 →
    (2*(d*u)+1).Prime

/-- In the negative inner branch, every odd divisor of du is 1 or 3 mod 8. -/
def H2 : Prop := ∀ d u c : ℕ, 1 < d → Odd d → 3 ≤ u → Odd u → 73 ≤ c → c % 16 = 9 →
    2^d - 1 = (2*(d*u)+1)*c →
    (∀ b : ℕ, b ∣ d*u → Odd b → b%8 = 1 ∨ b%8 = 3) →
    (2 : ZMod (d*u))^(d/2) * ((c+1 : ℕ) : ZMod (d*u))^(u/2) = -1 →
    (2*(d*u)+1).Prime

theorem main : H1 → H2 → OMA.R_mo_296166_R1.H1 := by
  intro pos neg d u c hd od hu ou hc eq strong
  obtain ⟨hm4,hc8,large⟩ := shape hd od ou hc eq
  let m := d*u
  let h := m/2
  have hr : m%4=3 := hm4
  have mid : m=2*h+1 := by dsimp [h]; omega
  have oh : Odd h := Nat.odd_iff.mpr (by dsimp [h]; omega)
  have dh := Nat.div_add_mod d 2
  have uh := Nat.div_add_mod u 2
  have dmod := Nat.odd_iff.mp od
  have umod := Nat.odd_iff.mp ou
  have exp : h=d/2+d*(u/2) := by
    have e : d*u=2*(d/2+d*(u/2))+1 := by nlinarith [congrArg (d*·) uh]
    dsimp [h,m]; omega
  have ppos : 0 < 2^d := by positivity
  have ee : 2^d = (2*m+1)*c+1 := by change 2^d-1=(2*m+1)*c at eq; omega
  have eclear : 2^d = (2*c)*m + (c+1) := by rw [ee];ring
  have zd : (2 : ZMod m)^d = (c+1 : ℕ) := by
    have hh : 2^d ≡ c+1 [MOD m] := by rw [eclear]; simp [Nat.ModEq,Nat.add_mod]
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hh
  have short : (2 : ZMod m)^h = 2^(d/2)*((c+1:ℕ):ZMod m)^(u/2) := by
    rw [exp,pow_add,pow_mul,zd]
  have d4 : 4 ≤ d := by
    by_contra! h
    have he : d=3 := by omega
    subst d
    norm_num at ee
    have lo : c ≤ (2*m+1)*c := Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have c16 : (2*(m%8)+1)*(c%16)%16=15 := by
    have dv : 16 ∣ 2^d := pow_dvd_pow 2 d4
    have mod0 := Nat.mod_eq_zero_of_dvd dv
    rw [ee,Nat.add_mod,Nat.mul_mod] at mod0
    have hm : (2*m+1)%16 = 2*(m%8)+1 := by omega
    rw [hm] at mod0
    omega
  have cofac (p : ℕ) (div : p ∣ c) : (2 : ZMod p)^d = 1 := by
    have hm' : 2^d ≡ 1 [MOD p] := by
      rw [ee]; exact Nat.ModEq.add_right 1 (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_right div _))
    simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr hm'
  have no3 : ¬3 ∣ c := fun h => no_shared (by decide : Nat.Prime 3) (by decide) od (by decide : (2:ZMod 3)^1 = -1) (cofac 3 h)
  have no5 : ¬5 ∣ c := fun h => no_shared (by decide : Nat.Prime 5) (by decide) od (by decide : (2:ZMod 5)^2 = -1) (cofac 5 h)
  rcases OMA.R_mo_296166_R1.strong_sign strong mid oh with hp|hn
  · have divisors (b : ℕ) (div : b ∣ d*u) (ob : Odd b) : b%8=1 ∨ b%8=7 := by
      have hj := character (a:=2) oh (by simpa using hp) b div
      rw [jacobiSym.at_two ob,ZMod.χ₈_nat_eq_if_mod_eight] at hj
      split_ifs at hj <;> simp_all
    have mr := divisors m (dvd_refl _) (od.mul ou)
    have mr7 : m%8=7 := by omega
    rw [mr7] at c16
    have cr : c%16=1 := by omega
    have no49 : c ≠ 49 := by
      intro he
      have hv := cofac 7 (he ▸ (by decide : 7 ∣ 49))
      have horder : orderOf (2:ZMod 7) = 3 := by
        apply orderOf_eq_prime (by decide) (by decide)
      have three := orderOf_dvd_of_pow_eq_one hv
      rw [horder] at three
      have impossible := divisors 3 (dvd_mul_of_dvd_left three u) (by decide)
      norm_num at impossible
    have bound : 97 ≤ c := by
      by_contra! lt
      have he : c=49 ∨ c=65 ∨ c=81 := by omega
      rcases he with he|he|he
      · exact no49 he
      · exact no5 (he ▸ (by decide : 5 ∣ 65))
      · exact no3 (he ▸ (by decide : 3 ∣ 81))
    exact pos d u c hd od hu ou bound cr eq divisors (short ▸ hp)
  · have divisors (b : ℕ) (div : b ∣ d*u) (ob : Odd b) : b%8=1 ∨ b%8=3 := by
      have hn' : ((-2 : ℤ) : ZMod m)^h = 1 := by push_cast; rw [oh.neg_pow,hn]; simp
      have hj := character oh hn' b div
      rw [jacobiSym.at_neg_two ob,ZMod.χ₈'_nat_eq_if_mod_eight] at hj
      split_ifs at hj <;> simp_all
    have mr := divisors m (dvd_refl _) (od.mul ou)
    have mr3 : m%8=3 := by omega
    rw [mr3] at c16
    exact neg d u c hd od hu ou (by omega) (by omega) eq divisors (short ▸ hn)

end OMA.R_mo_296166_R1_H1_R1
