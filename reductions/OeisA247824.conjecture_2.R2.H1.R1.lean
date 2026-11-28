import OMAReductions.R_OeisA247824_conjecture_2_R2

/-!
# Indexed primes in the divisibility witness for A247824

Khai-Hoan Nguyen-Dang's counterexample uses these two primes, whose sum is
exactly 31 times the sum of their proposed indices. Lucas certificates check
both primes. Only their absolute ranks remain as numerical hypotheses.
-/
namespace OMA.R_OeisA247824_conjecture_2_R2_H1_R1

private theorem even_power {p a e r s : ℕ}
    (old : (a : ZMod p)^e=(r : ZMod p)) (residue : (r*r)%p=s) :
    (a : ZMod p)^(2*e)=(s : ZMod p) := by
  rw [two_mul,pow_add,old,←Nat.cast_mul,←residue,ZMod.natCast_mod]

private theorem odd_power {p a e r s : ℕ}
    (old : (a : ZMod p)^e=(r : ZMod p)) (residue : (r*r*a)%p=s) :
    (a : ZMod p)^(2*e+1)=(s : ZMod p) := by
  rw [pow_succ,two_mul,pow_add,old,←Nat.cast_mul,←Nat.cast_mul,←residue,ZMod.natCast_mod]

private theorem nonunit_residue {p r : ℕ} (lo : 1<r) (hi : r<p) :
    (r : ZMod p) ≠ 1 := by
  intro h
  have eq : (r:ZMod p)=((1:ℕ):ZMod p) := by simpa only [Nat.cast_one] using h
  have red := (ZMod.natCast_eq_natCast_iff' r 1 p).mp eq
  rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (by omega : 1<p)] at red
  omega

private theorem prime2 : Nat.Prime 2 := by decide +kernel

private theorem prime3 : Nat.Prime 3 := by decide +kernel

private theorem prime11 : Nat.Prime 11 := by decide +kernel

private theorem prime13 : Nat.Prime 13 := by decide +kernel

private theorem prime17 : Nat.Prime 17 := by decide +kernel

private theorem prime167 : Nat.Prime 167 := by decide +kernel

private theorem prime251 : Nat.Prime 251 := by decide +kernel

private theorem prime331 : Nat.Prime 331 := by decide +kernel

private theorem pow503e0 : ((5:ℕ):ZMod 503)^0=((1:ℕ):ZMod 503) :=
  by simp

private theorem pow503e1 : ((5:ℕ):ZMod 503)^1=((5:ℕ):ZMod 503) :=
  odd_power (p:=503) (a:=5) (e:=0) (r:=1) pow503e0 rfl

private theorem pow503e2 : ((5:ℕ):ZMod 503)^2=((25:ℕ):ZMod 503) :=
  even_power (p:=503) (a:=5) (e:=1) (r:=5) pow503e1 rfl

private theorem pow503e3 : ((5:ℕ):ZMod 503)^3=((125:ℕ):ZMod 503) :=
  odd_power (p:=503) (a:=5) (e:=1) (r:=5) pow503e1 rfl

private theorem pow503e7 : ((5:ℕ):ZMod 503)^7=((160:ℕ):ZMod 503) :=
  odd_power (p:=503) (a:=5) (e:=3) (r:=125) pow503e3 rfl

private theorem pow503e15 : ((5:ℕ):ZMod 503)^15=((238:ℕ):ZMod 503) :=
  odd_power (p:=503) (a:=5) (e:=7) (r:=160) pow503e7 rfl

private theorem pow503e31 : ((5:ℕ):ZMod 503)^31=((31:ℕ):ZMod 503) :=
  odd_power (p:=503) (a:=5) (e:=15) (r:=238) pow503e15 rfl

private theorem pow503e62 : ((5:ℕ):ZMod 503)^62=((458:ℕ):ZMod 503) :=
  even_power (p:=503) (a:=5) (e:=31) (r:=31) pow503e31 rfl

private theorem pow503e125 : ((5:ℕ):ZMod 503)^125=((65:ℕ):ZMod 503) :=
  odd_power (p:=503) (a:=5) (e:=62) (r:=458) pow503e62 rfl

private theorem pow503e251 : ((5:ℕ):ZMod 503)^251=((502:ℕ):ZMod 503) :=
  odd_power (p:=503) (a:=5) (e:=125) (r:=65) pow503e125 rfl

private theorem pow503e502 : ((5:ℕ):ZMod 503)^502=((1:ℕ):ZMod 503) :=
  even_power (p:=503) (a:=5) (e:=251) (r:=502) pow503e251 rfl

private theorem prime503 : Nat.Prime 503 := by
  apply lucas_primality 503 ((5:ℕ):ZMod 503)
  · simpa only [Nat.cast_one] using pow503e502
  · intro q hq hd
    change q ∣ (2^1*(251^1)) at hd
    have which : q=2 ∨ q=251 := by
      rcases hq.dvd_mul.mp hd with part | hd
      · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime2 part)
      · apply Or.inr
        exact Nat.prime_eq_prime_of_dvd_pow hq prime251 hd
    rcases which with rfl | rfl
    · rw [show (503-1)/2=251 from rfl,pow503e251]
      exact nonunit_residue (p:=503) (r:=502) (by decide) (by decide)
    · rw [show (503-1)/251=2 from rfl,pow503e2]
      exact nonunit_residue (p:=503) (r:=25) (by decide) (by decide)

private theorem pow2593e0 : ((7:ℕ):ZMod 2593)^0=((1:ℕ):ZMod 2593) :=
  by simp

private theorem pow2593e1 : ((7:ℕ):ZMod 2593)^1=((7:ℕ):ZMod 2593) :=
  odd_power (p:=2593) (a:=7) (e:=0) (r:=1) pow2593e0 rfl

private theorem pow2593e2 : ((7:ℕ):ZMod 2593)^2=((49:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=1) (r:=7) pow2593e1 rfl

private theorem pow2593e3 : ((7:ℕ):ZMod 2593)^3=((343:ℕ):ZMod 2593) :=
  odd_power (p:=2593) (a:=7) (e:=1) (r:=7) pow2593e1 rfl

private theorem pow2593e5 : ((7:ℕ):ZMod 2593)^5=((1249:ℕ):ZMod 2593) :=
  odd_power (p:=2593) (a:=7) (e:=2) (r:=49) pow2593e2 rfl

private theorem pow2593e6 : ((7:ℕ):ZMod 2593)^6=((964:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=3) (r:=343) pow2593e3 rfl

private theorem pow2593e10 : ((7:ℕ):ZMod 2593)^10=((1608:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=5) (r:=1249) pow2593e5 rfl

private theorem pow2593e13 : ((7:ℕ):ZMod 2593)^13=((1828:ℕ):ZMod 2593) :=
  odd_power (p:=2593) (a:=7) (e:=6) (r:=964) pow2593e6 rfl

private theorem pow2593e20 : ((7:ℕ):ZMod 2593)^20=((443:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=10) (r:=1608) pow2593e10 rfl

private theorem pow2593e27 : ((7:ℕ):ZMod 2593)^27=((2228:ℕ):ZMod 2593) :=
  odd_power (p:=2593) (a:=7) (e:=13) (r:=1828) pow2593e13 rfl

private theorem pow2593e40 : ((7:ℕ):ZMod 2593)^40=((1774:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=20) (r:=443) pow2593e20 rfl

private theorem pow2593e54 : ((7:ℕ):ZMod 2593)^54=((982:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=27) (r:=2228) pow2593e27 rfl

private theorem pow2593e81 : ((7:ℕ):ZMod 2593)^81=((1997:ℕ):ZMod 2593) :=
  odd_power (p:=2593) (a:=7) (e:=40) (r:=1774) pow2593e40 rfl

private theorem pow2593e108 : ((7:ℕ):ZMod 2593)^108=((2321:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=54) (r:=982) pow2593e54 rfl

private theorem pow2593e162 : ((7:ℕ):ZMod 2593)^162=((2568:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=81) (r:=1997) pow2593e81 rfl

private theorem pow2593e216 : ((7:ℕ):ZMod 2593)^216=((1380:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=108) (r:=2321) pow2593e108 rfl

private theorem pow2593e324 : ((7:ℕ):ZMod 2593)^324=((625:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=162) (r:=2568) pow2593e162 rfl

private theorem pow2593e432 : ((7:ℕ):ZMod 2593)^432=((1138:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=216) (r:=1380) pow2593e216 rfl

private theorem pow2593e648 : ((7:ℕ):ZMod 2593)^648=((1675:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=324) (r:=625) pow2593e324 rfl

private theorem pow2593e864 : ((7:ℕ):ZMod 2593)^864=((1137:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=432) (r:=1138) pow2593e432 rfl

private theorem pow2593e1296 : ((7:ℕ):ZMod 2593)^1296=((2592:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=648) (r:=1675) pow2593e648 rfl

private theorem pow2593e2592 : ((7:ℕ):ZMod 2593)^2592=((1:ℕ):ZMod 2593) :=
  even_power (p:=2593) (a:=7) (e:=1296) (r:=2592) pow2593e1296 rfl

private theorem prime2593 : Nat.Prime 2593 := by
  apply lucas_primality 2593 ((7:ℕ):ZMod 2593)
  · simpa only [Nat.cast_one] using pow2593e2592
  · intro q hq hd
    change q ∣ (2^5*(3^4)) at hd
    have which : q=2 ∨ q=3 := by
      rcases hq.dvd_mul.mp hd with part | hd
      · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime2 part)
      · apply Or.inr
        exact Nat.prime_eq_prime_of_dvd_pow hq prime3 hd
    rcases which with rfl | rfl
    · rw [show (2593-1)/2=1296 from rfl,pow2593e1296]
      exact nonunit_residue (p:=2593) (r:=2592) (by decide) (by decide)
    · rw [show (2593-1)/3=864 from rfl,pow2593e864]
      exact nonunit_residue (p:=2593) (r:=1137) (by decide) (by decide)

private theorem pow11969e0 : ((3:ℕ):ZMod 11969)^0=((1:ℕ):ZMod 11969) :=
  by simp

private theorem pow11969e1 : ((3:ℕ):ZMod 11969)^1=((3:ℕ):ZMod 11969) :=
  odd_power (p:=11969) (a:=3) (e:=0) (r:=1) pow11969e0 rfl

private theorem pow11969e2 : ((3:ℕ):ZMod 11969)^2=((9:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=1) (r:=3) pow11969e1 rfl

private theorem pow11969e4 : ((3:ℕ):ZMod 11969)^4=((81:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=2) (r:=9) pow11969e2 rfl

private theorem pow11969e5 : ((3:ℕ):ZMod 11969)^5=((243:ℕ):ZMod 11969) :=
  odd_power (p:=11969) (a:=3) (e:=2) (r:=9) pow11969e2 rfl

private theorem pow11969e8 : ((3:ℕ):ZMod 11969)^8=((6561:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=4) (r:=81) pow11969e4 rfl

private theorem pow11969e11 : ((3:ℕ):ZMod 11969)^11=((9581:ℕ):ZMod 11969) :=
  odd_power (p:=11969) (a:=3) (e:=5) (r:=243) pow11969e5 rfl

private theorem pow11969e17 : ((3:ℕ):ZMod 11969)^17=((6622:ℕ):ZMod 11969) :=
  odd_power (p:=11969) (a:=3) (e:=8) (r:=6561) pow11969e8 rfl

private theorem pow11969e22 : ((3:ℕ):ZMod 11969)^22=((5300:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=11) (r:=9581) pow11969e11 rfl

private theorem pow11969e23 : ((3:ℕ):ZMod 11969)^23=((3931:ℕ):ZMod 11969) :=
  odd_power (p:=11969) (a:=3) (e:=11) (r:=9581) pow11969e11 rfl

private theorem pow11969e34 : ((3:ℕ):ZMod 11969)^34=((8437:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=17) (r:=6622) pow11969e17 rfl

private theorem pow11969e44 : ((3:ℕ):ZMod 11969)^44=((10726:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=22) (r:=5300) pow11969e22 rfl

private theorem pow11969e46 : ((3:ℕ):ZMod 11969)^46=((782:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=23) (r:=3931) pow11969e23 rfl

private theorem pow11969e68 : ((3:ℕ):ZMod 11969)^68=((3326:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=34) (r:=8437) pow11969e34 rfl

private theorem pow11969e88 : ((3:ℕ):ZMod 11969)^88=((1048:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=44) (r:=10726) pow11969e44 rfl

private theorem pow11969e93 : ((3:ℕ):ZMod 11969)^93=((3315:ℕ):ZMod 11969) :=
  odd_power (p:=11969) (a:=3) (e:=46) (r:=782) pow11969e46 rfl

private theorem pow11969e136 : ((3:ℕ):ZMod 11969)^136=((2920:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=68) (r:=3326) pow11969e68 rfl

private theorem pow11969e176 : ((3:ℕ):ZMod 11969)^176=((9125:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=88) (r:=1048) pow11969e88 rfl

private theorem pow11969e187 : ((3:ℕ):ZMod 11969)^187=((5049:ℕ):ZMod 11969) :=
  odd_power (p:=11969) (a:=3) (e:=93) (r:=3315) pow11969e93 rfl

private theorem pow11969e272 : ((3:ℕ):ZMod 11969)^272=((4472:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=136) (r:=2920) pow11969e136 rfl

private theorem pow11969e352 : ((3:ℕ):ZMod 11969)^352=((9261:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=176) (r:=9125) pow11969e176 rfl

private theorem pow11969e374 : ((3:ℕ):ZMod 11969)^374=((10400:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=187) (r:=5049) pow11969e187 rfl

private theorem pow11969e544 : ((3:ℕ):ZMod 11969)^544=((10554:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=272) (r:=4472) pow11969e272 rfl

private theorem pow11969e704 : ((3:ℕ):ZMod 11969)^704=((8236:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=352) (r:=9261) pow11969e352 rfl

private theorem pow11969e748 : ((3:ℕ):ZMod 11969)^748=((8116:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=374) (r:=10400) pow11969e374 rfl

private theorem pow11969e1088 : ((3:ℕ):ZMod 11969)^1088=((3402:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=544) (r:=10554) pow11969e544 rfl

private theorem pow11969e1496 : ((3:ℕ):ZMod 11969)^1496=((4049:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=748) (r:=8116) pow11969e748 rfl

private theorem pow11969e2992 : ((3:ℕ):ZMod 11969)^2992=((8840:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=1496) (r:=4049) pow11969e1496 rfl

private theorem pow11969e5984 : ((3:ℕ):ZMod 11969)^5984=((11968:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=2992) (r:=8840) pow11969e2992 rfl

private theorem pow11969e11968 : ((3:ℕ):ZMod 11969)^11968=((1:ℕ):ZMod 11969) :=
  even_power (p:=11969) (a:=3) (e:=5984) (r:=11968) pow11969e5984 rfl

private theorem prime11969 : Nat.Prime 11969 := by
  apply lucas_primality 11969 ((3:ℕ):ZMod 11969)
  · simpa only [Nat.cast_one] using pow11969e11968
  · intro q hq hd
    change q ∣ (2^6*(11^1*(17^1))) at hd
    have which : q=2 ∨ q=11 ∨ q=17 := by
      rcases hq.dvd_mul.mp hd with part | hd
      · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime2 part)
      · apply Or.inr
        rcases hq.dvd_mul.mp hd with part | hd
        · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime11 part)
        · apply Or.inr
          exact Nat.prime_eq_prime_of_dvd_pow hq prime17 hd
    rcases which with rfl | rfl | rfl
    · rw [show (11969-1)/2=5984 from rfl,pow11969e5984]
      exact nonunit_residue (p:=11969) (r:=11968) (by decide) (by decide)
    · rw [show (11969-1)/11=1088 from rfl,pow11969e1088]
      exact nonunit_residue (p:=11969) (r:=3402) (by decide) (by decide)
    · rw [show (11969-1)/17=704 from rfl,pow11969e704]
      exact nonunit_residue (p:=11969) (r:=8236) (by decide) (by decide)

private theorem pow51637e0 : ((5:ℕ):ZMod 51637)^0=((1:ℕ):ZMod 51637) :=
  by simp

private theorem pow51637e1 : ((5:ℕ):ZMod 51637)^1=((5:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=0) (r:=1) pow51637e0 rfl

private theorem pow51637e2 : ((5:ℕ):ZMod 51637)^2=((25:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=1) (r:=5) pow51637e1 rfl

private theorem pow51637e3 : ((5:ℕ):ZMod 51637)^3=((125:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=1) (r:=5) pow51637e1 rfl

private theorem pow51637e4 : ((5:ℕ):ZMod 51637)^4=((625:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=2) (r:=25) pow51637e2 rfl

private theorem pow51637e6 : ((5:ℕ):ZMod 51637)^6=((15625:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=3) (r:=125) pow51637e3 rfl

private theorem pow51637e7 : ((5:ℕ):ZMod 51637)^7=((26488:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=3) (r:=125) pow51637e3 rfl

private theorem pow51637e8 : ((5:ℕ):ZMod 51637)^8=((29166:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=4) (r:=625) pow51637e4 rfl

private theorem pow51637e9 : ((5:ℕ):ZMod 51637)^9=((42556:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=4) (r:=625) pow51637e4 rfl

private theorem pow51637e12 : ((5:ℕ):ZMod 51637)^12=((889:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=6) (r:=15625) pow51637e6 rfl

private theorem pow51637e15 : ((5:ℕ):ZMod 51637)^15=((7851:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=7) (r:=26488) pow51637e7 rfl

private theorem pow51637e16 : ((5:ℕ):ZMod 51637)^16=((39255:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=8) (r:=29166) pow51637e8 rfl

private theorem pow51637e19 : ((5:ℕ):ZMod 51637)^19=((1360:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=9) (r:=42556) pow51637e9 rfl

private theorem pow51637e25 : ((5:ℕ):ZMod 51637)^25=((27193:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=12) (r:=889) pow51637e12 rfl

private theorem pow51637e31 : ((5:ℕ):ZMod 51637)^31=((21389:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=15) (r:=7851) pow51637e15 rfl

private theorem pow51637e33 : ((5:ℕ):ZMod 51637)^33=((18355:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=16) (r:=39255) pow51637e16 rfl

private theorem pow51637e39 : ((5:ℕ):ZMod 51637)^39=((4977:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=19) (r:=1360) pow51637e19 rfl

private theorem pow51637e50 : ((5:ℕ):ZMod 51637)^50=((17409:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=25) (r:=27193) pow51637e25 rfl

private theorem pow51637e62 : ((5:ℕ):ZMod 51637)^62=((37138:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=31) (r:=21389) pow51637e31 rfl

private theorem pow51637e67 : ((5:ℕ):ZMod 51637)^67=((27911:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=33) (r:=18355) pow51637e33 rfl

private theorem pow51637e78 : ((5:ℕ):ZMod 51637)^78=((36406:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=39) (r:=4977) pow51637e39 rfl

private theorem pow51637e100 : ((5:ℕ):ZMod 51637)^100=((15728:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=50) (r:=17409) pow51637e50 rfl

private theorem pow51637e124 : ((5:ℕ):ZMod 51637)^124=((6774:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=62) (r:=37138) pow51637e62 rfl

private theorem pow51637e134 : ((5:ℕ):ZMod 51637)^134=((28139:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=67) (r:=27911) pow51637e67 rfl

private theorem pow51637e156 : ((5:ℕ):ZMod 51637)^156=((29957:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=78) (r:=36406) pow51637e78 rfl

private theorem pow51637e201 : ((5:ℕ):ZMod 51637)^201=((40496:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=100) (r:=15728) pow51637e100 rfl

private theorem pow51637e248 : ((5:ℕ):ZMod 51637)^248=((33420:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=124) (r:=6774) pow51637e124 rfl

private theorem pow51637e268 : ((5:ℕ):ZMod 51637)^268=((1563:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=134) (r:=28139) pow51637e134 rfl

private theorem pow51637e403 : ((5:ℕ):ZMod 51637)^403=((35939:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=201) (r:=40496) pow51637e201 rfl

private theorem pow51637e496 : ((5:ℕ):ZMod 51637)^496=((39727:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=248) (r:=33420) pow51637e248 rfl

private theorem pow51637e537 : ((5:ℕ):ZMod 51637)^537=((28513:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=268) (r:=1563) pow51637e268 rfl

private theorem pow51637e806 : ((5:ℕ):ZMod 51637)^806=((15440:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=403) (r:=35939) pow51637e403 rfl

private theorem pow51637e993 : ((5:ℕ):ZMod 51637)^993=((6305:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=496) (r:=39727) pow51637e496 rfl

private theorem pow51637e1075 : ((5:ℕ):ZMod 51637)^1075=((39568:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=537) (r:=28513) pow51637e537 rfl

private theorem pow51637e1613 : ((5:ℕ):ZMod 51637)^1613=((31129:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=806) (r:=15440) pow51637e806 rfl

private theorem pow51637e1986 : ((5:ℕ):ZMod 51637)^1986=((44172:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=993) (r:=6305) pow51637e993 rfl

private theorem pow51637e2151 : ((5:ℕ):ZMod 51637)^2151=((15557:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=1075) (r:=39568) pow51637e1075 rfl

private theorem pow51637e3227 : ((5:ℕ):ZMod 51637)^3227=((25132:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=1613) (r:=31129) pow51637e1613 rfl

private theorem pow51637e3972 : ((5:ℕ):ZMod 51637)^3972=((9902:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=1986) (r:=44172) pow51637e1986 rfl

private theorem pow51637e4303 : ((5:ℕ):ZMod 51637)^4303=((39787:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=2151) (r:=15557) pow51637e2151 rfl

private theorem pow51637e6454 : ((5:ℕ):ZMod 51637)^6454=((45277:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=3227) (r:=25132) pow51637e3227 rfl

private theorem pow51637e8606 : ((5:ℕ):ZMod 51637)^8606=((21497:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=4303) (r:=39787) pow51637e4303 rfl

private theorem pow51637e12909 : ((5:ℕ):ZMod 51637)^12909=((37508:ℕ):ZMod 51637) :=
  odd_power (p:=51637) (a:=5) (e:=6454) (r:=45277) pow51637e6454 rfl

private theorem pow51637e17212 : ((5:ℕ):ZMod 51637)^17212=((21496:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=8606) (r:=21497) pow51637e8606 rfl

private theorem pow51637e25818 : ((5:ℕ):ZMod 51637)^25818=((51636:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=12909) (r:=37508) pow51637e12909 rfl

private theorem pow51637e51636 : ((5:ℕ):ZMod 51637)^51636=((1:ℕ):ZMod 51637) :=
  even_power (p:=51637) (a:=5) (e:=25818) (r:=51636) pow51637e25818 rfl

private theorem prime51637 : Nat.Prime 51637 := by
  apply lucas_primality 51637 ((5:ℕ):ZMod 51637)
  · simpa only [Nat.cast_one] using pow51637e51636
  · intro q hq hd
    change q ∣ (2^2*(3^1*(13^1*(331^1)))) at hd
    have which : q=2 ∨ q=3 ∨ q=13 ∨ q=331 := by
      rcases hq.dvd_mul.mp hd with part | hd
      · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime2 part)
      · apply Or.inr
        rcases hq.dvd_mul.mp hd with part | hd
        · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime3 part)
        · apply Or.inr
          rcases hq.dvd_mul.mp hd with part | hd
          · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime13 part)
          · apply Or.inr
            exact Nat.prime_eq_prime_of_dvd_pow hq prime331 hd
    rcases which with rfl | rfl | rfl | rfl
    · rw [show (51637-1)/2=25818 from rfl,pow51637e25818]
      exact nonunit_residue (p:=51637) (r:=51636) (by decide) (by decide)
    · rw [show (51637-1)/3=17212 from rfl,pow51637e17212]
      exact nonunit_residue (p:=51637) (r:=21496) (by decide) (by decide)
    · rw [show (51637-1)/13=3972 from rfl,pow51637e3972]
      exact nonunit_residue (p:=51637) (r:=9902) (by decide) (by decide)
    · rw [show (51637-1)/331=156 from rfl,pow51637e156]
      exact nonunit_residue (p:=51637) (r:=29957) (by decide) (by decide)

private theorem pow1579909e0 : ((2:ℕ):ZMod 1579909)^0=((1:ℕ):ZMod 1579909) :=
  by simp

private theorem pow1579909e1 : ((2:ℕ):ZMod 1579909)^1=((2:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=0) (r:=1) pow1579909e0 rfl

private theorem pow1579909e2 : ((2:ℕ):ZMod 1579909)^2=((4:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=1) (r:=2) pow1579909e1 rfl

private theorem pow1579909e3 : ((2:ℕ):ZMod 1579909)^3=((8:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=1) (r:=2) pow1579909e1 rfl

private theorem pow1579909e4 : ((2:ℕ):ZMod 1579909)^4=((16:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=2) (r:=4) pow1579909e2 rfl

private theorem pow1579909e6 : ((2:ℕ):ZMod 1579909)^6=((64:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=3) (r:=8) pow1579909e3 rfl

private theorem pow1579909e8 : ((2:ℕ):ZMod 1579909)^8=((256:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=4) (r:=16) pow1579909e4 rfl

private theorem pow1579909e12 : ((2:ℕ):ZMod 1579909)^12=((4096:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=6) (r:=64) pow1579909e6 rfl

private theorem pow1579909e16 : ((2:ℕ):ZMod 1579909)^16=((65536:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=8) (r:=256) pow1579909e8 rfl

private theorem pow1579909e17 : ((2:ℕ):ZMod 1579909)^17=((131072:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=8) (r:=256) pow1579909e8 rfl

private theorem pow1579909e24 : ((2:ℕ):ZMod 1579909)^24=((978126:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=12) (r:=4096) pow1579909e12 rfl

private theorem pow1579909e32 : ((2:ℕ):ZMod 1579909)^32=((774634:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=16) (r:=65536) pow1579909e16 rfl

private theorem pow1579909e33 : ((2:ℕ):ZMod 1579909)^33=((1549268:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=16) (r:=65536) pow1579909e16 rfl

private theorem pow1579909e35 : ((2:ℕ):ZMod 1579909)^35=((1457345:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=17) (r:=131072) pow1579909e17 rfl

private theorem pow1579909e48 : ((2:ℕ):ZMod 1579909)^48=((777836:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=24) (r:=978126) pow1579909e24 rfl

private theorem pow1579909e64 : ((2:ℕ):ZMod 1579909)^64=((496211:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=32) (r:=774634) pow1579909e32 rfl

private theorem pow1579909e66 : ((2:ℕ):ZMod 1579909)^66=((404935:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=33) (r:=1549268) pow1579909e33 rfl

private theorem pow1579909e70 : ((2:ℕ):ZMod 1579909)^70=((159324:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=35) (r:=1457345) pow1579909e35 rfl

private theorem pow1579909e96 : ((2:ℕ):ZMod 1579909)^96=((1111437:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=48) (r:=777836) pow1579909e48 rfl

private theorem pow1579909e128 : ((2:ℕ):ZMod 1579909)^128=((1278598:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=64) (r:=496211) pow1579909e64 rfl

private theorem pow1579909e132 : ((2:ℕ):ZMod 1579909)^132=((1498660:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=66) (r:=404935) pow1579909e66 rfl

private theorem pow1579909e140 : ((2:ℕ):ZMod 1579909)^140=((1318982:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=70) (r:=159324) pow1579909e70 rfl

private theorem pow1579909e192 : ((2:ℕ):ZMod 1579909)^192=((855594:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=96) (r:=1111437) pow1579909e96 rfl

private theorem pow1579909e257 : ((2:ℕ):ZMod 1579909)^257=((855890:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=128) (r:=1278598) pow1579909e128 rfl

private theorem pow1579909e280 : ((2:ℕ):ZMod 1579909)^280=((1460701:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=140) (r:=1318982) pow1579909e140 rfl

private theorem pow1579909e385 : ((2:ℕ):ZMod 1579909)^385=((1054189:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=192) (r:=855594) pow1579909e192 rfl

private theorem pow1579909e514 : ((2:ℕ):ZMod 1579909)^514=((765524:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=257) (r:=855890) pow1579909e257 rfl

private theorem pow1579909e561 : ((2:ℕ):ZMod 1579909)^561=((111527:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=280) (r:=1460701) pow1579909e280 rfl

private theorem pow1579909e771 : ((2:ℕ):ZMod 1579909)^771=((274970:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=385) (r:=1054189) pow1579909e385 rfl

private theorem pow1579909e1028 : ((2:ℕ):ZMod 1579909)^1028=((828660:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=514) (r:=765524) pow1579909e514 rfl

private theorem pow1579909e1122 : ((2:ℕ):ZMod 1579909)^1122=((1228081:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=561) (r:=111527) pow1579909e561 rfl

private theorem pow1579909e1542 : ((2:ℕ):ZMod 1579909)^1542=((375796:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=771) (r:=274970) pow1579909e771 rfl

private theorem pow1579909e2057 : ((2:ℕ):ZMod 1579909)^2057=((1513951:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=1028) (r:=828660) pow1579909e1028 rfl

private theorem pow1579909e2244 : ((2:ℕ):ZMod 1579909)^2244=((231252:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=1122) (r:=1228081) pow1579909e1122 rfl

private theorem pow1579909e3085 : ((2:ℕ):ZMod 1579909)^3085=((195575:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=1542) (r:=375796) pow1579909e1542 rfl

private theorem pow1579909e4114 : ((2:ℕ):ZMod 1579909)^4114=((968287:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=2057) (r:=1513951) pow1579909e2057 rfl

private theorem pow1579909e4488 : ((2:ℕ):ZMod 1579909)^4488=((727672:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=2244) (r:=231252) pow1579909e2244 rfl

private theorem pow1579909e6171 : ((2:ℕ):ZMod 1579909)^6171=((1547379:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=3085) (r:=195575) pow1579909e3085 rfl

private theorem pow1579909e8228 : ((2:ℕ):ZMod 1579909)^8228=((97318:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=4114) (r:=968287) pow1579909e4114 rfl

private theorem pow1579909e8976 : ((2:ℕ):ZMod 1579909)^8976=((38234:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=4488) (r:=727672) pow1579909e4488 rfl

private theorem pow1579909e12343 : ((2:ℕ):ZMod 1579909)^12343=((903649:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=6171) (r:=1547379) pow1579909e6171 rfl

private theorem pow1579909e16457 : ((2:ℕ):ZMod 1579909)^16457=((57247:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=8228) (r:=97318) pow1579909e8228 rfl

private theorem pow1579909e17953 : ((2:ℕ):ZMod 1579909)^17953=((845862:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=8976) (r:=38234) pow1579909e8976 rfl

private theorem pow1579909e24686 : ((2:ℕ):ZMod 1579909)^24686=((808824:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=12343) (r:=903649) pow1579909e12343 rfl

private theorem pow1579909e32914 : ((2:ℕ):ZMod 1579909)^32914=((487743:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=16457) (r:=57247) pow1579909e16457 rfl

private theorem pow1579909e35907 : ((2:ℕ):ZMod 1579909)^35907=((387154:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=17953) (r:=845862) pow1579909e17953 rfl

private theorem pow1579909e49372 : ((2:ℕ):ZMod 1579909)^49372=((183528:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=24686) (r:=808824) pow1579909e24686 rfl

private theorem pow1579909e65829 : ((2:ℕ):ZMod 1579909)^65829=((32566:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=32914) (r:=487743) pow1579909e32914 rfl

private theorem pow1579909e71814 : ((2:ℕ):ZMod 1579909)^71814=((672977:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=35907) (r:=387154) pow1579909e35907 rfl

private theorem pow1579909e98744 : ((2:ℕ):ZMod 1579909)^98744=((446813:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=49372) (r:=183528) pow1579909e49372 rfl

private theorem pow1579909e131659 : ((2:ℕ):ZMod 1579909)^131659=((850834:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=65829) (r:=32566) pow1579909e65829 rfl

private theorem pow1579909e143628 : ((2:ℕ):ZMod 1579909)^143628=((1328589:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=71814) (r:=672977) pow1579909e71814 rfl

private theorem pow1579909e197488 : ((2:ℕ):ZMod 1579909)^197488=((1395911:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=98744) (r:=446813) pow1579909e98744 rfl

private theorem pow1579909e263318 : ((2:ℕ):ZMod 1579909)^263318=((1031938:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=131659) (r:=850834) pow1579909e131659 rfl

private theorem pow1579909e394977 : ((2:ℕ):ZMod 1579909)^394977=((367995:ℕ):ZMod 1579909) :=
  odd_power (p:=1579909) (a:=2) (e:=197488) (r:=1395911) pow1579909e197488 rfl

private theorem pow1579909e526636 : ((2:ℕ):ZMod 1579909)^526636=((1031937:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=263318) (r:=1031938) pow1579909e263318 rfl

private theorem pow1579909e789954 : ((2:ℕ):ZMod 1579909)^789954=((1579908:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=394977) (r:=367995) pow1579909e394977 rfl

private theorem pow1579909e1579908 : ((2:ℕ):ZMod 1579909)^1579908=((1:ℕ):ZMod 1579909) :=
  even_power (p:=1579909) (a:=2) (e:=789954) (r:=1579908) pow1579909e789954 rfl

private theorem prime1579909 : Nat.Prime 1579909 := by
  apply lucas_primality 1579909 ((2:ℕ):ZMod 1579909)
  · simpa only [Nat.cast_one] using pow1579909e1579908
  · intro q hq hd
    change q ∣ (2^2*(3^1*(11^1*(11969^1)))) at hd
    have which : q=2 ∨ q=3 ∨ q=11 ∨ q=11969 := by
      rcases hq.dvd_mul.mp hd with part | hd
      · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime2 part)
      · apply Or.inr
        rcases hq.dvd_mul.mp hd with part | hd
        · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime3 part)
        · apply Or.inr
          rcases hq.dvd_mul.mp hd with part | hd
          · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime11 part)
          · apply Or.inr
            exact Nat.prime_eq_prime_of_dvd_pow hq prime11969 hd
    rcases which with rfl | rfl | rfl | rfl
    · rw [show (1579909-1)/2=789954 from rfl,pow1579909e789954]
      exact nonunit_residue (p:=1579909) (r:=1579908) (by decide) (by decide)
    · rw [show (1579909-1)/3=526636 from rfl,pow1579909e526636]
      exact nonunit_residue (p:=1579909) (r:=1031937) (by decide) (by decide)
    · rw [show (1579909-1)/11=143628 from rfl,pow1579909e143628]
      exact nonunit_residue (p:=1579909) (r:=1328589) (by decide) (by decide)
    · rw [show (1579909-1)/11969=132 from rfl,pow1579909e132]
      exact nonunit_residue (p:=1579909) (r:=1498660) (by decide) (by decide)

private theorem pow2608559e0 : ((7:ℕ):ZMod 2608559)^0=((1:ℕ):ZMod 2608559) :=
  by simp

private theorem pow2608559e1 : ((7:ℕ):ZMod 2608559)^1=((7:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=0) (r:=1) pow2608559e0 rfl

private theorem pow2608559e2 : ((7:ℕ):ZMod 2608559)^2=((49:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=1) (r:=7) pow2608559e1 rfl

private theorem pow2608559e3 : ((7:ℕ):ZMod 2608559)^3=((343:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=1) (r:=7) pow2608559e1 rfl

private theorem pow2608559e4 : ((7:ℕ):ZMod 2608559)^4=((2401:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=2) (r:=49) pow2608559e2 rfl

private theorem pow2608559e5 : ((7:ℕ):ZMod 2608559)^5=((16807:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=2) (r:=49) pow2608559e2 rfl

private theorem pow2608559e7 : ((7:ℕ):ZMod 2608559)^7=((823543:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=3) (r:=343) pow2608559e3 rfl

private theorem pow2608559e9 : ((7:ℕ):ZMod 2608559)^9=((1225222:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=4) (r:=2401) pow2608559e4 rfl

private theorem pow2608559e10 : ((7:ℕ):ZMod 2608559)^10=((750877:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=5) (r:=16807) pow2608559e5 rfl

private theorem pow2608559e15 : ((7:ℕ):ZMod 2608559)^15=((2389856:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=7) (r:=823543) pow2608559e7 rfl

private theorem pow2608559e19 : ((7:ℕ):ZMod 2608559)^19=((1823015:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=9) (r:=1225222) pow2608559e9 rfl

private theorem pow2608559e20 : ((7:ℕ):ZMod 2608559)^20=((2326869:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=10) (r:=750877) pow2608559e10 rfl

private theorem pow2608559e31 : ((7:ℕ):ZMod 2608559)^31=((642136:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=15) (r:=2389856) pow2608559e15 rfl

private theorem pow2608559e39 : ((7:ℕ):ZMod 2608559)^39=((1046508:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=19) (r:=1823015) pow2608559e19 rfl

private theorem pow2608559e40 : ((7:ℕ):ZMod 2608559)^40=((2108438:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=20) (r:=2326869) pow2608559e20 rfl

private theorem pow2608559e62 : ((7:ℕ):ZMod 2608559)^62=((1112807:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=31) (r:=642136) pow2608559e31 rfl

private theorem pow2608559e79 : ((7:ℕ):ZMod 2608559)^79=((650292:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=39) (r:=1046508) pow2608559e39 rfl

private theorem pow2608559e81 : ((7:ℕ):ZMod 2608559)^81=((561600:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=40) (r:=2108438) pow2608559e40 rfl

private theorem pow2608559e125 : ((7:ℕ):ZMod 2608559)^125=((1341234:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=62) (r:=1112807) pow2608559e62 rfl

private theorem pow2608559e159 : ((7:ℕ):ZMod 2608559)^159=((1563474:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=79) (r:=650292) pow2608559e79 rfl

private theorem pow2608559e162 : ((7:ℕ):ZMod 2608559)^162=((1516987:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=81) (r:=561600) pow2608559e81 rfl

private theorem pow2608559e251 : ((7:ℕ):ZMod 2608559)^251=((1033176:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=125) (r:=1341234) pow2608559e125 rfl

private theorem pow2608559e318 : ((7:ℕ):ZMod 2608559)^318=((1612484:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=159) (r:=1563474) pow2608559e159 rfl

private theorem pow2608559e324 : ((7:ℕ):ZMod 2608559)^324=((2285400:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=162) (r:=1516987) pow2608559e162 rfl

private theorem pow2608559e503 : ((7:ℕ):ZMod 2608559)^503=((835953:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=251) (r:=1033176) pow2608559e251 rfl

private theorem pow2608559e636 : ((7:ℕ):ZMod 2608559)^636=((2598534:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=318) (r:=1612484) pow2608559e318 rfl

private theorem pow2608559e648 : ((7:ℕ):ZMod 2608559)^648=((688275:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=324) (r:=2285400) pow2608559e324 rfl

private theorem pow2608559e1006 : ((7:ℕ):ZMod 2608559)^1006=((113463:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=503) (r:=835953) pow2608559e503 rfl

private theorem pow2608559e1273 : ((7:ℕ):ZMod 2608559)^1273=((1802004:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=636) (r:=2598534) pow2608559e636 rfl

private theorem pow2608559e1296 : ((7:ℕ):ZMod 2608559)^1296=((335548:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=648) (r:=688275) pow2608559e648 rfl

private theorem pow2608559e2547 : ((7:ℕ):ZMod 2608559)^2547=((2283937:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=1273) (r:=1802004) pow2608559e1273 rfl

private theorem pow2608559e2593 : ((7:ℕ):ZMod 2608559)^2593=((2422986:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=1296) (r:=335548) pow2608559e1296 rfl

private theorem pow2608559e5094 : ((7:ℕ):ZMod 2608559)^5094=((1484961:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=2547) (r:=2283937) pow2608559e2547 rfl

private theorem pow2608559e5186 : ((7:ℕ):ZMod 2608559)^5186=((1750970:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=2593) (r:=2422986) pow2608559e2593 rfl

private theorem pow2608559e10189 : ((7:ℕ):ZMod 2608559)^10189=((2384879:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=5094) (r:=1484961) pow2608559e5094 rfl

private theorem pow2608559e20379 : ((7:ℕ):ZMod 2608559)^20379=((1456901:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=10189) (r:=2384879) pow2608559e10189 rfl

private theorem pow2608559e40758 : ((7:ℕ):ZMod 2608559)^40758=((2151091:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=20379) (r:=1456901) pow2608559e20379 rfl

private theorem pow2608559e81517 : ((7:ℕ):ZMod 2608559)^81517=((756917:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=40758) (r:=2151091) pow2608559e40758 rfl

private theorem pow2608559e163034 : ((7:ℕ):ZMod 2608559)^163034=((314601:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=81517) (r:=756917) pow2608559e81517 rfl

private theorem pow2608559e326069 : ((7:ℕ):ZMod 2608559)^326069=((1513920:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=163034) (r:=314601) pow2608559e163034 rfl

private theorem pow2608559e652139 : ((7:ℕ):ZMod 2608559)^652139=((308318:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=326069) (r:=1513920) pow2608559e326069 rfl

private theorem pow2608559e1304279 : ((7:ℕ):ZMod 2608559)^1304279=((2608558:ℕ):ZMod 2608559) :=
  odd_power (p:=2608559) (a:=7) (e:=652139) (r:=308318) pow2608559e652139 rfl

private theorem pow2608559e2608558 : ((7:ℕ):ZMod 2608559)^2608558=((1:ℕ):ZMod 2608559) :=
  even_power (p:=2608559) (a:=7) (e:=1304279) (r:=2608558) pow2608559e1304279 rfl

private theorem prime2608559 : Nat.Prime 2608559 := by
  apply lucas_primality 2608559 ((7:ℕ):ZMod 2608559)
  · simpa only [Nat.cast_one] using pow2608559e2608558
  · intro q hq hd
    change q ∣ (2^1*(503^1*(2593^1))) at hd
    have which : q=2 ∨ q=503 ∨ q=2593 := by
      rcases hq.dvd_mul.mp hd with part | hd
      · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime2 part)
      · apply Or.inr
        rcases hq.dvd_mul.mp hd with part | hd
        · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime503 part)
        · apply Or.inr
          exact Nat.prime_eq_prime_of_dvd_pow hq prime2593 hd
    rcases which with rfl | rfl | rfl
    · rw [show (2608559-1)/2=1304279 from rfl,pow2608559e1304279]
      exact nonunit_residue (p:=2608559) (r:=2608558) (by decide) (by decide)
    · rw [show (2608559-1)/503=5186 from rfl,pow2608559e5186]
      exact nonunit_residue (p:=2608559) (r:=1750970) (by decide) (by decide)
    · rw [show (2608559-1)/2593=1006 from rfl,pow2608559e1006]
      exact nonunit_residue (p:=2608559) (r:=113463) (by decide) (by decide)

private theorem pow20868473e0 : ((3:ℕ):ZMod 20868473)^0=((1:ℕ):ZMod 20868473) :=
  by simp

private theorem pow20868473e1 : ((3:ℕ):ZMod 20868473)^1=((3:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=0) (r:=1) pow20868473e0 rfl

private theorem pow20868473e2 : ((3:ℕ):ZMod 20868473)^2=((9:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=1) (r:=3) pow20868473e1 rfl

private theorem pow20868473e4 : ((3:ℕ):ZMod 20868473)^4=((81:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=2) (r:=9) pow20868473e2 rfl

private theorem pow20868473e8 : ((3:ℕ):ZMod 20868473)^8=((6561:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=4) (r:=81) pow20868473e4 rfl

private theorem pow20868473e9 : ((3:ℕ):ZMod 20868473)^9=((19683:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=4) (r:=81) pow20868473e4 rfl

private theorem pow20868473e19 : ((3:ℕ):ZMod 20868473)^19=((14495452:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=9) (r:=19683) pow20868473e9 rfl

private theorem pow20868473e39 : ((3:ℕ):ZMod 20868473)^39=((17638059:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=19) (r:=14495452) pow20868473e19 rfl

private theorem pow20868473e79 : ((3:ℕ):ZMod 20868473)^79=((7587372:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=39) (r:=17638059) pow20868473e39 rfl

private theorem pow20868473e159 : ((3:ℕ):ZMod 20868473)^159=((18031953:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=79) (r:=7587372) pow20868473e79 rfl

private theorem pow20868473e318 : ((3:ℕ):ZMod 20868473)^318=((5945250:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=159) (r:=18031953) pow20868473e159 rfl

private theorem pow20868473e636 : ((3:ℕ):ZMod 20868473)^636=((550277:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=318) (r:=5945250) pow20868473e318 rfl

private theorem pow20868473e1273 : ((3:ℕ):ZMod 20868473)^1273=((9700497:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=636) (r:=550277) pow20868473e636 rfl

private theorem pow20868473e2547 : ((3:ℕ):ZMod 20868473)^2547=((10710864:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=1273) (r:=9700497) pow20868473e1273 rfl

private theorem pow20868473e5094 : ((3:ℕ):ZMod 20868473)^5094=((13734620:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=2547) (r:=10710864) pow20868473e2547 rfl

private theorem pow20868473e10189 : ((3:ℕ):ZMod 20868473)^10189=((11851676:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=5094) (r:=13734620) pow20868473e5094 rfl

private theorem pow20868473e20379 : ((3:ℕ):ZMod 20868473)^20379=((10105955:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=10189) (r:=11851676) pow20868473e10189 rfl

private theorem pow20868473e40758 : ((3:ℕ):ZMod 20868473)^40758=((19600025:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=20379) (r:=10105955) pow20868473e20379 rfl

private theorem pow20868473e81517 : ((3:ℕ):ZMod 20868473)^81517=((3181212:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=40758) (r:=19600025) pow20868473e40758 rfl

private theorem pow20868473e163034 : ((3:ℕ):ZMod 20868473)^163034=((6413013:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=81517) (r:=3181212) pow20868473e81517 rfl

private theorem pow20868473e326069 : ((3:ℕ):ZMod 20868473)^326069=((14271486:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=163034) (r:=6413013) pow20868473e163034 rfl

private theorem pow20868473e652139 : ((3:ℕ):ZMod 20868473)^652139=((11827754:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=326069) (r:=14271486) pow20868473e326069 rfl

private theorem pow20868473e1304279 : ((3:ℕ):ZMod 20868473)^1304279=((14494384:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=652139) (r:=11827754) pow20868473e652139 rfl

private theorem pow20868473e2608559 : ((3:ℕ):ZMod 20868473)^2608559=((19776838:ℕ):ZMod 20868473) :=
  odd_power (p:=20868473) (a:=3) (e:=1304279) (r:=14494384) pow20868473e1304279 rfl

private theorem pow20868473e5217118 : ((3:ℕ):ZMod 20868473)^5217118=((14559506:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=2608559) (r:=19776838) pow20868473e2608559 rfl

private theorem pow20868473e10434236 : ((3:ℕ):ZMod 20868473)^10434236=((20868472:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=5217118) (r:=14559506) pow20868473e5217118 rfl

private theorem pow20868473e20868472 : ((3:ℕ):ZMod 20868473)^20868472=((1:ℕ):ZMod 20868473) :=
  even_power (p:=20868473) (a:=3) (e:=10434236) (r:=20868472) pow20868473e10434236 rfl

private theorem prime20868473 : Nat.Prime 20868473 := by
  apply lucas_primality 20868473 ((3:ℕ):ZMod 20868473)
  · simpa only [Nat.cast_one] using pow20868473e20868472
  · intro q hq hd
    change q ∣ (2^3*(2608559^1)) at hd
    have which : q=2 ∨ q=2608559 := by
      rcases hq.dvd_mul.mp hd with part | hd
      · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime2 part)
      · apply Or.inr
        exact Nat.prime_eq_prime_of_dvd_pow hq prime2608559 hd
    rcases which with rfl | rfl
    · rw [show (20868473-1)/2=10434236 from rfl,pow20868473e10434236]
      exact nonunit_residue (p:=20868473) (r:=20868472) (by decide) (by decide)
    · rw [show (20868473-1)/2608559=8 from rfl,pow20868473e8]
      exact nonunit_residue (p:=20868473) (r:=6561) (by decide) (by decide)

private theorem pow81744924555067e0 : ((2:ℕ):ZMod 81744924555067)^0=((1:ℕ):ZMod 81744924555067) :=
  by simp

private theorem pow81744924555067e1 : ((2:ℕ):ZMod 81744924555067)^1=((2:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=0) (r:=1) pow81744924555067e0 rfl

private theorem pow81744924555067e2 : ((2:ℕ):ZMod 81744924555067)^2=((4:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=1) (r:=2) pow81744924555067e1 rfl

private theorem pow81744924555067e3 : ((2:ℕ):ZMod 81744924555067)^3=((8:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1) (r:=2) pow81744924555067e1 rfl

private theorem pow81744924555067e4 : ((2:ℕ):ZMod 81744924555067)^4=((16:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=2) (r:=4) pow81744924555067e2 rfl

private theorem pow81744924555067e5 : ((2:ℕ):ZMod 81744924555067)^5=((32:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=2) (r:=4) pow81744924555067e2 rfl

private theorem pow81744924555067e6 : ((2:ℕ):ZMod 81744924555067)^6=((64:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=3) (r:=8) pow81744924555067e3 rfl

private theorem pow81744924555067e7 : ((2:ℕ):ZMod 81744924555067)^7=((128:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=3) (r:=8) pow81744924555067e3 rfl

private theorem pow81744924555067e9 : ((2:ℕ):ZMod 81744924555067)^9=((512:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=4) (r:=16) pow81744924555067e4 rfl

private theorem pow81744924555067e11 : ((2:ℕ):ZMod 81744924555067)^11=((2048:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=5) (r:=32) pow81744924555067e5 rfl

private theorem pow81744924555067e12 : ((2:ℕ):ZMod 81744924555067)^12=((4096:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=6) (r:=64) pow81744924555067e6 rfl

private theorem pow81744924555067e14 : ((2:ℕ):ZMod 81744924555067)^14=((16384:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=7) (r:=128) pow81744924555067e7 rfl

private theorem pow81744924555067e18 : ((2:ℕ):ZMod 81744924555067)^18=((262144:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=9) (r:=512) pow81744924555067e9 rfl

private theorem pow81744924555067e23 : ((2:ℕ):ZMod 81744924555067)^23=((8388608:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=11) (r:=2048) pow81744924555067e11 rfl

private theorem pow81744924555067e24 : ((2:ℕ):ZMod 81744924555067)^24=((16777216:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=12) (r:=4096) pow81744924555067e12 rfl

private theorem pow81744924555067e28 : ((2:ℕ):ZMod 81744924555067)^28=((268435456:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=14) (r:=16384) pow81744924555067e14 rfl

private theorem pow81744924555067e37 : ((2:ℕ):ZMod 81744924555067)^37=((137438953472:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=18) (r:=262144) pow81744924555067e18 rfl

private theorem pow81744924555067e47 : ((2:ℕ):ZMod 81744924555067)^47=((58992563800261:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=23) (r:=8388608) pow81744924555067e23 rfl

private theorem pow81744924555067e49 : ((2:ℕ):ZMod 81744924555067)^49=((72480406090910:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=24) (r:=16777216) pow81744924555067e24 rfl

private theorem pow81744924555067e56 : ((2:ℕ):ZMod 81744924555067)^56=((40315504913909:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=28) (r:=268435456) pow81744924555067e28 rfl

private theorem pow81744924555067e74 : ((2:ℕ):ZMod 81744924555067)^74=((75149049923801:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=37) (r:=137438953472) pow81744924555067e37 rfl

private theorem pow81744924555067e94 : ((2:ℕ):ZMod 81744924555067)^94=((80484325286587:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=47) (r:=58992563800261) pow81744924555067e47 rfl

private theorem pow81744924555067e98 : ((2:ℕ):ZMod 81744924555067)^98=((61575336259387:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=49) (r:=72480406090910) pow81744924555067e49 rfl

private theorem pow81744924555067e99 : ((2:ℕ):ZMod 81744924555067)^99=((41405747963707:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=49) (r:=72480406090910) pow81744924555067e49 rfl

private theorem pow81744924555067e113 : ((2:ℕ):ZMod 81744924555067)^113=((72390679429522:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=56) (r:=40315504913909) pow81744924555067e56 rfl

private theorem pow81744924555067e148 : ((2:ℕ):ZMod 81744924555067)^148=((72884896863757:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=74) (r:=75149049923801) pow81744924555067e74 rfl

private theorem pow81744924555067e188 : ((2:ℕ):ZMod 81744924555067)^188=((56399636301845:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=94) (r:=80484325286587) pow81744924555067e94 rfl

private theorem pow81744924555067e197 : ((2:ℕ):ZMod 81744924555067)^197=((20655418605989:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=98) (r:=61575336259387) pow81744924555067e98 rfl

private theorem pow81744924555067e198 : ((2:ℕ):ZMod 81744924555067)^198=((41310837211978:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=99) (r:=41405747963707) pow81744924555067e99 rfl

private theorem pow81744924555067e227 : ((2:ℕ):ZMod 81744924555067)^227=((1250684744555:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=113) (r:=72390679429522) pow81744924555067e113 rfl

private theorem pow81744924555067e297 : ((2:ℕ):ZMod 81744924555067)^297=((73597900908467:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=148) (r:=72884896863757) pow81744924555067e148 rfl

private theorem pow81744924555067e377 : ((2:ℕ):ZMod 81744924555067)^377=((11820254830449:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=188) (r:=56399636301845) pow81744924555067e188 rfl

private theorem pow81744924555067e394 : ((2:ℕ):ZMod 81744924555067)^394=((74630968981544:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=197) (r:=20655418605989) pow81744924555067e197 rfl

private theorem pow81744924555067e396 : ((2:ℕ):ZMod 81744924555067)^396=((53289102260975:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=198) (r:=41310837211978) pow81744924555067e198 rfl

private theorem pow81744924555067e455 : ((2:ℕ):ZMod 81744924555067)^455=((37579054707386:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=227) (r:=1250684744555) pow81744924555067e227 rfl

private theorem pow81744924555067e594 : ((2:ℕ):ZMod 81744924555067)^594=((80932819898089:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=297) (r:=73597900908467) pow81744924555067e297 rfl

private theorem pow81744924555067e754 : ((2:ℕ):ZMod 81744924555067)^754=((76424597136434:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=377) (r:=11820254830449) pow81744924555067e377 rfl

private theorem pow81744924555067e789 : ((2:ℕ):ZMod 81744924555067)^789=((10500221673836:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=394) (r:=74630968981544) pow81744924555067e394 rfl

private theorem pow81744924555067e793 : ((2:ℕ):ZMod 81744924555067)^793=((4513697671242:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=396) (r:=53289102260975) pow81744924555067e396 rfl

private theorem pow81744924555067e911 : ((2:ℕ):ZMod 81744924555067)^911=((36882584400094:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=455) (r:=37579054707386) pow81744924555067e455 rfl

private theorem pow81744924555067e1189 : ((2:ℕ):ZMod 81744924555067)^1189=((23822589668888:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=594) (r:=80932819898089) pow81744924555067e594 rfl

private theorem pow81744924555067e1509 : ((2:ℕ):ZMod 81744924555067)^1509=((72936661521488:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=754) (r:=76424597136434) pow81744924555067e754 rfl

private theorem pow81744924555067e1578 : ((2:ℕ):ZMod 81744924555067)^1578=((220630259185:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=789) (r:=10500221673836) pow81744924555067e789 rfl

private theorem pow81744924555067e1586 : ((2:ℕ):ZMod 81744924555067)^1586=((56481346351360:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=793) (r:=4513697671242) pow81744924555067e793 rfl

private theorem pow81744924555067e1823 : ((2:ℕ):ZMod 81744924555067)^1823=((67257688069357:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=911) (r:=36882584400094) pow81744924555067e911 rfl

private theorem pow81744924555067e2379 : ((2:ℕ):ZMod 81744924555067)^2379=((68019696449177:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1189) (r:=23822589668888) pow81744924555067e1189 rfl

private theorem pow81744924555067e3019 : ((2:ℕ):ZMod 81744924555067)^3019=((80481254743587:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1509) (r:=72936661521488) pow81744924555067e1509 rfl

private theorem pow81744924555067e3157 : ((2:ℕ):ZMod 81744924555067)^3157=((69972535764197:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1578) (r:=220630259185) pow81744924555067e1578 rfl

private theorem pow81744924555067e3172 : ((2:ℕ):ZMod 81744924555067)^3172=((78408000688080:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=1586) (r:=56481346351360) pow81744924555067e1586 rfl

private theorem pow81744924555067e3646 : ((2:ℕ):ZMod 81744924555067)^3646=((27552050539501:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=1823) (r:=67257688069357) pow81744924555067e1823 rfl

private theorem pow81744924555067e4758 : ((2:ℕ):ZMod 81744924555067)^4758=((50898329423524:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=2379) (r:=68019696449177) pow81744924555067e2379 rfl

private theorem pow81744924555067e6038 : ((2:ℕ):ZMod 81744924555067)^6038=((41437463361900:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=3019) (r:=80481254743587) pow81744924555067e3019 rfl

private theorem pow81744924555067e6315 : ((2:ℕ):ZMod 81744924555067)^6315=((5220508613445:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=3157) (r:=69972535764197) pow81744924555067e3157 rfl

private theorem pow81744924555067e6344 : ((2:ℕ):ZMod 81744924555067)^6344=((39139223423040:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=3172) (r:=78408000688080) pow81744924555067e3172 rfl

private theorem pow81744924555067e7293 : ((2:ℕ):ZMod 81744924555067)^7293=((14155880595979:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=3646) (r:=27552050539501) pow81744924555067e3646 rfl

private theorem pow81744924555067e9516 : ((2:ℕ):ZMod 81744924555067)^9516=((37550888771845:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=4758) (r:=50898329423524) pow81744924555067e4758 rfl

private theorem pow81744924555067e12077 : ((2:ℕ):ZMod 81744924555067)^12077=((450710320707:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=6038) (r:=41437463361900) pow81744924555067e6038 rfl

private theorem pow81744924555067e12631 : ((2:ℕ):ZMod 81744924555067)^12631=((40691783693435:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=6315) (r:=5220508613445) pow81744924555067e6315 rfl

private theorem pow81744924555067e12688 : ((2:ℕ):ZMod 81744924555067)^12688=((63965858743482:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=6344) (r:=39139223423040) pow81744924555067e6344 rfl

private theorem pow81744924555067e14587 : ((2:ℕ):ZMod 81744924555067)^14587=((16418073089905:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=7293) (r:=14155880595979) pow81744924555067e7293 rfl

private theorem pow81744924555067e19032 : ((2:ℕ):ZMod 81744924555067)^19032=((32436852538077:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=9516) (r:=37550888771845) pow81744924555067e9516 rfl

private theorem pow81744924555067e24155 : ((2:ℕ):ZMod 81744924555067)^24155=((78878390767218:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=12077) (r:=450710320707) pow81744924555067e12077 rfl

private theorem pow81744924555067e25263 : ((2:ℕ):ZMod 81744924555067)^25263=((4881299812030:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=12631) (r:=40691783693435) pow81744924555067e12631 rfl

private theorem pow81744924555067e25376 : ((2:ℕ):ZMod 81744924555067)^25376=((1494605248311:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=12688) (r:=63965858743482) pow81744924555067e12688 rfl

private theorem pow81744924555067e29175 : ((2:ℕ):ZMod 81744924555067)^29175=((31608208366274:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=14587) (r:=16418073089905) pow81744924555067e14587 rfl

private theorem pow81744924555067e38065 : ((2:ℕ):ZMod 81744924555067)^38065=((22299010895923:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=19032) (r:=32436852538077) pow81744924555067e19032 rfl

private theorem pow81744924555067e48311 : ((2:ℕ):ZMod 81744924555067)^48311=((56750079580235:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=24155) (r:=78878390767218) pow81744924555067e24155 rfl

private theorem pow81744924555067e50527 : ((2:ℕ):ZMod 81744924555067)^50527=((22043082327294:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=25263) (r:=4881299812030) pow81744924555067e25263 rfl

private theorem pow81744924555067e50753 : ((2:ℕ):ZMod 81744924555067)^50753=((495440517681:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=25376) (r:=1494605248311) pow81744924555067e25376 rfl

private theorem pow81744924555067e58351 : ((2:ℕ):ZMod 81744924555067)^58351=((62602519457472:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=29175) (r:=31608208366274) pow81744924555067e29175 rfl

private theorem pow81744924555067e76130 : ((2:ℕ):ZMod 81744924555067)^76130=((41775197662676:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=38065) (r:=22299010895923) pow81744924555067e38065 rfl

private theorem pow81744924555067e96622 : ((2:ℕ):ZMod 81744924555067)^96622=((66288934445741:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=48311) (r:=56750079580235) pow81744924555067e48311 rfl

private theorem pow81744924555067e101055 : ((2:ℕ):ZMod 81744924555067)^101055=((42257943256128:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=50527) (r:=22043082327294) pow81744924555067e50527 rfl

private theorem pow81744924555067e101507 : ((2:ℕ):ZMod 81744924555067)^101507=((22196033577511:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=50753) (r:=495440517681) pow81744924555067e50753 rfl

private theorem pow81744924555067e116703 : ((2:ℕ):ZMod 81744924555067)^116703=((77158072346907:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=58351) (r:=62602519457472) pow81744924555067e58351 rfl

private theorem pow81744924555067e152261 : ((2:ℕ):ZMod 81744924555067)^152261=((38612932068007:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=76130) (r:=41775197662676) pow81744924555067e76130 rfl

private theorem pow81744924555067e193245 : ((2:ℕ):ZMod 81744924555067)^193245=((23116023125458:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=96622) (r:=66288934445741) pow81744924555067e96622 rfl

private theorem pow81744924555067e202110 : ((2:ℕ):ZMod 81744924555067)^202110=((14205134354564:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=101055) (r:=42257943256128) pow81744924555067e101055 rfl

private theorem pow81744924555067e203015 : ((2:ℕ):ZMod 81744924555067)^203015=((30180968402433:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=101507) (r:=22196033577511) pow81744924555067e101507 rfl

private theorem pow81744924555067e233407 : ((2:ℕ):ZMod 81744924555067)^233407=((52450114312356:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=116703) (r:=77158072346907) pow81744924555067e116703 rfl

private theorem pow81744924555067e304523 : ((2:ℕ):ZMod 81744924555067)^304523=((9091700031810:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=152261) (r:=38612932068007) pow81744924555067e152261 rfl

private theorem pow81744924555067e386491 : ((2:ℕ):ZMod 81744924555067)^386491=((63432999702227:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=193245) (r:=23116023125458) pow81744924555067e193245 rfl

private theorem pow81744924555067e404220 : ((2:ℕ):ZMod 81744924555067)^404220=((20965962563678:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=202110) (r:=14205134354564) pow81744924555067e202110 rfl

private theorem pow81744924555067e406031 : ((2:ℕ):ZMod 81744924555067)^406031=((7567681963583:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=203015) (r:=30180968402433) pow81744924555067e203015 rfl

private theorem pow81744924555067e466814 : ((2:ℕ):ZMod 81744924555067)^466814=((14720579484800:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=233407) (r:=52450114312356) pow81744924555067e233407 rfl

private theorem pow81744924555067e609047 : ((2:ℕ):ZMod 81744924555067)^609047=((62180994583351:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=304523) (r:=9091700031810) pow81744924555067e304523 rfl

private theorem pow81744924555067e772982 : ((2:ℕ):ZMod 81744924555067)^772982=((78614334383671:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=386491) (r:=63432999702227) pow81744924555067e386491 rfl

private theorem pow81744924555067e808441 : ((2:ℕ):ZMod 81744924555067)^808441=((58363577143674:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=404220) (r:=20965962563678) pow81744924555067e404220 rfl

private theorem pow81744924555067e812062 : ((2:ℕ):ZMod 81744924555067)^812062=((76611828049873:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=406031) (r:=7567681963583) pow81744924555067e406031 rfl

private theorem pow81744924555067e933629 : ((2:ℕ):ZMod 81744924555067)^933629=((29165229841138:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=466814) (r:=14720579484800) pow81744924555067e466814 rfl

private theorem pow81744924555067e1218094 : ((2:ℕ):ZMod 81744924555067)^1218094=((74510687695985:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=609047) (r:=62180994583351) pow81744924555067e609047 rfl

private theorem pow81744924555067e1545965 : ((2:ℕ):ZMod 81744924555067)^1545965=((10263012581595:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=772982) (r:=78614334383671) pow81744924555067e772982 rfl

private theorem pow81744924555067e1616883 : ((2:ℕ):ZMod 81744924555067)^1616883=((21971358731920:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=808441) (r:=58363577143674) pow81744924555067e808441 rfl

private theorem pow81744924555067e1624125 : ((2:ℕ):ZMod 81744924555067)^1624125=((45004804040559:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=812062) (r:=76611828049873) pow81744924555067e812062 rfl

private theorem pow81744924555067e1867258 : ((2:ℕ):ZMod 81744924555067)^1867258=((2256096940828:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=933629) (r:=29165229841138) pow81744924555067e933629 rfl

private theorem pow81744924555067e2436188 : ((2:ℕ):ZMod 81744924555067)^2436188=((74018884274875:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=1218094) (r:=74510687695985) pow81744924555067e1218094 rfl

private theorem pow81744924555067e3091931 : ((2:ℕ):ZMod 81744924555067)^3091931=((27708151771285:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1545965) (r:=10263012581595) pow81744924555067e1545965 rfl

private theorem pow81744924555067e3233767 : ((2:ℕ):ZMod 81744924555067)^3233767=((61009803219574:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1616883) (r:=21971358731920) pow81744924555067e1616883 rfl

private theorem pow81744924555067e3248251 : ((2:ℕ):ZMod 81744924555067)^3248251=((72379648279641:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1624125) (r:=45004804040559) pow81744924555067e1624125 rfl

private theorem pow81744924555067e3734516 : ((2:ℕ):ZMod 81744924555067)^3734516=((12721416901233:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=1867258) (r:=2256096940828) pow81744924555067e1867258 rfl

private theorem pow81744924555067e4872377 : ((2:ℕ):ZMod 81744924555067)^4872377=((60688582219939:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=2436188) (r:=74018884274875) pow81744924555067e2436188 rfl

private theorem pow81744924555067e6183862 : ((2:ℕ):ZMod 81744924555067)^6183862=((2768718594258:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=3091931) (r:=27708151771285) pow81744924555067e3091931 rfl

private theorem pow81744924555067e6467534 : ((2:ℕ):ZMod 81744924555067)^6467534=((77356582023297:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=3233767) (r:=61009803219574) pow81744924555067e3233767 rfl

private theorem pow81744924555067e6496502 : ((2:ℕ):ZMod 81744924555067)^6496502=((28595075236271:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=3248251) (r:=72379648279641) pow81744924555067e3248251 rfl

private theorem pow81744924555067e7469033 : ((2:ℕ):ZMod 81744924555067)^7469033=((21962540217672:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=3734516) (r:=12721416901233) pow81744924555067e3734516 rfl

private theorem pow81744924555067e9744754 : ((2:ℕ):ZMod 81744924555067)^9744754=((45493582670651:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=4872377) (r:=60688582219939) pow81744924555067e4872377 rfl

private theorem pow81744924555067e12367725 : ((2:ℕ):ZMod 81744924555067)^12367725=((30187187540570:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=6183862) (r:=2768718594258) pow81744924555067e6183862 rfl

private theorem pow81744924555067e12935068 : ((2:ℕ):ZMod 81744924555067)^12935068=((49943033091885:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=6467534) (r:=77356582023297) pow81744924555067e6467534 rfl

private theorem pow81744924555067e12993005 : ((2:ℕ):ZMod 81744924555067)^12993005=((34127797026252:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=6496502) (r:=28595075236271) pow81744924555067e6496502 rfl

private theorem pow81744924555067e14938066 : ((2:ℕ):ZMod 81744924555067)^14938066=((74253389275408:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=7469033) (r:=21962540217672) pow81744924555067e7469033 rfl

private theorem pow81744924555067e19489508 : ((2:ℕ):ZMod 81744924555067)^19489508=((36388844888557:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=9744754) (r:=45493582670651) pow81744924555067e9744754 rfl

private theorem pow81744924555067e24735450 : ((2:ℕ):ZMod 81744924555067)^24735450=((19178689804305:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=12367725) (r:=30187187540570) pow81744924555067e12367725 rfl

private theorem pow81744924555067e25870137 : ((2:ℕ):ZMod 81744924555067)^25870137=((64132231718434:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=12935068) (r:=49943033091885) pow81744924555067e12935068 rfl

private theorem pow81744924555067e25986011 : ((2:ℕ):ZMod 81744924555067)^25986011=((37993122336113:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=12993005) (r:=34127797026252) pow81744924555067e12993005 rfl

private theorem pow81744924555067e29876133 : ((2:ℕ):ZMod 81744924555067)^29876133=((28590865335130:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=14938066) (r:=74253389275408) pow81744924555067e14938066 rfl

private theorem pow81744924555067e38979017 : ((2:ℕ):ZMod 81744924555067)^38979017=((27667725615512:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=19489508) (r:=36388844888557) pow81744924555067e19489508 rfl

private theorem pow81744924555067e49470900 : ((2:ℕ):ZMod 81744924555067)^49470900=((33666779827055:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=24735450) (r:=19178689804305) pow81744924555067e24735450 rfl

private theorem pow81744924555067e51740274 : ((2:ℕ):ZMod 81744924555067)^51740274=((38783482990703:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=25870137) (r:=64132231718434) pow81744924555067e25870137 rfl

private theorem pow81744924555067e51972023 : ((2:ℕ):ZMod 81744924555067)^51972023=((6904350624650:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=25986011) (r:=37993122336113) pow81744924555067e25986011 rfl

private theorem pow81744924555067e59752266 : ((2:ℕ):ZMod 81744924555067)^59752266=((48367083051449:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=29876133) (r:=28590865335130) pow81744924555067e29876133 rfl

private theorem pow81744924555067e77958035 : ((2:ℕ):ZMod 81744924555067)^77958035=((69467912170009:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=38979017) (r:=27667725615512) pow81744924555067e38979017 rfl

private theorem pow81744924555067e98941801 : ((2:ℕ):ZMod 81744924555067)^98941801=((59934184987184:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=49470900) (r:=33666779827055) pow81744924555067e49470900 rfl

private theorem pow81744924555067e103944046 : ((2:ℕ):ZMod 81744924555067)^103944046=((25319026677023:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=51972023) (r:=6904350624650) pow81744924555067e51972023 rfl

private theorem pow81744924555067e119504532 : ((2:ℕ):ZMod 81744924555067)^119504532=((56059127487344:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=59752266) (r:=48367083051449) pow81744924555067e59752266 rfl

private theorem pow81744924555067e155916070 : ((2:ℕ):ZMod 81744924555067)^155916070=((44144446204012:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=77958035) (r:=69467912170009) pow81744924555067e77958035 rfl

private theorem pow81744924555067e197883602 : ((2:ℕ):ZMod 81744924555067)^197883602=((72698084111425:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=98941801) (r:=59934184987184) pow81744924555067e98941801 rfl

private theorem pow81744924555067e207888093 : ((2:ℕ):ZMod 81744924555067)^207888093=((44446102374571:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=103944046) (r:=25319026677023) pow81744924555067e103944046 rfl

private theorem pow81744924555067e239009065 : ((2:ℕ):ZMod 81744924555067)^239009065=((27993216504869:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=119504532) (r:=56059127487344) pow81744924555067e119504532 rfl

private theorem pow81744924555067e311832140 : ((2:ℕ):ZMod 81744924555067)^311832140=((27781428106083:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=155916070) (r:=44144446204012) pow81744924555067e155916070 rfl

private theorem pow81744924555067e395767204 : ((2:ℕ):ZMod 81744924555067)^395767204=((79055160243728:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=197883602) (r:=72698084111425) pow81744924555067e197883602 rfl

private theorem pow81744924555067e415776186 : ((2:ℕ):ZMod 81744924555067)^415776186=((79096950776694:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=207888093) (r:=44446102374571) pow81744924555067e207888093 rfl

private theorem pow81744924555067e478018131 : ((2:ℕ):ZMod 81744924555067)^478018131=((70772153761018:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=239009065) (r:=27993216504869) pow81744924555067e239009065 rfl

private theorem pow81744924555067e623664280 : ((2:ℕ):ZMod 81744924555067)^623664280=((47615042563191:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=311832140) (r:=27781428106083) pow81744924555067e311832140 rfl

private theorem pow81744924555067e791534409 : ((2:ℕ):ZMod 81744924555067)^791534409=((64920643429408:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=395767204) (r:=79055160243728) pow81744924555067e395767204 rfl

private theorem pow81744924555067e831552373 : ((2:ℕ):ZMod 81744924555067)^831552373=((58130041812726:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=415776186) (r:=79096950776694) pow81744924555067e415776186 rfl

private theorem pow81744924555067e956036262 : ((2:ℕ):ZMod 81744924555067)^956036262=((16558667320642:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=478018131) (r:=70772153761018) pow81744924555067e478018131 rfl

private theorem pow81744924555067e1247328560 : ((2:ℕ):ZMod 81744924555067)^1247328560=((39347179240759:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=623664280) (r:=47615042563191) pow81744924555067e623664280 rfl

private theorem pow81744924555067e1583068818 : ((2:ℕ):ZMod 81744924555067)^1583068818=((78448052943949:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=791534409) (r:=64920643429408) pow81744924555067e791534409 rfl

private theorem pow81744924555067e1663104747 : ((2:ℕ):ZMod 81744924555067)^1663104747=((25713166297404:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=831552373) (r:=58130041812726) pow81744924555067e831552373 rfl

private theorem pow81744924555067e1912072524 : ((2:ℕ):ZMod 81744924555067)^1912072524=((65761977768376:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=956036262) (r:=16558667320642) pow81744924555067e956036262 rfl

private theorem pow81744924555067e2494657121 : ((2:ℕ):ZMod 81744924555067)^2494657121=((45865723621532:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1247328560) (r:=39347179240759) pow81744924555067e1247328560 rfl

private theorem pow81744924555067e3326209495 : ((2:ℕ):ZMod 81744924555067)^3326209495=((671579866707:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1663104747) (r:=25713166297404) pow81744924555067e1663104747 rfl

private theorem pow81744924555067e3824145048 : ((2:ℕ):ZMod 81744924555067)^3824145048=((34747913464039:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=1912072524) (r:=65761977768376) pow81744924555067e1912072524 rfl

private theorem pow81744924555067e4989314242 : ((2:ℕ):ZMod 81744924555067)^4989314242=((73108196903819:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=2494657121) (r:=45865723621532) pow81744924555067e2494657121 rfl

private theorem pow81744924555067e6652418990 : ((2:ℕ):ZMod 81744924555067)^6652418990=((80195330201028:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=3326209495) (r:=671579866707) pow81744924555067e3326209495 rfl

private theorem pow81744924555067e7648290096 : ((2:ℕ):ZMod 81744924555067)^7648290096=((18454293733195:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=3824145048) (r:=34747913464039) pow81744924555067e3824145048 rfl

private theorem pow81744924555067e9978628485 : ((2:ℕ):ZMod 81744924555067)^9978628485=((16163703970215:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=4989314242) (r:=73108196903819) pow81744924555067e4989314242 rfl

private theorem pow81744924555067e13304837980 : ((2:ℕ):ZMod 81744924555067)^13304837980=((72862995305435:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=6652418990) (r:=80195330201028) pow81744924555067e6652418990 rfl

private theorem pow81744924555067e15296580193 : ((2:ℕ):ZMod 81744924555067)^15296580193=((33451022583171:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=7648290096) (r:=18454293733195) pow81744924555067e7648290096 rfl

private theorem pow81744924555067e19957256971 : ((2:ℕ):ZMod 81744924555067)^19957256971=((23840417280922:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=9978628485) (r:=16163703970215) pow81744924555067e9978628485 rfl

private theorem pow81744924555067e26609675961 : ((2:ℕ):ZMod 81744924555067)^26609675961=((73311237234090:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=13304837980) (r:=72862995305435) pow81744924555067e13304837980 rfl

private theorem pow81744924555067e30593160387 : ((2:ℕ):ZMod 81744924555067)^30593160387=((23393663650391:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=15296580193) (r:=33451022583171) pow81744924555067e15296580193 rfl

private theorem pow81744924555067e39914513942 : ((2:ℕ):ZMod 81744924555067)^39914513942=((11460133416197:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=19957256971) (r:=23840417280922) pow81744924555067e19957256971 rfl

private theorem pow81744924555067e53219351923 : ((2:ℕ):ZMod 81744924555067)^53219351923=((33850510379879:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=26609675961) (r:=73311237234090) pow81744924555067e26609675961 rfl

private theorem pow81744924555067e61186320774 : ((2:ℕ):ZMod 81744924555067)^61186320774=((28012205951620:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=30593160387) (r:=23393663650391) pow81744924555067e30593160387 rfl

private theorem pow81744924555067e79829027885 : ((2:ℕ):ZMod 81744924555067)^79829027885=((17095487758838:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=39914513942) (r:=11460133416197) pow81744924555067e39914513942 rfl

private theorem pow81744924555067e106438703847 : ((2:ℕ):ZMod 81744924555067)^106438703847=((79350179202868:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=53219351923) (r:=33850510379879) pow81744924555067e53219351923 rfl

private theorem pow81744924555067e122372641549 : ((2:ℕ):ZMod 81744924555067)^122372641549=((38425507887175:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=61186320774) (r:=28012205951620) pow81744924555067e61186320774 rfl

private theorem pow81744924555067e159658055771 : ((2:ℕ):ZMod 81744924555067)^159658055771=((39514695679693:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=79829027885) (r:=17095487758838) pow81744924555067e79829027885 rfl

private theorem pow81744924555067e212877407695 : ((2:ℕ):ZMod 81744924555067)^212877407695=((45311657392447:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=106438703847) (r:=79350179202868) pow81744924555067e106438703847 rfl

private theorem pow81744924555067e244745283099 : ((2:ℕ):ZMod 81744924555067)^244745283099=((9735159784736:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=122372641549) (r:=38425507887175) pow81744924555067e122372641549 rfl

private theorem pow81744924555067e319316111543 : ((2:ℕ):ZMod 81744924555067)^319316111543=((7027643081558:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=159658055771) (r:=39514695679693) pow81744924555067e159658055771 rfl

private theorem pow81744924555067e425754815390 : ((2:ℕ):ZMod 81744924555067)^425754815390=((58417135857613:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=212877407695) (r:=45311657392447) pow81744924555067e212877407695 rfl

private theorem pow81744924555067e489490566198 : ((2:ℕ):ZMod 81744924555067)^489490566198=((58627465893034:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=244745283099) (r:=9735159784736) pow81744924555067e244745283099 rfl

private theorem pow81744924555067e638632223086 : ((2:ℕ):ZMod 81744924555067)^638632223086=((44252112258402:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=319316111543) (r:=7027643081558) pow81744924555067e319316111543 rfl

private theorem pow81744924555067e851509630781 : ((2:ℕ):ZMod 81744924555067)^851509630781=((64407958545277:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=425754815390) (r:=58417135857613) pow81744924555067e425754815390 rfl

private theorem pow81744924555067e1277264446172 : ((2:ℕ):ZMod 81744924555067)^1277264446172=((66231746356778:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=638632223086) (r:=44252112258402) pow81744924555067e638632223086 rfl

private theorem pow81744924555067e1703019261563 : ((2:ℕ):ZMod 81744924555067)^1703019261563=((3080414949274:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=851509630781) (r:=64407958545277) pow81744924555067e851509630781 rfl

private theorem pow81744924555067e2554528892345 : ((2:ℕ):ZMod 81744924555067)^2554528892345=((70361907320742:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1277264446172) (r:=66231746356778) pow81744924555067e1277264446172 rfl

private theorem pow81744924555067e3406038523127 : ((2:ℕ):ZMod 81744924555067)^3406038523127=((81334888563838:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=1703019261563) (r:=3080414949274) pow81744924555067e1703019261563 rfl

private theorem pow81744924555067e5109057784691 : ((2:ℕ):ZMod 81744924555067)^5109057784691=((80092408364495:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=2554528892345) (r:=70361907320742) pow81744924555067e2554528892345 rfl

private theorem pow81744924555067e6812077046255 : ((2:ℕ):ZMod 81744924555067)^6812077046255=((24316322905925:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=3406038523127) (r:=81334888563838) pow81744924555067e3406038523127 rfl

private theorem pow81744924555067e10218115569383 : ((2:ℕ):ZMod 81744924555067)^10218115569383=((20686500059585:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=5109057784691) (r:=80092408364495) pow81744924555067e5109057784691 rfl

private theorem pow81744924555067e13624154092511 : ((2:ℕ):ZMod 81744924555067)^13624154092511=((124048919987:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=6812077046255) (r:=24316322905925) pow81744924555067e6812077046255 rfl

private theorem pow81744924555067e20436231138766 : ((2:ℕ):ZMod 81744924555067)^20436231138766=((53682332887450:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=10218115569383) (r:=20686500059585) pow81744924555067e10218115569383 rfl

private theorem pow81744924555067e27248308185022 : ((2:ℕ):ZMod 81744924555067)^27248308185022=((124048919986:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=13624154092511) (r:=124048919987) pow81744924555067e13624154092511 rfl

private theorem pow81744924555067e40872462277533 : ((2:ℕ):ZMod 81744924555067)^40872462277533=((81744924555066:ℕ):ZMod 81744924555067) :=
  odd_power (p:=81744924555067) (a:=2) (e:=20436231138766) (r:=53682332887450) pow81744924555067e20436231138766 rfl

private theorem pow81744924555067e81744924555066 : ((2:ℕ):ZMod 81744924555067)^81744924555066=((1:ℕ):ZMod 81744924555067) :=
  even_power (p:=81744924555067) (a:=2) (e:=40872462277533) (r:=81744924555066) pow81744924555067e40872462277533 rfl

private theorem prime81744924555067 : Nat.Prime 81744924555067 := by
  apply lucas_primality 81744924555067 ((2:ℕ):ZMod 81744924555067)
  · simpa only [Nat.cast_one] using pow81744924555067e81744924555066
  · intro q hq hd
    change q ∣ (2^1*(3^1*(167^1*(51637^1*(1579909^1))))) at hd
    have which : q=2 ∨ q=3 ∨ q=167 ∨ q=51637 ∨ q=1579909 := by
      rcases hq.dvd_mul.mp hd with part | hd
      · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime2 part)
      · apply Or.inr
        rcases hq.dvd_mul.mp hd with part | hd
        · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime3 part)
        · apply Or.inr
          rcases hq.dvd_mul.mp hd with part | hd
          · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime167 part)
          · apply Or.inr
            rcases hq.dvd_mul.mp hd with part | hd
            · exact Or.inl (Nat.prime_eq_prime_of_dvd_pow hq prime51637 part)
            · apply Or.inr
              exact Nat.prime_eq_prime_of_dvd_pow hq prime1579909 hd
    rcases which with rfl | rfl | rfl | rfl | rfl
    · rw [show (81744924555067-1)/2=40872462277533 from rfl,pow81744924555067e40872462277533]
      exact nonunit_residue (p:=81744924555067) (r:=81744924555066) (by decide) (by decide)
    · rw [show (81744924555067-1)/3=27248308185022 from rfl,pow81744924555067e27248308185022]
      exact nonunit_residue (p:=81744924555067) (r:=124048919986) (by decide) (by decide)
    · rw [show (81744924555067-1)/167=489490566198 from rfl,pow81744924555067e489490566198]
      exact nonunit_residue (p:=81744924555067) (r:=58627465893034) (by decide) (by decide)
    · rw [show (81744924555067-1)/51637=1583068818 from rfl,pow81744924555067e1583068818]
      exact nonunit_residue (p:=81744924555067) (r:=78448052943949) (by decide) (by decide)
    · rw [show (81744924555067-1)/1579909=51740274 from rfl,pow81744924555067e51740274]
      exact nonunit_residue (p:=81744924555067) (r:=38783482990703) (by decide) (by decide)

private theorem indexed {p n : ℕ} (pr : p.Prime) (rank : Nat.primeCounting p=n+1) :
    Nat.nth Nat.Prime n=p := by
  change Nat.count Nat.Prime (p+1)=n+1 at rank
  rw [Nat.count_succ,if_pos pr] at rank
  have e : Nat.count Nat.Prime p=n := by omega
  rw [←e,Nat.nth_count pr]

def H1 : Prop := Nat.primeCounting 20868473 = 1322164

def H2 : Prop := Nat.primeCounting 81744924555067 = 2636932401176

theorem main : H1 → H2 → OMA.R_OeisA247824_conjecture_2_R2.H1 := by
  intro smallRank largeRank
  change Nat.primeCounting 20868473=1322164 at smallRank
  change Nat.primeCounting 81744924555067=2636932401176 at largeRank
  have smallIndex : Nat.nth Nat.Prime 1322163=20868473 :=
    indexed (p:=20868473) (n:=1322163) prime20868473 smallRank
  have largeIndex : Nat.nth Nat.Prime 2636932401175=81744924555067 :=
    indexed (p:=81744924555067) (n:=2636932401175) prime81744924555067 largeRank
  refine ⟨smallIndex,?_⟩
  rw [largeIndex]
  exact ⟨31,rfl⟩

end OMA.R_OeisA247824_conjecture_2_R2_H1_R1
