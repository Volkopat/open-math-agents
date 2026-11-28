import OMAStatements.S_oeis_a097703
import Mathlib

/-! Formalization of Amiram Eldar’s characterization of A097703. Unitary divisor sums are multiplicative on coprime inputs. Their comparison with ordinary divisor sums detects squarefreeness. -/
namespace Deldor14.Unitary
open Finset Nat OMA.S_oeis_a097703
open scoped ArithmeticFunction.sigma Pointwise
private def piece (n d : ℕ) := if d.Coprime (n/d) then d else 0
private theorem expanded (n : ℕ) : unitarySum n=∑ d ∈ n.divisors, piece n d := by
  simp [unitarySum,piece,Finset.sum_filter]
private theorem mult {m n : ℕ} (h : m.Coprime n) :
    unitarySum (m*n)=unitarySum m*unitarySum n := by
  rw [expanded, expanded, expanded, Nat.divisors_mul,Finset.mul_def,
    sum_image h.mul_injOn_divisors, sum_mul_sum, ← sum_product']
  apply sum_congr rfl
  rintro ⟨a,b⟩ hab
  obtain ⟨ham,hbn⟩ := mem_product.mp hab
  have ha := Nat.dvd_of_mem_divisors ham
  have hb := Nat.dvd_of_mem_divisors hbn
  have cross₁ := (h.coprime_dvd_left ha).coprime_dvd_right (Nat.div_dvd_of_dvd hb)
  have cross₂ := (h.symm.coprime_dvd_left hb).coprime_dvd_right (Nat.div_dvd_of_dvd ha)
  change piece (m*n) (a*b)=piece m a*piece n b
  simp only [piece,← Nat.div_mul_div_comm ha hb,Nat.coprime_mul_iff_left,Nat.coprime_mul_iff_right]
  split_ifs <;> simp_all
private theorem unit_le (n : ℕ) : unitarySum n ≤ ArithmeticFunction.sigma 1 n := by
  rw [expanded, ArithmeticFunction.sigma_one_apply]
  apply sum_le_sum
  intro d _
  dsimp [piece]
  split <;> omega
private theorem sigma_eq_iff {n : ℕ} (hn : 0<n) :
    ArithmeticFunction.sigma 1 n=unitarySum n ↔ Squarefree n := by
  constructor
  · intro eq
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp h
    have pd : p∣n := dvd_trans (dvd_mul_right p p) h
    have hpD : p ∈ n.divisors := Nat.mem_divisors.mpr ⟨pd,hn.ne'⟩
    have qd : p ∣ n/p := (Nat.dvd_div_iff_mul_dvd pd).mpr h
    have ncp : ¬p.Coprime (n/p) := hp.coprime_iff_not_dvd.not.mpr (not_not.mpr qd)
    have strict : unitarySum n < ArithmeticFunction.sigma 1 n := by
      rw [expanded, ArithmeticFunction.sigma_one_apply]
      apply sum_lt_sum
      · intro d _;dsimp [piece];split <;> omega
      · exact ⟨p,hpD,by simpa [piece,ncp] using hp.pos⟩
    omega
  · intro sq
    rw [expanded, ArithmeticFunction.sigma_one_apply]
    apply sum_congr rfl
    intro d hd
    have dv := Nat.dvd_of_mem_divisors hd
    have cp : d.Coprime (n/d) := Nat.coprime_of_squarefree_mul ((Nat.mul_div_cancel' dv).symm ▸ sq)
    simp [piece,cp]
private theorem unit_prime_power (p e : ℕ) (hp : p.Prime) (he : 0<e) :
    unitarySum (p^e)=1+p^e := by
  have pos := pow_pos hp.pos e
  have big := one_lt_pow₀ hp.one_lt he.ne'
  have seteq : (p^e).divisors.filter (fun d => d.Coprime ((p^e)/d))={1,p^e} := by
    ext d
    constructor
    · intro hd
      obtain ⟨mem,cop⟩ := mem_filter.mp hd
      obtain ⟨i,hi,rfl⟩ := (Nat.mem_divisors_prime_pow hp e).mp mem
      by_cases z : i=0
      · simp [z]
      by_cases t : i=e
      · simp [t]
      exfalso
      rw [Nat.pow_div hi hp.pos] at cop
      have a : p∣p^i := dvd_pow_self _ z
      have b : p∣p^(e-i) := dvd_pow_self _ (by omega)
      exact (hp.coprime_iff_not_dvd.mp (cop.coprime_dvd_left a)) b
    · simp only [mem_insert,mem_singleton]
      rintro (rfl|rfl)
      · exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd _,pos.ne'⟩,Nat.coprime_one_left _⟩
      · refine mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_refl _,pos.ne'⟩,?_⟩
        rw [Nat.div_self pos]
        exact Nat.coprime_one_right _
  rw [unitarySum,seteq]
  rw [sum_insert (by simpa using big.ne)]
  simp
private theorem three_sigma (e : ℕ) :
    2*ArithmeticFunction.sigma 1 (3^e)+1=3*3^e := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_three]
  induction e with
  | zero => norm_num
  | succ e ih => rw [sum_range_succ,pow_succ];omega
end Deldor14.Unitary

namespace Deldor14.Unitary
open Nat OMA.S_oeis_a097703
open scoped ArithmeticFunction.sigma
private theorem characterization (j : ℕ) : occurs j ↔ 3 ∣ 2*j+1 ∨ ¬Squarefree (2*j+1) := by
  let t := 2*j+1
  have tp : 0<t := by dsimp [t];omega
  have two : Nat.Coprime 2 t := Nat.prime_two.coprime_iff_not_dvd.mpr (by dsimp [t];omega)
  have s4 : ArithmeticFunction.sigma 1 4=7 := by decide +kernel
  have u4 : unitarySum 4=5 := by decide +kernel
  change ArithmeticFunction.sigma 1 (216*j+108) ≠ 2*unitarySum (216*j+108) ↔ 3∣t ∨ ¬Squarefree t
  rw [show 216*j+108=108*t by dsimp [t];ring]
  by_cases h3 : 3∣t
  · simp only [h3,true_or,iff_true]
    let e := t.factorization 3
    let s := t/(3^e)
    have hprod : 3^e*s=t := Nat.ordProj_mul_ordCompl_eq_self t 3
    have sp : 0<s := Nat.ordCompl_pos 3 tp.ne'
    have se : e≠0 := (Nat.Prime.factorization_pos_of_dvd Nat.prime_three tp.ne' h3).ne'
    have cp3 : Nat.Coprime 3 s := Nat.coprime_ordCompl Nat.prime_three tp.ne'
    have cp4 : Nat.Coprime 4 s := (two.pow_left 2).coprime_dvd_right (Nat.ordCompl_dvd t 3)
    let k := e+3
    have ks : 4≤k := by dsimp [k];omega
    have p81 : 81≤3^k := (show (3:ℕ)^4≤3^k from Nat.pow_le_pow_right (by decide) ks)
    have cm : Nat.Coprime 4 (3^k) := (by decide : Nat.Coprime 4 3).pow_right _
    have cn : Nat.Coprime (4*3^k) s := cp4.mul_left (cp3.pow_left k)
    have fac : 108*t=(4*3^k)*s := by dsimp [k]; rw [← hprod,pow_add];ring
    rw [fac,ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cn,
      ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cm, mult cn,mult cm,
      s4,u4,unit_prime_power 3 k Nat.prime_three (by omega)]
    have a := three_sigma k
    have gap : 10*(1+3^k)<7*ArithmeticFunction.sigma 1 (3^k) := by omega
    have ps : 0<ArithmeticFunction.sigma 1 s := ArithmeticFunction.sigma_pos_iff.mpr sp
    exact ne_of_gt (calc
      2*(5*(1+3^k)*unitarySum s) = 10*(1+3^k)*unitarySum s := by ring
      _ ≤ 10*(1+3^k)*ArithmeticFunction.sigma 1 s := Nat.mul_le_mul_left _ (unit_le s)
      _ < _ := Nat.mul_lt_mul_of_pos_right gap ps)
  · have cp3 := Nat.prime_three.coprime_iff_not_dvd.mpr h3
    have cp : Nat.Coprime 108 t := (two.pow_left 2).mul_left (cp3.pow_left 3)
    have sig : ArithmeticFunction.sigma 1 108=280 := by decide +kernel
    have uni : unitarySum 108=140 := by decide +kernel
    simp only [h3,false_or,ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime cp,
      mult cp,sig,uni]
    rw [←sigma_eq_iff tp]
    omega

theorem full : type_of% @OMA.S_oeis_a097703.main := by
  refine ⟨fun k => (characterization _).mpr (Or.inl ⟨2*k+1,by ring⟩),characterization⟩
end Deldor14.Unitary
theorem OMA.solution : type_of% @OMA.S_oeis_a097703.main := Deldor14.Unitary.full
