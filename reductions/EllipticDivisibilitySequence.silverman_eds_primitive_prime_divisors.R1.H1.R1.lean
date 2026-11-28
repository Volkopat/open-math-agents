import OMAReductions.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1
import Mathlib

/-! The Ward relation controls the support of each good prime. The two
remaining local statements treat multipliers prime to the residue
characteristic and one multiplication by that characteristic. -/
namespace OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H1_R1
open EllipticDivisibilitySequence

/-- Prime-to-p multipliers are units in the formal group parameter. -/
def H1 : Prop := ∀ W : ℤ → ℤ, IsNonsingularEDS W →
  (∀ i : ℤ, i ≠ 0 → W i ≠ 0) → ∃ S : Finset ℕ, ∀ p ∉ S, p.Prime →
  ∀ n k : ℕ, 0 < n → 0 < k → p ∣ (W n).natAbs → p.Coprime k →
    (W (↑(n*k):ℤ)).natAbs.factorization p = (W (n:ℤ)).natAbs.factorization p

/-- Multiplication by p raises the local valuation by one away from finitely many primes. -/
def H2 : Prop := ∀ W : ℤ → ℤ, IsNonsingularEDS W →
  (∀ i : ℤ, i ≠ 0 → W i ≠ 0) → ∃ S : Finset ℕ, ∀ p ∉ S, p.Prime →
  ∀ n : ℕ, 0 < n → p ∣ (W n).natAbs →
    (W (↑(n*p):ℤ)).natAbs.factorization p = (W (n:ℤ)).natAbs.factorization p + 1

/-- The least positive zero of W modulo p divides every other positive zero.
The single exceptional factor W(3) ensures the residue following that zero is nonzero. -/
theorem ward_rank {W : ℤ → ℤ} (hw : IsEllipticDvdSequence W) (h1 : W 1 = 1)
    {p : ℕ} (hp : p.Prime) (h3 : ¬ p ∣ (W 3).natAbs)
    (ex : ∃ n : ℕ, 0 < n ∧ p ∣ (W n).natAbs) :
    ∃ r : ℕ, 0 < r ∧ ∀ n : ℕ, 0 < n → (p ∣ (W n).natAbs ↔ r ∣ n) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let z (i : ℤ) : ZMod p := W i
  have zero (i : ℤ) : z i = 0 ↔ p ∣ (W i).natAbs := by
    change ((W i : ℤ) : ZMod p) = 0 ↔ _
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  have one : z 1 = 1 := by simp [z,h1]
  have three : z 3 ≠ 0 := fun e ↦ h3 ((zero _).mp e)
  have ward (a b : ℤ) : z (a+b)*z (a-b) =
      z (a+1)*z (a-1)*z b^2 - z (b+1)*z (b-1)*z a^2 := by
    have rel := hw.1 a b 1
    simp only [IsEllipticNet.rel, add_zero, h1, mul_one] at rel
    have eq : W (a+b)*W (a-b) =
        W (a+1)*W (a-1)*W b^2 - W (b+1)*W (b-1)*W a^2 := by
      linear_combination rel
    simpa only [Int.cast_mul, Int.cast_sub, Int.cast_pow,z] using
      congrArg (fun a : ℤ ↦ (a : ZMod p)) eq
  let r := Nat.find ex
  have hfound : 0 < r ∧ p ∣ (W r).natAbs := Nat.find_spec ex
  have zr : z (r : ℤ) = 0 := (zero _).mpr hfound.2
  have r2 : 2 ≤ r := by
    by_contra h
    have er : r = 1 := by omega
    simp [er,one] at zr
  have before (j : ℕ) (hj : 0 < j) (hjr : j < r) : z (j : ℤ) ≠ 0 := by
    intro e
    exact Nat.find_min ex hjr ⟨hj,(zero _).mp e⟩
  have zm : z ((r : ℤ)-1) ≠ 0 := by
    have eq : ((r-1 : ℕ) : ℤ) = (r:ℤ)-1 := by omega
    rw [← eq]
    exact before _ (by omega) (by omega)
  have adjacent (a : ℤ) (ha : z a ≠ 0) (hn : z (a+1)=0) : z (a+2) ≠ 0 := by
    intro h
    have v := ward a 2
    norm_num only [h,hn,show (2:ℤ)+1=3 by decide,show (2:ℤ)-1=1 by decide,one,
      mul_one,zero_mul] at v
    exact (mul_ne_zero three (pow_ne_zero 2 ha)) (by linear_combination v)
  have zp : z ((r:ℤ)+1) ≠ 0 := by
    have v := adjacent ((r:ℤ)-1) zm (by simpa using zr)
    simpa only [show (r:ℤ)-1+2=(r:ℤ)+1 by ring] using v
  have advance (a : ℤ) (ha : z a ≠ 0) : z (a+r) ≠ 0 := by
    intro h
    have v := ward a (r:ℤ)
    simp [h,zr,zp,zm,ha] at v
  have progression (j : ℕ) (hj : 0<j) (hjr : j<r) (k : ℕ) :
      z (↑(k*r+j):ℤ) ≠ 0 := by
    induction k with
    | zero => simpa using before j hj hjr
    | succ k ih =>
      have v := advance (↑(k*r+j):ℤ) ih
      have idx : (k+1)*r+j=(k*r+j)+r := by rw [Nat.add_mul,one_mul]; omega
      rw [idx,Nat.cast_add]
      exact v
  refine ⟨r,hfound.1,?_⟩
  intro n hn
  constructor
  · intro h
    by_contra hd
    have hm : n%r ≠ 0 := fun hz ↦ hd (Nat.dvd_of_mod_eq_zero hz)
    have bad := progression (n%r) (by omega) (Nat.mod_lt _ hfound.1) (n/r)
    have eq : n/r*r+n%r=n := by rw [Nat.mul_comm (n/r),Nat.div_add_mod]
    rw [eq] at bad
    exact bad ((zero _).mpr h)
  · intro h
    have hZ : (r:ℤ) ∣ (n:ℤ) := Int.natCast_dvd_natCast.mpr h
    have hW := hw.2 _ _ hZ
    rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs] at hfound ⊢
    exact dvd_trans hfound.2 hW

theorem main : H1 → H2 → OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1.H1 := by
  classical
  intro units prime W hw hn
  obtain ⟨A,hA⟩ := units W hw hn
  obtain ⟨B,hB⟩ := prime W hw hn
  refine ⟨(A ∪ B) ∪ (W 3).natAbs.primeFactors,?_⟩
  intro p hp hprime hex
  have outside : p ∉ A ∧ p ∉ B ∧ p ∉ (W 3).natAbs.primeFactors := by simpa [or_assoc] using hp
  have w3 : (W 3).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hn 3 (by decide))
  have no3 : ¬ p ∣ (W 3).natAbs := fun h ↦ outside.2.2 (Nat.mem_primeFactors.mpr ⟨hprime,h,w3⟩)
  obtain ⟨r,hr,rank⟩ := ward_rank hw.1 hw.2.1 hprime no3 hex
  refine ⟨r,hr,rank,?_⟩
  have powLift (e : ℕ) :
      (W (↑(r*p^e):ℤ)).natAbs.factorization p = (W (r:ℤ)).natAbs.factorization p + e := by
    induction e with
    | zero => simp
    | succ e ih =>
      have pos : 0 < r*p^e := Nat.mul_pos hr (pow_pos hprime.pos _)
      have step := hB p outside.2.1 hprime (r*p^e) pos
        ((rank _ pos).mpr (dvd_mul_right r _))
      rw [pow_succ,← Nat.mul_assoc,step,ih,Nat.add_assoc]
  intro k hk
  let e := k.factorization p
  let c := ordCompl[p] k
  have decomp : p^e*c=k := Nat.ordProj_mul_ordCompl_eq_self _ _
  have pos : 0 < r*p^e := Nat.mul_pos hr (pow_pos hprime.pos _)
  have unit := hA p outside.1 hprime (r*p^e) c pos (Nat.ordCompl_pos p hk.ne')
    ((rank _ pos).mpr (dvd_mul_right r _)) (Nat.coprime_ordCompl hprime hk.ne')
  have idx : r*p^e*c=r*k := by rw [Nat.mul_assoc,decomp]
  rw [idx] at unit
  exact unit.trans (powLift e)

end OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H1_R1
