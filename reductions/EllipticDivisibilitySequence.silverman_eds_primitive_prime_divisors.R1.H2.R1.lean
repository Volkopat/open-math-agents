import OMAReductions.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1
import Mathlib

/-! Compare the reduced denominator of the difference x(nP)−x(P) with
W(n)² using the Ward recurrence. Only primes dividing W(3) can cancel
a pair of consecutive positive-index terms. The global denominator
height and subquadratic contribution at each fixed prime are separate inputs. -/
namespace OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1
open EllipticDivisibilitySequence Filter Finset Real

/-- Global quadratic growth of the reduced denominator of the abscissa difference. -/
def H1 : Prop := ∀ W : ℤ → ℤ, IsNonsingularEDS W →
  (∀ i : ℤ, i ≠ 0 → W i ≠ 0) →
    let d (n : ℕ) := (W (n:ℤ)).natAbs^2 /
      Nat.gcd ((W (↑(n+1):ℤ)).natAbs * (W (↑(n-1):ℤ)).natAbs) ((W (n:ℤ)).natAbs^2)
    ∃ c : ℝ, 0<c ∧ Tendsto (fun n : ℕ ↦ log (d n)/(n:ℝ)^2) atTop (nhds c)

/-- A fixed finite place contributes subquadratically to that denominator. -/
def H2 : Prop := ∀ W : ℤ → ℤ, IsNonsingularEDS W →
  (∀ i : ℤ, i ≠ 0 → W i ≠ 0) →
    let d (n : ℕ) := (W (n:ℤ)).natAbs^2 /
      Nat.gcd ((W (↑(n+1):ℤ)).natAbs * (W (↑(n-1):ℤ)).natAbs) ((W (n:ℤ)).natAbs^2)
    ∀ p : ℕ, Tendsto (fun n : ℕ ↦ ((d n).factorization p:ℝ)/(n:ℝ)^2) atTop (nhds 0)

theorem noAdjacent {W : ℤ → ℤ} (hw : IsEllipticSequence W) (h1 : W 1=1)
    {p : ℕ} (hp : p.Prime) (h3 : ¬p ∣ (W 3).natAbs) (n : ℕ) (hn : 0<n) :
    ¬ (p ∣ (W (n:ℤ)).natAbs ∧ p ∣ (W (↑(n+1):ℤ)).natAbs) := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let z (a : ℤ) : ZMod p := W a
  have zero (a : ℤ) : z a=0 ↔ p ∣ (W a).natAbs := by
    change ((W a : ℤ) : ZMod p)=0 ↔ _
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  have one : z 1=1 := by simp [z,h1]
  have three : z 3≠0 := fun e ↦ h3 ((zero 3).mp e)
  have advance (a : ℤ) (h : z a≠0) (e : z (a+1)=0) : z (a+2)≠0 := by
    intro f
    have rel := hw a 2 1
    norm_num only [IsEllipticNet.rel,add_zero,h1,mul_one,
      show (2:ℤ)+1=3 by decide,show (2:ℤ)-1=1 by decide] at rel
    have v := congrArg (fun b : ℤ ↦ (b : ZMod p)) rel
    simp only [Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_zero] at v
    change z (a+2)*z (a-2) - z (a+1)*z (a-1)*z 2*z 2 + z 3*z a*z a = 0 at v
    simp [f,e,three,h] at v
  have step (k : ℕ) : ¬ (z ((k:ℤ)+1)=0 ∧ z ((k:ℤ)+2)=0) := by
    induction k with
    | zero => simp [one]
    | succ k ih =>
      intro h
      have e : z ((k:ℤ)+2)=0 := by simpa [Nat.cast_succ,add_assoc] using h.1
      have a : z ((k:ℤ)+1)≠0 := fun eq ↦ ih ⟨eq,e⟩
      have f := advance ((k:ℤ)+1) a (by simpa [add_assoc] using e)
      exact f (by simpa only [Nat.cast_succ] using h.2)
  cases n with
  | zero => omega
  | succ k =>
    intro ⟨a,b⟩
    exact step k ⟨by simpa using (zero _).mpr a,by simpa [Nat.cast_succ,add_assoc] using (zero _).mpr b⟩

theorem log_on_support (z : ℕ) (T : Finset ℕ) (h : z.primeFactors ⊆ T) :
    ∑ p ∈ T, (z.factorization p:ℝ)*log p = log z := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum, Nat.support_factorization]
  symm
  apply Finset.sum_subset h
  intro p hp hn
  have hz : z.factorization p=0 := Finsupp.notMem_support_iff.mp (by simpa using hn)
  simp [hz]

theorem main : H1 → H2 → OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1.H2 := by
  classical
  intro globalHeight localHeight W hw hn
  let w (n : ℕ) := (W (n:ℤ)).natAbs
  let g (n : ℕ) := Nat.gcd (w (n+1)*w (n-1)) (w n^2)
  let d (n : ℕ) := w n^2/g n
  obtain ⟨c,hc,lim⟩ := globalHeight W hw hn
  change Tendsto (fun n : ℕ ↦ log (d n)/(n:ℝ)^2) atTop (nhds c) at lim
  have loc (p : ℕ) : Tendsto (fun n : ℕ ↦ ((d n).factorization p:ℝ)/(n:ℝ)^2) atTop (nhds 0) :=
    localHeight W hw hn p
  let bad := (W 3).natAbs.primeFactors
  have w3 : (W 3).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr (hn 3 (by decide))
  refine ⟨bad,?_⟩
  intro S hS
  have factor (n p : ℕ) (hn2 : 2≤n) (pp : p.Prime) (hout : p ∉ S) :
      (d n).factorization p = 2 * (w n).factorization p := by
    have no3 : ¬ p ∣ (W 3).natAbs := fun h ↦ hout (hS (Nat.mem_primeFactors.mpr ⟨pp,h,w3⟩))
    have clean : ¬p ∣ g n := by
      intro h
      have a : p ∣ w n := pp.dvd_of_dvd_pow (h.trans (Nat.gcd_dvd_right _ _))
      have b := pp.dvd_mul.mp (h.trans (Nat.gcd_dvd_left (w (n+1)*w (n-1)) (w n^2)))
      rcases b with plus | minus
      · exact noAdjacent hw.1.1 hw.2.1 pp no3 n (by omega) ⟨a,plus⟩
      · apply noAdjacent hw.1.1 hw.2.1 pp no3 (n-1) (by omega)
        refine ⟨minus,?_⟩
        have idx : n-1+1=n := by omega
        simpa only [idx] using a
    dsimp only [d]
    rw [Nat.factorization_div (Nat.gcd_dvd_right _ _),Finsupp.tsub_apply,
      Nat.factorization_eq_zero_of_not_dvd clean, Nat.sub_zero, Nat.factorization_pow,
      Finsupp.smul_apply,nsmul_eq_mul]
    norm_num
  have removed : Tendsto (fun n : ℕ ↦ (∑ p ∈ S, ((d n).factorization p:ℝ)*log p)/(n:ℝ)^2)
      atTop (nhds 0) := by
    have each (p : ℕ) : Tendsto (fun n : ℕ ↦ ((d n).factorization p:ℝ)/(n:ℝ)^2 * log p)
        atTop (nhds 0) := by simpa using (loc p).mul_const (log p)
    have all := tendsto_finsetSum S (fun p _ ↦ each p)
    simp only [Finset.sum_const_zero] at all
    convert all using 1
    funext n
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p _
    ring
  refine ⟨c/2,by positivity,?_⟩
  have hlim := (lim.sub removed).div_const 2
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn2
  let T := (w n).primeFactors ∪ S
  have wpos : w n ≠ 0 := Int.natAbs_ne_zero.mpr (hn _ (by exact_mod_cast (show n≠0 by omega)))
  have sub : (d n).primeFactors ⊆ T := by
    intro p h
    obtain ⟨pp,pd,_⟩ := Nat.mem_primeFactors.mp h
    apply Finset.mem_union_left
    refine Nat.mem_primeFactors.mpr ⟨pp,?_,wpos⟩
    exact pp.dvd_of_dvd_pow (pd.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right _ _)))
  have split : (∑ p ∈ (w n).primeFactors \ S, ((d n).factorization p:ℝ)*log p) +
      (∑ p ∈ S, ((d n).factorization p:ℝ)*log p) = log (d n) := by
    rw [← Finset.sum_union Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union]
    exact log_on_support _ T sub
  have twice : (∑ p ∈ (w n).primeFactors \ S, ((d n).factorization p:ℝ)*log p) =
      2 * ∑ p ∈ (w n).primeFactors \ S, ((w n).factorization p:ℝ)*log p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpos,hout⟩ := Finset.mem_sdiff.mp hp
    rw [factor n p hn2 (Nat.prime_of_mem_primeFactors hpos) hout, Nat.cast_mul]
    push_cast
    ring
  change (log (d n)/(n:ℝ)^2 - (∑ p ∈ S, ((d n).factorization p:ℝ)*log p)/(n:ℝ)^2)/2 =
    (∑ p ∈ (w n).primeFactors \ S, ((w n).factorization p:ℝ)*log p)/(n:ℝ)^2
  rw [twice] at split
  rw [← split]
  ring

end OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1_H2_R1
