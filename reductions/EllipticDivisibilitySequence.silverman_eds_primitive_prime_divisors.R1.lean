import FormalConjectures.Wikipedia.EllipticDivisibilitySequence
import Mathlib

/-!
A local rank-of-apparition formula and an archimedean height estimate imply
the primitive divisor theorem. Both inputs concern the part supported away
from a finite exceptional set, so they accommodate a change of model.
-/
namespace OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1

open EllipticDivisibilitySequence Filter Finset Real

/-- Good primes divide precisely the multiples of their first index, with
the usual additive valuation increment under multiplication of that index. -/
def H1 : Prop := ∀ W : ℤ → ℤ, IsNonsingularEDS W →
    (∀ n : ℤ, n ≠ 0 → W n ≠ 0) → ∃ S : Finset ℕ,
    ∀ p ∉ S, p.Prime → (∃ n : ℕ, 0 < n ∧ p ∣ (W n).natAbs) →
    ∃ r : ℕ, 0 < r ∧ (∀ n : ℕ, 0 < n → (p ∣ (W n).natAbs ↔ r ∣ n)) ∧
      ∀ k : ℕ, 0 < k → (W (↑(r*k):ℤ)).natAbs.factorization p =
        (W (r:ℤ)).natAbs.factorization p + k.factorization p

/-- After removing exceptional primes, the logarithmic size divided by
the square of the index tends to a positive height. Further finite
exclusions are allowed. -/
def H2 : Prop := ∀ W : ℤ → ℤ, IsNonsingularEDS W →
    (∀ n : ℤ, n ≠ 0 → W n ≠ 0) → ∃ S₀ : Finset ℕ, ∀ S : Finset ℕ, S₀ ⊆ S →
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ =>
      let z := (W n).natAbs
      (∑ p ∈ z.primeFactors \ S, (z.factorization p:ℝ)*log p)/(n:ℝ)^2)
      atTop (nhds c)


/-- An old prime can be charged to an immediate proper divisor, apart
from its valuation in the index itself. -/
theorem oldCharge {w : ℕ → ℕ} {p r n k : ℕ}
    (_hr : 0 < r) (hk : 0 < k) (hkn : k < n) (hpk : p ∣ w k) (hpn : p ∣ w n)
    (rank : ∀ m, 0 < m → (p ∣ w m ↔ r ∣ m))
    (lift : ∀ a : ℕ, 0 < a → (w (r*a)).factorization p =
        (w r).factorization p + a.factorization p) :
    ∃ q ∈ Finset.Icc 2 n, (w n).factorization p ≤
      n.factorization p + (w (n/q)).factorization p := by
  have hn : 0 < n := hk.trans hkn
  have rk : r ≤ k := Nat.le_of_dvd hk ((rank k hk).mp hpk)
  obtain ⟨a,ha⟩ := (rank n hn).mp hpn
  have a1 : 1 < a := by
    by_contra! h
    interval_cases a <;> simp_all
    omega
  obtain ⟨q,pq,dq⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
  obtain ⟨b,hb⟩ := dq
  have bp : 0 < b := by by_contra! h; simp_all
  have qn : q ≤ n := (Nat.le_of_dvd (by omega : 0 < a) ⟨b,hb⟩).trans
    (Nat.le_of_dvd hn ⟨r,by simpa [Nat.mul_comm] using ha⟩)
  have quo : n/q = r*b := by
    rw [ha,hb,show r*(q*b)=(r*b)*q by ring,Nat.mul_div_cancel _ pq.pos]
  have v := lift a (by omega)
  have small := lift b bp
  have va := (Nat.factorization_le_iff_dvd (by omega : a ≠ 0) hn.ne').mpr
    (show a ∣ n from ⟨r,by simpa [Nat.mul_comm] using ha⟩) p
  refine ⟨q,Finset.mem_Icc.mpr ⟨pq.two_le,qn⟩,?_⟩
  rw [quo,small]
  rw [←ha] at v
  omega

/-- Summing only selected primes cannot increase the log of the retained
part, even when the selected primes came from another sequence term. -/
theorem weightSubset (z : ℕ) (U S : Finset ℕ) (away : ∀ p ∈ U, p ∉ S) :
    ∑ p ∈ U, (z.factorization p:ℝ)*log p ≤
    ∑ p ∈ z.primeFactors \ S, (z.factorization p:ℝ)*log p := by
  classical
  let V := z.primeFactors \ S
  let f (p : ℕ) : ℝ := (z.factorization p:ℝ)*log p
  have non (p : ℕ) : 0 ≤ f p := mul_nonneg (by positivity) (log_natCast_nonneg p)
  have eqn : ∑ p ∈ U ∩ V, f p = ∑ p ∈ U, f p := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hp hnot
    have nf : p ∉ z.primeFactors := by
      intro hf
      exact hnot (Finset.mem_inter.mpr ⟨hp,Finset.mem_sdiff.mpr ⟨hf,away p hp⟩⟩)
    have zero : z.factorization p = 0 := by
      by_contra h
      exact nf (by change p ∈ z.factorization.support; exact Finsupp.mem_support_iff.mpr h)
    simp [f,zero]
  change ∑ p ∈ U, f p ≤ ∑ p ∈ V, f p
  rw [←eqn]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun p _ _ => non p)


/-- Without a new prime, the retained logarithm is bounded by the log of
the index plus the retained logarithms at smaller quotients. -/
theorem oldSum (w : ℕ → ℕ) (S : Finset ℕ) (n : ℕ)
    (charge : ∀ p ∈ (w n).primeFactors \ S, ∃ q ∈ Finset.Icc 2 n,
      (w n).factorization p ≤ n.factorization p + (w (n/q)).factorization p) :
    let L (m : ℕ) := ∑ p ∈ (w m).primeFactors \ S, ((w m).factorization p:ℝ)*log p
    L n ≤ log n + ∑ q ∈ Finset.Icc 2 n, L (n/q) := by
  classical
  let U := (w n).primeFactors \ S
  let Q := Finset.Icc 2 n
  let f (z p : ℕ) : ℝ := (z.factorization p:ℝ)*log p
  let L (m : ℕ) := ∑ p ∈ (w m).primeFactors \ S, f (w m) p
  have non (z p : ℕ) : 0 ≤ f z p := mul_nonneg (by positivity) (log_natCast_nonneg p)
  have away : ∀ p ∈ U, p ∉ S := fun _ hp => (Finset.mem_sdiff.mp hp).2
  have single (p : ℕ) (hp : p ∈ U) :
      f (w n) p ≤ f n p + ∑ q ∈ Q, f (w (n/q)) p := by
    obtain ⟨q,hq,h⟩ := charge p hp
    have v : ((w n).factorization p:ℝ) ≤ (n.factorization p:ℝ)+((w (n/q)).factorization p:ℝ) := by exact_mod_cast h
    have pick := Finset.single_le_sum (f := fun i => f (w (n/i)) p) (fun i _ => non _ _) hq
    calc f (w n) p ≤ f n p + f (w (n/q)) p := by
            simpa [f,add_mul] using mul_le_mul_of_nonneg_right v (log_natCast_nonneg p)
         _ ≤ _ := add_le_add_right pick _
  have correction : ∑ p ∈ U, f n p ≤ log n := by
    have t := weightSubset n U ∅ (by simp)
    simpa [f,Real.log_nat_eq_sum_factorization n,Finsupp.sum,Nat.support_factorization] using t
  change ∑ p ∈ U, f (w n) p ≤ log n + ∑ q ∈ Q, L (n/q)
  calc
    _ ≤ ∑ p ∈ U, (f n p + ∑ q ∈ Q, f (w (n/q)) p) := Finset.sum_le_sum single
    _ = (∑ p ∈ U, f n p) + ∑ q ∈ Q, ∑ p ∈ U, f (w (n/q)) p := by
      rw [Finset.sum_add_distrib,Finset.sum_comm (s := U) (t := Q)]
    _ ≤ _ := add_le_add correction (Finset.sum_le_sum fun q _ => weightSubset (w (n/q)) U S away)


/-- A finite initial segment contributes a single uniform additive error
when a positive quadratic limit is used at smaller divisor indices. -/
theorem quadraticApprox (L : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (lim : Tendsto (fun n : ℕ => L n/(n:ℝ)^2) atTop (nhds c)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 0 < n →
      |L n-c*(n:ℝ)^2| ≤ c/10*(n:ℝ)^2+D := by
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp lim (c/10) (by positivity)
  let D := ∑ i ∈ Finset.range N, |L i-c*(i:ℝ)^2|
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨D,hD,?_⟩
  intro n hn
  by_cases h : N ≤ n
  · have near := (hN n h).le
    rw [Real.dist_eq] at near
    have sq : 0 < (n:ℝ)^2 := by positivity
    have eqn : L n-c*(n:ℝ)^2 = (L n/(n:ℝ)^2-c)*(n:ℝ)^2 := by
      field_simp
    rw [eqn,abs_mul,abs_of_pos sq]
    linarith [mul_le_mul_of_nonneg_right near sq.le]
  · have mem := Finset.mem_range.mpr (lt_of_not_ge h)
    have bound : |L n-c*(n:ℝ)^2| ≤ D := Finset.single_le_sum (fun i _ => abs_nonneg (L i-c*(i:ℝ)^2)) mem
    linarith [show 0 ≤ c/10*(n:ℝ)^2 by positivity]


/-- An elementary telescoping bound, retaining the saving in the first term. -/
theorem reciprocalSquares (n : ℕ) (hn : 2 ≤ n) :
    ∑ q ∈ Finset.Icc 2 n, 1/(q:ℝ)^2 ≤ 3/4 - 1/(n:ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ n+1)]
    have hp : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have step : 1/((n:ℝ)+1)^2 ≤ 1/(n:ℝ) - 1/((n:ℝ)+1) := by
      field_simp
      nlinarith
    push_cast
    linarith

/-- A uniformly quadratically approximated size eventually exceeds the
entire divisor bound, including all additive errors from small indices. -/
theorem heightGap (L : ℕ → ℝ) (c D : ℝ) (hc : 0 < c) (hD : 0 ≤ D)
    (height : ∀ m : ℕ, 0 < m → |L m-c*(m:ℝ)^2| ≤ c/10*(m:ℝ)^2+D) :
    ∀ᶠ n : ℕ in atTop, log n + ∑ q ∈ Finset.Icc 2 n, L (n/q) < L n := by
  obtain ⟨M,hM⟩ := exists_nat_gt (40*(1+2*D)/c)
  filter_upwards [eventually_ge_atTop M,eventually_ge_atTop 2] with n hm hn
  let Q := Finset.Icc 2 n
  have n1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have np : (0:ℝ) < n := by linarith
  have size : 40*(1+2*D) < c*n := by
    have h := hM.trans_le (show (M:ℝ) ≤ n by exact_mod_cast hm)
    simpa [mul_comm] using (div_lt_iff₀ hc).mp h
  have each (q : ℕ) (hq : q ∈ Q) : L (n/q) ≤
      (11*c/10*(n:ℝ)^2)*(1/(q:ℝ)^2)+D := by
    obtain ⟨q2,qn⟩ := Finset.mem_Icc.mp hq
    have qpos : 0 < q := by omega
    have hsmall := (abs_le.mp (height (n/q) (Nat.div_pos qn qpos))).2
    have qR : (0:ℝ) < q := by exact_mod_cast qpos
    have divR : (↑(n/q):ℝ) ≤ (n:ℝ)/q := by
      apply (le_div_iff₀ qR).mpr
      exact_mod_cast Nat.div_mul_le_self n q
    have sq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ ↑(n/q)) divR 2
    have step := mul_le_mul_of_nonneg_left sq (show 0 ≤ 11*c/10 by positivity)
    rw [div_pow] at step
    nlinarith [show (11*c/10*(n:ℝ)^2)*(1/(q:ℝ)^2) = 11*c/10*((n:ℝ)^2/(q:ℝ)^2) by ring]
  have total := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib,←Finset.mul_sum] at total
  have weight : ∑ q ∈ Q, 1/(q:ℝ)^2 ≤ 3/4 := (reciprocalSquares n hn).trans (sub_le_self _ (by positivity))
  have weighted := mul_le_mul_of_nonneg_left weight (show 0 ≤ 11*c/10*(n:ℝ)^2 by positivity)
  have count : Q.card ≤ n := by simp [Q,Nat.card_Icc]
  have drift : (Q.card:ℝ)*D ≤ (n:ℝ)*D := mul_le_mul_of_nonneg_right (by exact_mod_cast count) hD
  simp only [Finset.sum_const,nsmul_eq_mul] at total
  have low := (abs_le.mp (height n (by omega))).1
  have logle : log (n:ℝ) ≤ n := (Real.log_le_sub_one_of_pos np).trans (by linarith)
  have big := mul_lt_mul_of_pos_right size np
  have err := mul_le_mul_of_nonneg_right n1 hD
  change log (n:ℝ) + ∑ q ∈ Q, L (n/q) < L n
  nlinarith only [total,weighted,drift,low,logle,big,err,hD]


theorem main : H1 → H2 → type_of% @EllipticDivisibilitySequence.silverman_eds_primitive_prime_divisors := by
  classical
  intro localLaw globalHeight W hW hz
  obtain ⟨A,good⟩ := localLaw W hW hz
  obtain ⟨B,measure⟩ := globalHeight W hW hz
  let S := A ∪ B
  obtain ⟨c,hc,lim⟩ := measure S Finset.subset_union_right
  let w (n : ℕ) := (W n).natAbs
  let L (n : ℕ) := ∑ p ∈ (w n).primeFactors \ S, ((w n).factorization p:ℝ)*log p
  obtain ⟨D,hD,est⟩ := quadraticApprox L c hc lim
  have gap := heightGap L c D hc hD est
  filter_upwards [gap,eventually_ge_atTop 1] with n top hn
  by_contra none
  apply (not_le.mpr top)
  apply oldSum w S n
  intro p hp
  obtain ⟨member,away⟩ := Finset.mem_sdiff.mp hp
  have prime := Nat.prime_of_mem_primeFactors member
  have divides := Nat.dvd_of_mem_primeFactors member
  have outside : p ∉ A := fun h => away (Finset.mem_union_left _ h)
  obtain ⟨r,hr,rank,lift⟩ := good p outside prime ⟨n,hn,divides⟩
  have earlier : ∃ k : ℕ, 0 < k ∧ k < n ∧ p ∣ w k := by
    by_contra! no
    apply none
    exact ⟨p,prime,Int.natCast_dvd.mpr divides,fun k hk lt dvd => no k hk lt (Int.natCast_dvd.mp dvd)⟩
  obtain ⟨k,hk,lt,prev⟩ := earlier
  exact oldCharge (w := w) hr hk lt prev divides rank lift

end OMA.R_EllipticDivisibilitySequence_silverman_eds_primitive_prime_divisors_R1
