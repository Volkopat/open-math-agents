import FormalConjectures.ErdosProblems.«985»
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Ring

/-!
# Prime primitive roots from subgroup prime counts

This reduction uses inclusion–exclusion over the maximal proper subgroups of the cyclic unit
group modulo a prime. The two children bound the even and odd intersection errors separately.
The local Euler product at 1 bounds the even error automatically for many factorizations.
The unconditional elementary cases use quadratic reciprocity and verified factor certificates.

The prime nonsquare, power-of-two, safe-prime, and odd-cofactor order arguments are from
@MrSeizy's Open Math Agents reduction Erdos985.erdos_985.R1.H2.R1 (#2213).
The small finite check is adapted from @Halldon’s merged proof Erdos985.erdos_985.R2.H1 (#3232),
with its original order test and prime candidates. McGown, Treviño and Trudgian, “Resolving
Grosswald's conjecture on GRH” (2016), analyze character sums for prime primitive roots.
-/

open Finset
namespace PrimeRootSieve

/-- Inclusion–exclusion for avoiding all the tests. -/
theorem survivors (P F : Finset ℕ) (test : ℕ → ℕ → Prop) [DecidableRel test] :
    ((P.filter (fun q => ∀ r ∈ F, ¬ test q r)).card : ℚ) =
      ∑ T ∈ F.powerset, (-1 : ℚ)^T.card * (P.filter (fun q => ∀ r ∈ T, test q r)).card := by
  classical
  let b (q r : ℕ) : ℚ := if test q r then 1 else 0
  have mulbit (q : ℕ) (T : Finset ℕ) :
      ∏ r ∈ T, b q r = if ∀ r ∈ T, test q r then (1:ℚ) else 0 := by
    by_cases h : ∀ r ∈ T, test q r
    · rw [if_pos h]
      exact Finset.prod_eq_one (fun r hr => by simp [b,h r hr])
    · obtain ⟨r,hr,hn⟩ := by simpa only [not_forall, exists_prop] using h
      simp [h, Finset.prod_eq_zero hr (show b q r = 0 by simp [b,hn])]
  have avoid (q : ℕ) :
      (if ∀r ∈ F, ¬test q r then (1:ℚ) else 0) = ∏ r ∈ F, (1 + -(b q r)) := by
    by_cases h : ∀ r ∈ F, ¬test q r
    · rw [if_pos h]
      exact (Finset.prod_eq_one (fun r hr => by simp [b,h r hr])).symm
    · obtain ⟨r,hr,hn⟩ := by simpa only [not_forall,exists_prop,not_not] using h
      rw [if_neg h]
      exact (Finset.prod_eq_zero hr (show 1 + -(b q r) = 0 by simp [b,hn])).symm
  calc _ = ∑ q ∈ P, (if ∀r ∈ F, ¬test q r then (1:ℚ) else 0) := by simp
       _ = ∑ q ∈ P, ∑ T ∈ F.powerset, ∏ r ∈ T, -b q r := by
         apply Finset.sum_congr rfl
         intro q _
         rw [avoid, Finset.prod_one_add]
       _ = _ := by
         rw [Finset.sum_comm]
         apply Finset.sum_congr rfl
         intro T _
         simp_rw [Finset.prod_neg, mulbit, ← Finset.mul_sum]
         simp

/-- The corresponding alternating sum for a density model factors over its tests. -/
theorem independent_mass (P F : Finset ℕ) :
    (P.card : ℚ) * (∏ r ∈ F, (1 - (r:ℚ)⁻¹)) =
      ∑ T ∈ F.powerset, (-1:ℚ)^T.card * ((P.card:ℚ)*∏ r ∈ T, (r:ℚ)⁻¹) := by
  simp_rw [sub_eq_add_neg, Finset.prod_one_add, Finset.prod_neg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intros
  ring

theorem positivity_of_errors (P F : Finset ℕ) (test : ℕ → ℕ → Prop) [DecidableRel test] :
    let count := fun T : Finset ℕ => ((P.filter fun q => ∀ r ∈ T, test q r).card : ℚ)
    let expected := fun T : Finset ℕ => (P.card:ℚ) * ∏ r ∈ T, (r:ℚ)⁻¹
    let main := (P.card:ℚ) * ∏ r ∈ F, (1 - (r:ℚ)⁻¹)
    let evenSets := F.powerset.filter (fun T => Even T.card)
    let oddSets := F.powerset.filter (fun T => ¬Even T.card)
    (∑ T ∈ evenSets, (expected T - count T)) ≤ main / 2 →
    (∑ T ∈ oddSets, (count T - expected T)) < main / 2 →
    ∃ q ∈ P, ∀ r ∈ F, ¬test q r := by
  classical
  intro count expected main evs ods he ho
  let diff := fun T : Finset ℕ => ((-1:ℚ)^T.card)*(expected T-count T)
  have hd : main - ((P.filter fun q => ∀ r ∈ F, ¬test q r).card:ℚ) = ∑T ∈ F.powerset,diff T := by
    dsimp [main]
    rw [independent_mass, survivors, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro T _
    dsimp [diff,expected,count]
    ring
  have ev : (∑T ∈ evs, diff T) = ∑T ∈ evs, (expected T-count T) := by
    apply Finset.sum_congr rfl
    intro T hT
    have h : Even T.card := (Finset.mem_filter.mp hT).2
    simp [diff,h.neg_one_pow]
  have od : (∑T ∈ ods, diff T) = ∑T ∈ ods, (count T-expected T) := by
    apply Finset.sum_congr rfl
    intro T hT
    have h : ¬Even T.card := (Finset.mem_filter.mp hT).2
    simp [diff,(Nat.not_even_iff_odd.mp h).neg_one_pow]
  have whole : (∑T ∈ evs,diff T) + (∑T ∈ ods,diff T) = ∑T ∈ F.powerset,diff T :=
    Finset.sum_filter_add_sum_filter_not ..
  rw [← whole, ev, od] at hd
  have pos : 0 < ((P.filter fun q => ∀ r ∈ F, ¬test q r).card:ℚ) := by linarith
  obtain ⟨q,hq⟩ := Finset.card_pos.mp (show 0 < (P.filter fun q => ∀ r ∈ F, ¬test q r).card by exact_mod_cast pos)
  exact ⟨q,(Finset.mem_filter.mp hq).1,(Finset.mem_filter.mp hq).2⟩

end PrimeRootSieve

open Finset
namespace PrimeRootSieve

/-- The simultaneous tests form the kernel of the one power indexed by the
squarefree product of the selected prime divisors. -/
theorem tests_as_one {G : Type*} [Group G] [Fintype G]
    (T : Finset ℕ) (sub : T ⊆ (Fintype.card G).primeFactors) (x : G) :
    (∀ r ∈ T, x^(Fintype.card G/r)=1) ↔ x^(Fintype.card G / ∏ r ∈ T,r)=1 := by
  let n := Fintype.card G
  let e := orderOf x
  let d := ∏ r ∈ T,r
  have e_dvd : e ∣ n := orderOf_dvd_card
  have epos : 0 < e := orderOf_pos x
  have npos : 0 < n := Fintype.card_pos
  have product_dvd (m : ℕ) (hm : m ≠ 0) (hdiv : ∀r ∈ T, r ∣ m) : d ∣ m := by
    have st : T ⊆ m.primeFactors := fun r hr => Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors (sub hr),hdiv r hr,hm⟩
    exact (Finset.prod_dvd_prod_of_subset T m.primeFactors id st).trans (Nat.prod_primeFactors_dvd m)
  have members : ∀r ∈ T,r ∣ n := fun _ hr => (Nat.mem_primeFactors.mp (sub hr)).2.1
  have total := product_dvd n npos.ne' members
  have criterion (r : ℕ) (hr : r ∣ n) : x^(n/r)=1 ↔ r ∣ n/e := by
    rw [← orderOf_dvd_iff_pow_eq_one, Nat.dvd_div_iff_mul_dvd hr,
        Nat.dvd_div_iff_mul_dvd e_dvd, mul_comm]
  change (∀ r ∈ T, x^(n/r)=1) ↔ x^(n/d)=1
  rw [criterion d total]
  constructor
  · intro h
    exact product_dvd _ (Nat.div_pos (Nat.le_of_dvd npos e_dvd) epos).ne'
      (fun r hr => (criterion r (members r hr)).mp (h r hr))
  · intro dh r hr
    exact (criterion r (members r hr)).mpr ((Finset.dvd_prod_of_mem id hr).trans dh)

/-- Uniform on a finite cyclic group, the exact density of a squarefree
intersection is the reciprocal of its squarefree index. -/
theorem uniform_intersection {G : Type*} [Group G] [Fintype G] [IsCyclic G] [DecidableEq G]
    (T : Finset ℕ) (sub : T ⊆ (Fintype.card G).primeFactors) :
    (Finset.univ.filter (fun x : G => ∀ r ∈ T, x^(Fintype.card G/r)=1)).card =
      Fintype.card G / ∏r ∈ T,r := by
  classical
  let n := Fintype.card G
  let d := ∏ r ∈ T,r
  let k := n/d
  have hd : d ∣ n := (Finset.prod_dvd_prod_of_subset T n.primeFactors id sub).trans
    (Nat.prod_primeFactors_dvd n)
  have hkn : k ∣ n := Nat.div_dvd_of_dvd hd
  have np : 0<n := Fintype.card_pos
  have dp : 0<d := Nat.pos_of_dvd_of_pos hd np
  have kp : 0<k := Nat.div_pos (Nat.le_of_dvd np hd) dp
  simp_rw [tests_as_one T sub]
  change (Finset.univ.filter fun x : G => x^k=1).card=k
  rw [← sum_card_orderOf_eq_card_pow_eq_one (G:=G) kp.ne']
  calc _ = ∑ i ∈ k.divisors,Nat.totient i := by
         apply Finset.sum_congr rfl
         intro i hi
         exact IsCyclic.card_orderOf_eq_totient ((Nat.dvd_of_mem_divisors hi).trans hkn)
       _ = k := Nat.sum_totient _

end PrimeRootSieve

open Finset
namespace PrimeRootSieve

/-- The empty intersection already pays the entire even Bonferroni loss
whenever the unsigned local Euler product is at most two. -/
theorem even_cheap (P F : Finset ℕ) (test : ℕ → ℕ → Prop) [DecidableRel test]
    (cheap : (∏ r ∈ F, (1+(r:ℚ)⁻¹)) ≤ 2) :
    let count := fun T : Finset ℕ => ((P.filter fun q => ∀ r ∈ T, test q r).card:ℚ)
    let expected := fun T : Finset ℕ => (P.card:ℚ) * ∏ r ∈ T, (r:ℚ)⁻¹
    (∑ T ∈ F.powerset.filter (fun T => Even T.card), (expected T-count T)) ≤
      ((P.card:ℚ) * ∏ r ∈ F, (1-(r:ℚ)⁻¹))/2 := by
  classical
  intro count expected
  let ev := F.powerset.filter (fun T => Even T.card)
  let od := F.powerset.filter (fun T => ¬Even T.card)
  let sign := fun T : Finset ℕ => (-1:ℚ)^T.card * expected T
  have tot : (∑T ∈ ev,expected T) + (∑T ∈ od,expected T) = ∑T ∈ F.powerset,expected T :=
    Finset.sum_filter_add_sum_filter_not ..
  have upper : (∑T ∈ F.powerset,expected T) ≤ P.card * (2:ℚ) := by
    dsimp [expected]
    rw [← Finset.mul_sum, ← Finset.prod_one_add]
    exact mul_le_mul_of_nonneg_left cheap (by positivity)
  have stot : (∑T ∈ ev,sign T) + (∑T ∈ od,sign T) = ∑T ∈ F.powerset,sign T :=
    Finset.sum_filter_add_sum_filter_not ..
  have es : (∑T ∈ ev,sign T) = ∑T ∈ ev,expected T := by
    exact Finset.sum_congr rfl fun T h => by
      have hh : Even T.card := (Finset.mem_filter.mp h).2
      simp [sign,hh.neg_one_pow]
  have os : (∑T ∈ od,sign T) = -(∑T ∈ od,expected T) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun T h => by
      have hh : ¬Even T.card := (Finset.mem_filter.mp h).2
      simp [sign,(Nat.not_even_iff_odd.mp hh).neg_one_pow]
  have signed : (P.card:ℚ) * (∏ r ∈ F, (1-(r:ℚ)⁻¹)) = ∑T ∈ F.powerset,sign T :=
    independent_mass P F
  have blank : (∅:Finset ℕ) ∈ ev := by simp [ev]
  have cnt : (P.card:ℚ) ≤ ∑ T ∈ ev, count T := by
    have hh := Finset.single_le_sum (f:=count) (fun t (_:t∈ev) => show 0≤count t by dsimp [count]; positivity) blank
    simpa [count] using hh
  change (∑T ∈ ev,(expected T-count T)) ≤ _
  rw [Finset.sum_sub_distrib]
  rw [es,os,← signed] at stot
  linarith
end PrimeRootSieve

namespace PrimeRootSieve

theorem nz_cast {p q : ℕ} (hq : q.Prime) (hlt : q < p) : (q : ZMod p) ≠ 0 := by
  intro h
  exact (Nat.le_of_dvd hq.pos ((ZMod.natCast_eq_zero_iff _ _).mp h)).not_gt hlt

theorem prime_nonsquare (p : ℕ) (hp : p.Prime) (h2 : p ≠ 2) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ ¬IsSquare (q : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨x,hx⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have hex : ∃ n : ℕ, n < p ∧ ¬IsSquare (n : ZMod p) :=
    ⟨x.val, x.val_lt, by rwa [ZMod.natCast_zmod_val]⟩
  classical
  let q := Nat.find hex
  obtain ⟨hlt, hn⟩ := Nat.find_spec hex
  refine ⟨q, ?_, hlt, hn⟩
  apply Nat.prime_iff_not_exists_mul_eq.mpr
  constructor
  · by_contra! hl
    change q < 2 at hl
    change ¬IsSquare (q : ZMod p) at hn
    interval_cases q <;> simp_all
  · rintro ⟨a,b,ha,hb,hab⟩
    have small (i : ℕ) (hi : i < q) : IsSquare (i : ZMod p) := by
      by_contra h
      exact (Nat.find_min hex hi) ⟨hi.trans hlt,h⟩
    exact hn (by change IsSquare (q : ZMod p); rw [← hab, Nat.cast_mul]; exact (small a ha).mul (small b hb))

theorem nonsquare_half {p q : ℕ} (hp : p.Prime) (h2 : p ≠ 2)
    (hq : q.Prime) (hlt : q < p) (hn : ¬IsSquare (q : ZMod p)) :
    (q : ZMod p) ^ ((p-1)/2) ≠ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hodd := (hp.mod_two_eq_one_iff_ne_two).mpr h2
  rw [show (p-1)/2 = p/2 by omega]
  exact fun h => hn ((ZMod.euler_criterion p (nz_cast hq hlt)).mpr h)

theorem two_power_case {p a : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (he : p-1 = 2^a) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p-1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q,hq,hlt,hn⟩ := prime_nonsquare p hp h2
  refine ⟨q,hq,hlt,orderOf_eq_of_pow_and_pow_div_prime (by have := hp.two_le; omega)
    (ZMod.pow_card_sub_one_eq_one (nz_cast hq hlt)) ?_⟩
  intro s hs hd
  rw [he] at hd
  obtain rfl := Nat.prime_eq_prime_of_dvd_pow hs Nat.prime_two hd
  exact nonsquare_half hp h2 hq hlt hn

theorem safe_case {p r : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (hr : r.Prime)
    (he : p-1 = 2*r) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p-1 := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨q,hq,hlt,hn⟩ := prime_nonsquare p hp h2
  refine ⟨q,hq,hlt,orderOf_eq_of_pow_and_pow_div_prime (by have := hp.two_le; omega)
    (ZMod.pow_card_sub_one_eq_one (nz_cast hq hlt)) ?_⟩
  intro s hs hd
  rw [he] at hd
  rcases hs.dvd_mul.mp hd with h | h
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp h
    exact nonsquare_half hp h2 hq hlt hn
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hs hr).mp h
    rw [he, Nat.mul_div_cancel _ hr.pos]
    intro hsq
    rcases sq_eq_one_iff.mp hsq with h | h
    · have hval := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hlt, ZMod.val_one'' (by have := hp.two_le; omega)] at hval
      exact hq.ne_one hval
    · have hsum : ((q+1 : ℕ) : ZMod p) = 0 := by push_cast; rw [h]; ring
      have hd := (ZMod.natCast_eq_zero_iff _ _).mp hsum
      have hqp : q+1 = p := by have := Nat.le_of_dvd (by omega : 0 < q+1) hd; omega
      have hdq : 2 ∣ q := ⟨s, by omega⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp hdq
      have := hr.two_le
      omega

theorem three_nonsquare {p : ℕ} (hp : p.Prime) (h4 : p%4 = 1) (h3 : p%3 = 2) :
    ¬IsSquare (3 : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro h
  have h' := (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := 3) h4 (by decide)).mp (by simpa using h)
  rw [← ZMod.natCast_mod p 3, h3] at h'
  exact (by decide : ¬IsSquare ((2 : ℕ) : ZMod 3)) h'

theorem prime_factor_order {p r a q : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hq : q.Prime) (hlt : q < p) (he : p-1 = 2^a*r)
    (hh : (q : ZMod p)^((p-1)/2) ≠ 1) (ho : (q : ZMod p)^(2^a) ≠ 1) :
    orderOf (q : ZMod p) = p-1 := by
  let : Fact p.Prime := ⟨hp⟩
  apply orderOf_eq_of_pow_and_pow_div_prime (by have := hp.two_le; omega)
    (ZMod.pow_card_sub_one_eq_one (nz_cast hq hlt))
  intro s hs hd
  rw [he] at hd
  rcases hs.dvd_mul.mp hd with hd | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hs Nat.prime_two hd
    exact hh
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hs hr).mp hd
    simpa only [he, Nat.mul_div_cancel _ hr.pos] using ho

/-- If the odd prime cofactor differs from three, reciprocity makes three a
quadratic nonresidue. Failure of full order forces the indicated half power
of three to be minus one. -/
theorem exception_dvd {p a r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (h3 : r ≠ 3) (he : p = 2^(a+2)*r+1)
    (hbad : orderOf (3 : ZMod p) ≠ p-1) : p ∣ 3^(2^(a+1))+1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hpow : 2^(a+2) = 4*2^a := by ring
  have h4 : p%4 = 1 := by rw [he, hpow, Nat.mul_assoc]; omega
  have hbig : 3 < p := by have := hr.two_le; have := Nat.two_pow_pos a; rw [he,hpow]; nlinarith
  have hmod3 : p%3 = 2 := by
    have hnd : ¬3 ∣ 2^(a+2)*r := by
      intro h
      rcases Nat.prime_three.dvd_mul.mp h with h | h
      · exact (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
      · exact h3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp h).symm
    have hnp : ¬3 ∣ p := fun h => (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h |>.not_lt hbig
    omega
  have hh := nonsquare_half hp (by omega) Nat.prime_three hbig (by simpa using three_nonsquare hp h4 hmod3)
  have he' : p-1 = 2^(a+2)*r := by omega
  have hfull : (3 : ZMod p)^(2^(a+2)) = 1 := by
    by_contra h
    exact hbad (prime_factor_order hp hr Nat.prime_three hbig he' hh (by simpa using h))
  have hhalf : (3 : ZMod p)^(2^(a+1)) ≠ 1 := by
    intro h
    have heq : (p-1)/2 = 2^(a+1)*r := by rw [he',pow_succ (2 : ℕ) (a+1), Nat.mul_right_comm, Nat.mul_div_cancel _ (by decide : 0 < 2)]
    apply hh
    simp [heq, pow_mul, h]
  have hsq : ((3 : ZMod p)^(2^(a+1)))^2 = 1 := by rwa [← pow_mul, ← pow_succ]
  have hneg := (sq_eq_one_iff.mp hsq).resolve_left hhalf
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  push_cast
  rw [hneg, neg_add_cancel]

theorem large_linear {p a r : ℕ} (hp : p.Prime) (hr : r.Prime) (h3 : r ≠ 3)
    (he : p = 2^(a+2)*r+1) (large : 3^(2^(a+1))+1 < p) :
    orderOf (3 : ZMod p) = p-1 := by
  by_contra bad
  exact (Nat.le_of_dvd (by positivity) (exception_dvd hp hr h3 he bad)).not_gt large


end PrimeRootSieve

namespace PrimeRootSieve

theorem small_join (start left right : ℕ) (test : ℕ → Bool)
    (hs : (List.range' start left).all test = true)
    (ht : (List.range' (start+left) right).all test = true) :
    (List.range' start (left+right)).all test = true := by
  rw [← List.range'_append, List.all_append, hs]
  simpa only [Nat.one_mul, Bool.true_and] using ht

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem small_table :
    (List.range 2792).all (fun p =>
      (decide (p < 3) || (List.range' 2 52).any (fun r => decide (r < p ∧ r ∣ p))) ||
      ([2,3,5,7,11,13,17,19,23,29,31,37,41,43,53] : List ℕ).any (fun q =>
        decide (q.Prime ∧ q < p) && (p-1).primeFactorsList.all
          (fun r => decide (q^((p-1)/r) % p ≠ 1)))) = true := by
  rw [List.range_eq_range']
  apply small_join 0 1396 1396
  · apply small_join 0 698 698
    · apply small_join 0 349 349
      · apply small_join 0 174 175
        · decide +kernel
        · decide +kernel
      · apply small_join 349 174 175
        · decide +kernel
        · decide +kernel
    · apply small_join 698 349 349
      · apply small_join 698 174 175
        · decide +kernel
        · decide +kernel
      · apply small_join 1047 174 175
        · decide +kernel
        · decide +kernel
  · apply small_join 1396 698 698
    · apply small_join 1396 349 349
      · apply small_join 1396 174 175
        · decide +kernel
        · decide +kernel
      · apply small_join 1745 174 175
        · decide +kernel
        · decide +kernel
    · apply small_join 2094 349 349
      · apply small_join 2094 174 175
        · decide +kernel
        · decide +kernel
      · apply small_join 2443 174 175
        · decide +kernel
        · decide +kernel

/- Prime primitive roots up through the verified bound of the second public reduction. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
theorem finite_range (p : ℕ) (hp : p.Prime) (h₂ : p ≠ 2) (hbound : p ≤ 2791) :
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p-1 := by
  let candidates : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 53]
  let certifies (p q : ℕ) := decide (q.Prime ∧ q < p) &&
    (p-1).primeFactorsList.all (fun r => decide (q^((p-1)/r) % p ≠ 1))
  let canSkip (p : ℕ) := decide (p < 3) || (List.range' 2 52).any (fun r => decide (r < p ∧ r ∣ p))
  let covered (p : ℕ) := canSkip p || candidates.any (certifies p)
  have cannotSkip : canSkip p = false := by
    cases h : canSkip p with
    | false => rfl
    | true =>
      exfalso
      rcases Bool.or_eq_true_iff.mp h with hlt | hdvd
      · have := hp.two_le
        have : p < 3 := of_decide_eq_true hlt
        omega
      · obtain ⟨r, hr, hdiv⟩ := List.any_eq_true.mp hdvd
        obtain ⟨hrp, hrdiv⟩ : r < p ∧ r ∣ p := of_decide_eq_true hdiv
        exact (Nat.prime_def_lt'.mp hp).2 r (List.mem_range'_1.mp hr).1 hrp hrdiv
  have checkedTable : (List.range 2792).all covered = true := small_table
  have certified_order {q : ℕ} (h : certifies p q = true) :
      q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p-1 := by
    have hcert := Bool.and_eq_true_iff.mp h
    obtain ⟨hq, hqp⟩ : q.Prime ∧ q < p := of_decide_eq_true hcert.1
    let : Fact p.Prime := ⟨hp⟩
    have hnz : (q : ZMod p) ≠ 0 := by
      intro hz
      exact (Nat.le_of_dvd hq.pos ((ZMod.natCast_eq_zero_iff _ _).mp hz)).not_gt hqp
    have hp₁ := hp.one_lt
    refine ⟨hq, hqp, orderOf_eq_of_pow_and_pow_div_prime (by omega)
      (ZMod.pow_card_sub_one_eq_one hnz) ?_⟩
    intro r hr hd hpow
    have hmem := (Nat.mem_primeFactorsList_iff_dvd (by omega) hr).2 hd
    have hres : q ^ ((p - 1) / r) % p ≠ 1 :=
      of_decide_eq_true (List.all_eq_true.mp hcert.2 r hmem)
    apply hres
    have hval := congrArg ZMod.val hpow
    rw [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_one'' hp.ne_one] at hval
    exact hval
  have hmem : p ∈ List.range 2792 := List.mem_range.mpr (by omega)
  have hc := List.all_eq_true.mp checkedTable p hmem
  have hq : candidates.any (certifies p) = true := by
    simpa [covered, cannotSkip] using hc
  obtain ⟨q, _, hcert⟩ := List.any_eq_true.mp hq
  exact ⟨q, certified_order hcert⟩

end PrimeRootSieve

/- Certificates for the prime divisors of 3^(2^(a−1))+1 at a=2,...,8.
The repeated-squaring lemma is from @MrSeizy’s accepted reduction of the finite part of Erdős 985. -/
namespace OMA.E985.Range
private theorem power_eval (q p e f : ℕ) :
    (Nat.rec (motive := fun _ => ℕ → ℕ) (fun t => q^t % p)
      (fun _ prev t => (prev (t/4)^4 * q^(t%4)) % p) f e) = q^e % p := by
  induction f generalizing e with
  | zero => rfl
  | succ f ih =>
    change ((Nat.rec _ _ f (e/4))^4 * q^(e%4)) % p = _
    rw [ih, Nat.mul_mod, Nat.pow_mod (q^(e/4) % p), Nat.mod_mod, ← Nat.pow_mod,
      ← Nat.mul_mod, ← pow_mul, ← pow_add]
    congr 2
    omega


private theorem pow_one {p b e : ℕ} (h : b^e % p = 1) : (b:ZMod p)^e=1 := by
  have hc := congrArg (fun n : ℕ => (n:ZMod p)) h
  simpa using hc

private theorem pow_not_one {p b e : ℕ} (hp : p ≠ 1) (h : b^e % p ≠ 1) : (b:ZMod p)^e≠1 := by
  intro he
  apply h
  rw [← ZMod.val_natCast,Nat.cast_pow,he,ZMod.val_one'' hp]

private theorem cert18191 : Nat.Prime 18191 := by
  apply lucas_primality 18191 (29:ZMod 18191)
  · apply pow_one (b:=29)
    rw [← power_eval _ _ _ 8]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^1 * (5^1 * (17^1 * (107^1 * (1)))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=29) (by decide)
    rw [← power_eval _ _ _ 8]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 5) h
    apply pow_not_one (b:=29) (by decide)
    rw [← power_eval _ _ _ 8]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 17) h
    apply pow_not_one (b:=29) (by decide)
    rw [← power_eval _ _ _ 8]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 107) h
    apply pow_not_one (b:=29) (by decide)
    rw [← power_eval _ _ _ 8]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert19801 : Nat.Prime 19801 := by
  apply lucas_primality 19801 (13:ZMod 19801)
  · apply pow_one (b:=13)
    rw [← power_eval _ _ _ 8]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^3 * (3^2 * (5^2 * (11^1 * (1)))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=13) (by decide)
    rw [← power_eval _ _ _ 8]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 3) h
    apply pow_not_one (b:=13) (by decide)
    rw [← power_eval _ _ _ 8]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 5) h
    apply pow_not_one (b:=13) (by decide)
    rw [← power_eval _ _ _ 8]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 11) h
    apply pow_not_one (b:=13) (by decide)
    rw [← power_eval _ _ _ 8]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert275201 : Nat.Prime 275201 := by
  apply lucas_primality 275201 (6:ZMod 275201)
  · apply pow_one (b:=6)
    rw [← power_eval _ _ _ 10]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^8 * (5^2 * (43^1 * (1))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 10]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 5) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 10]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 43) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 10]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert2643131 : Nat.Prime 2643131 := by
  apply lucas_primality 2643131 (2:ZMod 2643131)
  · apply pow_one (b:=2)
    rw [← power_eval _ _ _ 12]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^1 * (5^1 * (7^1 * (61^1 * (619^1 * (1))))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=2) (by decide)
    rw [← power_eval _ _ _ 12]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 5) h
    apply pow_not_one (b:=2) (by decide)
    rw [← power_eval _ _ _ 12]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 7) h
    apply pow_not_one (b:=2) (by decide)
    rw [← power_eval _ _ _ 12]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 61) h
    apply pow_not_one (b:=2) (by decide)
    rw [← power_eval _ _ _ 12]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 619) h
    apply pow_not_one (b:=2) (by decide)
    rw [← power_eval _ _ _ 12]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert21523361 : Nat.Prime 21523361 := by
  apply lucas_primality 21523361 (6:ZMod 21523361)
  · apply pow_one (b:=6)
    rw [← power_eval _ _ _ 13]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^5 * (5^1 * (17^1 * (41^1 * (193^1 * (1))))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 13]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 5) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 13]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 17) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 13]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 41) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 13]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 193) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 13]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert159898891 : Nat.Prime 159898891 := by
  apply lucas_primality 159898891 (2:ZMod 159898891)
  · apply pow_one (b:=2)
    rw [← power_eval _ _ _ 15]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^1 * (3^1 * (5^1 * (293^1 * (18191^1 * (1))))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=2) (by decide)
    rw [← power_eval _ _ _ 15]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 3) h
    apply pow_not_one (b:=2) (by decide)
    rw [← power_eval _ _ _ 15]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 5) h
    apply pow_not_one (b:=2) (by decide)
    rw [← power_eval _ _ _ 15]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 293) h
    apply pow_not_one (b:=2) (by decide)
    rw [← power_eval _ _ _ 15]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert18191 h
    apply pow_not_one (b:=2) (by decide)
    rw [← power_eval _ _ _ 15]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert584118287 : Nat.Prime 584118287 := by
  apply lucas_primality 584118287 (5:ZMod 584118287)
  · apply pow_one (b:=5)
    rw [← power_eval _ _ _ 16]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^1 * (97^1 * (347^1 * (8677^1 * (1)))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=5) (by decide)
    rw [← power_eval _ _ _ 16]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 97) h
    apply pow_not_one (b:=5) (by decide)
    rw [← power_eval _ _ _ 16]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 347) h
    apply pow_not_one (b:=5) (by decide)
    rw [← power_eval _ _ _ 16]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 8677) h
    apply pow_not_one (b:=5) (by decide)
    rw [← power_eval _ _ _ 16]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert138424618868737 : Nat.Prime 138424618868737 := by
  apply lucas_primality 138424618868737 (5:ZMod 138424618868737)
  · apply pow_one (b:=5)
    rw [← power_eval _ _ _ 24]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^13 * (3^1 * (2131^1 * (2643131^1 * (1)))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=5) (by decide)
    rw [← power_eval _ _ _ 24]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 3) h
    apply pow_not_one (b:=5) (by decide)
    rw [← power_eval _ _ _ 24]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2131) h
    apply pow_not_one (b:=5) (by decide)
    rw [← power_eval _ _ _ 24]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert2643131 h
    apply pow_not_one (b:=5) (by decide)
    rw [← power_eval _ _ _ 24]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert926510094425921 : Nat.Prime 926510094425921 := by
  apply lucas_primality 926510094425921 (7:ZMod 926510094425921)
  · apply pow_one (b:=7)
    rw [← power_eval _ _ _ 26]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^6 * (5^1 * (17^1 * (41^1 * (193^1 * (21523361^1 * (1)))))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=7) (by decide)
    rw [← power_eval _ _ _ 26]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 5) h
    apply pow_not_one (b:=7) (by decide)
    rw [← power_eval _ _ _ 26]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 17) h
    apply pow_not_one (b:=7) (by decide)
    rw [← power_eval _ _ _ 26]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 41) h
    apply pow_not_one (b:=7) (by decide)
    rw [← power_eval _ _ _ 26]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 193) h
    apply pow_not_one (b:=7) (by decide)
    rw [← power_eval _ _ _ 26]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert21523361 h
    apply pow_not_one (b:=7) (by decide)
    rw [← power_eval _ _ _ 26]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert3913786281514524929 : Nat.Prime 3913786281514524929 := by
  apply lucas_primality 3913786281514524929 (6:ZMod 3913786281514524929)
  · apply pow_one (b:=6)
    rw [← power_eval _ _ _ 32]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^8 * (31^1 * (787^1 * (3919^1 * (159898891^1 * (1))))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 32]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 31) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 32]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 787) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 32]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 3919) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 32]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert159898891 h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 32]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert153849834853910661121 : Nat.Prime 153849834853910661121 := by
  apply lucas_primality 153849834853910661121 (13:ZMod 153849834853910661121)
  · apply pow_one (b:=13)
    rw [← power_eval _ _ _ 35]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^11 * (3^1 * (5^1 * (433^1 * (19801^1 * (584118287^1 * (1)))))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=13) (by decide)
    rw [← power_eval _ _ _ 35]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 3) h
    apply pow_not_one (b:=13) (by decide)
    rw [← power_eval _ _ _ 35]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 5) h
    apply pow_not_one (b:=13) (by decide)
    rw [← power_eval _ _ _ 35]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 433) h
    apply pow_not_one (b:=13) (by decide)
    rw [← power_eval _ _ _ 35]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert19801 h
    apply pow_not_one (b:=13) (by decide)
    rw [← power_eval _ _ _ 35]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert584118287 h
    apply pow_not_one (b:=13) (by decide)
    rw [← power_eval _ _ _ 35]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

private theorem cert1716841910146256242328924544641 : Nat.Prime 1716841910146256242328924544641 := by
  apply lucas_primality 1716841910146256242328924544641 (6:ZMod 1716841910146256242328924544641)
  · apply pow_one (b:=6)
    rw [← power_eval _ _ _ 51]
    decide +kernel
  intro q hq hd
  have hd : q ∣ 2^7 * (5^1 * (17^1 * (41^1 * (193^1 * (21523361^1 * (926510094425921^1 * (1))))))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 51]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 5) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 51]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 17) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 51]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 41) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 51]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 193) h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 51]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert21523361 h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 51]
    decide +kernel
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert926510094425921 h
    apply pow_not_one (b:=6) (by decide)
    rw [← power_eval _ _ _ 51]
    decide +kernel
  exact (hq.not_dvd_one hd).elim

theorem no_exception_2 {q r : ℕ} (hq : q.Prime) (_hr : r.Prime) (hl : 2791 < q) (he : q = 4*r+1) (hd : q ∣ 3^(2^1)+1) : False := by
  have hd : q ∣ 2^1 * (5^1 * (1)) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 5) h
    omega
  exact (hq.not_dvd_one hd).elim

theorem no_exception_3 {q r : ℕ} (hq : q.Prime) (_hr : r.Prime) (hl : 2791 < q) (he : q = 8*r+1) (hd : q ∣ 3^(2^2)+1) : False := by
  have hd : q ∣ 2^1 * (41^1 * (1)) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 41) h
    omega
  exact (hq.not_dvd_one hd).elim

theorem no_exception_4 {q r : ℕ} (hq : q.Prime) (_hr : r.Prime) (hl : 2791 < q) (he : q = 16*r+1) (hd : q ∣ 3^(2^3)+1) : False := by
  have hd : q ∣ 2^1 * (17^1 * (193^1 * (1))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 17) h
    omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 193) h
    omega
  exact (hq.not_dvd_one hd).elim

theorem no_exception_5 {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hl : 2791 < q) (he : q = 32*r+1) (hd : q ∣ 3^(2^4)+1) : False := by
  have hd : q ∣ 2^1 * (21523361^1 * (1)) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert21523361 h
    have hh : r = 672605 := by omega
    have t : 5 ∣ r := by rw [hh]; decide
    rcases (Nat.dvd_prime hr).mp t with h | h <;> omega
  exact (hq.not_dvd_one hd).elim

theorem no_exception_6 {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hl : 2791 < q) (he : q = 64*r+1) (hd : q ∣ 3^(2^5)+1) : False := by
  have hd : q ∣ 2^1 * (926510094425921^1 * (1)) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert926510094425921 h
    have hh : r = 14476720225405 := by omega
    have t : 5 ∣ r := by rw [hh]; decide
    rcases (Nat.dvd_prime hr).mp t with h | h <;> omega
  exact (hq.not_dvd_one hd).elim

theorem no_exception_7 {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hl : 2791 < q) (he : q = 128*r+1) (hd : q ∣ 3^(2^6)+1) : False := by
  have hd : q ∣ 2^1 * (1716841910146256242328924544641^1 * (1)) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert1716841910146256242328924544641 h
    have hh : r = 13412827423017626893194723005 := by omega
    have t : 5 ∣ r := by rw [hh]; decide
    rcases (Nat.dvd_prime hr).mp t with h | h <;> omega
  exact (hq.not_dvd_one hd).elim

theorem no_exception_8 {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hl : 2791 < q) (he : q = 256*r+1) (hd : q ∣ 3^(2^7)+1) : False := by
  have hd : q ∣ 2^1 * (257^1 * (275201^1 * (138424618868737^1 * (3913786281514524929^1 * (153849834853910661121^1 * (1)))))) := hd
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 2) h
    omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq (by norm_num : Nat.Prime 257) h
    omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert275201 h
    have hh : r = 1075 := by omega
    have t : 5 ∣ r := by rw [hh]; decide
    rcases (Nat.dvd_prime hr).mp t with h | h <;> omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert138424618868737 h
    have hh : r = 540721167456 := by omega
    have t : 2 ∣ r := by rw [hh]; decide
    rcases (Nat.dvd_prime hr).mp t with h | h <;> omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert3913786281514524929 h
    have hh : r = 15288227662166113 := by omega
    have t : 31 ∣ r := by rw [hh]; decide
    rcases (Nat.dvd_prime hr).mp t with h | h <;> omega
  rcases hq.dvd_mul.mp hd with h | hd
  · obtain rfl := Nat.prime_eq_prime_of_dvd_pow hq cert153849834853910661121 h
    have hh : r = 600975917398088520 := by omega
    have t : 2 ∣ r := by rw [hh]; decide
    rcases (Nat.dvd_prime hr).mp t with h | h <;> omega
  exact (hq.not_dvd_one hd).elim

end OMA.E985.Range

namespace OMA.R_Erdos985_erdos_985_R3

/-- The combined even-intersection deficit in the sieve for primes below p. -/
def H1 : Prop := ∀ p : ℕ, p.Prime → 2791 < p →
    2 < (∏ r ∈ (p-1).primeFactors, (1+(r:ℚ)⁻¹)) →
    let P := (Finset.range p).filter Nat.Prime
    let F := (p-1).primeFactors
    let C := fun T : Finset ℕ => ((P.filter fun (q : ℕ) => ∀ r ∈ T, (q:ZMod p)^((p-1)/r) = 1).card:ℚ)
    let E := fun T : Finset ℕ => (P.card:ℚ) * ∏ r ∈ T, (r:ℚ)⁻¹
    let M := (P.card:ℚ) * ∏ r ∈ F, (1-(r:ℚ)⁻¹)
    (∑ T ∈ F.powerset.filter (fun T => Even T.card), (E T - C T)) ≤ M/2

/-- The odd-intersection excess in the cyclic subgroup sieve, outside the elementary families. -/
def H2 : Prop := ∀ p : ℕ, p.Prime → 2791 < p →
    (∀ a : ℕ, p-1 ≠ 2^a) → (∀ r : ℕ, r.Prime → p-1 ≠ 2*r) →
    (∀ a r : ℕ, r.Prime → r ≠ 3 → p = 2^(a+2)*r+1 →
      7 ≤ a ∧ p ∣ 3^(2^(a+1))+1) →
    let P := (Finset.range p).filter Nat.Prime
    let F := (p-1).primeFactors
    let C := fun T : Finset ℕ => ((P.filter fun (q : ℕ) => ∀ r ∈ T, (q:ZMod p)^((p-1)/r) = 1).card:ℚ)
    let E := fun T : Finset ℕ => (P.card:ℚ) * ∏ r ∈ T, (r:ℚ)⁻¹
    let M := (P.card:ℚ) * ∏ r ∈ F, (1-(r:ℚ)⁻¹)
    (∑ T ∈ F.powerset.filter (fun T => ¬Even T.card), (C T - E T)) < M/2

theorem main : H1 → H2 → type_of% @Erdos985.erdos_985 := by
  intro he ho p hp hp2
  classical
  by_cases small : p ≤ 2791
  · exact PrimeRootSieve.finite_range p hp hp2 small
  have large : 2791 < p := by omega
  by_cases hpow : ∃ a : ℕ, p-1 = 2^a
  · obtain ⟨a,ha⟩ := hpow
    exact PrimeRootSieve.two_power_case hp hp2 ha
  by_cases hsafe : ∃ r : ℕ, r.Prime ∧ p-1 = 2*r
  · obtain ⟨r,hr,heq⟩ := hsafe
    exact PrimeRootSieve.safe_case hp hp2 hr heq
  by_cases primitive : orderOf (3:ZMod p) = p-1
  · exact ⟨3, Nat.prime_three, by omega, primitive⟩
  have guard : ∀ a r : ℕ, r.Prime → r ≠ 3 → p=2^(a+2)*r+1 →
      7 ≤ a ∧ p ∣ 3^(2^(a+1))+1 := by
    intro a r hr h3 hform
    have divides := PrimeRootSieve.exception_dvd hp hr h3 hform primitive
    refine ⟨?_,divides⟩
    by_contra! smalla
    interval_cases a
    · exact OMA.E985.Range.no_exception_2 hp hr large hform divides
    · exact OMA.E985.Range.no_exception_3 hp hr large hform divides
    · exact OMA.E985.Range.no_exception_4 hp hr large hform divides
    · exact OMA.E985.Range.no_exception_5 hp hr large hform divides
    · exact OMA.E985.Range.no_exception_6 hp hr large hform divides
    · exact OMA.E985.Range.no_exception_7 hp hr large hform divides
    · exact OMA.E985.Range.no_exception_8 hp hr large hform divides
  let P := (Finset.range p).filter Nat.Prime
  let F := (p-1).primeFactors
  let test := fun q r : ℕ => (q:ZMod p)^((p-1)/r) = 1
  have hh1 : (∀ a : ℕ, p-1 ≠ 2^a) := fun a ha => hpow ⟨a,ha⟩
  have hh2 : (∀ r : ℕ, r.Prime → p-1 ≠ 2*r) := fun r hr h => hsafe ⟨r,hr,h⟩
  have oddLoss := ho p hp large hh1 hh2 guard
  have evenLoss : (∑ T ∈ F.powerset.filter (fun T => Even T.card),
    ((P.card:ℚ) * (∏ r ∈ T, (r:ℚ)⁻¹) - ((P.filter fun q => ∀ r ∈ T, test q r).card:ℚ))) ≤
    ((P.card:ℚ) * ∏ r ∈ F, (1-(r:ℚ)⁻¹))/2 := by
    by_cases many : 2 < ∏ r ∈ F, (1+(r:ℚ)⁻¹)
    · exact he p hp large many
    · exact PrimeRootSieve.even_cheap P F test (le_of_not_gt many)
  obtain ⟨q,hq,avoid⟩ := PrimeRootSieve.positivity_of_errors P F test evenLoss oddLoss
  obtain ⟨hqLt,hqP⟩ := Finset.mem_filter.mp hq
  have qlt : q < p := Finset.mem_range.mp hqLt
  let : Fact p.Prime := ⟨hp⟩
  have nz : (q:ZMod p) ≠ 0 := PrimeRootSieve.nz_cast hqP qlt
  refine ⟨q,hqP,qlt,orderOf_eq_of_pow_and_pow_div_prime (by omega) (ZMod.pow_card_sub_one_eq_one nz) ?_⟩
  intro r hr hd
  exact avoid r (Nat.mem_primeFactors.mpr ⟨hr,hd,by omega⟩)

end OMA.R_Erdos985_erdos_985_R3
