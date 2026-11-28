import OMAStatements.S_oeis_a398343
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Order.WellQuasiOrder
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace OMA.S_oeis_a398343

open Finset

open ArithmeticFunction
open scoped zeta

lemma rad_apply {n : ℕ} (hn : n≠0) : rad n = ∏ p ∈ n.primeFactors,p := by
  change (if n=0 then 0 else _) = _
  rw [if_neg hn]

lemma rad_mult : IsMultiplicative rad := by
  constructor
  · simp [rad_apply]
  · intro a b hc
    by_cases ha : a=0
    · simp [ha]
    by_cases hb : b=0
    · simp [hb]
    rw [rad_apply (mul_ne_zero ha hb),rad_apply ha,rad_apply hb,Nat.primeFactors_mul ha hb,
      prod_union hc.disjoint_primeFactors]

lemma sumrad_prod (n : ℕ) (hn : n≠0) :
    (∑ d ∈ n.divisors, rad d) = ∏ p ∈ n.primeFactors,(n.factorization p*p+1) := by
  rw [← zeta_mul_apply,(isMultiplicative_zeta.mul rad_mult).multiplicative_factorization _ hn]
  apply prod_congr n.support_factorization
  intro p hp
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
  change (ζ*rad) (p^(n.factorization p)) = _
  rw [zeta_mul_apply,Nat.sum_divisors_prime_pow hp',sum_range_succ']
  simp [rad_apply, hp'.ne_zero, Nat.primeFactors_pow_succ,hp'.primeFactors]

def ratio {r : ℕ} (e p : Fin r → ℕ) : ℚ :=
  ∏ i, ((e i:ℚ) + 1/(p i:ℚ))

lemma finite_prime_choices (r m : ℕ) (e : Fin r → ℕ) :
    {p : Fin r → ℕ | (∀ i, 0<p i) ∧ ratio e p = m}.Finite := by
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro p hp q hq hpq hle
  obtain ⟨hp,hpe⟩ := hp
  obtain ⟨hq,hqe⟩ := hq
  have hs : ∃ i, p i < q i := by
    by_contra! hn
    exact hpq (funext fun i => le_antisymm (hle i) (hn i))
  have hlt : ratio e q < ratio e p := by
    unfold ratio
    apply prod_lt_prod
    · intro i _
      have : 0 < (q i:ℚ) := by exact_mod_cast hq i
      positivity
    · intro i _
      have h : 0 < (p i:ℚ) := by exact_mod_cast hp i
      have hsub : (p i:ℚ) ≤ (q i:ℚ) := by exact_mod_cast hle i
      exact add_le_add_right (one_div_le_one_div_of_le h hsub) _
    · obtain ⟨i,hi⟩ := hs
      have h : 0 < (p i:ℚ) := by exact_mod_cast hp i
      have hsub : (p i:ℚ) < (q i:ℚ) := by exact_mod_cast hi
      exact ⟨i,mem_univ _,add_lt_add_right (one_div_lt_one_div_of_lt h hsub) _⟩
  rw [hpe,hqe] at hlt
  exact (lt_irrefl _ hlt)

lemma divisor_bounds (n m : ℕ)
    (H : (∏ p ∈ n.primeFactors,(n.factorization p*p+1)) = m*(∏ p ∈ n.primeFactors,p)) :
    n.primeFactors.card ≤ m + m.factorization 2 + 2 ∧
      ∀ p ∈ n.primeFactors, n.factorization p ≤ m := by
  classical
  let S := n.primeFactors
  let e := n.factorization
  have hp (p) (h : p ∈ S) : p.Prime := Nat.prime_of_mem_primeFactors h
  have he (p) (h : p ∈ S) : 1≤e p := by
    change 0<n.factorization p
    exact Finsupp.mem_support_iff.mp (by simpa [S] using h) |> Nat.pos_of_ne_zero
  have hD : 0 < ∏ p ∈ S,p := prod_pos fun p h => (hp p h).pos
  have hN : 0 < ∏ p ∈ S,(e p*p+1) := prod_pos fun _ _ => Nat.succ_pos _
  change (∏ p ∈ S,(e p*p+1)) = m*(∏ p ∈ S,p) at H
  have hm : m≠0 := by intro hm; rw [hm,zero_mul] at H; omega
  have heprod : (∏ p ∈ S,e p) ≤ m := by
    refine Nat.le_of_mul_le_mul_right ?_ hD
    · rw [← prod_mul_distrib,← H]
      exact prod_le_prod' fun _ _ => Nat.le_succ _
  let L := S.filter fun p => 2 ≤ e p
  have hL : L.card ≤ m := by
    have hpow : 2^L.card ≤ ∏ p ∈ L,e p := by
      simpa using (prod_le_prod' (s:=L) (f:=fun _ => 2) (g:=fun p => e p)
        fun p h => (mem_filter.mp h).2)
    have hc := prod_le_prod_of_subset_of_one_le (s:=L) (t:=S) (f:=fun p => e p)
      (filter_subset _ _) (fun _ _ => Nat.zero_le _) (fun p hp _ => he p hp)
    have htwo : L.card < 2^L.card := Nat.lt_two_pow_self
    omega
  let T := S.filter fun p => e p=1 ∧ p≠2
  have hv : T.card ≤ m.factorization 2+1 := by
    have hd : 2^T.card ∣ ∏ p ∈ S,(e p*p+1) := by
      have ha : (∏ _ ∈ T,(2:ℕ)) ∣ ∏ p ∈ T,(e p*p+1) := by
        apply prod_dvd_prod_of_dvd
        intro p h
        obtain ⟨hs,heq,hne⟩ := mem_filter.mp h
        have hodd := (hp p hs).eq_two_or_odd.resolve_left hne
        rw [heq,one_mul]
        omega
      have hb := prod_dvd_prod_of_subset T S (fun p => e p*p+1) (show T⊆S from filter_subset _ _)
      exact (by simpa using ha : 2^T.card ∣ ∏ p ∈ T,(e p*p+1)).trans hb
    rw [H] at hd
    have hh := (Nat.prime_two.pow_dvd_iff_le_factorization (mul_ne_zero hm hD.ne')).mp hd
    rw [Nat.factorization_mul hm hD.ne',Finsupp.add_apply] at hh
    have hs : Squarefree (∏ p ∈ S,p) := by
      refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p h q k hpq => ?_)
        fun p h => (hp p h).squarefree
      change IsRelPrime p q
      rw [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (hp p h) (hp q k)).mpr hpq
    have ho := hs.natFactorization_le_one 2
    omega
  constructor
  · have hsub : S ⊆ L ∪ T ∪ {2} := by
      intro p hp'
      have hep := he p hp'
      by_cases h2 : 2≤e p
      · simp [L,T,hp',h2]
      by_cases hp2 : p=2
      · simp [hp2]
      · have he1 : e p=1 := by omega
        simp [L,T,hp',he1,hp2]
    have h := card_le_card hsub
    have h1 := card_union_le L T
    have h2 := card_union_le (L ∪ T) ({2} : Finset ℕ)
    simp only [card_singleton] at h2
    change S.card ≤ _
    omega
  · intro p hp'
    have hh := prod_le_prod_of_subset_of_one_le (s:={p}) (t:=S) (f:=fun p => e p)
      (singleton_subset_iff.mpr hp') (fun _ _ => Nat.zero_le _) (fun q h _ => he q h)
    simpa using hh.trans heprod

theorem solution : ∀ m : ℕ,
    {k : ℕ | 0<k ∧ (∑ d ∈ k.divisors, rad d) = m * rad k}.Finite := by
  classical
  intro m
  let B := m + m.factorization 2 + 2
  let C (r : Fin (B+1)) (e : Fin r.val → Fin (m+1)) : Set (Fin r.val → ℕ) :=
    {p | (∀ i, 0<p i) ∧ ratio (fun i => (e i).val) p = m}
  let P (r : Fin (B+1)) (e : Fin r.val → Fin (m+1)) (p : Fin r.val → ℕ) :=
    ∏ i, p i ^ (e i).val
  have hU : (⋃ r : Fin (B+1), ⋃ e : Fin r.val → Fin (m+1), P r e '' C r e).Finite := by
    apply Set.finite_iUnion
    intro r
    apply Set.finite_iUnion
    intro e
    exact (finite_prime_choices r m (fun i => (e i).val)).image _
  apply hU.subset
  intro n hn
  obtain ⟨hn,h⟩ := hn
  rw [sumrad_prod n hn.ne',rad_apply hn.ne'] at h
  obtain ⟨hc,he⟩ := divisor_bounds n m h
  let r : Fin (B+1) := ⟨n.primeFactors.card,by dsimp [B];omega⟩
  let eqv : Fin r.val ≃ n.primeFactors :=
    (Fintype.equivFinOfCardEq (by simp [r] : Fintype.card n.primeFactors = r.val)).symm
  let p : Fin r.val → ℕ := fun i => (eqv i).val
  have hp (i) : p i ∈ n.primeFactors := (eqv i).property
  have hpos (i) : 0<p i := (Nat.prime_of_mem_primeFactors (hp i)).pos
  let e : Fin r.val → Fin (m+1) := fun i => ⟨n.factorization (p i),Nat.lt_succ_of_le (he _ (hp i))⟩
  have hprod (f : ℕ → ℕ) : (∏ i, f (p i)) = ∏ q ∈ n.primeFactors, f q := by
    calc
      _ = ∏ q : n.primeFactors, f q.val := Fintype.prod_equiv eqv _ _ (fun _ => rfl)
      _ = _ := by rw [prod_coe_sort_eq_attach,prod_attach]
  apply Set.mem_iUnion.mpr
  refine ⟨r,Set.mem_iUnion.mpr ⟨e, p,⟨hpos,?_⟩,?_⟩⟩
  · have HN : (∏ i, ((e i).val * p i + 1)) = m*(∏ i,p i) := by
      change (∏ i, (n.factorization (p i)*p i+1)) = _
      rw [hprod (fun q => n.factorization q*q+1),hprod (fun q => q)]
      exact h
    have HQ : (∏ i, (((e i).val:ℚ)*(p i:ℚ)+1)) = (m:ℚ)*(∏ i,(p i:ℚ)) := by exact_mod_cast HN
    change ratio (fun i => (e i).val) p = m
    unfold ratio
    have hrewrite (i : Fin r.val) : ((e i).val:ℚ)+1/(p i:ℚ) =
        (((e i).val:ℚ)*(p i:ℚ)+1)/(p i:ℚ) := by
      have hpz : (p i:ℚ)≠0 := by exact_mod_cast (hpos i).ne'
      field_simp
    simp_rw [hrewrite]
    rw [prod_div_distrib,div_eq_iff]
    · exact HQ
    · exact prod_ne_zero_iff.mpr fun i _ => by exact_mod_cast (hpos i).ne'
  · change (∏ i, p i ^ n.factorization (p i)) = n
    rw [hprod (fun q => q^n.factorization q)]
    simpa [Finsupp.prod] using Nat.prod_factorization_pow_eq_self hn.ne'

end OMA.S_oeis_a398343

theorem OMA.solution : type_of% @OMA.S_oeis_a398343.main :=
  OMA.S_oeis_a398343.solution
