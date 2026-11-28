import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H2_R1
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Sigma
import Mathlib.Algebra.Group.Pointwise.Set.Card
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Blocks
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard

/-!
Choose one nontrivial Sylow orbit inside each ambient orbit. The centralizer
factorization proves faithfulness on their disjoint union. Inside each ambient
orbit, the nontrivial Sylow orbit lengths are pairwise coprime divisors of its
length, so their sum is bounded by that length.

This is the degree bound used in Roney-Dougal and Tracey, Theorem 3,
https://arxiv.org/html/2503.05416#S7.
-/

namespace OMA.Erdos1162OrbitBudget

open Finset

private theorem product_dvd_of_pairwise_coprime {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (N : ℕ) (hcop : (s : Set ι).Pairwise (fun i j => (f i).Coprime (f j)))
    (hdvd : ∀ i ∈ s, f i ∣ N) :
    (∏ i ∈ s, f i) ∣ N := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · apply Nat.Coprime.prod_right
      intro i hi
      exact hcop (mem_insert_self a s) (mem_insert_of_mem hi)
        (fun he => ha (he.symm ▸ hi))
    · exact hdvd a (mem_insert_self a s)
    · exact ih (hcop.mono (by
        intro i hi
        exact mem_insert_of_mem hi)) fun i hi => hdvd i (mem_insert_of_mem hi)

private theorem sum_le_product_of_two_le {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (htwo : ∀ i ∈ s, 2 ≤ f i) : (∑ i ∈ s, f i) ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    by_cases hs : s.Nonempty
    · obtain ⟨i, hi⟩ := hs
      have hi' := ih fun j hj => htwo j (mem_insert_of_mem hj)
      have hsum : f i ≤ ∑ j ∈ s, f j :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
      have hp : 2 ≤ ∏ j ∈ s, f j :=
        (htwo i (mem_insert_of_mem hi)).trans (hsum.trans hi')
      exact (Nat.add_le_add_left hi' _).trans (Nat.add_le_mul (htwo a (mem_insert_self a s)) hp)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp

/-- A set of pairwise coprime divisors of a positive number, all at least two,
has total size at most that number. -/
theorem sum_le_of_pairwise_coprime_divisors {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    {N : ℕ} (hN : 0 < N)
    (hcop : (s : Set ι).Pairwise (fun i j => (f i).Coprime (f j)))
    (hsize : ∀ i ∈ s, 2 ≤ f i ∧ f i ∣ N) :
    (∑ i ∈ s, f i) ≤ N :=
  (sum_le_product_of_two_le s f (fun i hi => (hsize i hi).1)).trans
    (Nat.le_of_dvd hN (product_dvd_of_pairwise_coprime s f N hcop (fun i hi => (hsize i hi).2)))

end OMA.Erdos1162OrbitBudget

namespace OMA.Erdos1162OrbitCard

open MulAction
open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

/-- The orbit of a normal subgroup has cardinality dividing that of the containing orbit. -/
theorem orbit_ncard_dvd_of_normal (N : Subgroup G) [N.Normal] (x : X) :
    (orbit N x).ncard ∣ (orbit G x).ncard := by
  let a : orbit G x := ⟨x, mem_orbit_self x⟩
  have himage : Subtype.val '' orbit N a = orbit N x := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (mem_subgroup_orbit_iff.mp hz)
    · intro hy
      exact ⟨⟨y, orbit_subgroup_subset N x hy⟩, mem_subgroup_orbit_iff.mpr hy, rfl⟩
  have hcard : (orbit N a).ncard = (orbit N x).ncard := by
    rw [← himage, Subtype.val_injective.injOn.ncard_image]
  simpa only [hcard, Nat.card_coe_set_eq] using
    (IsBlock.orbit_of_normal (G := G) (N := N) a).ncard_dvd_card
      ⟨a, mem_orbit_self a⟩

/-- Every orbit of a Sylow subgroup is a prime power. -/
theorem sylow_orbit_ncard_eq_pow [Finite X] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (x : X) : ∃ k : ℕ, (orbit (P : Subgroup G) x).ncard = p ^ k := by
  simpa only [Nat.card_coe_set_eq] using P.isPGroup'.card_orbit x

/-- A Sylow orbit in a nilpotent action has size dividing its containing orbit size. -/
theorem sylow_orbit_ncard_dvd [Finite G] [Group.IsNilpotent G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (x : X) :
    (orbit (P : Subgroup G) x).ncard ∣ (orbit G x).ncard :=
  orbit_ncard_dvd_of_normal (P : Subgroup G) x

/-- A nontrivial Sylow orbit has at least as many points as its prime. -/
theorem prime_le_sylow_orbit_ncard [Finite X] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (x : X) (h : 1 < (orbit (P : Subgroup G) x).ncard) :
    p ≤ (orbit (P : Subgroup G) x).ncard := by
  obtain ⟨k, hk⟩ := sylow_orbit_ncard_eq_pow P x
  have hkpos : 0 < k := Nat.pos_of_ne_zero fun he => by simp [hk, he] at h
  rw [hk]
  exact Nat.le_of_dvd (pow_pos (Fact.out (p := p.Prime)).pos k)
    (dvd_pow_self _ hkpos.ne')

/-- Sylow orbit cardinalities at distinct primes are coprime. -/
theorem sylow_orbit_ncard_coprime [Finite X] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (P : Sylow p G) (Q : Sylow q G) (hpq : p ≠ q) (x y : X) :
    (orbit (P : Subgroup G) x).ncard.Coprime (orbit (Q : Subgroup G) y).ncard := by
  obtain ⟨k, hk⟩ := sylow_orbit_ncard_eq_pow P x
  obtain ⟨l, hl⟩ := sylow_orbit_ncard_eq_pow Q y
  rw [hk, hl]
  exact Nat.coprime_pow_primes k l Fact.out Fact.out hpq

end OMA.Erdos1162OrbitCard

namespace OMA.Erdos1162SylowCentralizer

theorem sylow_sup_centralizer_eq_top {G : Type*} [Group G] [Finite G]
    (hG : Group.IsNilpotent G) {p : ℕ} (hp : p.Prime) (P : Sylow p G) :
    (P : Subgroup G) ⊔ Subgroup.centralizer ((P : Subgroup G) : Set G) = ⊤ := by
  classical
  let _ : Group.IsNilpotent G := hG
  let _ : Fact p.Prime := ⟨hp⟩
  let C := Subgroup.centralizer ((P : Subgroup G) : Set G)
  let K := (P : Subgroup G) ⊔ C
  change K = ⊤
  by_contra hK
  have hIndex : K.index ≠ 1 := fun h => hK (Subgroup.index_eq_one.mp h)
  obtain ⟨q, hq, hqIndex⟩ := Nat.exists_prime_and_dvd hIndex
  let _ : Fact q.Prime := ⟨hq⟩
  let Q : Sylow q G := default
  have hQ : (Q : Subgroup G) ≤ K := by
    by_cases hqp : q = p
    · subst q
      exact (Q.isPGroup'.le_sylow_of_normal P).trans le_sup_left
    · have hDisj : Disjoint (P : Subgroup G) (Q : Subgroup G) :=
        IsPGroup.disjoint_of_ne p q (fun h => hqp h.symm) _ _ P.isPGroup' Q.isPGroup'
      have hCentral : (Q : Subgroup G) ≤ C := by
        intro x hx
        refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
        exact (Subgroup.commute_of_normal_of_disjoint _ _ inferInstance inferInstance
          hDisj y x hy hx).eq
      exact hCentral.trans le_sup_right
  exact Q.not_dvd_index (hqIndex.trans (Subgroup.index_dvd_of_le hQ))

theorem sylow_mul_centralizer {G : Type*} [Group G] [Finite G]
    (hG : Group.IsNilpotent G) {p : ℕ} (hp : p.Prime) (P : Sylow p G) (g : G) :
    ∃ a : P, ∃ b : Subgroup.centralizer ((P : Subgroup G) : Set G),
      g = (a : G) * (b : G) := by
  let _ : Group.IsNilpotent G := hG
  let _ : Fact p.Prime := ⟨hp⟩
  have hg : g ∈ (P : Subgroup G) ⊔ Subgroup.centralizer ((P : Subgroup G) : Set G) := by
    rw [sylow_sup_centralizer_eq_top hG hp P]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab.symm⟩

end OMA.Erdos1162SylowCentralizer

namespace OMA.Erdos1162FaithfulSelected

open MulAction

variable {G X : Type*} [Group G] [MulAction G X] [Finite X]

abbrev ActiveOrbit (P : Subgroup G) :=
  {ω : orbitRel.Quotient G X // 1 < Nat.card (orbit P ω.out)}

abbrev SelectedPoints (P : Subgroup G) :=
  Σ ω : ActiveOrbit (X := X) P, orbit P ω.val.out

private theorem fixes_all_of_fixes_representative_orbits (P : Subgroup G)
    (factor : ∀ g : G, ∃ a : P, ∃ b : Subgroup.centralizer (P : Set G),
      g = (a : G) * (b : G)) (u : P)
    (fix : ∀ w : ActiveOrbit (X := X) P, ∀ y : orbit P w.val.out, u • y = y)
    (x : X) : u • x = x := by
  let w : orbitRel.Quotient G X := Quotient.mk'' x
  have hx : x ∈ w.orbit := (orbitRel.Quotient.mem_orbit).mpr rfl
  rw [orbitRel.Quotient.orbit_eq_orbit_out w Quotient.out_eq'] at hx
  obtain ⟨g, hg⟩ := hx
  obtain ⟨a, b, rfl⟩ := factor g
  have ha' : (a : G) * (b : G) = (b : G) * (a : G) :=
    Subgroup.mem_centralizer_iff.mp b.property a a.property
  have hu' : (u : G) * (b : G) = (b : G) * (u : G) :=
    Subgroup.mem_centralizer_iff.mp b.property u u.property
  let y : orbit P w.out := ⟨a • w.out, mem_orbit w.out a⟩
  have hy : u • y = y := by
    by_cases h : 1 < Nat.card (orbit P w.out)
    · exact fix ⟨w, h⟩ y
    · have : Subsingleton (orbit P w.out) := Finite.card_le_one_iff_subsingleton.mp (le_of_not_gt h)
      exact Subsingleton.elim _ _
  have hy' : (u : G) • (y : X) = y := congrArg Subtype.val hy
  have hx' : (b : G) • (y : X) = x := by
    change ((a : G) * (b : G)) • w.out = x at hg
    rw [← hg, ha', mul_smul]
    rfl
  change (u : G) • x = x
  calc
    (u : G) • x = (u : G) • ((b : G) • (y : X)) := by rw [hx']
    _ = (b : G) • ((u : G) • (y : X)) := by rw [← mul_smul, hu', mul_smul]
    _ = x := by rw [hy', hx']

theorem selectedAction_injective [FaithfulSMul G X] (P : Subgroup G)
    (factor : ∀ g : G, ∃ a : P, ∃ b : Subgroup.centralizer (P : Set G),
      g = (a : G) * (b : G)) :
    Function.Injective (MulAction.toPermHom P (SelectedPoints (X := X) P)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro u hu
  change (MulAction.toPermHom P (SelectedPoints (X := X) P)) u = 1 at hu
  apply Subgroup.mem_bot.mpr
  apply eq_of_smul_eq_smul (α := X)
  intro x
  rw [one_smul]
  apply fixes_all_of_fixes_representative_orbits P factor u _ x
  intro w y
  have h := congrArg (fun σ : Equiv.Perm (SelectedPoints (X := X) P) => σ ⟨w, y⟩) hu
  exact heq_iff_eq.mp (Sigma.ext_iff.mp h).2

theorem activeOrbit_nonempty [FaithfulSMul G X] (P : Subgroup G) [Nontrivial P]
    (factor : ∀ g : G, ∃ a : P, ∃ b : Subgroup.centralizer (P : Set G),
      g = (a : G) * (b : G)) : Nonempty (ActiveOrbit (X := X) P) := by
  obtain ⟨u, hu⟩ := exists_ne (1 : P)
  by_contra noOrbit
  apply hu
  apply selectedAction_injective (X := X) P factor
  apply Equiv.ext
  intro z
  exact (noOrbit ⟨z.1⟩).elim

end OMA.Erdos1162FaithfulSelected

namespace OMA.Erdos1162SelectedDegree

open Finset MulAction
open scoped BigOperators

variable {D X : Type*} [Group D] [MulAction D X]
  [Fintype (orbitRel.Quotient D X)]

noncomputable def selectedDegree (P : Subgroup D) : ℕ :=
  ∑ w ∈ (univ : Finset (orbitRel.Quotient D X)).filter
    (fun w => 1 < Nat.card (orbit P w.out)), Nat.card (orbit P w.out)

theorem selectedDegree_eq_card [Finite X] (P : Subgroup D) :
    selectedDegree (X := X) P =
      Nat.card (Σ w : {w : orbitRel.Quotient D X // 1 < Nat.card (orbit P w.out)},
        orbit P w.val.out) := by
  classical
  rw [Nat.card_sigma]
  unfold selectedDegree
  exact Finset.sum_subtype
    (p := fun w : orbitRel.Quotient D X => 1 < Nat.card (orbit P w.out))
    ((univ : Finset (orbitRel.Quotient D X)).filter (fun w => 1 < Nat.card (orbit P w.out)))
    (fun w => by simp only [mem_filter, mem_univ, true_and]) (fun w => Nat.card (orbit P w.out))

omit [Fintype (orbitRel.Quotient D X)] in
private theorem orbit_sum_le [Finite D] [Finite X] (hD : Group.IsNilpotent D)
    (P : (p : (Nat.card D).primeFactors) → Sylow p D) (w : orbitRel.Quotient D X) :
    (∑ p : (Nat.card D).primeFactors,
      if 1 < Nat.card (orbit (P p : Subgroup D) w.out) then
        Nat.card (orbit (P p : Subgroup D) w.out) else 0) ≤ Nat.card (orbit D w.out) := by
  classical
  let _ : Group.IsNilpotent D := hD
  let S := (Nat.card D).primeFactors
  let size (p : S) := Nat.card (orbit (P p : Subgroup D) w.out)
  let active := (univ : Finset S).filter (fun p => 1 < size p)
  have hN : 0 < Nat.card (orbit D w.out) := by
    let _ : Nonempty (orbit D w.out) := ⟨⟨w.out, mem_orbit_self _⟩⟩
    exact Nat.card_pos
  change (∑ p : S, if 1 < size p then size p else 0) ≤ _
  calc
    _ = ∑ p ∈ active, size p := by simp only [active, sum_filter]
    _ ≤ _ := by
      apply OMA.Erdos1162OrbitBudget.sum_le_of_pairwise_coprime_divisors active size hN
      · intro p _ q _ hpq
        let _ : Fact (Nat.Prime (p : ℕ)) := ⟨Nat.prime_of_mem_primeFactors p.property⟩
        let _ : Fact (Nat.Prime (q : ℕ)) := ⟨Nat.prime_of_mem_primeFactors q.property⟩
        have hne : (p : ℕ) ≠ (q : ℕ) := fun h => hpq (Subtype.ext h)
        simpa only [size, Nat.card_coe_set_eq] using
          OMA.Erdos1162OrbitCard.sylow_orbit_ncard_coprime (P p) (P q) hne w.out w.out
      · intro p hp
        let _ : Fact (Nat.Prime (p : ℕ)) := ⟨Nat.prime_of_mem_primeFactors p.property⟩
        have hActive : 1 < size p := (mem_filter.mp hp).2
        refine ⟨by omega, ?_⟩
        simpa only [size, Nat.card_coe_set_eq] using
          OMA.Erdos1162OrbitCard.sylow_orbit_ncard_dvd (P p) w.out

theorem sum_selectedDegree_le [Finite D] [Finite X] (hD : Group.IsNilpotent D)
    (P : (p : (Nat.card D).primeFactors) → Sylow p D) :
    (∑ p : (Nat.card D).primeFactors, selectedDegree (X := X) (P p : Subgroup D)) ≤
      Nat.card X := by
  classical
  simp_rw [selectedDegree, sum_filter]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ w : orbitRel.Quotient D X, Nat.card (orbit D w.out) :=
      sum_le_sum (fun w _ => orbit_sum_le hD P w)
    _ = Nat.card X := Nat.card_sigma.symm.trans
      (Nat.card_congr (selfEquivSigmaOrbits D X).symm)

theorem sum_degree_le [Finite D] [Finite X] (hD : Group.IsNilpotent D)
    (P : (p : (Nat.card D).primeFactors) → Sylow p D) {m : ℕ → ℕ}
    (hm : ∀ p : (Nat.card D).primeFactors, m p = selectedDegree (X := X) (P p : Subgroup D)) :
    (∑ p ∈ (Nat.card D).primeFactors, m p) ≤ Nat.card X := by
  rw [← Finset.sum_finset_coe]
  exact (sum_congr rfl (fun p _ => hm p)).le.trans (sum_selectedDegree_le hD P)

end OMA.Erdos1162SelectedDegree

namespace OMA.Erdos1162ActionCore

open Finset MulAction
open OMA.Erdos1162FaithfulSelected OMA.Erdos1162SelectedDegree

private theorem sylow_nontrivial {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p ∈ (Nat.card G).primeFactors) (P : Sylow p G) : Nontrivial P := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  let _ : Fact p.Prime := ⟨hprime⟩
  have h := Nat.dvd_of_mem_primeFactors hp
  rw [← (P : Subgroup G).card_mul_index] at h
  have hdvd : p ∣ Nat.card P := (hprime.dvd_mul.mp h).resolve_right P.not_dvd_index
  exact Finite.one_lt_card_iff_nontrivial.mp (hprime.one_lt.trans_le (Nat.le_of_dvd Nat.card_pos hdvd))

private theorem prime_le_selectedDegree {D X : Type*} [Group D] [Finite D]
    [MulAction D X] [Finite X] [FaithfulSMul D X] [Fintype (orbitRel.Quotient D X)]
    (hD : Group.IsNilpotent D) {p : ℕ} (hp : p ∈ (Nat.card D).primeFactors) (P : Sylow p D) :
    p ≤ selectedDegree (X := X) (P : Subgroup D) := by
  classical
  have hprime := Nat.prime_of_mem_primeFactors hp
  let _ : Fact p.Prime := ⟨hprime⟩
  let _ : Nontrivial P := sylow_nontrivial hp P
  obtain ⟨w, hw⟩ := (activeOrbit_nonempty (X := X) (P : Subgroup D)
    (OMA.Erdos1162SylowCentralizer.sylow_mul_centralizer hD hprime P)).some
  have hsize := OMA.Erdos1162OrbitCard.prime_le_sylow_orbit_ncard P w.out
    (by simpa only [Nat.card_coe_set_eq] using hw)
  unfold selectedDegree
  have hwActive : w ∈ (univ : Finset (orbitRel.Quotient D X)).filter (fun j =>
      1 < Nat.card (orbit (P : Subgroup D) j.out)) := mem_filter.mpr ⟨mem_univ w, hw⟩
  have hsum := Finset.single_le_sum (f := fun j : orbitRel.Quotient D X =>
    Nat.card (orbit (P : Subgroup D) j.out)) (fun _ _ => Nat.zero_le _) hwActive
  exact (show p ≤ Nat.card (orbit (P : Subgroup D) w.out) by
    simpa only [Nat.card_coe_set_eq] using hsize).trans hsum

theorem faithful_sylow_degrees (n : ℕ) (D : Subgroup (Equiv.Perm (Fin n)))
    (hD : Group.IsNilpotent D) (P : (p : (Nat.card D).primeFactors) → Sylow p D) :
    ∃ m : ℕ → ℕ, (∀ p ∈ (Nat.card D).primeFactors, p ≤ m p) ∧
      (∑ p ∈ (Nat.card D).primeFactors, m p) ≤ n ∧
      ∀ p, ∃ f : P p →* Equiv.Perm (Fin (m p)), Function.Injective f := by
  classical
  let _ : Fintype (orbitRel.Quotient D (Fin n)) := Fintype.ofFinite _
  let S := (Nat.card D).primeFactors
  let m (p : ℕ) := if hp : p ∈ S then selectedDegree (X := Fin n) (P ⟨p, hp⟩ : Subgroup D) else 0
  have hm (p : S) : m p = selectedDegree (X := Fin n) (P p : Subgroup D) := dif_pos p.property
  refine ⟨m, fun p hp => ?_, ?_, fun p => ?_⟩
  · rw [hm (⟨p, hp⟩ : S)]
    exact prime_le_selectedDegree (X := Fin n) hD hp (P ⟨p, hp⟩)
  · simpa only [Nat.card_fin] using sum_degree_le (X := Fin n) hD P hm
  · let T := SelectedPoints (X := Fin n) (P p : Subgroup D)
    have hT : Nat.card T = m p := by
      rw [hm p, selectedDegree_eq_card]
    let e := Finite.equivFinOfCardEq hT
    refine ⟨e.permCongrHom.toMonoidHom.comp (toPermHom (P p) T),
      e.permCongrHom.injective.comp ?_⟩
    exact selectedAction_injective (P p : Subgroup D)
      (OMA.Erdos1162SylowCentralizer.sylow_mul_centralizer hD
        (Nat.prime_of_mem_primeFactors p.property) (P p))

end OMA.Erdos1162ActionCore

theorem OMA.solution :
    OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H2_R1.H2 := by
  intro n D hD P
  exact OMA.Erdos1162ActionCore.faithful_sylow_degrees n D hD P
