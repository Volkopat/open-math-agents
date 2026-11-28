import FormalConjectures.Wikipedia.LeinsterGroup

/-!
# Abelian Leinster Groups

Proof that a finite abelian group is a Leinster group if and only if it is cyclic
and its order is a perfect number (Leinster 2001, Theorem 2.1).
-/

-- Original Lean proof by @TheWaler (PR #220).
-- Standard subgroup and coprime-product APIs replace preliminary constructions.

open scoped Classical

private lemma isLeinster_iff_sum_subgroup (G : Type*) [CommGroup G] [Fintype G] :
    LeinsterGroup.IsLeinster G ↔ ∑ H : Subgroup G, Nat.card H = 2 * Fintype.card G := by
  unfold LeinsterGroup.IsLeinster
  constructor <;> intro h
  · rw [← h]
    exact (Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun H : Subgroup G =>
      H.normal_of_isMulCommutative) _ _ fun _ => rfl).symm
  · rw [← h]
    exact Fintype.sum_equiv (Equiv.subtypeUnivEquiv fun H : Subgroup G =>
      H.normal_of_isMulCommutative) _ _ fun _ => rfl

private lemma sum_subgroup_eq_sum_addSubgroup (G : Type*) [CommGroup G] [Fintype G] :
    (∑ H : Subgroup G, Nat.card H) = ∑ H : AddSubgroup (Additive G), Nat.card H := by
  refine Fintype.sum_equiv (Subgroup.toAddSubgroup (G := G)).toEquiv _ _ fun H => ?_
  exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun _ => Iff.rfl)

private lemma sum_subgroup_of_isCyclic (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] :
    (∑ H : Subgroup G, Nat.card H) = ∑ d ∈ (Fintype.card G).divisors, d := by
  have hker : ∀ H : Subgroup G, H = (powMonoidHom (α := G) (Nat.card H)).ker := by
    intro H
    have hle : H ≤ (powMonoidHom (α := G) (Nat.card H)).ker := by
      intro x hx
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have h1 : (⟨x, hx⟩ : H) ^ Nat.card H = 1 := by
        rw [Nat.card_eq_fintype_card]
        exact pow_card_eq_one
      exact congrArg Subtype.val h1
    have hcard : Nat.card H = Nat.card (powMonoidHom (α := G) (Nat.card H)).ker := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right (Subgroup.card_subgroup_dvd_card H)]
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

  refine Finset.sum_bij (fun H _ => Nat.card H) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro H _
    rw [Nat.mem_divisors]
    exact ⟨by simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H,
      Fintype.card_ne_zero⟩
  · intro H₁ _ H₂ _ h
    rw [hker H₁, hker H₂, h]
  · intro d hd
    rw [Nat.mem_divisors] at hd
    refine ⟨(powMonoidHom (α := G) d).ker, Finset.mem_univ _, ?_⟩
    rw [IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, Nat.gcd_eq_right hd.1]

private lemma isAddCyclic_pi_zmod {ι : Type*} [Fintype ι] {n : ι → ℕ}
    (hn : ∀ i, n i ≠ 0) (hcop : Pairwise fun i j => (n i).Coprime (n j)) :
    IsAddCyclic (∀ i : ι, ZMod (n i)) := by
  have : ∀ i, NeZero (n i) := fun i => ⟨hn i⟩
  let g : ∀ i : ι, ZMod (n i) := fun _ => 1
  refine isAddCyclic_iff_exists_natCard_le_addOrderOf.mpr ⟨g, ?_⟩
  have hdvd : ∀ i : ι, n i ∣ addOrderOf g := by
    intro i
    have h0 : addOrderOf g • g = 0 := addOrderOf_nsmul_eq_zero g
    have hi : (addOrderOf g : ZMod (n i)) = 0 := by
      simpa [g] using congrFun h0 i
    exact (ZMod.natCast_eq_zero_iff (addOrderOf g) (n i)).mp hi
  have hprod : (∏ i : ι, n i) ∣ addOrderOf g :=
    Fintype.prod_dvd_of_isRelPrime (fun _ _ hij =>
      Nat.coprime_iff_isRelPrime.mp (hcop hij)) hdvd
  have hcard : Nat.card (∀ i : ι, ZMod (n i)) = ∏ i : ι, n i := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi]
    simp [ZMod.card]
  rw [hcard]
  exact Nat.le_of_dvd (addOrderOf_pos_iff.mpr (isOfFinAddOrder_of_finite g)) hprod

private lemma exists_surj_zmod_prod_of_not_isCyclic (G : Type*) [CommGroup G] [Fintype G]
    (hnc : ¬ IsCyclic G) :
    ∃ p : ℕ, p.Prime ∧ ∃ f : Additive G →+ ZMod p × ZMod p, Function.Surjective f := by
  obtain ⟨ι, hι, p, hp, e, ⟨φ⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite (Additive G)
  let ψ : Additive G ≃+ (∀ i : ι, ZMod (p i ^ e i)) := φ.trans (DirectSum.addEquivProd _)
  by_cases hpair : ∃ i j : ι, i ≠ j ∧ e i ≠ 0 ∧ e j ≠ 0 ∧ p i = p j
  · obtain ⟨i, j, hij, hei, hej, hpij⟩ := hpair
    refine ⟨p i, hp i, ?_⟩
    have hi_dvd : p i ∣ p i ^ e i := dvd_pow_self (p i) hei
    have hj_dvd : p i ∣ p j ^ e j := by rw [hpij]; exact dvd_pow_self (p j) hej
    let proj : (∀ k : ι, ZMod (p k ^ e k)) →+ ZMod (p i) × ZMod (p i) :=
      AddMonoidHom.prod
        ((ZMod.castHom hi_dvd (ZMod (p i))).toAddMonoidHom.comp (Pi.evalAddMonoidHom _ i))
        ((ZMod.castHom hj_dvd (ZMod (p i))).toAddMonoidHom.comp (Pi.evalAddMonoidHom _ j))
    refine ⟨proj.comp ψ.toAddMonoidHom, ?_⟩
    intro ⟨a, b⟩
    obtain ⟨a', ha'⟩ := ZMod.castHom_surjective hi_dvd a
    obtain ⟨b', hb'⟩ := ZMod.castHom_surjective hj_dvd b
    let x : ∀ k : ι, ZMod (p k ^ e k) :=
      fun k => if hki : k = i then hki ▸ a' else if hkj : k = j then hkj ▸ b' else 0
    refine ⟨ψ.symm x, ?_⟩
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    ext
    · simp [proj, x, ha']
    · simp [proj, x, hij.symm, hb']
  · exfalso
    apply hnc
    have hcop : Pairwise fun i j : ι => (p i ^ e i).Coprime (p j ^ e j) := by
      intro i j hij
      by_cases hei : e i = 0
      · simp [hei]
      by_cases hej : e j = 0
      · simp [hej]
      have hpne : p i ≠ p j := fun h => hpair ⟨i, j, hij, hei, hej, h⟩
      exact ((Nat.coprime_primes (hp i) (hp j)).mpr hpne).pow (e i) (e j)
    have hcyc_pi : IsAddCyclic (∀ i : ι, ZMod (p i ^ e i)) :=
      isAddCyclic_pi_zmod (fun i => pow_ne_zero (e i) (hp i).ne_zero) hcop
    have hcyc_add : IsAddCyclic (Additive G) := ψ.isAddCyclic.mpr hcyc_pi
    exact isAddCyclic_additive_iff.mp hcyc_add

private lemma not_isLeinster_of_surj_zmod_prod (G : Type*) [CommGroup G] [Fintype G]
    {p : ℕ} (hp : p.Prime) (f : Additive G →+ ZMod p × ZMod p) (hf : Function.Surjective f) :
    ¬ LeinsterGroup.IsLeinster G := by
  have : Fact p.Prime := ⟨hp⟩
  let line : Option (ZMod p) → (ZMod p × ZMod p →+ ZMod p)
    | none => AddMonoidHom.snd (ZMod p) (ZMod p)
    | some a =>
      { toFun := fun v => v.1 + a * v.2
        map_zero' := by simp
        map_add' := fun v w => by simp [mul_add]; ring }
  have hline_surj : ∀ t : Option (ZMod p), Function.Surjective (line t) := by
    rintro (_ | a) z
    · exact ⟨(0, z), rfl⟩
    · exact ⟨(z, 0), by simp [line]⟩
  let K : Option (ZMod p) → AddSubgroup (Additive G) := fun t => ((line t).comp f).ker
  have hK_inj : Function.Injective K := by
    intro t₁ t₂ hK
    have hker : (line t₁).ker = (line t₂).ker := by
      ext v
      obtain ⟨g, rfl⟩ := hf v
      simpa [K] using SetLike.ext_iff.mp hK g
    cases t₁ with
    | none =>
      cases t₂ with
      | none => rfl
      | some a =>
        have hmem : (1, 0) ∈ (line none).ker := by
          rw [AddMonoidHom.mem_ker]
          rfl
        rw [hker] at hmem
        simp [line] at hmem
    | some a =>
      cases t₂ with
      | none =>
        have hmem : (1, 0) ∈ (line none).ker := by
          rw [AddMonoidHom.mem_ker]
          rfl
        rw [← hker] at hmem
        simp [line] at hmem
      | some b =>
        have hmem : (-a, 1) ∈ (line (some a)).ker := by simp [line]
        rw [hker] at hmem
        simp [line] at hmem
        have : a = b := by linear_combination -hmem
        rw [this]
  have hK_card : ∀ t : Option (ZMod p), Nat.card (K t) * p = Fintype.card G := by
    intro t
    have hsurj : Function.Surjective ((line t).comp f) := (hline_surj t).comp hf
    have hmul := AddSubgroup.card_mul_index (K t)
    have hidx : (K t).index = p := by
      rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hsurj, AddSubgroup.card_top,
        Nat.card_zmod]
    simpa [hidx, Nat.card_eq_fintype_card] using hmul
  have hK_ne_top : ∀ t : Option (ZMod p), K t ≠ ⊤ := by
    intro t htop
    have h1 := hK_card t
    simp [htop, Nat.card_eq_fintype_card] at h1
    have hpos : 0 < Fintype.card G := Fintype.card_pos
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith
  intro hL
  have hsum : ∑ H : AddSubgroup (Additive G), Nat.card H = 2 * Fintype.card G := by
    rw [← sum_subgroup_eq_sum_addSubgroup, ← isLeinster_iff_sum_subgroup]
    exact hL
  let S : Finset (AddSubgroup (Additive G)) := insert ⊤ (Finset.univ.image K)
  have hle : ∑ H ∈ S, Nat.card H ≤ ∑ H : AddSubgroup (Additive G), Nat.card H :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have htop_notMem : (⊤ : AddSubgroup (Additive G)) ∉ Finset.univ.image K := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact hK_ne_top
  have hS_eq : ∑ H ∈ S, Nat.card H = Fintype.card G + ∑ t : Option (ZMod p), Nat.card (K t) := by
    rw [Finset.sum_insert htop_notMem, Finset.sum_image (fun _ _ _ _ h => hK_inj h)]
    simp [Nat.card_eq_fintype_card]
  have hmul_le : p * (∑ H ∈ S, Nat.card H) ≤ p * (2 * Fintype.card G) := by
    rw [← hsum]
    exact Nat.mul_le_mul_left p hle
  have hmul_S : p * (∑ H ∈ S, Nat.card H) = (2 * p + 1) * Fintype.card G := by
    rw [hS_eq, mul_add, Finset.mul_sum]
    have hsum_t : ∑ t : Option (ZMod p), p * Nat.card (K t) = (p + 1) * Fintype.card G := by
      calc ∑ t : Option (ZMod p), p * Nat.card (K t)
          = ∑ _t : Option (ZMod p), Fintype.card G := by
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [mul_comm, hK_card t]
        _ = Fintype.card (Option (ZMod p)) * Fintype.card G := by simp
        _ = (p + 1) * Fintype.card G := by simp [ZMod.card]
    rw [hsum_t]
    ring
  rw [hmul_S] at hmul_le
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  nlinarith

theorem OMA.solution : type_of% @LeinsterGroup.abelian_is_leinster_iff_cyclic_perfect := by
  intro G _ _
  constructor
  · intro hL
    have hcyc : IsCyclic G := by
      by_contra hnc
      obtain ⟨p, hp, f, hf⟩ := exists_surj_zmod_prod_of_not_isCyclic G hnc
      exact not_isLeinster_of_surj_zmod_prod G hp f hf hL
    refine ⟨hcyc, ?_⟩
    rw [Nat.perfect_iff_sum_divisors_eq_two_mul Fintype.card_pos, ← sum_subgroup_of_isCyclic G]
    exact (isLeinster_iff_sum_subgroup G).mp hL
  · rintro ⟨hcyc, hperf⟩
    rw [isLeinster_iff_sum_subgroup G, sum_subgroup_of_isCyclic G]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul Fintype.card_pos).mp hperf
