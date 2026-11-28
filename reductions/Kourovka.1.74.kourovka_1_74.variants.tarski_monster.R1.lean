import FormalConjectures.Kourovka.«1_74»
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
Reduction `Kourovka.1.74.kourovka_1_74.variants.tarski_monster.R1` of the topologizable
Tarski monster theorem (Klyachko, Olshanskii, and Osin 2013, Theorem 1.4).
Credit: @B221393

- `H1`: Algebraic/combinatorial group-theoretic core (Klyachko-Olshanskii-Osin 2013):
  existence of a Tarski monster group `G` admitting a non-discrete, non-indiscrete
  conjugation-invariant group neighborhood filter at `1`.
- `H2`: Point-set topological group core (Bourbaki neighborhood-filter theorem): any group
  equipped with such a neighborhood filter admits a non-discrete, non-indiscrete group topology.
- `main`: Unconditionally proves that every Tarski monster group is simple, applies simplicity
  to the closed normal subgroup `closure {1}` together with non-indiscreteness to deduce
  `IsClosed {1}`, and concludes `T2Space G` via `IsTopologicalGroup.t2Space_iff_one_closed`.
-/

namespace OMA.R_Kourovka_1_74_kourovka_1_74_variants_tarski_monster_R1

open scoped Pointwise

/-- Klyachko-Olshanskii-Osin (2013): there exists a Tarski monster group admitting a
non-trivial, non-indiscrete group neighborhood filter at the identity. -/
def H1 : Prop :=
  ∃ (G : Type) (_ : Group G), Kourovka.«1.74».IsTarskiMonster G ∧
    ∃ 𝓕 : Filter G,
      (∀ U ∈ 𝓕, (1 : G) ∈ U) ∧
      (∀ U ∈ 𝓕, ∃ V ∈ 𝓕, ∀ x ∈ V, ∀ y ∈ V, x * y ∈ U) ∧
      (∀ U ∈ 𝓕, (fun x : G => x⁻¹) ⁻¹' U ∈ 𝓕) ∧
      (∀ g : G, ∀ U ∈ 𝓕, (fun x : G => g * x * g⁻¹) ⁻¹' U ∈ 𝓕) ∧
      𝓕 ≠ pure 1 ∧
      ∃ U ∈ 𝓕, U ≠ Set.univ

/-- Bourbaki neighborhood-filter construction for topological groups: any group with a
non-trivial, non-indiscrete conjugation-invariant group neighborhood filter at `1` admits a
non-discrete, non-indiscrete group topology. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] (𝓕 : Filter G),
    (∀ U ∈ 𝓕, (1 : G) ∈ U) →
    (∀ U ∈ 𝓕, ∃ V ∈ 𝓕, ∀ x ∈ V, ∀ y ∈ V, x * y ∈ U) →
    (∀ U ∈ 𝓕, (fun x : G => x⁻¹) ⁻¹' U ∈ 𝓕) →
    (∀ g : G, ∀ U ∈ 𝓕, (fun x : G => g * x * g⁻¹) ⁻¹' U ∈ 𝓕) →
    𝓕 ≠ pure 1 →
    (∃ U ∈ 𝓕, U ≠ Set.univ) →
    ∃ (_ : TopologicalSpace G),
      IsTopologicalGroup G ∧ ¬ DiscreteTopology G ∧
      ∃ U : Set G, IsOpen U ∧ U.Nonempty ∧ U ≠ Set.univ

lemma tarski_monster_simple (G : Type) [Group G]
    (hTM : Kourovka.«1.74».IsTarskiMonster G)
    (N : Subgroup G) (hN : N.Normal) : N = ⊥ ∨ N = ⊤ := by
  rcases hTM with ⟨hinf, p, hp, hsub⟩
  by_contra hneither
  push Not at hneither
  rcases hneither with ⟨hNbot, hNtop⟩
  have hNcard : Nat.card N = p := hsub N hNbot hNtop
  have hp_pos : 0 < p := hp.pos
  haveI hNfin : Finite N := Nat.finite_of_card_ne_zero (by omega)
  have hNne1 : ∃ x ∈ N, x ≠ (1 : G) := by
    by_contra hall1
    push Not at hall1
    apply hNbot
    ext x
    simp only [Subgroup.mem_bot]
    exact ⟨fun hx => hall1 x hx, fun hx => hx ▸ N.one_mem⟩
  rcases hNne1 with ⟨x, hxN, hx1⟩
  have hxp : x ^ p = 1 := by
    haveI : Fintype N := Fintype.ofFinite N
    have hpow : (⟨x, hxN⟩ : N) ^ Fintype.card N = 1 := pow_card_eq_one
    have hcard_eq : Fintype.card N = p := by rw [← Nat.card_eq_fintype_card, hNcard]
    rw [hcard_eq] at hpow
    exact congrArg Subtype.val hpow
  have hNg : ∃ g : G, g ∉ N := by
    by_contra hall
    push Not at hall
    apply hNtop
    ext g
    simp [hall g]
  rcases hNg with ⟨g, hgN⟩
  have hg1 : g ≠ 1 := fun h => hgN (h ▸ N.one_mem)
  let K : Subgroup G := Subgroup.zpowers g
  have hKbot : K ≠ ⊥ := by
    intro h
    have hmem : g ∈ (⊥ : Subgroup G) := h ▸ Subgroup.mem_zpowers g
    exact hg1 (Subgroup.mem_bot.mp hmem)
  have hKtop : K ≠ ⊤ := by
    intro htop
    have hxK : x ∈ K := htop.symm ▸ Subgroup.mem_top x
    rcases Subgroup.mem_zpowers_iff.mp hxK with ⟨m, hm⟩
    have hm0 : m ≠ 0 := by
      intro hm0
      rw [hm0, zpow_zero] at hm
      exact hx1 hm.symm
    have hgp : g ^ (m * (p : ℤ)) = 1 := by
      rw [zpow_mul, hm, zpow_natCast, hxp]
    have hfinord : IsOfFinOrder g := by
      rw [isOfFinOrder_iff_pow_eq_one]
      refine ⟨(m * (p : ℤ)).natAbs, Int.natAbs_pos.mpr (mul_ne_zero hm0 (by exact_mod_cast hp.ne_zero)), ?_⟩
      cases Int.natAbs_eq (m * (p : ℤ)) with
      | inl h =>
        have h1 : g ^ ((m * (p : ℤ)).natAbs : ℤ) = 1 := by rw [← h, hgp]
        rwa [zpow_natCast] at h1
      | inr h =>
        have h1 : (g ^ ((m * (p : ℤ)).natAbs : ℤ))⁻¹ = 1 := by rw [← zpow_neg, ← h, hgp]
        have h2 : g ^ ((m * (p : ℤ)).natAbs : ℤ) = 1 := inv_eq_one.mp h1
        rwa [zpow_natCast] at h2
    have hKfin : Finite K := by
      let n : ℕ := orderOf g
      have hn : 0 < n := hfinord.orderOf_pos
      have hsurj : Function.Surjective (fun i : Fin n => (⟨g ^ (i : ℕ), Subgroup.npow_mem_zpowers g i⟩ : K)) := by
        rintro ⟨y, hy⟩
        rcases Subgroup.mem_zpowers_iff.mp hy with ⟨k, rfl⟩
        have hmod : (k % (n : ℤ)).toNat < n := by
          have h1 : 0 ≤ k % (n : ℤ) := Int.emod_nonneg k (by exact_mod_cast hn.ne')
          have h2 : k % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos k (by exact_mod_cast hn)
          omega
        refine ⟨⟨(k % (n : ℤ)).toNat, hmod⟩, Subtype.ext ?_⟩
        dsimp only
        have h1 : 0 ≤ k % (n : ℤ) := Int.emod_nonneg k (by exact_mod_cast hn.ne')
        have heq_int : ((k % (n : ℤ)).toNat : ℤ) = k % (n : ℤ) := Int.toNat_of_nonneg h1
        have hpow_eq : g ^ k = g ^ (k % (n : ℤ)) := by
          have hdiv := (Int.mul_ediv_add_emod k (n : ℤ)).symm
          conv_lhs => rw [hdiv, zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow, one_mul]
        rw [hpow_eq, ← heq_int, zpow_natCast]
        simp only [Int.toNat_natCast]
      exact Finite.of_surjective _ hsurj
    have hGfin : Finite G := by
      have heq : Set.univ = (K : Set G) := by rw [htop, Subgroup.coe_top]
      exact Finite.of_equiv K (Equiv.ofBijective Subtype.val
        ⟨Subtype.val_injective, fun y => ⟨⟨y, htop.symm ▸ Subgroup.mem_top y⟩, rfl⟩⟩)
    exact not_finite G
  have hKcard : Nat.card K = p := hsub K hKbot hKtop
  haveI hKfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  let M : Subgroup G := N ⊔ K
  have hMbot : M ≠ ⊥ := by
    intro h
    have : N ≤ ⊥ := le_trans le_sup_left (le_of_eq h)
    exact hNbot (le_antisymm this bot_le)
  have hMfin : Finite M := by
    let φ : N × K → M := fun ⟨a, b⟩ =>
      ⟨(a : G) * (b : G), M.mul_mem (Subgroup.mem_sup_left a.2) (Subgroup.mem_sup_right b.2)⟩
    have hsurj : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      have hmem : y ∈ (N : Set G) * (K : Set G) := by
        rw [← Subgroup.normal_mul N K]
        exact hy
      rcases Set.mem_mul.mp hmem with ⟨a, ha, b, hb, rfl⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
    exact Finite.of_surjective φ hsurj
  have hMtop : M ≠ ⊤ := by
    intro htop
    have hGfin : Finite G :=
      Finite.of_equiv M (Equiv.ofBijective Subtype.val
        ⟨Subtype.val_injective, fun y => ⟨⟨y, htop.symm ▸ Subgroup.mem_top y⟩, rfl⟩⟩)
    exact not_finite G
  have hMcard : Nat.card M = p := hsub M hMbot hMtop
  haveI : Fintype N := Fintype.ofFinite N
  haveI : Fintype M := Fintype.ofFinite M
  let ι : N → M := fun a => ⟨a.1, Subgroup.mem_sup_left a.2⟩
  have hinj : Function.Injective ι := fun a b h =>
    Subtype.ext (congrArg (Subtype.val : M → G) h)
  have hcard_eq : Fintype.card N = Fintype.card M := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hNcard, hMcard]
  have hsurj_ι : Function.Surjective ι :=
    (Fintype.bijective_iff_injective_and_card ι).mpr ⟨hinj, hcard_eq⟩ |>.2
  have hgM : g ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  rcases hsurj_ι ⟨g, hgM⟩ with ⟨a, ha⟩
  have hag : a.1 = g := congrArg (Subtype.val : M → G) ha
  exact hgN (hag ▸ a.2)

theorem main : H1 → H2 → type_of% @Kourovka.«1.74».kourovka_1_74.variants.tarski_monster := by
  intro h1 h2
  rcases h1 with ⟨G, hGrp, hTM, 𝓕, h1mem, hmul, hinv, hconj, hne_pure, hne_univ⟩
  letI : Group G := hGrp
  rcases h2 G 𝓕 h1mem hmul hinv hconj hne_pure hne_univ with
    ⟨hTop, hTG, hndisc, U, hUopen, ⟨u₀, hu₀⟩, hUne⟩
  letI : TopologicalSpace G := hTop
  have hT2 : T2Space G := by
    rw [IsTopologicalGroup.t2Space_iff_one_closed]
    let C : Subgroup G := (⊥ : Subgroup G).topologicalClosure
    have hCnorm : C.Normal := Subgroup.is_normal_topologicalClosure (⊥ : Subgroup G)
    rcases tarski_monster_simple G hTM C hCnorm with hCbot | hCtop
    · have hcl : closure ({1} : Set G) = {1} := by
        rw [← Subgroup.coe_topologicalClosure_bot]
        change (C : Set G) = {1}
        rw [hCbot, Subgroup.coe_bot]
      exact closure_eq_iff_isClosed.mp hcl
    · exfalso
      have hy : ∃ y : G, y ∉ U := by
        by_contra hall
        push Not at hall
        apply hUne
        ext x
        simp [hall x]
      rcases hy with ⟨y, hyU⟩
      have hclosed : IsClosed ((fun x : G => y * x) ⁻¹' Uᶜ) :=
        hUopen.isClosed_compl.preimage (continuous_const_mul y)
      have h1in : ({1} : Set G) ⊆ (fun x : G => y * x) ⁻¹' Uᶜ := by
        intro x hx
        rw [Set.mem_singleton_iff.mp hx, Set.mem_preimage, mul_one]
        exact hyU
      have hcl_sub : closure ({1} : Set G) ⊆ (fun x : G => y * x) ⁻¹' Uᶜ :=
        closure_minimal h1in hclosed
      have hcl_univ : closure ({1} : Set G) = Set.univ := by
        rw [← Subgroup.coe_topologicalClosure_bot]
        change (C : Set G) = Set.univ
        rw [hCtop, Subgroup.coe_top]
      have hmem : y⁻¹ * u₀ ∈ (fun x : G => y * x) ⁻¹' Uᶜ := by
        apply hcl_sub
        rw [hcl_univ]
        trivial
      rw [Set.mem_preimage, mul_inv_cancel_left] at hmem
      exact hmem hu₀
  exact ⟨G, hGrp, hTop, hTM, hTG, hT2, hndisc⟩

end OMA.R_Kourovka_1_74_kourovka_1_74_variants_tarski_monster_R1
