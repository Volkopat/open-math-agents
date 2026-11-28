import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R2
import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Finset.Nat

/-!
# A fixed-cofactor bound by automorphism moments

This proof follows the Sylow-core and extension counting argument of Ning Su
and Binzhou Xia, arXiv:2610.11092, Section 8. For every odd cofactor q, a finite
quotient of order 2^c q acts on the normal core of a Sylow 2-subgroup.
The number of prescribed outer actions and central factor sets bounds the
number of extensions. Increasing the moment to c + floor(log₂ q) gives the
index used in this step. The proof treats even q by removing its power of two.
-/

namespace Erdos1160.FixedCofactor

open Subgroup MulAction MonoidHom

/-- A ação nas classes laterais dá o limite fatorial para o índice do núcleo normal. -/
theorem normalCore_index_dvd_factorial {G : Type*} [Group G] [Finite G]
    (P : Subgroup G) : P.normalCore.index ∣ P.index.factorial := by
  rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
  exact card_subgroup_dvd_card (toPermHom G (G ⧸ P)).range

/-- Para cada Sylow de ordem potência de dois, seu núcleo normal tem ordem
2^(a-c). O quociente tem ordem 2^c q e c é limitado só em função de q. -/
theorem sylow_core_orders {G : Type*} [Group G] [Finite G] {a q : ℕ}
    (hG : Nat.card G = 2 ^ a * q) (hq : Odd q) (P : Sylow 2 G) :
    ∃ c ≤ a, c ≤ q.factorial.factorization 2 ∧
      Nat.card (P.normalCore) = 2 ^ (a - c) ∧
      Nat.card (G ⧸ P.normalCore) = 2 ^ c * q ∧ 2 ^ c * q ∣ q.factorial := by
  have hq2 : ¬ 2 ∣ q := hq.not_two_dvd_nat
  have hcard : Nat.card P = 2 ^ a := by
    rw [P.card_eq_multiplicity, hG,
      Nat.factorization_mul (by positivity) (by omega : q ≠ 0),
      Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hq2, add_zero]
  have hindex : P.index = q := by
    have h := P.index_mul_card
    rw [hcard, hG, Nat.mul_comm (2 ^ a) q] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h
  have hrel : P.normalCore.relIndex P ∣ 2 ^ a := by
    rw [← hcard]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨c, hca, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrel
  have hquot : P.normalCore.index = 2 ^ c * q := by
    rw [← Subgroup.relIndex_mul_index P.normalCore_le, hc, hindex]
  have hfac := normalCore_index_dvd_factorial (P : Subgroup G)
  rw [hquot, hindex] at hfac
  have hcq : c ≤ q.factorial.factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp
      (dvd_trans (dvd_mul_right _ _) hfac)
  refine ⟨c, hca, hcq, ?_, P.normalCore.index_eq_card.symm.trans hquot, hfac⟩
  apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ c * q by
    exact Nat.mul_pos (Nat.two_pow_pos _) (by omega))
  calc
    (2 ^ c * q) * Nat.card P.normalCore = Nat.card G := hquot ▸ P.normalCore.index_mul_card
    _ = 2 ^ a * q := hG
    _ = (2 ^ c * q) * 2 ^ (a - c) := by
      rw [Nat.mul_right_comm, ← pow_add, Nat.add_sub_of_le hca]

section Extensions

variable {N H E : Type*} [Group N] [Group H] [Group E]

private theorem conjugation_on_kernel (S : GroupExtension N E H) (n : N) :
    S.conjAct (S.inl n) = MulAut.conj n := by
  ext t
  apply S.inl_injective
  simp [GroupExtension.inl_conjAct_comm, MulAut.conj_apply]

private noncomputable def factor (S : GroupExtension N E H) (s : S.Section) (h k : H) : N :=
  (s.mul_mul_mul_inv_mem_range_inl h k).choose

private theorem factor_spec (S : GroupExtension N E H) (s : S.Section) (h k : H) :
    S.inl (factor S s h k) = s h * s k * (s (h * k))⁻¹ :=
  (s.mul_mul_mul_inv_mem_range_inl h k).choose_spec

private theorem factor_action (S : GroupExtension N E H) (s : S.Section) (h k : H) :
    MulAut.conj (factor S s h k) =
      S.conjAct (s h) * S.conjAct (s k) * (S.conjAct (s (h * k)))⁻¹ := by
  rw [← conjugation_on_kernel S, factor_spec, map_mul, map_mul, map_inv]

private noncomputable def coordinates (S : GroupExtension N E H) (s : S.Section) : N × H ≃ E :=
  Equiv.ofBijective (fun p => S.inl p.1 * s p.2) (by
    constructor
    · rintro ⟨n, h⟩ ⟨t, k⟩ he
      change S.inl n * s h = S.inl t * s k at he
      have hk := congrArg S.rightHom he
      simp only [map_mul, S.rightHom_inl, one_mul, s.rightHom_section] at hk
      subst k
      exact Prod.ext (S.inl_injective (mul_right_cancel he)) rfl
    · intro e
      have hm : e * (s (S.rightHom e))⁻¹ ∈ S.inl.range := by
        rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
        simp [s.rightHom_section]
      obtain ⟨n, hn⟩ := hm
      exact ⟨(n, S.rightHom e), by
        change S.inl n * s (S.rightHom e) = e
        rw [hn, inv_mul_cancel_right]⟩)

private theorem coordinates_mul (S : GroupExtension N E H) (s : S.Section) (n t : N) (h k : H) :
    coordinates S s (n, h) * coordinates S s (t, k) =
      coordinates S s (n * S.conjAct (s h) t * factor S s h k, h * k) := by
  change (S.inl n * s h) * (S.inl t * s k) = S.inl _ * s (h * k)
  rw [map_mul, map_mul, S.inl_conjAct_comm, factor_spec]
  simp [mul_assoc]

private noncomputable def equiv_of_same_data {D : Type*} [Group D]
    (S : GroupExtension N E H) (T : GroupExtension N D H) (s : S.Section) (t : T.Section)
    (ha : ∀ h, S.conjAct (s h) = T.conjAct (t h))
    (hf : ∀ h k, factor S s h k = factor T t h k) : S.Equiv T := by
  let e := (coordinates S s).symm.trans (coordinates T t)
  have he (p : N × H) : e (coordinates S s p) = coordinates T t p := by simp [e]
  let f : E ≃* D := { e with
    map_mul' := by
      intro x y
      obtain ⟨⟨n,h⟩, rfl⟩ := (coordinates S s).surjective x
      obtain ⟨⟨v,k⟩, rfl⟩ := (coordinates S s).surjective y
      change e _ = e _ * e _
      rw [coordinates_mul, he, he, he, coordinates_mul, ha, hf] }
  have hcoord (n : N) (h : H) : f (S.inl n * s h) = T.inl n * t h := he (n,h)
  have hsection (h : H) : f (s h) = t h := by simpa using hcoord 1 h
  refine { toMulEquiv := f, inl_comm := ?_, rightHom_comm := ?_ }
  · funext n
    apply mul_right_cancel (b := t 1)
    simpa only [Function.comp_apply, map_mul, hsection] using hcoord n 1
  · funext x
    obtain ⟨⟨n,h⟩, rfl⟩ := (coordinates S s).surjective x
    change T.rightHom (f (S.inl n * s h)) = S.rightHom (S.inl n * s h)
    simp [hcoord, s.rightHom_section, t.rightHom_section]

/-- Forma de contagem do lema 8.8 de Su e Xia. Cada índice representa uma
extensão inequivalente, com as identificações do núcleo N e do quociente H
fixadas. A hipótese sobre a ação externa permite trocar representantes por
conjugações internas em N. -/
theorem extension_family_encoding {I : Type*}
    {D : I → Type*} [∀ i, Group (D i)] (S : ∀ i, GroupExtension N (D i) H)
    (action : H → MulAut N)
    (outer : ∀ i h, ∃ e : D i, ∃ n : N, (S i).rightHom e = h ∧
      MulAut.conj n * (S i).conjAct e = action h)
    (distinct : ∀ i j, Nonempty ((S i).Equiv (S j)) → i = j) :
    Nonempty (I ↪ (H × H → Subgroup.center N)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hempty =>
    let _ := hempty
    exact ⟨⟨isEmptyElim, fun i => isEmptyElim i⟩⟩
  | inr hnonempty =>
    obtain ⟨i₀⟩ := hnonempty
    have lifts (i : I) (h : H) : ∃ e : D i, (S i).rightHom e = h ∧
        (S i).conjAct e = action h := by
      obtain ⟨e,n,hπ,ha⟩ := outer i h
      exact ⟨(S i).inl n * e, by simp [hπ],
        by rw [map_mul, conjugation_on_kernel, ha]⟩
    let s (i : I) : (S i).Section :=
      ⟨fun h => (lifts i h).choose, fun h => (lifts i h).choose_spec.1⟩
    have act (i : I) (h : H) : (S i).conjAct (s i h) = action h := (lifts i h).choose_spec.2
    let u (i : I) (p : H × H) := factor (S i) (s i) p.1 p.2
    have common (i : I) (p : H × H) : MulAut.conj (u i p) = MulAut.conj (u i₀ p) := by
      simp only [u, factor_action, act]
    have central (i : I) (p : H × H) : (u i₀ p)⁻¹ * u i p ∈ Subgroup.center N := by
      have hone : MulAut.conj ((u i₀ p)⁻¹ * u i p) = 1 := by
        rw [map_mul, map_inv, common i p, inv_mul_cancel]
      apply Subgroup.mem_center_iff.mpr
      intro x
      have hx := congrArg (fun v : MulAut N => v x) hone
      change _ * x * _⁻¹ = x at hx
      exact ((mul_inv_eq_iff_eq_mul).mp hx).symm
    let code (i : I) (p : H × H) : Subgroup.center N := ⟨_, central i p⟩
    have hinj : Function.Injective code := by
      intro i j hij
      apply distinct i j
      apply Nonempty.intro
      apply equiv_of_same_data (S i) (S j) (s i) (s j) (fun h => (act i h).trans (act j h).symm)
      intro h k
      have hh := congrArg (fun z => (z : Subgroup.center N).val) (congrFun hij (h,k))
      exact mul_left_cancel hh
    exact ⟨⟨code, hinj⟩⟩

theorem extension_count_fixed_outer_action {I : Type*} [Finite N] [Finite H]
    {D : I → Type*} [∀ i, Group (D i)] (S : ∀ i, GroupExtension N (D i) H)
    (action : H → MulAut N)
    (outer : ∀ i h, ∃ e : D i, ∃ n : N, (S i).rightHom e = h ∧
      MulAut.conj n * (S i).conjAct e = action h)
    (distinct : ∀ i j, Nonempty ((S i).Equiv (S j)) → i = j) :
    Nat.card I ≤ Nat.card (Subgroup.center N) ^ (Nat.card H ^ 2) := by
  obtain ⟨f⟩ := extension_family_encoding S action outer distinct
  calc
    Nat.card I ≤ Nat.card (H × H → Subgroup.center N) := Nat.card_le_card_of_injective f f.injective
    _ = _ := by rw [Nat.card_fun, Nat.card_prod, pow_two]

/-- Aplicação ao núcleo de Sylow: para tipos de núcleo e quociente e uma ação
externa fixados, o logaritmo na base dois do número de extensões cresce no
máximo linearmente em a. A constante explícita depende somente de q. -/
theorem extension_count_at_fixed_cofactor {I : Type*} [Finite N] [Finite H]
    {D : I → Type*} [∀ i, Group (D i)] (S : ∀ i, GroupExtension N (D i) H)
    (action : H → MulAut N)
    (outer : ∀ i h, ∃ e : D i, ∃ n : N, (S i).rightHom e = h ∧
      MulAut.conj n * (S i).conjAct e = action h)
    (distinct : ∀ i j, Nonempty ((S i).Equiv (S j)) → i = j)
    {a q : ℕ} (hN : Nat.card N ≤ 2 ^ a) (hH : Nat.card H ∣ q.factorial) :
    Nat.card I ≤ 2 ^ (a * q.factorial ^ 2) := by
  have hc : Nat.card (Subgroup.center N) ≤ 2 ^ a :=
    (Nat.card_le_card_of_injective (fun z : Subgroup.center N => (z : N))
      Subtype.val_injective).trans hN
  calc
    Nat.card I ≤ Nat.card (Subgroup.center N) ^ (Nat.card H ^ 2) :=
      extension_count_fixed_outer_action S action outer distinct
    _ ≤ (2 ^ a) ^ (Nat.card H ^ 2) := Nat.pow_le_pow_left hc _
    _ = 2 ^ (a * Nat.card H ^ 2) := (pow_mul _ _ _).symm
    _ ≤ 2 ^ (a * q.factorial ^ 2) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left a
        (Nat.pow_le_pow_left (Nat.le_of_dvd (Nat.factorial_pos _) hH) 2))

private instance inner_normal (K : Type*) [Group K] :
    (MulAut.conj : K →* MulAut K).range.Normal where
  conj_mem := by
    rintro _ ⟨n, rfl⟩ a
    refine ⟨a n, ?_⟩
    ext x
    simp [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply]

/-- Automorfismos do núcleo a menos de conjugação interna. -/
abbrev OuterAut (K : Type*) [Group K] := MulAut K ⧸ (MulAut.conj : K →* MulAut K).range

private def outerProjection : MulAut N →* OuterAut N := QuotientGroup.mk' _

private theorem equal_outer_iff (a b : MulAut N) :
    outerProjection a = outerProjection b ↔ ∃ n : N, MulAut.conj n * b = a := by
  change (a : OuterAut N) = b ↔ _
  rw [QuotientGroup.eq_iff_div_mem]
  exact exists_congr fun n => eq_div_iff_mul_eq'

private noncomputable def outerActionOfSection (S : GroupExtension N E H) (s : S.Section) :
    H →* OuterAut N := by
  let f (h : H) := outerProjection (S.conjAct (s h))
  have hf (h k : H) : f (h*k) = f h * f k := by
    dsimp only [f]
    rw [← map_mul]
    apply Eq.symm
    apply (equal_outer_iff _ _).mpr
    exact ⟨factor S s h k, by rw [factor_action, inv_mul_cancel_right]⟩
  have hone := hf 1 1
  rw [one_mul] at hone
  exact { toFun := f, map_mul' := hf, map_one' := mul_left_cancel (hone.symm.trans (mul_one _).symm) }

private theorem card_by_labels {I L A : Type*} [Finite L] [Finite A] (f : I → L)
    (encode : ∀ l, Nonempty ({i : I // f i = l} ↪ A)) : Nat.card I ≤ Nat.card L * Nat.card A := by
  classical
  let _ : Fintype L := Fintype.ofFinite _
  let F (l : L) := {i : I // f i = l}
  let (l : L) : Finite (F l) := Finite.of_injective _ (encode l).some.injective
  calc
    Nat.card I = Nat.card ((l : L) × F l) := (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ l, Nat.card (F l) := Nat.card_sigma
    _ ≤ ∑ _l : L, Nat.card A :=
      Finset.sum_le_sum fun l _ => Nat.card_le_card_of_injective _ (encode l).some.injective
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, smul_eq_mul]

/-- Sem fixar a ação externa: basta especificar seus valores em um conjunto
gerador de H. A fibra de cada escolha tem a cota do lema 8.8. -/
theorem extension_count_from_generators {I : Type*} [Finite N] [Finite H]
    {D : I → Type*} [∀ i, Group (D i)] (S : ∀ i, GroupExtension N (D i) H)
    (distinct : ∀ i j, Nonempty ((S i).Equiv (S j)) → i = j)
    (T : Finset H) (hT : Subgroup.closure (T : Set H) = ⊤) :
    Nat.card I ≤ Nat.card (OuterAut N) ^ T.card * Nat.card (Subgroup.center N) ^ (Nat.card H ^ 2) := by
  classical
  let s (i : I) := (S i).surjInvRightHom
  let out (i : I) := outerActionOfSection (S i) (s i)
  let label (i : I) (t : ↥T) : OuterAut N := out i t.val
  let L := ↥T → OuterAut N
  let F (l : L) := {i : I // label i = l}
  have emb (l : L) : Nonempty (F l ↪ (H × H → Subgroup.center N)) := by
    cases isEmpty_or_nonempty (F l) with
    | inl h => let _ := h; exact ⟨⟨isEmptyElim, fun i => isEmptyElim i⟩⟩
    | inr h =>
      obtain ⟨i₀⟩ := h
      apply extension_family_encoding (fun i : F l => S i.val) (fun h => (S i₀.val).conjAct (s i₀.val h))
      · intro i h
        have he : out i₀.val = out i.val := by
          apply MonoidHom.eq_of_eqOn_dense hT
          intro x hx
          exact congrFun (i₀.property.trans i.property.symm) ⟨x,hx⟩
        have hp := DFunLike.congr_fun he h
        change outerProjection ((S i₀.val).conjAct (s i₀.val h)) =
          outerProjection ((S i.val).conjAct (s i.val h)) at hp
        obtain ⟨n, hn⟩ := (equal_outer_iff _ _).mp hp
        exact ⟨s i.val h, n, (s i.val).rightHom_section h, hn⟩
      · intro i j h
        exact Subtype.ext (distinct _ _ h)
  simpa only [Nat.card_fun, Nat.card_prod, Nat.card_eq_fintype_card (α := ↥T),
    Fintype.card_coe, pow_two] using card_by_labels label emb

end Extensions

section Actions

variable {H K : Type*} [Group H] [Group K] [Finite K]

/-- Acima de P, cada inclusão estrita na cadeia de subgrupos consome ao
menos um fator primo do índice, contado com multiplicidade. -/
theorem generators_above_subgroup [Finite H] (P : Subgroup H) :
    ∃ T : Finset H, P ⊔ Subgroup.closure (T : Set H) = ⊤ ∧
      T.card ≤ P.index.primeFactorsList.length := by
  classical
  suffices aux : ∀ n (A : Subgroup H), A.index = n →
      ∃ T : Finset H, A ⊔ Subgroup.closure (T : Set H) = ⊤ ∧
        T.card ≤ A.index.primeFactorsList.length from aux _ P rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro A hidx
    by_cases htop : A = ⊤
    · exact ⟨∅, by simp [htop], by simp⟩
    have hex : ∃ x : H, x ∉ A := by
      by_contra! hall
      exact htop (top_unique fun x _ => hall x)
    obtain ⟨x,hx⟩ := hex
    let B := A ⊔ Subgroup.closure ({x} : Set H)
    have hlt : A < B := by
      refine lt_of_le_of_ne le_sup_left (fun he => hx ?_)
      rw [he]
      exact (le_sup_right : Subgroup.closure ({x} : Set H) ≤ B)
        (Subgroup.subset_closure (Set.mem_singleton x))
    obtain ⟨T,hgen,hcard⟩ := ih B.index (hidx ▸ Subgroup.index_strictAnti hlt) B rfl
    refine ⟨insert x T, ?_, ?_⟩
    · rw [Finset.coe_insert, ← Set.singleton_union, Subgroup.closure_union, ← sup_assoc]
      exact hgen
    · have hrel0 : A.relIndex B ≠ 0 := by
        change (A.subgroupOf B).index ≠ 0
        exact Subgroup.index_ne_zero_of_finite
      have hrel1 : A.relIndex B ≠ 1 := fun h => hlt.not_ge (Subgroup.relIndex_eq_one.mp h)
      have hlen : 0 < (A.relIndex B).primeFactorsList.length :=
        List.length_pos_iff.mpr ((Nat.primeFactorsList_ne_nil _).mpr (by omega))
      have split := (Nat.perm_primeFactorsList_mul hrel0 (Subgroup.index_ne_zero_of_finite (H := B))).length_eq
      rw [Subgroup.relIndex_mul_index hlt.le, List.length_append] at split
      exact (Finset.card_insert_le x T).trans (by omega)

/-- Contagem das ações externas antes da escolha dos fatores centrais. Se x
e T geram H, usa-se uma classe de conjugação para a imagem de x e um elemento
de K para cada gerador restante. Este é o passo de contagem do lema 8.7. -/
theorem hom_classes_le_of_generators {I J : Type*} [Finite J]
    (f : I → H →* K) (x : H) (T : Finset H)
    (hgen : Subgroup.closure (insert x (T : Set H)) = ⊤)
    (rep : J → K) (cover : ∀ i, ∃ j a, MulAut.conj a (f i x) = rep j)
    (distinct : ∀ i j, (∃ a : K, ∀ h, MulAut.conj a (f i h) = f j h) → i = j) :
    Nat.card I ≤ Nat.card J * Nat.card K ^ T.card := by
  classical
  choose label a ha using cover
  let normalized (i : I) := (MulAut.conj (a i)).toMonoidHom.comp (f i)
  let code (i : I) : J × (↥T → K) := (label i, fun t => normalized i t.val)
  have hinj : Function.Injective code := by
    intro i j he
    have hl : label i = label j := congrArg Prod.fst he
    have hnorm : normalized i = normalized j := by
      apply MonoidHom.eq_of_eqOn_dense hgen
      intro h hh
      rcases hh with h | ht
      · subst h
        exact (ha i).trans ((congrArg rep hl).trans (ha j).symm)
      · exact congrFun (congrArg Prod.snd he) ⟨h,ht⟩
    apply distinct i j
    refine ⟨(a j)⁻¹ * a i, fun h => ?_⟩
    have hval := DFunLike.congr_fun hnorm h
    change MulAut.conj (a i) (f i h) = MulAut.conj (a j) (f j h) at hval
    rw [map_mul, MulAut.mul_apply, hval, map_inv]
    exact MulAut.inv_apply_self K (MulAut.conj (a j)) (f j h)
  calc
    Nat.card I ≤ Nat.card (J × (↥T → K)) := Nat.card_le_card_of_injective code hinj
    _ = _ := by rw [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := ↥T), Fintype.card_coe]

/-- Ao fixar a imagem de x até conjugação, o expoente é o número de fatores
primos de [H : ⟨x⟩], com multiplicidade. Para x de ordem prima, isso poupa
um gerador em relação ao limite obtido de |H|. -/
theorem hom_classes_le_from_element [Finite H] {I J : Type*} [Finite J]
    (f : I → H →* K) (x : H) (rep : J → K)
    (cover : ∀ i, ∃ j a, MulAut.conj a (f i x) = rep j)
    (distinct : ∀ i j, (∃ a : K, ∀ h, MulAut.conj a (f i h) = f j h) → i = j) :
    Nat.card I ≤ Nat.card J * Nat.card K ^ (Subgroup.zpowers x).index.primeFactorsList.length := by
  obtain ⟨T, hgen, hcard⟩ := generators_above_subgroup (Subgroup.zpowers x)
  have hg : Subgroup.closure (insert x (T : Set H)) = ⊤ := by
    rw [← Set.singleton_union, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
    exact hgen
  exact (hom_classes_le_of_generators f x T hg rep cover distinct).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right Nat.card_pos hcard))

end Actions

section MiddleGroups

variable {N E H : Type*} [Group N] [Group E] [Group H]

private def reidentifyKernel (S : GroupExtension N E H) (a : MulAut N) : GroupExtension N E H where
  inl := S.inl.comp a.symm.toMonoidHom
  rightHom := S.rightHom
  inl_injective := S.inl_injective.comp a.symm.injective
  rightHom_surjective := S.rightHom_surjective
  range_inl_eq_ker_rightHom := by
    rw [← S.range_inl_eq_ker_rightHom]
    ext e
    constructor
    · rintro ⟨n,rfl⟩
      exact ⟨a.symm n,rfl⟩
    · rintro ⟨n,rfl⟩
      exact ⟨a n, by simp⟩

private theorem reidentify_action (S : GroupExtension N E H) (a : MulAut N) (e : E) :
    (reidentifyKernel S a).conjAct e = MulAut.conj a (S.conjAct e) := by
  ext n
  apply a.symm.injective
  apply S.inl_injective
  change (reidentifyKernel S a).inl ((reidentifyKernel S a).conjAct e n) = _
  rw [GroupExtension.inl_conjAct_comm]
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  exact (S.inl_conjAct_comm (e := e) (n := a.symm n)).symm

/-- Cota para os tipos de isomorfismo de grupos do meio com núcleo N e
quociente H. Para a imagem do primeiro gerador x, só contamos representantes
de conjugação de automorfismos externos cuja ordem divide a ordem de x. -/
theorem middle_groups_le [Finite N] [Finite H] {I J : Type*} [Finite J]
    {D : I → Type*} [∀ i, Group (D i)] (S : ∀ i, GroupExtension N (D i) H)
    (distinct : ∀ i j, Nonempty (D i ≃* D j) → i = j)
    (x : H) (rep : J → OuterAut N)
    (cover : ∀ u : OuterAut N, u ^ orderOf x = 1 → ∃ j a, MulAut.conj a u = rep j) :
    Nat.card I ≤ (Nat.card J * Nat.card (OuterAut N) ^ (Subgroup.zpowers x).index.primeFactorsList.length) *
      Nat.card (Subgroup.center N) ^ (Nat.card H ^ 2) := by
  classical
  obtain ⟨T,hg,hcard⟩ := generators_above_subgroup (Subgroup.zpowers x)
  have hgen : Subgroup.closure (insert x (T : Set H)) = ⊤ := by
    rw [← Set.singleton_union, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
    exact hg
  let s (i : I) := (S i).surjInvRightHom
  let out (i : I) := outerActionOfSection (S i) (s i)
  have hx (i : I) : (out i x) ^ orderOf x = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  choose key b hb using fun i => cover (out i x) (hx i)
  have lifts (i : I) : ∃ a : MulAut N, outerProjection a = b i := (QuotientGroup.mk'_surjective _) _
  choose a ha using lifts
  let Q (i : I) := reidentifyKernel (S i) (a i)
  let t (i : I) : (Q i).Section := ⟨s i,(s i).rightHom_section⟩
  let norm (i : I) := (MulAut.conj (b i)).toMonoidHom.comp (out i)
  have norm_eq (i : I) (h : H) : outerProjection ((Q i).conjAct (t i h)) = norm i h := by
    rw [reidentify_action]
    change outerProjection (a i * (S i).conjAct (s i h) * (a i)⁻¹) =
      b i * outerProjection ((S i).conjAct (s i h)) * (b i)⁻¹
    rw [map_mul, map_mul, map_inv, ha i]
  let label (i : I) : J × (↥T → OuterAut N) := (key i, fun y => norm i y.val)
  have emb (l : J × (↥T → OuterAut N)) :
      Nonempty ({i : I // label i = l} ↪ (H × H → Subgroup.center N)) := by
    let F := {i : I // label i = l}
    cases isEmpty_or_nonempty F with
    | inl hempty => let _ := hempty; exact ⟨⟨isEmptyElim, fun i => isEmptyElim i⟩⟩
    | inr hn =>
      obtain ⟨i₀⟩ := hn
      apply extension_family_encoding (fun i : F => Q i.val) (fun h => (Q i₀.val).conjAct (t i₀.val h))
      · intro i h
        have he := i₀.property.trans i.property.symm
        have same : norm i₀.val = norm i.val := by
          apply MonoidHom.eq_of_eqOn_dense hgen
          intro y hy
          rcases hy with hy | hy
          · subst y
            exact (hb i₀.val).trans ((congrArg rep (congrArg Prod.fst he)).trans (hb i.val).symm)
          · exact congrFun (congrArg Prod.snd he) ⟨y,hy⟩
        have hp := (norm_eq i₀.val h).trans ((DFunLike.congr_fun same h).trans (norm_eq i.val h).symm)
        obtain ⟨n, hn⟩ := (equal_outer_iff _ _).mp hp
        exact ⟨t i.val h,n,(t i.val).rightHom_section h,hn⟩
      · intro i j e
        exact Subtype.ext (distinct _ _ (e.map fun v => v.toMulEquiv))
  have hbnd := card_by_labels label emb
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := ↥T),
    Fintype.card_coe, ← pow_two] at hbnd
  exact hbnd.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_right Nat.card_pos hcard)))

/-- Número de classes de conjugação de ordem ímpar em Out(N). -/
noncomputable def oddOuterClassCount (N : Type*) [Group N] : ℕ :=
  Nat.card (ConjClasses.mk '' {u : OuterAut N | Odd (orderOf u)})

/-- Estimativa usada para cofator ímpar na proposição 8.9 de Su e Xia.
q.primeFactorsList.length é Ω(q). O núcleo e o quociente estão fixos, e os
grupos do meio são contados a menos de isomorfismo, sem marcações. -/
theorem odd_cofactor_extension_bound [Finite N] [Finite H] {I : Type*}
    {D : I → Type*} [∀ i, Group (D i)] (S : ∀ i, GroupExtension N (D i) H)
    (distinct : ∀ i j, Nonempty (D i ≃* D j) → i = j)
    {c q : ℕ} (hH : Nat.card H = 2^c * q) (hq : Odd q) (hq' : 1 < q) :
    Nat.card I ≤ (oddOuterClassCount N * Nat.card (MulAut N) ^ (c + q.primeFactorsList.length - 1)) *
      Nat.card (Subgroup.center N) ^ (Nat.card H ^ 2) := by
  classical
  let p := q.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  let _ : Fact p.Prime := ⟨hp⟩
  have hpq : p ∣ q := Nat.minFac_dvd _
  have hpH : p ∣ Nat.card H := hH ▸ dvd_mul_of_dvd_right hpq _
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p hpH
  let J := ConjClasses.mk '' {u : OuterAut N | Odd (orderOf u)}
  let rep (j : J) : OuterAut N := j.property.choose
  have cover (u : OuterAut N) (hu : u ^ orderOf x = 1) :
      ∃ j a, MulAut.conj a u = rep j := by
    have hodd : Odd (orderOf x) := hx ▸ hq.of_dvd_nat hpq
    let j : J := ⟨ConjClasses.mk u, u, hodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one hu), rfl⟩
    have he : ConjClasses.mk (rep j) = ConjClasses.mk u := j.property.choose_spec.2
    obtain ⟨a,ha⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp he.symm)
    exact ⟨j,a,ha⟩
  have hidx : (Subgroup.zpowers x).index.primeFactorsList.length = c + q.primeFactorsList.length - 1 := by
    let A := Subgroup.zpowers x
    have hprod : A.index * p = Nat.card H := by
      rw [← hx, ← Nat.card_zpowers]
      exact A.index_mul_card
    have hleft := (Nat.perm_primeFactorsList_mul
      (Subgroup.index_ne_zero_of_finite (H := A)) hp.ne_zero).length_eq
    rw [hprod, List.length_append, Nat.primeFactorsList_prime hp] at hleft
    have hright := (Nat.perm_primeFactorsList_mul (Nat.two_pow_pos c).ne' (by omega : q ≠ 0)).length_eq
    rw [← hH, List.length_append, Nat.prime_two.primeFactorsList_pow, List.length_replicate] at hright
    change A.index.primeFactorsList.length = _
    simp only [List.length_cons, List.length_nil] at hleft
    omega
  have hout : Nat.card (OuterAut N) ≤ Nat.card (MulAut N) :=
    Nat.card_le_card_of_surjective outerProjection (QuotientGroup.mk'_surjective _)
  have hb := middle_groups_le S distinct x rep cover
  rw [hidx] at hb
  exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hout _)))

end MiddleGroups

end Erdos1160.FixedCofactor

open CategoryTheory
namespace Erdos1160.FixedCofactor

/-- Classes de grupos de ordem n usadas na definição de Erdos1160.g. -/
abbrev OrderClasses (n : ℕ) := ↥(Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
  {G : FiniteGrp.{0} | Nat.card G = n})

/-- Representante escolhido de uma classe de isomorfismo de grupos de ordem n. -/
noncomputable def orderRepresentative {n : ℕ} (i : OrderClasses n) : FiniteGrp.{0} :=
  i.property.choose

theorem orderRepresentative_spec {n : ℕ} (i : OrderClasses n) :
    Nat.card (orderRepresentative i) = n ∧
      Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (orderRepresentative i) = i.val :=
  i.property.choose_spec

private theorem rep_distinct {n : ℕ} {i j : OrderClasses n}
    (e : Nonempty (orderRepresentative i ≃* orderRepresentative j)) : i = j := by
  obtain ⟨e⟩ := e
  apply Subtype.ext
  rw [← (orderRepresentative_spec i).2, ← (orderRepresentative_spec j).2]
  exact Quotient.sound ⟨InducedCategory.isoMk (F := FiniteGrp.toGrp)
    (MulEquiv.toGrpIso (X := (orderRepresentative i).toGrp) (Y := (orderRepresentative j).toGrp) e)⟩

/-- Uma tabela de multiplicação em Fin n determina a classe do grupo. -/
noncomputable instance orderClassesFintype (n : ℕ) : Fintype (OrderClasses n) := by
  classical
  letI (i : OrderClasses n) : Fintype (orderRepresentative i) := Fintype.ofFinite _
  let e (i : OrderClasses n) : orderRepresentative i ≃ Fin n :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card, (orderRepresentative_spec i).1])
  let tbl (i : OrderClasses n) (a b : Fin n) := e i ((e i).symm a * (e i).symm b)
  apply Fintype.ofInjective tbl
  intro i j h
  let u := (e i).trans (e j).symm
  apply rep_distinct
  refine ⟨{ toEquiv := u, map_mul' := ?_ }⟩
  intro x y
  apply (e j).injective
  have hh := congrFun (congrFun h (e i x)) (e i y)
  simpa [tbl, u] using hh

private def classOf (G : FiniteGrp.{0}) {n : ℕ} (h : Nat.card G = n) : OrderClasses n :=
  ⟨Quotient.mk _ G, G, h, rfl⟩

private noncomputable def equivToRep (G : FiniteGrp.{0}) {n : ℕ} (h : Nat.card G = n) :
    G ≃* orderRepresentative (classOf G h) := by
  have he := (orderRepresentative_spec (classOf G h)).2.symm
  change Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G =
    Quotient.mk _ (orderRepresentative (classOf G h)) at he
  let f : G ≅ orderRepresentative (classOf G h) := Classical.choice (Quotient.exact he)
  exact Iso.groupIsoToMulEquiv ((inducedFunctor FiniteGrp.toGrp).mapIso f)

private def coreExtension {G N H : Type*} [Group G] [Group N] [Group H]
    (K : Subgroup G) [K.Normal] (e : N ≃* K) (f : (G ⧸ K) ≃* H) :
    GroupExtension N G H where
  inl := K.subtype.comp e.toMonoidHom
  rightHom := f.toMonoidHom.comp (QuotientGroup.mk' K)
  inl_injective := Subtype.coe_injective.comp e.injective
  rightHom_surjective := f.surjective.comp (QuotientGroup.mk'_surjective K)
  range_inl_eq_ker_rightHom := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective, QuotientGroup.ker_mk']
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (e v).property
    · intro hx
      exact ⟨e.symm ⟨x,hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩

abbrev CoreLabels (a q : ℕ) := (c : Fin (q.factorial.factorization 2 + 1)) ×
  (OrderClasses (2 ^ (a - c.val)) × OrderClasses (2 ^ c.val * q))

/-- Peso de um par de classes. A única dependência dos representantes está
nas ordens de grupos de automorfismos, de seus centros e no número de classes
de conjugação de ordem ímpar no grupo de automorfismos externos. -/
noncomputable def coreWeight {a q : ℕ} (l : CoreLabels a q) : ℕ :=
  let N := orderRepresentative l.2.1
  let H := orderRepresentative l.2.2
  (oddOuterClassCount N * Nat.card (MulAut N) ^ (l.1.val + q.primeFactorsList.length - 1)) *
    Nat.card (Subgroup.center N) ^ (Nat.card H ^ 2)

/-- Estimativa incondicional para todos os grupos de ordem 2^a q. O lado
esquerdo é, por definição, g(2^a q) do problema 1160. -/
theorem count_le_sum_core_weights (a q : ℕ) (hq : Odd q) (hq' : 1 < q) :
    Nat.card (OrderClasses (2^a * q)) ≤ ∑ l : CoreLabels a q, coreWeight l := by
  classical
  let C := OrderClasses (2^a * q)
  have cover (i : C) : ∃ l : CoreLabels a q,
      Nonempty (GroupExtension (orderRepresentative l.2.1) (orderRepresentative i) (orderRepresentative l.2.2)) := by
    let G := orderRepresentative i
    let P : Sylow 2 G := Classical.arbitrary _
    obtain ⟨c,_,hc,hK,hH,_⟩ := sylow_core_orders (orderRepresentative_spec i).1 hq P
    let N := FiniteGrp.of P.normalCore
    let H := FiniteGrp.of (G ⧸ P.normalCore)
    let l : CoreLabels a q := ⟨⟨c, by omega⟩, classOf N hK, classOf H hH⟩
    exact ⟨l, ⟨coreExtension P.normalCore (equivToRep N hK).symm (equivToRep H hH)⟩⟩
  choose label extData using cover
  let F (l : CoreLabels a q) := {i : C // label i = l}
  have hb (l : CoreLabels a q) : Nat.card (F l) ≤ coreWeight l := by
    have extAt (i : F l) : Nonempty
        (GroupExtension (orderRepresentative l.2.1) (orderRepresentative i.val) (orderRepresentative l.2.2)) := by
      obtain ⟨i, rfl⟩ := i
      exact extData i
    exact odd_cofactor_extension_bound (fun i : F l => (extAt i).some)
      (fun i j h => Subtype.ext (rep_distinct h)) (orderRepresentative_spec l.2.2).1 hq hq'
  calc
    Nat.card C = Nat.card ((l : CoreLabels a q) × F l) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv label)).symm
    _ = ∑ l : CoreLabels a q, Nat.card (F l) := Nat.card_sigma
    _ ≤ ∑ l : CoreLabels a q, coreWeight l := Finset.sum_le_sum fun l _ => hb l

/-- Momento de automorfismos dos 2-grupos de ordem 2^k, ponderado pelas
classes de ordem ímpar dos seus grupos de automorfismos externos. -/
noncomputable def automorphismMoment (k d : ℕ) : ℕ :=
  ∑ i : OrderClasses (2^k), oddOuterClassCount (orderRepresentative i) *
    Nat.card (MulAut (orderRepresentative i)) ^ d

/-- Para q fixo, o fator fora da soma tem expoente linear em a. Os únicos
termos de crescimento desconhecido na soma são os momentos dos 2-grupos. -/
theorem count_le_sum_automorphism_moments (a q : ℕ) (hq : Odd q) (hq' : 1 < q) :
    Nat.card (OrderClasses (2^a * q)) ≤
      (∑ c : Fin (q.factorial.factorization 2 + 1),
        Nat.card (OrderClasses (2^c.val * q)) *
        automorphismMoment (a - c.val) (c.val + q.primeFactorsList.length - 1)) *
        2 ^ (a * (2 ^ (q.factorial.factorization 2) * q) ^ 2) := by
  classical
  let B := 2 ^ (q.factorial.factorization 2) * q
  let M (l : CoreLabels a q) := oddOuterClassCount (orderRepresentative l.2.1) *
    Nat.card (MulAut (orderRepresentative l.2.1)) ^ (l.1.val + q.primeFactorsList.length - 1)
  have hweight (l : CoreLabels a q) : coreWeight l ≤ M l * 2 ^ (a * B^2) := by
    let N := orderRepresentative l.2.1
    let H := orderRepresentative l.2.2
    have hn : Nat.card (Subgroup.center N) ≤ 2 ^ a := calc
      Nat.card (Subgroup.center N) ≤ Nat.card N :=
        Nat.card_le_card_of_injective (fun z : Subgroup.center N => (z : N)) Subtype.val_injective
      _ = 2 ^ (a - l.1.val) := (orderRepresentative_spec l.2.1).1
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
    have hh : Nat.card H ≤ B := (orderRepresentative_spec l.2.2).1.le.trans
      (Nat.mul_le_mul_right q (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ l.1.isLt)))
    apply Nat.mul_le_mul_left (M l)
    calc
      Nat.card (Subgroup.center N) ^ (Nat.card H ^ 2) ≤ (2^a) ^ (Nat.card H ^ 2) :=
        Nat.pow_le_pow_left hn _
      _ ≤ (2^a) ^ (B ^ 2) := Nat.pow_le_pow_right (Nat.two_pow_pos _) (Nat.pow_le_pow_left hh _)
      _ = _ := (pow_mul _ _ _).symm
  have hsum : ∑ l : CoreLabels a q, M l =
      ∑ c : Fin (q.factorial.factorization 2 + 1), Nat.card (OrderClasses (2^c.val * q)) *
        automorphismMoment (a - c.val) (c.val + q.primeFactorsList.length - 1) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c _
    rw [Fintype.sum_prod_type, automorphismMoment, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    change (∑ _ : OrderClasses (2^c.val * q), oddOuterClassCount (orderRepresentative i) *
      Nat.card (MulAut (orderRepresentative i)) ^ (c.val + q.primeFactorsList.length - 1)) = _
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card (α := OrderClasses (2^c.val * q))]
    simp
  calc
    Nat.card (OrderClasses (2^a * q)) ≤ ∑ l : CoreLabels a q, coreWeight l :=
      count_le_sum_core_weights a q hq hq'
    _ ≤ ∑ l : CoreLabels a q, M l * 2 ^ (a * B^2) := Finset.sum_le_sum fun l _ => hweight l
    _ = _ := by rw [← Finset.sum_mul, hsum]

end Erdos1160.FixedCofactor

open Filter Finset
namespace Erdos1160.FixedCofactor

/-- Número de classes de grupos da ordem indicada, na convenção do problema 1160. -/
noncomputable abbrev groupCount (n : ℕ) := Nat.card (OrderClasses n)

/-- Momento sem o peso de classes de conjugação da proposição 8.5. -/
noncomputable def plainMoment (b d : ℕ) := ∑ i : OrderClasses (2^b),
  Nat.card (MulAut (orderRepresentative i)) ^ d

theorem plainMoment_zero (b : ℕ) : plainMoment b 0 = groupCount (2^b) := by
  classical
  simp only [plainMoment, pow_zero, sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.cast_id]
  exact (Nat.card_eq_fintype_card (α := OrderClasses (2^b))).symm

/-- Uma potência adicional de |Aut| basta para absorver todas as classes externas. -/
theorem moment_le_plainMoment (b d : ℕ) : automorphismMoment b d ≤ plainMoment b (d+1) := by
  classical
  apply sum_le_sum
  intro i _
  let N := orderRepresentative i
  let : Finite (ConjClasses (OuterAut N)) := Finite.of_surjective ConjClasses.mk ConjClasses.mk_surjective
  have ha : oddOuterClassCount N ≤ Nat.card (MulAut N) := calc
    oddOuterClassCount N ≤ Nat.card (ConjClasses (OuterAut N)) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    _ ≤ Nat.card (OuterAut N) :=
      Nat.card_le_card_of_surjective _ ConjClasses.mk_surjective
    _ ≤ Nat.card (MulAut N) := Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
  rw [pow_succ, Nat.mul_comm]
  exact Nat.mul_le_mul_left _ ha

end Erdos1160.FixedCofactor

open Filter Finset CategoryTheory

namespace Erdos1160.FixedCofactor

private theorem plainMoment_mono_exponent (a : ℕ) {d e : ℕ} (h : d ≤ e) :
    plainMoment a d ≤ plainMoment a e := by
  classical
  apply sum_le_sum
  intro i _
  exact Nat.pow_le_pow_right (Nat.card_pos (α := MulAut (orderRepresentative i))) h

private theorem odd_moment_sum (q : ℕ) (hq : Odd q) : ∃ R E : ℕ, ∀ k : ℕ,
    groupCount (2^k*q) ≤ 2^(E*(k+1)) *
      ∑ d ∈ range (R+1), plainMoment (k + Nat.log 2 q - d) d := by
  classical
  by_cases hone : q = 1
  · subst q
    exact ⟨0, 0, fun k => by simp [plainMoment_zero]⟩
  have hqpos : 0 < q := by obtain ⟨v,hv⟩ := hq; omega
  have hq1 : 1 < q := by omega
  have homega : 0 < q.primeFactorsList.length := by
    by_contra! h
    have hl := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    have hp := Nat.prod_primeFactorsList hqpos.ne'
    simp [hl] at hp
    omega
  have hlog : q.primeFactorsList.length ≤ Nat.log 2 q := Nat.le_log_of_pow_le (by decide)
    ((List.pow_card_le_prod q.primeFactorsList 2
      (fun _ hp => (Nat.prime_of_mem_primeFactorsList hp).two_le)).trans_eq (Nat.prod_primeFactorsList hqpos.ne'))
  let v := q.factorial.factorization 2
  let L := Nat.log 2 q
  let B := (2^v*q)^2
  let W (c : Fin (v+1)) := groupCount (2^c.val*q)
  let K := ∑ c : Fin (v+1), W c
  refine ⟨v+L, K+B, fun k => ?_⟩
  let S := ∑ d ∈ range (v+L+1), plainMoment (k+L-d) d
  have hv (c : Fin (v+1)) :
      automorphismMoment (k-c.val) (c.val+q.primeFactorsList.length-1) ≤ S := by
    have h := moment_le_plainMoment (k-c.val) (c.val+q.primeFactorsList.length-1)
    rw [Nat.sub_add_cancel (show 1 ≤ c.val+q.primeFactorsList.length by omega)] at h
    have h' := plainMoment_mono_exponent (k-c.val)
      (show c.val+q.primeFactorsList.length ≤ c.val+L by dsimp [L]; omega)
    have hd : c.val+L ∈ range (v+L+1) := mem_range.mpr (by have := c.isLt; omega)
    have h'' : plainMoment (k+L-(c.val+L)) (c.val+L) ≤ S :=
      single_le_sum (fun (d : ℕ) _ => Nat.zero_le (plainMoment (k+L-d) d)) hd
    rw [show k+L-(c.val+L) = k-c.val by omega] at h''
    exact h.trans (h'.trans h'')
  have hb : groupCount (2^k*q) ≤ K*S*2^(k*B) := by
    apply (count_le_sum_automorphism_moments k q hq hq1).trans
    apply Nat.mul_le_mul_right
    dsimp only [K]
    rw [sum_mul]
    exact sum_le_sum fun c _ => Nat.mul_le_mul_left _ (hv c)
  calc
    _ ≤ K*S*2^(k*B) := hb
    _ ≤ 2^K*S*2^(k*B) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le)
    _ = 2^(K+k*B)*S := by rw [pow_add]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide)
      (show K+k*B ≤ (K+B)*(k+1) by nlinarith only [Nat.zero_le (K*k),Nat.zero_le B]))

private theorem log_two_power_times (e s : ℕ) (hs : s ≠ 0) :
    Nat.log 2 (2^e*s) = e+Nat.log 2 s := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ,show (2^e*2)*s = (2^e*s)*2 by ring,
      Nat.log_mul_base (by decide) (Nat.mul_ne_zero (by positivity) hs),ih]
    omega

theorem fixed_moment_sum (q : ℕ) (hq : 0 < q) : ∃ R E : ℕ, ∀ k : ℕ,
    groupCount (2^k*q) ≤ 2^(E*(k+1)) *
      ∑ d ∈ range (R+1), plainMoment (k + Nat.log 2 q - d) d := by
  obtain ⟨e,s,hs,rfl⟩ := Nat.exists_eq_two_pow_mul_odd hq.ne'
  have hspos : 0 < s := by obtain ⟨v,hv⟩ := hs; omega
  obtain ⟨R,E,hE⟩ := odd_moment_sum s hs
  refine ⟨R,E*(e+1),fun k => ?_⟩
  rw [log_two_power_times e s hspos.ne',← Nat.add_assoc k e,← mul_assoc,← pow_add]
  apply (hE (k+e)).trans
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide)
    (show E*(k+e+1) ≤ E*(e+1)*(k+1) by nlinarith only [Nat.zero_le (E*e*k)]))

theorem sigma_plain_moment (d a : ℕ) :
    Nat.card ((c : OrderClasses (2^a)) × (Fin d → MulAut (orderRepresentative c))) =
      plainMoment a d := by
  classical
  rw [Nat.card_sigma]
  simp only [plainMoment,Nat.card_fun,Nat.card_fin]

end Erdos1160.FixedCofactor

open Filter Finset CategoryTheory Erdos1160

theorem OMA.solution : OMA.R_Erdos1160_erdos_1160_variants_sum_R3_H2_R2.H2 := by
  intro q hq
  obtain ⟨R,E,h⟩ := Erdos1160.FixedCofactor.fixed_moment_sum q hq
  refine ⟨R,E,Filter.Eventually.of_forall fun k => ?_⟩
  change Erdos1160.FixedCofactor.groupCount (2^k*q) ≤ 2^(E*(k+1)) *
    ∑ d ∈ range (R+1), Nat.card ((c : Erdos1160.FixedCofactor.OrderClasses (2^(k+Nat.log 2 q-d))) ×
      (Fin d → MulAut (Erdos1160.FixedCofactor.orderRepresentative c)))
  simp only [Erdos1160.FixedCofactor.sigma_plain_moment]
  exact h k
