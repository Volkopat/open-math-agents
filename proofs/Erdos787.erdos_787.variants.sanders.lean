import FormalConjectures.ErdosProblems.«787»
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.RuzsaCovering
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

/-! Proof of Sanders theorem on sum-free subsets (Erdos Problem 787). -/

namespace Erdos787Sanders

open Finset Filter
open scoped Pointwise Combinatorics.Additive

/- ### Part 1A: Integer model and positive integer reduction -/

private lemma integer_model (A : Finset ℝ) :
    ∃ F : ℝ → ℤ, Set.InjOn F (A : Set ℝ) ∧
      ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, F a + F b = F c ↔ a + b = c := by
  classical
  let P : Finset ℝ := (A ×ˢ A).image fun ab => ab.1 - ab.2
  let Q : Finset ℝ := (A ×ˢ (A ×ˢ A)).image fun abc => abc.1 + abc.2.1 - abc.2.2
  let D := (P ∪ Q).erase 0
  have hD (v : D) : (v : ℝ) ≠ 0 := (Finset.mem_erase.mp v.property).1
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ)
    (fun v : D => (v : ℝ)) hD
  let d : ℕ := ∏ a ∈ A, (f a).den
  have hdn : 0 < d := Finset.prod_pos fun a _ => Rat.pos (f a)
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast hdn.ne'
  let F (a : ℝ) : ℤ := ((d / (f a).den : ℕ) : ℤ) * (f a).num
  have hF (a : ℝ) (ha : a ∈ A) : (F a : ℚ) = (d : ℚ) * f a := by
    have hdvd : (f a).den ∣ d := Finset.dvd_prod_of_mem (fun x => (f x).den) ha
    have hmul : ((d / (f a).den : ℕ) : ℚ) * ((f a).den : ℚ) = (d : ℚ) := by
      exact_mod_cast Nat.div_mul_cancel hdvd
    have ha₀ : ((f a).den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_nz (f a)
    have hnum : ((f a).den : ℚ) * f a = ((f a).num : ℚ) := by
      calc
        ((f a).den : ℚ) * f a = (((f a).num : ℚ) / ((f a).den : ℚ)) * ((f a).den : ℚ) := by
          rw [Rat.num_div_den, mul_comm]
        _ = _ := div_mul_cancel₀ _ ha₀
    calc
      (F a : ℚ) = ((d / (f a).den : ℕ) : ℚ) * ((f a).num : ℚ) := by
        simp only [F, Int.cast_mul, Int.cast_natCast]
      _ = ((d / (f a).den : ℕ) : ℚ) * (((f a).den : ℚ) * f a) := by rw [hnum]
      _ = (d : ℚ) * f a := by rw [← mul_assoc, hmul]
  refine ⟨F, ?_, ?_⟩
  · intro a ha b hb heq
    by_contra hab
    have hmemP : a - b ∈ P := Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
    have hmem : a - b ∈ D := Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hab, Finset.mem_union_left _ hmemP⟩
    have hq := congrArg (fun z : ℤ => (z : ℚ)) heq
    rw [hF a ha, hF b hb] at hq
    have hfab : f a = f b := mul_left_cancel₀ hd hq
    exact hf ⟨a - b, hmem⟩ (by rw [map_sub, hfab, sub_self])
  · intro a ha b hb c hc
    have he : ((F a + F b : ℤ) : ℚ) = (d : ℚ) * f (a + b) := by
      rw [Int.cast_add, hF a ha, hF b hb, map_add, mul_add]
    constructor
    · intro h
      by_contra hABC
      have hmemQ : a + b - c ∈ Q := Finset.mem_image.mpr
        ⟨(a, b, c), Finset.mem_product.mpr ⟨ha, Finset.mem_product.mpr ⟨hb, hc⟩⟩, rfl⟩
      have hmem : a + b - c ∈ D :=
        Finset.mem_erase.mpr ⟨sub_ne_zero.mpr hABC, Finset.mem_union_right _ hmemQ⟩
      have hq := congrArg (fun z : ℤ => (z : ℚ)) h
      rw [he, hF c hc] at hq
      have hfc : f (a + b) = f c := mul_left_cancel₀ hd hq
      exact hf ⟨_, hmem⟩ (by rw [map_sub, hfc, sub_self])
    · intro h
      apply Rat.intCast_injective
      rw [he, hF c hc, h]

private lemma pullback_sumfree {G H : Type*} [Add G] [Add H] [DecidableEq G] [DecidableEq H]
    (A : Finset G) (f : G → H) (hf : Set.InjOn f (A : Set G))
    (hadd : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, f a + f b = f c ↔ a + b = c)
    (C : Finset H) (hC : C ⊆ A.image f) (hfree : Disjoint C.restrictedSumset (A.image f)) :
    ∃ B ⊆ A, C.card = B.card ∧ Disjoint B.restrictedSumset A := by
  let B := A.filter (fun a => f a ∈ C)
  have hBA : B ⊆ A := Finset.filter_subset _ _
  have hBC : B.image f = C := by
    ext c
    constructor
    · intro hc
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hc
      exact (Finset.mem_filter.mp hb).2
    · intro hc
      obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (hC hc)
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, he.symm ▸ hc⟩, he⟩
  refine ⟨B, hBA, ?_, ?_⟩
  · rw [← hBC]
    exact Finset.card_image_of_injOn (hf.mono (Finset.coe_subset.mpr hBA))
  · apply (Erdos787.disjoint_restrictedSumset_iff A B).mpr
    intro a ha b hb hne hsum
    obtain ⟨haA, haC⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbA, hbC⟩ := Finset.mem_filter.mp hb
    have hne' : f a ≠ f b := fun h => hne (hf haA hbA h)
    have hsum' : f a + f b ∈ A.image f := Finset.mem_image.mpr
      ⟨a + b, hsum, ((hadd a haA b hbA (a + b) hsum).mpr rfl).symm⟩
    exact (Erdos787.disjoint_restrictedSumset_iff (A.image f) C).mp hfree (f a) haC (f b) hbC hne' hsum'

private lemma le_g_of_pos_int {n m : ℕ}
    (h : ∀ A : Finset ℤ, (∀ x ∈ A, 0 < x) → (n - 1) / 2 ≤ A.card →
      ∃ B ⊆ A, m ≤ B.card ∧ Disjoint B.restrictedSumset A) : m ≤ Erdos787.g ℝ n := by
  apply Erdos787.le_g
  intro A_R hA_R
  obtain ⟨F, hFinj, hFadd⟩ := integer_model A_R
  let A : Finset ℤ := A_R.image F
  have hAcard : A.card = n := (Finset.card_image_of_injOn hFinj).trans hA_R
  let P := A.filter (fun x : ℤ => 0 < x)
  let N := A.filter (fun x : ℤ => x < 0)
  let Z := A.filter (fun x : ℤ => x = 0)
  have hpart : A.card ≤ P.card + N.card + 1 := by
    have hu : P ∪ N ∪ Z = A := by
      ext x
      simp only [P, N, Z, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro ((hx | hx) | hx) <;> exact hx.1
      · intro hx
        rcases lt_trichotomy x 0 with hlt | heq | hgt
        · exact Or.inl (Or.inr ⟨hx, hlt⟩)
        · exact Or.inr ⟨hx, heq⟩
        · exact Or.inl (Or.inl ⟨hx, hgt⟩)
    have hZ : Z.card ≤ 1 := by
      have : Z ⊆ {0} := fun x hx => Finset.mem_singleton.mpr (Finset.mem_filter.mp hx).2
      simpa using Finset.card_le_card this
    rw [← hu]
    have h1 := Finset.card_union_le P N
    have h2 := Finset.card_union_le (P ∪ N) Z
    omega
  have hC_exists : ∃ C ⊆ A, m ≤ C.card ∧ Disjoint C.restrictedSumset A := by
    by_cases hPN : N.card ≤ P.card
    · have hPcard : (n - 1) / 2 ≤ P.card := by omega
      obtain ⟨C, hCP, hmC, hCfree⟩ := h P (fun _ hx => (Finset.mem_filter.mp hx).2) hPcard
      refine ⟨C, hCP.trans (Finset.filter_subset _ _), hmC, ?_⟩
      apply (Erdos787.disjoint_restrictedSumset_iff A C).mpr
      intro a ha b hb hne hsum
      have hap : 0 < a := (Finset.mem_filter.mp (hCP ha)).2
      have hbp : 0 < b := (Finset.mem_filter.mp (hCP hb)).2
      exact (Erdos787.disjoint_restrictedSumset_iff P C).mp hCfree a ha b hb hne
        (Finset.mem_filter.mpr ⟨hsum, by omega⟩)
    · let neg : ℤ ↪ ℤ := ⟨fun x => -x, neg_injective⟩
      let M := N.map neg
      have hMcard : (n - 1) / 2 ≤ M.card := by rw [Finset.card_map]; omega
      have hMpos : ∀ x ∈ M, 0 < x := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        have := (Finset.mem_filter.mp hy).2
        change 0 < -y; omega
      obtain ⟨C0, hC0M, hmC0, hC0free⟩ := h M hMpos hMcard
      let C := C0.map neg
      refine ⟨C, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
        obtain ⟨z, hz, hzy⟩ := Finset.mem_map.mp (hC0M hy)
        change -z = y at hzy
        have hxz : neg y = z := by change -y = z; omega
        rw [hxz]
        exact (Finset.mem_filter.mp hz).1
      · rw [Finset.card_map]
        exact hmC0
      · apply (Erdos787.disjoint_restrictedSumset_iff A C).mpr
        intro a ha b hb hne hsum
        obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ha
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hb
        have huv : u ≠ v := fun he => hne (congrArg neg he)
        have hu_pos : 0 < u := hMpos u (hC0M hu)
        have hv_pos : 0 < v := hMpos v (hC0M hv)
        change -u + -v ∈ A at hsum
        have hmemN : -(u + v) ∈ N := by
          refine Finset.mem_filter.mpr ⟨?_, by omega⟩
          rwa [neg_add]
        have hmemM : u + v ∈ M := Finset.mem_map.mpr ⟨-(u + v), hmemN, by change -(-(u + v)) = u + v; omega⟩
        exact (Erdos787.disjoint_restrictedSumset_iff M C0).mp hC0free u hu v hv huv hmemM
  obtain ⟨C, hCA, hmC, hCfree⟩ := hC_exists
  obtain ⟨B, hBA, hCB, hBfree⟩ := pullback_sumfree A_R F hFinj hFadd C hCA hCfree
  exact ⟨B, hBA, hmC.trans_eq hCB, hBfree⟩

/- ### Part 1B: Summing sets, Hereditarily Energetic sets, and 2-adic valuation -/

private def IsSumming (k : ℕ) (A X : Finset ℤ) : Prop :=
  ∀ S ⊆ A, S.card = k → ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a + b ∈ X

private lemma isSumming_iff_no_sumfree {k : ℕ} {A X : Finset ℤ} :
    IsSumming k A X ↔ ¬ ∃ S ⊆ A, S.card = k ∧ Disjoint S.restrictedSumset X := by
  constructor
  · rintro h ⟨S, hSA, hSk, hdisj⟩
    obtain ⟨a, ha, b, hb, hne, hmem⟩ := h S hSA hSk
    exact (Erdos787.disjoint_restrictedSumset_iff X S).mp hdisj a ha b hb hne hmem
  · intro h S hSA hSk
    by_contra hno
    push Not at hno
    exact h ⟨S, hSA, hSk, (Erdos787.disjoint_restrictedSumset_iff X S).mpr hno⟩

private def HereditarilyEnergetic (ν : ℝ) (A : Finset ℤ) : Prop :=
  ∀ S ⊆ A, ν * (S.card : ℝ) ^ 4 ≤ (A.card : ℝ) * (E[S] : ℝ)

private lemma hereditarilyEnergetic_of_doubling {A : Finset ℤ} {K : ℝ} (hK : 0 < K)
    (hdbl : ((A + A).card : ℝ) ≤ K * (A.card : ℝ)) :
    HereditarilyEnergetic (K⁻¹) A := by
  intro S hSA
  have h1 : ((S.card : ℝ) ^ 2) * ((S.card : ℝ) ^ 2) ≤ ((S + S).card : ℝ) * (E[S] : ℝ) := by
    exact_mod_cast Finset.le_card_add_mul_addEnergy S S
  have h2 : ((S + S).card : ℝ) ≤ ((A + A).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.add_subset_add hSA hSA)
  have h3 : (S.card : ℝ) ^ 4 ≤ K * (A.card : ℝ) * (E[S] : ℝ) := by
    calc (S.card : ℝ) ^ 4 = ((S.card : ℝ) ^ 2) * ((S.card : ℝ) ^ 2) := by ring
      _ ≤ ((S + S).card : ℝ) * (E[S] : ℝ) := h1
      _ ≤ ((A + A).card : ℝ) * (E[S] : ℝ) := mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
      _ ≤ (K * (A.card : ℝ)) * (E[S] : ℝ) := mul_le_mul_of_nonneg_right hdbl (Nat.cast_nonneg _)
  have h4 := mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hK.le)
  calc K⁻¹ * (S.card : ℝ) ^ 4 ≤ K⁻¹ * (K * (A.card : ℝ) * (E[S] : ℝ)) := h4
    _ = (A.card : ℝ) * (E[S] : ℝ) := by field_simp

private lemma hereditarilyEnergetic_of_summing {k : ℕ} {A X : Finset ℤ} {K : ℝ}
    (hk : 2 ≤ k) (hK : 1 ≤ K) (hX : (X.card : ℝ) ≤ K * (A.card : ℝ))
    (hsum : IsSumming k A X) :
    HereditarilyEnergetic (1 / (4 * K * (k : ℝ) ^ 4)) A := by
  intro S hSA
  by_cases hSsmall : S.card ≤ k ^ 2
  · have hE : (S.card : ℝ) ^ 2 ≤ (E[S] : ℝ) := by
      exact_mod_cast Finset.le_addEnergy_self (s := S)
    have hSA' : (S.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hSA
    have hSk : (S.card : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hSsmall
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    have hden_pos : (0 : ℝ) < 4 * K * (k : ℝ) ^ 4 := by positivity
    rw [one_div, inv_mul_le_iff₀ hden_pos]
    have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
    have hS4 : (S.card : ℝ) ^ 4 ≤ (k : ℝ) ^ 2 * (A.card : ℝ) * (S.card : ℝ) ^ 2 := by
      calc (S.card : ℝ) ^ 4 = (S.card : ℝ) * (S.card : ℝ) * (S.card : ℝ) ^ 2 := by ring
        _ ≤ (k : ℝ) ^ 2 * (A.card : ℝ) * (S.card : ℝ) ^ 2 := by
          gcongr
    have h4K : (k : ℝ) ^ 2 ≤ 4 * K * (k : ℝ) ^ 4 := by
      have hk4 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
        calc (k : ℝ) ^ 2 = (k : ℝ) ^ 2 * 1 := by ring
          _ ≤ (k : ℝ) ^ 2 * (k : ℝ) ^ 2 := by gcongr
          _ = (k : ℝ) ^ 4 := by ring
      nlinarith
    calc (S.card : ℝ) ^ 4 ≤ (k : ℝ) ^ 2 * (A.card : ℝ) * (S.card : ℝ) ^ 2 := hS4
      _ ≤ (4 * K * (k : ℝ) ^ 4) * (A.card : ℝ) * (S.card : ℝ) ^ 2 := by gcongr
      _ ≤ (4 * K * (k : ℝ) ^ 4) * ((A.card : ℝ) * (E[S] : ℝ)) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)) (by positivity)
  · push Not at hSsmall
    have hSpos : 0 < S.card := by
      have : 0 < k ^ 2 := by positivity
      omega
    let T : Finset (Fin k → ℤ) := Fintype.piFinset (fun _ : Fin k => S)
    let pairs : Finset (Fin k × Fin k) := (univ : Finset (Fin k × Fin k)).filter (fun p => p.1 < p.2)
    have hTcard : T.card = S.card ^ k := by simp [T]
    have hpairs_card : pairs.card = k * (k - 1) / 2 := by
      have h1 : pairs.card * 2 = ((univ : Finset (Fin k × Fin k)).filter (fun p => p.1 ≠ p.2)).card := by
        have hdisj : Disjoint pairs ((univ : Finset (Fin k × Fin k)).filter (fun p => p.2 < p.1)) := by
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          have h1 := (Finset.mem_filter.mp hp1).2
          have h2 := (Finset.mem_filter.mp hp2).2
          exact lt_asymm h1 h2
        have hu : pairs ∪ (univ.filter (fun p : Fin k × Fin k => p.2 < p.1)) =
            univ.filter (fun p : Fin k × Fin k => p.1 ≠ p.2) := by
          ext p
          simp only [pairs, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
          exact (ne_iff_lt_or_gt (a := p.1) (b := p.2)).symm
        have hswap : (univ.filter (fun p : Fin k × Fin k => p.2 < p.1)).card = pairs.card := by
          refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
          · intro p hp; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
          · intro p₁ _ p₂ _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
          · intro q hq; exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩, rfl⟩
        rw [← hu, Finset.card_union_of_disjoint hdisj, hswap, mul_two]
      have hne_card : ((univ : Finset (Fin k × Fin k)).filter (fun p => p.1 ≠ p.2)).card = k * k - k := by
        have hdiag : ((univ : Finset (Fin k × Fin k)).filter (fun p => p.1 = p.2)).card = k := by
          refine (Finset.card_bij (fun p _ => p.1) (fun _ _ => Finset.mem_univ _) ?_ ?_).trans (by simp)
          · intro p₁ hp₁ p₂ hp₂ h
            have e1 := (Finset.mem_filter.mp hp₁).2
            have e2 := (Finset.mem_filter.mp hp₂).2
            exact Prod.ext h (e1.symm.trans (h.trans e2))
          · intro i _; exact ⟨(i, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, rfl⟩
        have hsum := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin k × Fin k))) (fun p => p.1 = p.2)
        simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hsum
        rw [hdiag] at hsum
        exact Nat.eq_sub_of_add_eq' hsum
      have hkk : k * k - k = k * (k - 1) := by
        rw [Nat.mul_sub_left_distrib, mul_one]
      have h2p : pairs.card * 2 = k * (k - 1) := by rw [h1, hne_card, hkk]
      omega
    let badRep := T.filter (fun x => ∃ p ∈ pairs, x p.1 = x p.2)
    let goodSum := T.filter (fun x => ∃ p ∈ pairs, x p.1 + x p.2 ∈ X)
    have hT_sub : T ⊆ badRep ∪ goodSum := by
      intro x hx
      rw [Finset.mem_union]
      by_cases hrep : ∃ p ∈ pairs, x p.1 = x p.2
      · exact Or.inl (Finset.mem_filter.mpr ⟨hx, hrep⟩)
      · right
        refine Finset.mem_filter.mpr ⟨hx, ?_⟩
        have hx_inj : Function.Injective x := by
          intro i j hij
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hrep ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, hij⟩
          · exact hrep ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, hij.symm⟩
        have himg_sub : (univ : Finset (Fin k)).image x ⊆ A := by
          intro y hy
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
          exact hSA ((Fintype.mem_piFinset.mp hx) i)
        have himg_card : ((univ : Finset (Fin k)).image x).card = k := by
          rw [Finset.card_image_of_injective _ hx_inj, Finset.card_univ, Fintype.card_fin]
        obtain ⟨a, ha, b, hb, hne, habX⟩ := hsum _ himg_sub himg_card
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
        have hij : i ≠ j := fun h => hne (congrArg x h)
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, habX⟩
        · exact ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩, by rwa [add_comm]⟩
    have hbad_le : badRep.card ≤ pairs.card * S.card ^ (k - 1) := by
      calc badRep.card ≤ (pairs.biUnion (fun p => T.filter (fun x => x p.1 = x p.2))).card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨hxT, p, hp, hxp⟩ := Finset.mem_filter.mp hx
            exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hxT, hxp⟩⟩
        _ ≤ ∑ p ∈ pairs, (T.filter (fun x => x p.1 = x p.2)).card := Finset.card_biUnion_le
        _ = ∑ _p ∈ pairs, S.card ^ (k - 1) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            have hne : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
            let U := Fintype.piFinset (fun _ : {i : Fin k // i ≠ p.2} => S)
            have hUcard : U.card = S.card ^ (k - 1) := by
              simp [U, Fintype.card_piFinset, Fintype.card_subtype_compl]
            rw [← hUcard]
            refine Finset.card_bij (fun x _ i => x i.1) ?_ ?_ ?_
            · intro x hx
              exact Fintype.mem_piFinset.mpr fun i => (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1) i.1
            · intro x₁ hx₁ x₂ hx₂ h
              funext i
              by_cases hi : i = p.2
              · subst hi
                have e1 := (Finset.mem_filter.mp hx₁).2
                have e2 := (Finset.mem_filter.mp hx₂).2
                have h1 := congrFun h ⟨p.1, hne⟩
                exact e1.symm.trans (h1.trans e2)
              · exact congrFun h ⟨i, hi⟩
            · intro y hy
              let x : Fin k → ℤ := fun i => if hi : i = p.2 then y ⟨p.1, hne⟩ else y ⟨i, hi⟩
              refine ⟨x, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩, ?_⟩
              · by_cases hi : i = p.2
                · simp [x, hi, Fintype.mem_piFinset.mp hy]
                · simp [x, hi, Fintype.mem_piFinset.mp hy]
              · simp [x, hne]
              · funext i; simp [x, i.2]
        _ = pairs.card * S.card ^ (k - 1) := by simp
    let sumPairs := (S ×ˢ S).filter (fun ab => ab.1 + ab.2 ∈ X)
    have hgood_le : goodSum.card ≤ pairs.card * (sumPairs.card * S.card ^ (k - 2)) := by
      calc goodSum.card ≤ (pairs.biUnion (fun p => T.filter (fun x => x p.1 + x p.2 ∈ X))).card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨hxT, p, hp, hxp⟩ := Finset.mem_filter.mp hx
            exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hxT, hxp⟩⟩
        _ ≤ ∑ p ∈ pairs, (T.filter (fun x => x p.1 + x p.2 ∈ X)).card := Finset.card_biUnion_le
        _ = ∑ _p ∈ pairs, (sumPairs.card * S.card ^ (k - 2)) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            have hne : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
            let U := Fintype.piFinset (fun _ : {i : Fin k // i ≠ p.1 ∧ i ≠ p.2} => S)
            have hsub_card : Fintype.card {i : Fin k // i ≠ p.1 ∧ i ≠ p.2} = k - 2 := by
              have h1 : Fintype.card {i : Fin k // i ≠ p.1 ∧ i ≠ p.2} =
                  ((univ : Finset (Fin k)).filter (fun i => i ≠ p.1 ∧ i ≠ p.2)).card := Fintype.card_subtype _
              rw [h1]
              have h2 : (univ : Finset (Fin k)).filter (fun i => i ≠ p.1 ∧ i ≠ p.2) =
                  (univ : Finset (Fin k)) \ {p.1, p.2} := by
                ext i; simp [not_or]
              rw [h2, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
                  Fintype.card_fin, Finset.card_pair hne]
            have hUcard : (sumPairs ×ˢ U).card = sumPairs.card * S.card ^ (k - 2) := by
              rw [Finset.card_product]
              simp [U, Fintype.card_piFinset, hsub_card]
            rw [← hUcard]
            refine Finset.card_bij (fun x _ => ((x p.1, x p.2), fun i => x i.1)) ?_ ?_ ?_
            · intro x hx
              have hxT := (Finset.mem_filter.mp hx).1
              have hxp := (Finset.mem_filter.mp hx).2
              refine Finset.mem_product.mpr ⟨?_, ?_⟩
              · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
                  ⟨Fintype.mem_piFinset.mp hxT p.1, Fintype.mem_piFinset.mp hxT p.2⟩, hxp⟩
              · exact Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hxT i.1
            · intro x₁ _ x₂ _ h
              have h1 := congrArg (fun q => q.1.1) h
              have h2 := congrArg (fun q => q.1.2) h
              have h3 := congrArg Prod.snd h
              funext i
              by_cases hi1 : i = p.1
              · subst hi1; exact h1
              · by_cases hi2 : i = p.2
                · subst hi2; exact h2
                · exact congrFun h3 ⟨i, hi1, hi2⟩
            · rintro ⟨⟨a, b⟩, y⟩ hmem
              obtain ⟨hab, hy⟩ := Finset.mem_product.mp hmem
              obtain ⟨habS, habX⟩ := Finset.mem_filter.mp hab
              obtain ⟨haS, hbS⟩ := Finset.mem_product.mp habS
              let x : Fin k → ℤ := fun i =>
                if hi1 : i = p.1 then a else if hi2 : i = p.2 then b else y ⟨i, hi1, hi2⟩
              refine ⟨x, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩, ?_⟩
              · by_cases hi1 : i = p.1
                · simp [x, hi1, haS]
                · by_cases hi2 : i = p.2
                  · simp [x, hi2, hne.symm, hbS]
                  · simp [x, hi1, hi2, Fintype.mem_piFinset.mp hy]
              · simp [x, hne.symm, habX]
              · refine Prod.ext (Prod.ext (by simp [x]) (by simp [x, hne.symm])) ?_
                funext i; simp [x, i.2.1, i.2.2]
        _ = pairs.card * (sumPairs.card * S.card ^ (k - 2)) := by simp
    have hcomb : S.card ^ k ≤ pairs.card * S.card ^ (k - 1) + pairs.card * (sumPairs.card * S.card ^ (k - 2)) := by
      have h1 := Finset.card_le_card hT_sub
      rw [hTcard] at h1
      exact h1.trans ((Finset.card_union_le badRep goodSum).trans (Nat.add_le_add hbad_le hgood_le))
    have hpow1 : S.card ^ k = S.card * S.card ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
    have hpow2 : S.card ^ (k - 1) = S.card * S.card ^ (k - 2) := by
      conv_lhs => rw [show k - 1 = (k - 2) + 1 by omega, pow_succ']
    have hpow_pos : 0 < S.card ^ (k - 2) := pow_pos hSpos _
    have hcancel : S.card * S.card ≤ pairs.card * S.card + pairs.card * sumPairs.card := by
      have hmul : (S.card * S.card) * S.card ^ (k - 2) ≤
          (pairs.card * S.card + pairs.card * sumPairs.card) * S.card ^ (k - 2) := by
        calc (S.card * S.card) * S.card ^ (k - 2)
            = S.card * (S.card * S.card ^ (k - 2)) := by ring
          _ = S.card ^ k := by rw [← hpow2, ← hpow1]
          _ ≤ pairs.card * S.card ^ (k - 1) + pairs.card * (sumPairs.card * S.card ^ (k - 2)) := hcomb
          _ = (pairs.card * S.card + pairs.card * sumPairs.card) * S.card ^ (k - 2) := by rw [hpow2]; ring
      exact Nat.le_of_mul_le_mul_right hmul hpow_pos
    have hpairs_le : 2 * pairs.card ≤ k ^ 2 := by
      rw [hpairs_card, sq]
      have h1 : 2 * (k * (k - 1) / 2) ≤ k * (k - 1) := Nat.mul_div_le _ 2
      have h2 : k * (k - 1) ≤ k * k := Nat.mul_le_mul_left k (Nat.sub_le k 1)
      omega
    have hsum_lb : (S.card : ℝ) ^ 2 ≤ (k : ℝ) ^ 2 * (sumPairs.card : ℝ) := by
      have hcancelR : (S.card : ℝ) * (S.card : ℝ) ≤ (pairs.card : ℝ) * (S.card : ℝ) + (pairs.card : ℝ) * (sumPairs.card : ℝ) := by
        exact_mod_cast hcancel
      have hpairsR : 2 * (pairs.card : ℝ) ≤ (k : ℝ) ^ 2 := by exact_mod_cast hpairs_le
      have hSkR : (k : ℝ) ^ 2 < (S.card : ℝ) := by exact_mod_cast hSsmall
      nlinarith
    have hcs : (sumPairs.card : ℝ) ^ 2 ≤ (X.card : ℝ) * (E[S] : ℝ) := by
      exact_mod_cast Finset.card_sq_le_card_mul_addEnergy S S X
    have hden_pos : (0 : ℝ) < 4 * K * (k : ℝ) ^ 4 := by positivity
    rw [one_div, inv_mul_le_iff₀ hden_pos]
    have h1 : (S.card : ℝ) ^ 4 ≤ (k : ℝ) ^ 4 * (sumPairs.card : ℝ) ^ 2 := by
      calc (S.card : ℝ) ^ 4 = ((S.card : ℝ) ^ 2) ^ 2 := by ring
        _ ≤ ((k : ℝ) ^ 2 * (sumPairs.card : ℝ)) ^ 2 := by
          gcongr
        _ = (k : ℝ) ^ 4 * (sumPairs.card : ℝ) ^ 2 := by ring
    have h2 : (k : ℝ) ^ 4 * (sumPairs.card : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 * (K * (A.card : ℝ) * (E[S] : ℝ)) := by
      have hcs' : (sumPairs.card : ℝ) ^ 2 ≤ K * (A.card : ℝ) * (E[S] : ℝ) :=
        hcs.trans (mul_le_mul_of_nonneg_right hX (Nat.cast_nonneg _))
      exact mul_le_mul_of_nonneg_left hcs' (by positivity)
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) A.card) (Nat.cast_nonneg (α := ℝ) E[S])]

private noncomputable def v2Class (z : ℤ) : Option ℕ :=
  if z = 0 then none else some (padicValInt 2 z)

private lemma two_pow_dvd_of_v2Class_eq {z : ℤ} {m : ℕ} (h : v2Class z = some m) :
    (2 : ℤ) ^ m ∣ z ∧ ¬ ((2 : ℤ) ^ (m + 1) ∣ z) := by
  have hz : z ≠ 0 := by
    intro h0; simp [v2Class, h0] at h
  simp only [v2Class, hz, ↓reduceIte, Option.some.injEq] at h
  subst h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨padicValInt_dvd z, ?_⟩
  intro hdvd
  have hle := (padicValInt_dvd_iff (p := 2) (padicValInt 2 z + 1) z).mp hdvd
  rcases hle with rfl | hle
  · exact hz rfl
  · omega

private lemma v2Class_ultrametric {a₁ a₂ a₃ a₄ : ℤ} (heq : a₁ + a₂ = a₃ + a₄) :
    v2Class a₁ = v2Class a₂ ∨ v2Class a₁ = v2Class a₃ ∨ v2Class a₁ = v2Class a₄ ∨
    v2Class a₂ = v2Class a₃ ∨ v2Class a₂ = v2Class a₄ ∨ v2Class a₃ = v2Class a₄ := by
  by_contra hno
  push Not at hno
  rcases hno with ⟨h12, h13, h14, h23, h24, h34⟩
  let vals : Finset ℕ := ({a₁, a₂, a₃, a₄} : Finset ℤ).filter (· ≠ 0) |>.image (padicValInt 2)
  have hvals_ne : vals.Nonempty := by
    by_cases h1 : a₁ = 0
    · have h2 : a₂ ≠ 0 := fun h2 => h12 (by simp [v2Class, h1, h2])
      exact ⟨padicValInt 2 a₂, Finset.mem_image.mpr ⟨a₂, Finset.mem_filter.mpr ⟨by simp, h2⟩, rfl⟩⟩
    · exact ⟨padicValInt 2 a₁, Finset.mem_image.mpr ⟨a₁, Finset.mem_filter.mpr ⟨by simp, h1⟩, rfl⟩⟩
  let m := vals.min' hvals_ne
  have hm_mem : m ∈ vals := Finset.min'_mem vals hvals_ne
  obtain ⟨u, hu_filt, hum⟩ := Finset.mem_image.mp hm_mem
  obtain ⟨hu_in, hu_ne⟩ := Finset.mem_filter.mp hu_filt
  have hdiv_other : ∀ x ∈ ({a₁, a₂, a₃, a₄} : Finset ℤ), v2Class x ≠ some m → (2 : ℤ) ^ (m + 1) ∣ x := by
    intro x hx hne
    by_cases hx0 : x = 0
    · subst hx0; exact dvd_zero _
    · have hx_val : padicValInt 2 x ∈ vals :=
        Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hx0⟩, rfl⟩
      have hge : m ≤ padicValInt 2 x := Finset.min'_le vals _ hx_val
      have hneq : padicValInt 2 x ≠ m := by
        intro he
        exact hne (by simp [v2Class, hx0, he])
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact (padicValInt_dvd_iff (p := 2) (m + 1) x).mpr (Or.inr (by omega))
  have hu_v2 : v2Class u = some m := by simp [v2Class, hu_ne, hum]
  have hnot_u : ¬ ((2 : ℤ) ^ (m + 1) ∣ u) := (two_pow_dvd_of_v2Class_eq hu_v2).2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu_in
  rcases hu_in with rfl | rfl | rfl | rfl
  · have d2 := hdiv_other a₂ (by simp) (by rw [← hu_v2]; exact h12.symm)
    have d3 := hdiv_other a₃ (by simp) (by rw [← hu_v2]; exact h13.symm)
    have d4 := hdiv_other a₄ (by simp) (by rw [← hu_v2]; exact h14.symm)
    have hu_eq : u = a₃ + a₄ - a₂ := by omega
    exact hnot_u (hu_eq ▸ dvd_sub (dvd_add d3 d4) d2)
  · have d1 := hdiv_other a₁ (by simp) (by rw [← hu_v2]; exact h12)
    have d3 := hdiv_other a₃ (by simp) (by rw [← hu_v2]; exact h23.symm)
    have d4 := hdiv_other a₄ (by simp) (by rw [← hu_v2]; exact h24.symm)
    have hu_eq : u = a₃ + a₄ - a₁ := by omega
    exact hnot_u (hu_eq ▸ dvd_sub (dvd_add d3 d4) d1)
  · have d1 := hdiv_other a₁ (by simp) (by rw [← hu_v2]; exact h13)
    have d2 := hdiv_other a₂ (by simp) (by rw [← hu_v2]; exact h23)
    have d4 := hdiv_other a₄ (by simp) (by rw [← hu_v2]; exact h34.symm)
    have hu_eq : u = a₁ + a₂ - a₄ := by omega
    exact hnot_u (hu_eq ▸ dvd_sub (dvd_add d1 d2) d4)
  · have d1 := hdiv_other a₁ (by simp) (by rw [← hu_v2]; exact h14)
    have d2 := hdiv_other a₂ (by simp) (by rw [← hu_v2]; exact h24)
    have d3 := hdiv_other a₃ (by simp) (by rw [← hu_v2]; exact h34)
    have hu_eq : u = a₁ + a₂ - a₃ := by omega
    exact hnot_u (hu_eq ▸ dvd_sub (dvd_add d1 d2) d3)

private lemma twoAdic_energy_prune {A : Finset ℤ} {ν ε : ℝ}
    (hν : 0 < ν) (hε : 0 < ε) (hHE : HereditarilyEnergetic ν A) :
    let heavy : Finset (Option ℕ) := (A.image v2Class).filter
      (fun c => ε ^ 2 * ν * (A.card : ℝ) < ((A.filter (fun z => v2Class z = c)).card : ℝ))
    let Alow : Finset ℤ := A.filter (fun z => v2Class z ∉ heavy)
    (Alow.card : ℝ) ≤ 3 * ε * (A.card : ℝ) ∧
    (heavy.card : ℝ) * (ε ^ 2 * ν) ≤ 1 := by
  classical
  intro heavy Alow
  have hheavy_card : (heavy.card : ℝ) * (ε ^ 2 * ν) ≤ 1 := by
    by_cases hA0 : A.card = 0
    · have : heavy = ∅ := by
        have hAe : A = ∅ := Finset.card_eq_zero.mp hA0
        simp [heavy, hAe]
      simp [this]
    · have hApos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hA0
      have hsum_le : ∑ c ∈ heavy, ((A.filter (fun z => v2Class z = c)).card : ℝ) ≤ (A.card : ℝ) := by
        have hdisj : (heavy : Set (Option ℕ)).PairwiseDisjoint (fun c => A.filter (fun z => v2Class z = c)) := by
          intro c₁ _ c₂ _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro z hz1 hz2
          exact hne ((Finset.mem_filter.mp hz1).2.symm.trans (Finset.mem_filter.mp hz2).2)
        have hsub : heavy.biUnion (fun c => A.filter (fun z => v2Class z = c)) ⊆ A := by
          intro z hz
          obtain ⟨_, _, hzA⟩ := Finset.mem_biUnion.mp hz
          exact (Finset.mem_filter.mp hzA).1
        have hnat : ∑ c ∈ heavy, (A.filter (fun z => v2Class z = c)).card ≤ A.card := by
          rw [← Finset.card_biUnion hdisj]
          exact Finset.card_le_card hsub
        exact_mod_cast hnat
      have hsum_gt : (heavy.card : ℝ) * (ε ^ 2 * ν * (A.card : ℝ)) ≤
          ∑ c ∈ heavy, ((A.filter (fun z => v2Class z = c)).card : ℝ) := by
        calc (heavy.card : ℝ) * (ε ^ 2 * ν * (A.card : ℝ))
            = ∑ _c ∈ heavy, (ε ^ 2 * ν * (A.card : ℝ)) := by simp
          _ ≤ ∑ c ∈ heavy, ((A.filter (fun z => v2Class z = c)).card : ℝ) :=
              Finset.sum_le_sum fun c hc => le_of_lt (Finset.mem_filter.mp hc).2
      have hmul : (heavy.card : ℝ) * (ε ^ 2 * ν) * (A.card : ℝ) ≤ 1 * (A.card : ℝ) := by
        nlinarith
      exact le_of_mul_le_mul_right hmul hApos
  refine ⟨?_, hheavy_card⟩
  let Q := ((Alow ×ˢ Alow) ×ˢ (Alow ×ˢ Alow)).filter (fun q => q.1.1 + q.2.1 = q.1.2 + q.2.2)
  have hEQ : E[Alow] = Q.card := rfl
  let Q12 := Q.filter (fun q => v2Class q.1.1 = v2Class q.2.1)
  let Q13 := Q.filter (fun q => v2Class q.1.1 = v2Class q.1.2)
  let Q14 := Q.filter (fun q => v2Class q.1.1 = v2Class q.2.2)
  let Q23 := Q.filter (fun q => v2Class q.2.1 = v2Class q.1.2)
  let Q24 := Q.filter (fun q => v2Class q.2.1 = v2Class q.2.2)
  let Q34 := Q.filter (fun q => v2Class q.1.2 = v2Class q.2.2)
  have hQ_sub : Q ⊆ Q12 ∪ Q13 ∪ Q14 ∪ Q23 ∪ Q24 ∪ Q34 := by
    intro q hq
    have heq := (Finset.mem_filter.mp hq).2
    have hor := v2Class_ultrametric heq
    simp only [Q12, Q13, Q14, Q23, Q24, Q34, Finset.mem_union, Finset.mem_filter]
    rcases hor with h | h | h | h | h | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨hq, h⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨hq, h⟩))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hq, h⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨hq, h⟩))
    · exact Or.inl (Or.inr ⟨hq, h⟩)
    · exact Or.inr ⟨hq, h⟩
  have hfiber_le : ∀ z ∈ Alow, ((Alow.filter (fun w => v2Class w = v2Class z)).card : ℝ) ≤
      ε ^ 2 * ν * (A.card : ℝ) := by
    intro z hz
    have hzA : z ∈ A := (Finset.mem_filter.mp hz).1
    have hnot : v2Class z ∉ heavy := (Finset.mem_filter.mp hz).2
    have himg : v2Class z ∈ A.image v2Class := Finset.mem_image_of_mem _ hzA
    have hle : ((A.filter (fun w => v2Class w = v2Class z)).card : ℝ) ≤ ε ^ 2 * ν * (A.card : ℝ) := by
      by_contra hgt
      push Not at hgt
      exact hnot (Finset.mem_filter.mpr ⟨himg, hgt⟩)
    have hsub : Alow.filter (fun w => v2Class w = v2Class z) ⊆ A.filter (fun w => v2Class w = v2Class z) :=
      Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hle
  let pairCount : Finset (ℤ × ℤ × ℤ) := (Alow ×ˢ (Alow ×ˢ Alow)).filter (fun t => v2Class t.1 = v2Class t.2.1)
  have hpairCount_le : (pairCount.card : ℝ) ≤ ε ^ 2 * ν * (A.card : ℝ) * (Alow.card : ℝ) ^ 2 := by
    have hcard_eq : pairCount.card = ∑ a ∈ Alow, ∑ _c ∈ Alow, (Alow.filter (fun b => v2Class a = v2Class b)).card := by
      have h1 : pairCount.card = ∑ a ∈ Alow, ((Alow ×ˢ Alow).filter (fun bc => v2Class a = v2Class bc.1)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.card_filter]
      rw [h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.card_filter, Finset.sum_product_right]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.card_filter]
    have hcard_eqR : (pairCount.card : ℝ) =
        ∑ a ∈ Alow, ∑ _c ∈ Alow, ((Alow.filter (fun b => v2Class b = v2Class a)).card : ℝ) := by
      rw [hcard_eq]; push_cast
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      congr 2; ext b; simp [eq_comm]
    rw [hcard_eqR]
    calc ∑ a ∈ Alow, ∑ _c ∈ Alow, ((Alow.filter (fun b => v2Class b = v2Class a)).card : ℝ)
        ≤ ∑ _a ∈ Alow, ∑ _c ∈ Alow, (ε ^ 2 * ν * (A.card : ℝ)) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun _ _ => hfiber_le a ha
      _ = ε ^ 2 * ν * (A.card : ℝ) * (Alow.card : ℝ) ^ 2 := by
          simp only [Finset.sum_const, nsmul_eq_mul]; ring
  have hle_pc : ∀ (P : Finset ((ℤ × ℤ) × (ℤ × ℤ)))
      (f : ((ℤ × ℤ) × (ℤ × ℤ)) → ℤ × ℤ × ℤ),
      (∀ q ∈ P, f q ∈ pairCount) → Set.InjOn f (P : Set _) → P.card ≤ pairCount.card :=
    fun P f hm hi => Finset.card_le_card_of_injOn f hm hi
  have h12 : Q12.card ≤ pairCount.card := hle_pc Q12 (fun q => (q.1.1, q.2.1, q.1.2))
    (fun q hq => by
      obtain ⟨hqQ, hv⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqP, _⟩ := Finset.mem_filter.mp hqQ
      obtain ⟨h1, h3⟩ := Finset.mem_product.mp hqP
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp h1).1,
        Finset.mem_product.mpr ⟨(Finset.mem_product.mp h3).1, (Finset.mem_product.mp h1).2⟩⟩, hv⟩)
    (fun q₁ hq₁ q₂ hq₂ h => by
      dsimp only at h
      have e1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₁).1).2
      have e2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₂).1).2
      have ha : q₁.1.1 = q₂.1.1 := congrArg (fun t : ℤ × ℤ × ℤ => t.1) h
      have hb : q₁.2.1 = q₂.2.1 := congrArg (fun t => t.2.1) h
      have hc : q₁.1.2 = q₂.1.2 := congrArg (fun t => t.2.2) h
      have hd : q₁.2.2 = q₂.2.2 := by omega
      exact Prod.ext (Prod.ext ha hc) (Prod.ext hb hd))
  have h13 : Q13.card ≤ pairCount.card := hle_pc Q13 (fun q => (q.1.1, q.1.2, q.2.1))
    (fun q hq => by
      obtain ⟨hqQ, hv⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqP, _⟩ := Finset.mem_filter.mp hqQ
      obtain ⟨h1, h3⟩ := Finset.mem_product.mp hqP
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp h1).1,
        Finset.mem_product.mpr ⟨(Finset.mem_product.mp h1).2, (Finset.mem_product.mp h3).1⟩⟩, hv⟩)
    (fun q₁ hq₁ q₂ hq₂ h => by
      dsimp only at h
      have e1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₁).1).2
      have e2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₂).1).2
      have ha : q₁.1.1 = q₂.1.1 := congrArg (fun t : ℤ × ℤ × ℤ => t.1) h
      have hc : q₁.1.2 = q₂.1.2 := congrArg (fun t => t.2.1) h
      have hb : q₁.2.1 = q₂.2.1 := congrArg (fun t => t.2.2) h
      have hd : q₁.2.2 = q₂.2.2 := by omega
      exact Prod.ext (Prod.ext ha hc) (Prod.ext hb hd))
  have h14 : Q14.card ≤ pairCount.card := hle_pc Q14 (fun q => (q.1.1, q.2.2, q.2.1))
    (fun q hq => by
      obtain ⟨hqQ, hv⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqP, _⟩ := Finset.mem_filter.mp hqQ
      obtain ⟨h1, h3⟩ := Finset.mem_product.mp hqP
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp h1).1,
        Finset.mem_product.mpr ⟨(Finset.mem_product.mp h3).2, (Finset.mem_product.mp h3).1⟩⟩, hv⟩)
    (fun q₁ hq₁ q₂ hq₂ h => by
      dsimp only at h
      have e1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₁).1).2
      have e2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₂).1).2
      have ha : q₁.1.1 = q₂.1.1 := congrArg (fun t : ℤ × ℤ × ℤ => t.1) h
      have hd : q₁.2.2 = q₂.2.2 := congrArg (fun t => t.2.1) h
      have hb : q₁.2.1 = q₂.2.1 := congrArg (fun t => t.2.2) h
      have hc : q₁.1.2 = q₂.1.2 := by omega
      exact Prod.ext (Prod.ext ha hc) (Prod.ext hb hd))
  have h23 : Q23.card ≤ pairCount.card := hle_pc Q23 (fun q => (q.2.1, q.1.2, q.1.1))
    (fun q hq => by
      obtain ⟨hqQ, hv⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqP, _⟩ := Finset.mem_filter.mp hqQ
      obtain ⟨h1, h3⟩ := Finset.mem_product.mp hqP
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp h3).1,
        Finset.mem_product.mpr ⟨(Finset.mem_product.mp h1).2, (Finset.mem_product.mp h1).1⟩⟩, hv⟩)
    (fun q₁ hq₁ q₂ hq₂ h => by
      dsimp only at h
      have e1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₁).1).2
      have e2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₂).1).2
      have hb : q₁.2.1 = q₂.2.1 := congrArg (fun t : ℤ × ℤ × ℤ => t.1) h
      have hc : q₁.1.2 = q₂.1.2 := congrArg (fun t => t.2.1) h
      have ha : q₁.1.1 = q₂.1.1 := congrArg (fun t => t.2.2) h
      have hd : q₁.2.2 = q₂.2.2 := by omega
      exact Prod.ext (Prod.ext ha hc) (Prod.ext hb hd))
  have h24 : Q24.card ≤ pairCount.card := hle_pc Q24 (fun q => (q.2.1, q.2.2, q.1.1))
    (fun q hq => by
      obtain ⟨hqQ, hv⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqP, _⟩ := Finset.mem_filter.mp hqQ
      obtain ⟨h1, h3⟩ := Finset.mem_product.mp hqP
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp h3).1,
        Finset.mem_product.mpr ⟨(Finset.mem_product.mp h3).2, (Finset.mem_product.mp h1).1⟩⟩, hv⟩)
    (fun q₁ hq₁ q₂ hq₂ h => by
      dsimp only at h
      have e1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₁).1).2
      have e2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₂).1).2
      have hb : q₁.2.1 = q₂.2.1 := congrArg (fun t : ℤ × ℤ × ℤ => t.1) h
      have hd : q₁.2.2 = q₂.2.2 := congrArg (fun t => t.2.1) h
      have ha : q₁.1.1 = q₂.1.1 := congrArg (fun t => t.2.2) h
      have hc : q₁.1.2 = q₂.1.2 := by omega
      exact Prod.ext (Prod.ext ha hc) (Prod.ext hb hd))
  have h34 : Q34.card ≤ pairCount.card := hle_pc Q34 (fun q => (q.1.2, q.2.2, q.1.1))
    (fun q hq => by
      obtain ⟨hqQ, hv⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqP, _⟩ := Finset.mem_filter.mp hqQ
      obtain ⟨h1, h3⟩ := Finset.mem_product.mp hqP
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp h1).2,
        Finset.mem_product.mpr ⟨(Finset.mem_product.mp h3).2, (Finset.mem_product.mp h1).1⟩⟩, hv⟩)
    (fun q₁ hq₁ q₂ hq₂ h => by
      dsimp only at h
      have e1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₁).1).2
      have e2 := (Finset.mem_filter.mp (Finset.mem_filter.mp hq₂).1).2
      have hc : q₁.1.2 = q₂.1.2 := congrArg (fun t : ℤ × ℤ × ℤ => t.1) h
      have hd : q₁.2.2 = q₂.2.2 := congrArg (fun t => t.2.1) h
      have ha : q₁.1.1 = q₂.1.1 := congrArg (fun t => t.2.2) h
      have hb : q₁.2.1 = q₂.2.1 := by omega
      exact Prod.ext (Prod.ext ha hc) (Prod.ext hb hd))
  have hQ_le : Q.card ≤ 6 * pairCount.card := by
    have h1 := Finset.card_le_card hQ_sub
    have u1 := Finset.card_union_le (Q12 ∪ Q13 ∪ Q14 ∪ Q23 ∪ Q24) Q34
    have u2 := Finset.card_union_le (Q12 ∪ Q13 ∪ Q14 ∪ Q23) Q24
    have u3 := Finset.card_union_le (Q12 ∪ Q13 ∪ Q14) Q23
    have u4 := Finset.card_union_le (Q12 ∪ Q13) Q14
    have u5 := Finset.card_union_le Q12 Q13
    omega
  have hE_ub : (E[Alow] : ℝ) ≤ 6 * ε ^ 2 * ν * (A.card : ℝ) * (Alow.card : ℝ) ^ 2 := by
    rw [hEQ]
    calc (Q.card : ℝ) ≤ 6 * (pairCount.card : ℝ) := by exact_mod_cast hQ_le
      _ ≤ 6 * (ε ^ 2 * ν * (A.card : ℝ) * (Alow.card : ℝ) ^ 2) := by linarith
      _ = 6 * ε ^ 2 * ν * (A.card : ℝ) * (Alow.card : ℝ) ^ 2 := by ring
  have hE_lb : ν * (Alow.card : ℝ) ^ 4 ≤ (A.card : ℝ) * (E[Alow] : ℝ) :=
    hHE Alow (Finset.filter_subset _ _)
  have hsq : (Alow.card : ℝ) ^ 2 ≤ (3 * ε * (A.card : ℝ)) ^ 2 := by
    by_cases h0 : Alow.card = 0
    · simp [h0]; positivity
    · have hpos : (0 : ℝ) < (Alow.card : ℝ) ^ 2 := by positivity
      have h1 : ν * (Alow.card : ℝ) ^ 4 ≤ 6 * ε ^ 2 * ν * (A.card : ℝ) ^ 2 * (Alow.card : ℝ) ^ 2 := by
        calc ν * (Alow.card : ℝ) ^ 4 ≤ (A.card : ℝ) * (E[Alow] : ℝ) := hE_lb
          _ ≤ (A.card : ℝ) * (6 * ε ^ 2 * ν * (A.card : ℝ) * (Alow.card : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hE_ub (Nat.cast_nonneg _)
          _ = 6 * ε ^ 2 * ν * (A.card : ℝ) ^ 2 * (Alow.card : ℝ) ^ 2 := by ring
      have h2 : (Alow.card : ℝ) ^ 2 ≤ 6 * ε ^ 2 * (A.card : ℝ) ^ 2 := by
        have hmul : (Alow.card : ℝ) ^ 2 * (ν * (Alow.card : ℝ) ^ 2) ≤
            (6 * ε ^ 2 * (A.card : ℝ) ^ 2) * (ν * (Alow.card : ℝ) ^ 2) := by linarith
        exact le_of_mul_le_mul_right hmul (mul_pos hν hpos)
      nlinarith
  nlinarith [Nat.cast_nonneg (α := ℝ) Alow.card, mul_nonneg hε.le (Nat.cast_nonneg (α := ℝ) A.card)]

private def scale2Finset (j : ℕ) (S : Finset ℤ) : Finset ℤ :=
  S.image (fun x => (2 : ℤ) ^ j * x)

private lemma twoAdic_dilation_small {A S : Finset ℤ} {ν K κ : ℝ} {r : ℕ}
    (hν : 0 < ν) (hK : 1 ≤ K) (hκ : 0 < κ)
    (hHE_A : HereditarilyEnergetic ν A) (hHE_S : HereditarilyEnergetic ν S)
    (hSK : (S.card : ℝ) ≤ K * (A.card : ℝ))
    (hAbig : 10 ≤ κ * (A.card : ℝ))
    (hAll : ∀ j ∈ Finset.Icc 1 r, κ * (A.card : ℝ) ≤ ((scale2Finset j S ∩ A).card : ℝ)) :
    (r : ℝ) ≤ (100 * (1 + K) / κ) ^ 4 / ν ^ 2 := by
  classical
  let ε : ℝ := κ / (8 * (1 + K))
  have hε : 0 < ε := by positivity
  obtain ⟨hAlow, hIA⟩ := twoAdic_energy_prune hν hε hHE_A
  obtain ⟨hSlow, hIS⟩ := twoAdic_energy_prune hν hε hHE_S
  set IA := (A.image v2Class).filter (fun c => ε ^ 2 * ν * (A.card : ℝ) < ((A.filter (fun z => v2Class z = c)).card : ℝ))
  set IS := (S.image v2Class).filter (fun c => ε ^ 2 * ν * (S.card : ℝ) < ((S.filter (fun z => v2Class z = c)).card : ℝ))
  set Alow := A.filter (fun z => v2Class z ∉ IA)
  set Slow := S.filter (fun z => v2Class z ∉ IS)
  have hex : ∀ j ∈ Finset.Icc 1 r, ∃ i ∈ IA, ∃ i' ∈ IS, ∃ a b : ℕ, i = some a ∧ i' = some b ∧ a = j + b := by
    intro j hj
    let E := (scale2Finset j S ∩ A).filter (fun t => t ≠ 0 ∧ v2Class t ∈ IA ∧
      ∃ s ∈ S, (2 : ℤ) ^ j * s = t ∧ v2Class s ∈ IS)
    have hE_ne : E.Nonempty := by
      by_contra hEmp
      rw [Finset.not_nonempty_iff_eq_empty] at hEmp
      have hsub : scale2Finset j S ∩ A ⊆ ({0} : Finset ℤ) ∪ Alow ∪ scale2Finset j Slow := by
        intro t ht
        obtain ⟨htS, htA⟩ := Finset.mem_inter.mp ht
        obtain ⟨s, hsS, hst⟩ := Finset.mem_image.mp htS
        by_cases ht0 : t = 0
        · simp [ht0]
        · by_cases htv : v2Class t ∈ IA
          · by_cases hsv : v2Class s ∈ IS
            · exfalso
              have : t ∈ E := Finset.mem_filter.mpr ⟨ht, ht0, htv, s, hsS, hst, hsv⟩
              rw [hEmp] at this; exact Finset.notMem_empty _ this
            · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨hsS, hsv⟩, hst⟩)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨htA, htv⟩))
      have hcard_le : ((scale2Finset j S ∩ A).card : ℝ) ≤ 1 + (Alow.card : ℝ) + (Slow.card : ℝ) := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le (({0} : Finset ℤ) ∪ Alow) (scale2Finset j Slow)
        have h3 := Finset.card_union_le ({0} : Finset ℤ) Alow
        have h4 : (scale2Finset j Slow).card ≤ Slow.card := Finset.card_image_le
        have h5 : (({0} : Finset ℤ)).card = 1 := Finset.card_singleton 0
        have hnat : (scale2Finset j S ∩ A).card ≤ 1 + Alow.card + Slow.card := by omega
        exact_mod_cast hnat
      have hSlow' : (Slow.card : ℝ) ≤ 3 * ε * K * (A.card : ℝ) := by
        calc (Slow.card : ℝ) ≤ 3 * ε * (S.card : ℝ) := hSlow
          _ ≤ 3 * ε * (K * (A.card : ℝ)) := mul_le_mul_of_nonneg_left hSK (by positivity)
          _ = 3 * ε * K * (A.card : ℝ) := by ring
      have h3eps : 3 * ε * (A.card : ℝ) + 3 * ε * K * (A.card : ℝ) = (3 / 8) * κ * (A.card : ℝ) := by
        dsimp only [ε]; field_simp
      have hbig := hAll j hj
      linarith
    obtain ⟨t, htE⟩ := hE_ne
    obtain ⟨_, ht0, htIA, s, _, hst, hsIS⟩ := Finset.mem_filter.mp htE
    have hs0 : s ≠ 0 := by intro h0; subst h0; simp at hst; exact ht0 hst.symm
    have hvt : v2Class t = some (padicValInt 2 t) := by simp [v2Class, ht0]
    have hvs : v2Class s = some (padicValInt 2 s) := by simp [v2Class, hs0]
    refine ⟨v2Class t, htIA, v2Class s, hsIS, padicValInt 2 t, padicValInt 2 s, hvt, hvs, ?_⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [← hst, padicValInt.mul (pow_ne_zero j (by norm_num)) hs0]
    have hpow2 : padicValInt 2 ((2 : ℤ) ^ j) = j := by
      have hcast : ((2 : ℤ) ^ j) = ((2 ^ j : ℕ) : ℤ) := by norm_cast
      rw [hcast, padicValInt.of_nat, padicValNat.prime_pow]
    rw [hpow2]
  choose fi hfi fi' hfi' fa fb hfa hfb hfab using hex
  have hinj : (Finset.Icc 1 r).card ≤ (IA ×ˢ IS).card := by
    refine Finset.card_le_card_of_injOn (fun j => if hj : j ∈ Finset.Icc 1 r then (fi j hj, fi' j hj) else (none, none)) ?_ ?_
    · intro j hj
      rw [Finset.mem_coe] at hj
      dsimp only
      rw [dif_pos hj]
      exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hfi j hj, hfi' j hj⟩)
    · intro j₁ hj₁ j₂ hj₂ hEq
      rw [Finset.mem_coe] at hj₁ hj₂
      dsimp only at hEq
      rw [dif_pos hj₁, dif_pos hj₂, Prod.mk.injEq] at hEq
      have ha : fa j₁ hj₁ = fa j₂ hj₂ := Option.some.inj ((hfa j₁ hj₁).symm.trans (hEq.1.trans (hfa j₂ hj₂)))
      have hb : fb j₁ hj₁ = fb j₂ hj₂ := Option.some.inj ((hfb j₁ hj₁).symm.trans (hEq.2.trans (hfb j₂ hj₂)))
      have e1 := hfab j₁ hj₁
      have e2 := hfab j₂ hj₂
      omega
  have hr_le : (r : ℝ) ≤ (IA.card : ℝ) * (IS.card : ℝ) := by
    have h1 : r ≤ IA.card * IS.card := by
      simpa [Nat.card_Icc, Finset.card_product] using hinj
    exact_mod_cast h1
  have hIA' : (IA.card : ℝ) ≤ 1 / (ε ^ 2 * ν) := by
    rw [le_div_iff₀ (by positivity)]; exact hIA
  have hIS' : (IS.card : ℝ) ≤ 1 / (ε ^ 2 * ν) := by
    rw [le_div_iff₀ (by positivity)]; exact hIS
  have h1 : (r : ℝ) ≤ (1 / (ε ^ 2 * ν)) * (1 / (ε ^ 2 * ν)) :=
    hr_le.trans (mul_le_mul hIA' hIS' (Nat.cast_nonneg _) (by positivity))
  have h2 : (1 / (ε ^ 2 * ν)) * (1 / (ε ^ 2 * ν)) = (8 * (1 + K) / κ) ^ 4 / ν ^ 2 := by
    dsimp only [ε]; field_simp
  rw [h2] at h1
  refine h1.trans ?_
  have h8 : 8 * (1 + K) / κ ≤ 100 * (1 + K) / κ := by
    apply div_le_div_of_nonneg_right _ hκ.le; linarith
  gcongr

/- ### Part 1C: Sanders's Proposition 2.7 from PropG, and Main Theorem from Proposition 2.7 -/

private def PropGSpec : Prop :=
  ∃ (C₁ C₂ C₃ C₄ C₅ C₆ : ℕ),
    ∀ (k r : ℕ) (η : ℝ) (A X : Finset ℤ),
      2 ≤ k → 1 ≤ r → 0 < η → η ≤ 1 →
      A.Nonempty → A ⊆ X → ((X \ A).card : ℝ) ≤ η * (A.card : ℝ) →
      IsSumming k A X →
      (1 / η ≤ ((k * r : ℕ) : ℝ) ^ C₁) ∨
      ((A.card : ℝ) ≤ Real.exp (((k * r : ℕ) : ℝ) ^ C₂)) ∨
      (∃ S : Finset ℤ, S.Nonempty ∧
        HereditarilyEnergetic (1 / (k : ℝ) ^ C₃) S ∧
        (A.card : ℝ) ≤ (k : ℝ) ^ C₄ * (S.card : ℝ) ∧
        (S.card : ℝ) ≤ (k : ℝ) ^ C₅ * (A.card : ℝ) ∧
        ∀ j ∈ Finset.Icc 1 r, (S.card : ℝ) ≤ (k : ℝ) ^ C₆ * ((scale2Finset j S ∩ A).card : ℝ))

private def Prop27Spec : Prop :=
  ∃ (L D : ℕ), 1 ≤ D ∧
    ∀ (k : ℕ) (η : ℝ) (A X : Finset ℤ),
      2 ≤ k → 0 < η → η ≤ 1 →
      A.Nonempty → A ⊆ X → ((X \ A).card : ℝ) ≤ η * (A.card : ℝ) →
      IsSumming k A X →
      (1 / η ≤ (k : ℝ) ^ L) ∨ ((A.card : ℝ) ≤ Real.exp ((k : ℝ) ^ D))

private lemma prop27_of_propG (hG : PropGSpec) : Prop27Spec := by
  obtain ⟨C₁, C₂, C₃, C₄, C₅, C₆, hPropG⟩ := hG
  let B := max (C₃) 4
  let R := 4 * C₅ + 4 * C₄ + 4 * C₆ + 2 * B + 40
  refine ⟨C₁ * (R + 1) + 2, C₂ * (R + 1) + C₄ + C₆ + 10, by omega, ?_⟩
  intro k η A X hk hηpos hη1 hAne hAX hXA hsum
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  let r : ℕ := k ^ R
  have hr1 : 1 ≤ r := Nat.one_le_pow R k (by omega)
  have hkr : ((k * r : ℕ) : ℝ) = (k : ℝ) ^ (R + 1) := by
    simp only [r, Nat.cast_mul, Nat.cast_pow]; rw [← pow_succ']
  rcases hPropG k r η A X hk hr1 hηpos hη1 hAne hAX hXA hsum with h1 | h2 | ⟨S, _, hHE_S, hAS, hSA, hAll⟩
  · left
    rw [hkr, ← pow_mul] at h1
    calc 1 / η ≤ (k : ℝ) ^ ((R + 1) * C₁) := h1
      _ = (k : ℝ) ^ (C₁ * (R + 1)) := by ring_nf
      _ ≤ (k : ℝ) ^ (C₁ * (R + 1) + 2) :=
          pow_le_pow_right₀ (by linarith) (by omega)
  · right
    rw [hkr, ← pow_mul] at h2
    refine h2.trans (Real.exp_le_exp.mpr ?_)
    have : (k : ℝ) ^ ((R + 1) * C₂) = (k : ℝ) ^ (C₂ * (R + 1)) := by ring_nf
    rw [this]
    exact pow_le_pow_right₀ (by linarith) (by omega)
  · -- Apply 2-adic valuation contradiction!
    have hXle : (X.card : ℝ) ≤ 2 * (A.card : ℝ) := by
      have hcard : X.card = A.card + (X \ A).card := by
        have := Finset.card_sdiff_add_card_eq_card hAX
        omega
      have hcardR : (X.card : ℝ) = (A.card : ℝ) + ((X \ A).card : ℝ) := by exact_mod_cast hcard
      nlinarith
    have hHE_A0 := hereditarilyEnergetic_of_summing hk (by norm_num : (1 : ℝ) ≤ 2) hXle hsum
    let ν : ℝ := 1 / (8 * (k : ℝ) ^ B)
    have hν : 0 < ν := by positivity
    have hHE_A : HereditarilyEnergetic ν A := by
      intro U hUA
      have h0 := hHE_A0 U hUA
      have hle : ν ≤ 1 / (4 * 2 * (k : ℝ) ^ 4) := by
        dsimp only [ν]
        apply one_div_le_one_div_of_le (by positivity)
        have : (k : ℝ) ^ 4 ≤ (k : ℝ) ^ B := pow_le_pow_right₀ (by linarith) (le_max_right _ _)
        linarith
      exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans h0
    have hHE_S' : HereditarilyEnergetic ν S := by
      intro U hUS
      have h0 := hHE_S U hUS
      have hle : ν ≤ 1 / (k : ℝ) ^ C₃ := by
        dsimp only [ν]
        apply one_div_le_one_div_of_le (by positivity)
        have : (k : ℝ) ^ C₃ ≤ (k : ℝ) ^ B := pow_le_pow_right₀ (by linarith) (le_max_left _ _)
        nlinarith [pow_pos hk_pos B]
      exact (mul_le_mul_of_nonneg_right hle (by positivity)).trans h0
    let K : ℝ := (k : ℝ) ^ C₅
    have hK : 1 ≤ K := one_le_pow₀ (by linarith)
    let κ : ℝ := 1 / ((k : ℝ) ^ C₄ * (k : ℝ) ^ C₆)
    have hκ : 0 < κ := by positivity
    by_cases hAbig : 10 ≤ κ * (A.card : ℝ)
    · have hAll' : ∀ j ∈ Finset.Icc 1 r, κ * (A.card : ℝ) ≤ ((scale2Finset j S ∩ A).card : ℝ) := by
        intro j hj
        have h1 := hAll j hj
        have h2 : (A.card : ℝ) ≤ (k : ℝ) ^ C₄ * (k : ℝ) ^ C₆ * ((scale2Finset j S ∩ A).card : ℝ) := by
          calc (A.card : ℝ) ≤ (k : ℝ) ^ C₄ * (S.card : ℝ) := hAS
            _ ≤ (k : ℝ) ^ C₄ * ((k : ℝ) ^ C₆ * ((scale2Finset j S ∩ A).card : ℝ)) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = (k : ℝ) ^ C₄ * (k : ℝ) ^ C₆ * ((scale2Finset j S ∩ A).card : ℝ) := by ring
        dsimp only [κ]
        rw [one_div, inv_mul_le_iff₀ (by positivity)]
        exact h2
      have hcontra := twoAdic_dilation_small hν hK hκ hHE_A hHE_S' hSA hAbig hAll'
      exfalso
      have h1K : 1 + K ≤ 2 * (k : ℝ) ^ C₅ := by dsimp only [K]; linarith
      have hnum : 100 * (1 + K) / κ ≤ 200 * (k : ℝ) ^ (C₅ + C₄ + C₆) := by
        dsimp only [κ]
        rw [div_div_eq_mul_div, div_one]
        have : (k : ℝ) ^ C₅ * ((k : ℝ) ^ C₄ * (k : ℝ) ^ C₆) = (k : ℝ) ^ (C₅ + C₄ + C₆) := by
          rw [pow_add, pow_add]; ring
        calc 100 * (1 + K) * ((k : ℝ) ^ C₄ * (k : ℝ) ^ C₆)
            ≤ 100 * (2 * (k : ℝ) ^ C₅) * ((k : ℝ) ^ C₄ * (k : ℝ) ^ C₆) := by gcongr
          _ = 200 * (k : ℝ) ^ (C₅ + C₄ + C₆) := by rw [← this]; ring
      have h200 : (200 : ℝ) ≤ (k : ℝ) ^ 8 := by
        have : (2 : ℝ) ^ 8 ≤ (k : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hk2 8
        norm_num at this; linarith
      have h8sq : (8 : ℝ) ^ 2 ≤ (k : ℝ) ^ 6 := by
        have : (2 : ℝ) ^ 6 ≤ (k : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hk2 6
        norm_num at this; linarith
      have hrb : (100 * (1 + K) / κ) ^ 4 / ν ^ 2 < (k : ℝ) ^ R := by
        have hstep1 : (100 * (1 + K) / κ) ^ 4 ≤ (k : ℝ) ^ (4 * (C₅ + C₄ + C₆) + 32) := by
          calc (100 * (1 + K) / κ) ^ 4 ≤ (200 * (k : ℝ) ^ (C₅ + C₄ + C₆)) ^ 4 :=
                pow_le_pow_left₀ (by positivity) hnum 4
            _ = (200 : ℝ) ^ 4 * (k : ℝ) ^ (4 * (C₅ + C₄ + C₆)) := by
                rw [mul_pow, ← pow_mul, mul_comm _ 4]
            _ ≤ ((k : ℝ) ^ 8) ^ 4 * (k : ℝ) ^ (4 * (C₅ + C₄ + C₆)) := by gcongr
            _ = (k : ℝ) ^ (4 * (C₅ + C₄ + C₆) + 32) := by
                rw [← pow_mul, ← pow_add]; ring_nf
        have hstep2 : 1 / ν ^ 2 ≤ (k : ℝ) ^ (2 * B + 6) := by
          dsimp only [ν]
          rw [one_div_pow, one_div_one_div, mul_pow, ← pow_mul, mul_comm B 2]
          calc (8 : ℝ) ^ 2 * (k : ℝ) ^ (2 * B) ≤ (k : ℝ) ^ 6 * (k : ℝ) ^ (2 * B) := by gcongr
            _ = (k : ℝ) ^ (2 * B + 6) := by rw [← pow_add]; ring_nf
        have hstep3 : (100 * (1 + K) / κ) ^ 4 / ν ^ 2 ≤ (k : ℝ) ^ (4 * C₅ + 4 * C₄ + 4 * C₆ + 2 * B + 38) := by
          rw [div_eq_mul_one_div]
          calc (100 * (1 + K) / κ) ^ 4 * (1 / ν ^ 2)
              ≤ (k : ℝ) ^ (4 * (C₅ + C₄ + C₆) + 32) * (k : ℝ) ^ (2 * B + 6) :=
                mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
            _ = (k : ℝ) ^ (4 * C₅ + 4 * C₄ + 4 * C₆ + 2 * B + 38) := by
                rw [← pow_add]; ring_nf
        have hlt : (k : ℝ) ^ (4 * C₅ + 4 * C₄ + 4 * C₆ + 2 * B + 38) < (k : ℝ) ^ R :=
          pow_lt_pow_right₀ (by linarith) (by omega)
        linarith
      have hr_eq : (r : ℝ) = (k : ℝ) ^ R := by simp [r]
      linarith
    · -- A is small: κ * |A| < 10 → |A| ≤ 10 * k^(C₄ + C₆) ≤ exp(k^(...))
      right
      push Not at hAbig
      have hA_le : (A.card : ℝ) ≤ 10 * (k : ℝ) ^ (C₄ + C₆) := by
        dsimp only [κ] at hAbig
        rw [one_div, inv_mul_lt_iff₀ (by positivity)] at hAbig
        rw [pow_add]; linarith
      have h10 : (10 : ℝ) ≤ (k : ℝ) ^ 4 := by
        have : (2 : ℝ) ^ 4 ≤ (k : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hk2 4
        norm_num at this; linarith
      have hA_pow : (A.card : ℝ) ≤ (k : ℝ) ^ (C₂ * (R + 1) + C₄ + C₆ + 10) := by
        calc (A.card : ℝ) ≤ 10 * (k : ℝ) ^ (C₄ + C₆) := hA_le
          _ ≤ (k : ℝ) ^ 4 * (k : ℝ) ^ (C₄ + C₆) := by gcongr
          _ = (k : ℝ) ^ (C₄ + C₆ + 4) := by rw [← pow_add]; ring_nf
          _ ≤ (k : ℝ) ^ (C₂ * (R + 1) + C₄ + C₆ + 10) :=
              pow_le_pow_right₀ (by linarith) (by omega)
      exact hA_pow.trans (Real.add_one_le_exp _ |>.trans' (by linarith))

private lemma exists_top_slice (A : Finset ℤ) (m : ℕ) (hm : m ≤ A.card) :
    ∃ Z ⊆ A, Z.card = m ∧ ∀ x ∈ A \ Z, ∀ z ∈ Z, x < z := by
  let L := A.sort (· ≥ ·)
  have hLlen : L.length = A.card := A.length_sort _
  have hLnd : L.Nodup := A.sort_nodup _
  let Z := (L.take m).toFinset
  have hZnd : (L.take m).Nodup := hLnd.sublist (List.take_sublist m L)
  have hZcard : Z.card = m := by
    rw [List.toFinset_card_of_nodup hZnd, List.length_take, hLlen, min_eq_left hm]
  have hZA : Z ⊆ A := by
    intro x hx
    have hmem : x ∈ L := List.mem_of_mem_take (List.mem_toFinset.mp hx)
    exact (A.mem_sort _).mp hmem
  refine ⟨Z, hZA, hZcard, ?_⟩
  intro x hx z hz
  obtain ⟨hxA, hxZ⟩ := Finset.mem_sdiff.mp hx
  have hz_take : z ∈ L.take m := List.mem_toFinset.mp hz
  have hx_L : x ∈ L := (A.mem_sort _).mpr hxA
  obtain ⟨iz, hiz_lt, hiz_eq⟩ := List.getElem_of_mem hz_take
  have hiz_m : iz < m := by
    have := List.length_take (i := m) (l := L)
    omega
  obtain ⟨ix, hix_lt, hix_eq⟩ := List.getElem_of_mem hx_L
  have hix_ge : m ≤ ix := by
    by_contra hlt
    push Not at hlt
    apply hxZ
    rw [List.mem_toFinset]
    have hix_t : ix < (L.take m).length := by rw [List.length_take, hLlen]; omega
    have heq : (L.take m)[ix]'hix_t = x := by rw [List.getElem_take, hix_eq]
    rw [← heq]
    exact List.getElem_mem hix_t
  have hiz_L : iz < L.length := by omega
  have hpw := A.pairwise_sort (· ≥ ·)
  have hge : L[iz]'hiz_L ≥ L[ix]'hix_lt := List.pairwise_iff_getElem.mp hpw iz ix hiz_L hix_lt (by omega)
  have hz_eq : L[iz]'hiz_L = z := by
    have := List.getElem_take (xs := L) (i := iz) (j := m) (h := hiz_lt)
    exact this.symm.trans hiz_eq
  have hne : x ≠ z := fun h => hxZ (h ▸ hz)
  rw [hz_eq, hix_eq] at hge
  omega

private lemma sanders_peel_step {k l m D : ℕ} {A : Finset ℤ}
    (_hk : 2 ≤ k) (hl : 1 ≤ l) (hD : 1 ≤ D)
    (hApos : ∀ x ∈ A, 0 < x)
    (hAsize : 2 * D * (2 * l * (m * k + 1)) ^ m ≤ A.card)
    (hP27 : ∀ (U V : Finset ℤ), U.Nonempty → U ⊆ V →
      (D : ℝ) ≤ (U.card : ℝ) → ((V \ U).card : ℝ) ≤ (1 / (l : ℝ)) * (U.card : ℝ) →
      ∃ S ⊆ U, S.card = k ∧ Disjoint S.restrictedSumset V) :
    ∀ r ≤ m, ∃ (S : Fin r → Finset ℤ),
      (∀ i : Fin r, S i ⊆ A ∧ (S i).card = k) ∧
      (∀ i j : Fin r, i ≠ j → Disjoint (S i) (S j)) ∧
      (∀ i : Fin r, ∃ Z ⊆ A, Z.card = 2 * D * (2 * l * (m * k + 1)) ^ i.val ∧
        (∀ x ∈ A \ Z, ∀ z ∈ Z, x < z) ∧ S i ⊆ Z) ∧
      Disjoint (Finset.biUnion Finset.univ S).restrictedSumset A := by
  classical
  let q : ℕ := 2 * l * (m * k + 1)
  have hq_pos : 1 ≤ q := Nat.mul_pos (by omega) (by omega)
  intro r hr
  induction r with
  | zero =>
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
            fun i => Fin.elim0 i, ?_⟩
    simp [Finset.restrictedSumset]
  | succ r ih =>
    obtain ⟨Sprev, hSsub, hSdisj, hSslice, hSfree⟩ := ih (by omega)
    let sz : ℕ := 2 * D * q ^ r
    have hsz_le : sz ≤ A.card := by
      calc sz = 2 * D * q ^ r := rfl
        _ ≤ 2 * D * q ^ m := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq_pos (by omega))
        _ ≤ A.card := hAsize
    obtain ⟨Zr, hZrA, hZrcard, hZrtop⟩ := exists_top_slice A sz hsz_le
    let Uprev : Finset ℤ := Finset.biUnion Finset.univ Sprev
    have hUprev_card : Uprev.card ≤ r * k := by
      calc Uprev.card ≤ ∑ i : Fin r, (Sprev i).card := Finset.card_biUnion_le
        _ = ∑ _i : Fin r, k := Finset.sum_congr rfl fun i _ => (hSsub i).2
        _ = r * k := by simp
    have hnext : ∃ Sr ⊆ Zr, Sr.card = k ∧ Disjoint Sr.restrictedSumset Zr ∧
        Disjoint Sr Uprev ∧ ∀ x ∈ Sr, ∀ y ∈ Uprev, x + y ∉ A := by
      cases r with
      | zero =>
        have hZr_ne : Zr.Nonempty := by
          apply Finset.card_pos.mp
          rw [hZrcard]; dsimp [sz]; positivity
        have hDle : (D : ℝ) ≤ (Zr.card : ℝ) := by
          have : D ≤ Zr.card := by rw [hZrcard]; dsimp [sz]; omega
          exact_mod_cast this
        obtain ⟨Sr, hSrZ, hSrk, hSrfree⟩ := hP27 Zr Zr hZr_ne Subset.rfl hDle (by simp; positivity)
        refine ⟨Sr, hSrZ, hSrk, hSrfree, by simp [Uprev], by simp [Uprev]⟩
      | succ r' =>
        let prevIdx : Fin (r' + 1) := ⟨r', by omega⟩
        obtain ⟨Zprev, hZprevA, hZprev_card, hZprev_top, _⟩ := hSslice prevIdx
        have hUprev_sub_Zprev : Uprev ⊆ Zprev := by
          intro x hx
          obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
          obtain ⟨Zj, hZjA, hZj_card, hZj_top, hSjZ⟩ := hSslice j
          have hxZj : x ∈ Zj := hSjZ hxj
          by_contra hx_not
          have hZj_le : Zj.card ≤ Zprev.card := by
            rw [hZj_card, hZprev_card]
            have hj_le : j.val ≤ prevIdx.val := by
              have := j.isLt; dsimp [prevIdx]; omega
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq_pos hj_le)
          have hsub : insert x Zprev ⊆ Zj := by
            intro y hy
            rcases Finset.mem_insert.mp hy with rfl | hyZ
            · exact hxZj
            · by_contra hy_not
              have h1 : y < x := hZj_top y (Finset.mem_sdiff.mpr ⟨hZprevA hyZ, hy_not⟩) x hxZj
              have h2 : x < y := hZprev_top x (Finset.mem_sdiff.mpr ⟨hZjA hxZj, hx_not⟩) y hyZ
              omega
          have hcard_lt := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hx_not] at hcard_lt
          omega
        let forbid : Finset ℤ := Zprev - (insert 0 Uprev)
        let Ar : Finset ℤ := Zr \ forbid
        have hforbid_le : forbid.card ≤ Zprev.card * (m * k + 1) := by
          calc forbid.card ≤ Zprev.card * (insert 0 Uprev).card := Finset.card_sub_le
            _ ≤ Zprev.card * (Uprev.card + 1) := Nat.mul_le_mul_left _ (Finset.card_insert_le _ _)
            _ ≤ Zprev.card * (m * k + 1) := by
              have : Uprev.card ≤ m * k := hUprev_card.trans (Nat.mul_le_mul_right k (by omega))
              exact Nat.mul_le_mul_left _ (by omega)
        have hsz_eq : sz = q * Zprev.card := by
          dsimp [sz]
          rw [hZprev_card]
          rw [show 2 * D * q ^ (r' + 1) = q * (2 * D * q ^ r') by rw [pow_succ]; ring]
        have hdiff_le : (Zr \ Ar).card ≤ forbid.card := by
          apply Finset.card_le_card
          intro x hx
          have h1 := (Finset.mem_sdiff.mp hx).1
          have h2 := (Finset.mem_sdiff.mp hx).2
          by_contra hnot
          exact h2 (Finset.mem_sdiff.mpr ⟨h1, hnot⟩)
        have hforbid_small : 2 * l * forbid.card ≤ Zr.card := by
          rw [hZrcard, hsz_eq]
          dsimp only [q]
          calc 2 * l * forbid.card ≤ 2 * l * (Zprev.card * (m * k + 1)) := Nat.mul_le_mul_left _ hforbid_le
            _ = 2 * l * (m * k + 1) * Zprev.card := by ring
        have hAr_ge : Zr.card ≤ 2 * Ar.card := by
          have hsub : Ar ⊆ Zr := Finset.sdiff_subset
          have hcard := Finset.card_sdiff_add_card_eq_card hsub
          have : 2 * (Zr \ Ar).card ≤ Zr.card := by
            have := hdiff_le
            nlinarith
          omega
        have hAr_ne : Ar.Nonempty := by
          apply Finset.card_pos.mp
          have : 2 ≤ Zr.card := by rw [hZrcard]; dsimp [sz]; nlinarith [Nat.one_le_pow (r' + 1) q hq_pos]
          omega
        have hAr_D : (D : ℝ) ≤ (Ar.card : ℝ) := by
          have h1 : 2 * D ≤ Zr.card := by
            rw [hZrcard]; dsimp [sz]
            exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))
          exact_mod_cast (show D ≤ Ar.card by omega)
        have hAr_rat : ((Zr \ Ar).card : ℝ) ≤ (1 / (l : ℝ)) * (Ar.card : ℝ) := by
          rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
          have hnat : (Zr \ Ar).card * l ≤ Ar.card := by
            have h1 := hdiff_le
            have h2 := hforbid_small
            have h3 := hAr_ge
            nlinarith
          exact_mod_cast hnat
        obtain ⟨Sr, hSrAr, hSrk, hSrfree⟩ := hP27 Ar Zr hAr_ne Finset.sdiff_subset hAr_D hAr_rat
        refine ⟨Sr, hSrAr.trans Finset.sdiff_subset, hSrk, hSrfree, ?_, ?_⟩
        · rw [Finset.disjoint_left]
          intro x hxSr hxU
          have hx_not_f : x ∉ forbid := (Finset.mem_sdiff.mp (hSrAr hxSr)).2
          apply hx_not_f
          exact Finset.mem_sub.mpr ⟨x, hUprev_sub_Zprev hxU, 0, Finset.mem_insert_self _ _, sub_zero x⟩
        · intro x hxSr y hyU hxyA
          have hx_pos : 0 < x := hApos x (hZrA (Finset.sdiff_subset (hSrAr hxSr)))
          have hxy_Zprev : x + y ∈ Zprev := by
            by_contra hnot
            have hlt := hZprev_top (x + y) (Finset.mem_sdiff.mpr ⟨hxyA, hnot⟩) y (hUprev_sub_Zprev hyU)
            omega
          have hx_not_f : x ∉ forbid := (Finset.mem_sdiff.mp (hSrAr hxSr)).2
          apply hx_not_f
          exact Finset.mem_sub.mpr ⟨x + y, hxy_Zprev, y, Finset.mem_insert_of_mem hyU, by ring⟩
    obtain ⟨Sr, hSrZ, hSrk, hSrfreeZ, hSrDisjU, hSrNoCross⟩ := hnext
    let Snew : Fin (r + 1) → Finset ℤ := Fin.snoc Sprev Sr
    refine ⟨Snew, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Snew, Fin.snoc_last]; exact ⟨hSrZ.trans hZrA, hSrk⟩
      · intro j; simp only [Snew, Fin.snoc_castSucc]; exact hSsub j
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · intro hij; exact (hij rfl).elim
        · intro j' _; simp only [Snew, Fin.snoc_last, Fin.snoc_castSucc]
          exact hSrDisjU.mono_right (Finset.subset_biUnion_of_mem Sprev (Finset.mem_univ j'))
      · intro i' j
        refine Fin.lastCases ?_ ?_ j
        · intro _; simp only [Snew, Fin.snoc_last, Fin.snoc_castSucc]
          exact (hSrDisjU.mono_right (Finset.subset_biUnion_of_mem Sprev (Finset.mem_univ i'))).symm
        · intro j' hij
          simp only [Snew, Fin.snoc_castSucc]
          exact hSdisj i' j' (fun h => hij (congrArg Fin.castSucc h))
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Snew, Fin.snoc_last, Fin.val_last]
        exact ⟨Zr, hZrA, hZrcard, hZrtop, hSrZ⟩
      · intro j
        simp only [Snew, Fin.snoc_castSucc, Fin.val_castSucc]
        exact hSslice j
    · -- Show restrictedSumset (⋃ Snew) is disjoint from A
      apply (Erdos787.disjoint_restrictedSumset_iff A _).mpr
      intro a ha b hb hne habA
      obtain ⟨ia, _, haS⟩ := Finset.mem_biUnion.mp ha
      obtain ⟨ib, _, hbS⟩ := Finset.mem_biUnion.mp hb
      revert haS
      refine Fin.lastCases ?_ ?_ ia
      · -- a ∈ Sr
        intro haS
        simp only [Snew, Fin.snoc_last] at haS
        revert hbS
        refine Fin.lastCases ?_ ?_ ib
        · -- b ∈ Sr: since a, b ∈ Sr ⊆ Zr and positive, a + b > a, so a + b ∈ Zr!
          intro hbS
          simp only [Snew, Fin.snoc_last] at hbS
          have hb_pos : 0 < b := hApos b (hZrA (hSrZ hbS))
          have habZr : a + b ∈ Zr := by
            by_contra hnot
            have hlt := hZrtop (a + b) (Finset.mem_sdiff.mpr ⟨habA, hnot⟩) a (hSrZ haS)
            omega
          exact (Erdos787.disjoint_restrictedSumset_iff Zr Sr).mp hSrfreeZ a haS b hbS hne habZr
        · intro jb hbS
          simp only [Snew, Fin.snoc_castSucc] at hbS
          exact hSrNoCross a haS b (Finset.mem_biUnion.mpr ⟨jb, Finset.mem_univ _, hbS⟩) habA
      · intro ja haS
        simp only [Snew, Fin.snoc_castSucc] at haS
        revert hbS
        refine Fin.lastCases ?_ ?_ ib
        · intro hbS
          simp only [Snew, Fin.snoc_last] at hbS
          rw [add_comm] at habA
          exact hSrNoCross b hbS a (Finset.mem_biUnion.mpr ⟨ja, Finset.mem_univ _, haS⟩) habA
        · intro jb hbS
          simp only [Snew, Fin.snoc_castSucc] at hbS
          exact (Erdos787.disjoint_restrictedSumset_iff A Uprev).mp hSfree
            a (Finset.mem_biUnion.mpr ⟨ja, Finset.mem_univ _, haS⟩)
            b (Finset.mem_biUnion.mpr ⟨jb, Finset.mem_univ _, hbS⟩) hne habA

private lemma sanders_of_prop27 (h27 : Prop27Spec) :
    ∃ c > (0 : ℝ), ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ^ (1 + c) ≤ (Erdos787.g ℝ n : ℝ) := by
  obtain ⟨L, D, hD1, hP27⟩ := h27
  let c : ℝ := 1 / (4 * (D : ℝ))
  have hc : 0 < c := by positivity
  refine ⟨c, hc, ?_⟩
  have htend : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev1 : ∀ᶠ n : ℕ in atTop,
      (Real.log (n : ℝ)) ^ (1 / (2 * (D : ℝ))) ≥ 4 ∧
      Real.log (n : ℝ) ≥ 100 ∧
      ((L : ℝ) + 4) * Real.log (Real.log (n : ℝ)) ≤ (Real.log (n : ℝ)) ^ (1 / (4 * (D : ℝ))) / 8 := by
    have hlog_ge4 : ∀ᶠ n : ℕ in atTop, (Real.log (n : ℝ)) ^ (1 / (2 * (D : ℝ))) ≥ 4 :=
      ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < 1 / (2 * (D : ℝ)))).comp htend).eventually_ge_atTop 4
    have hlog_ge100 : ∀ᶠ n : ℕ in atTop, Real.log (n : ℝ) ≥ 100 :=
      htend.eventually_ge_atTop 100
    have hlo : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ (1 / (4 * (D : ℝ)))) :=
      isLittleO_log_rpow_atTop (by positivity)
    have hbound : ∀ᶠ x : ℝ in atTop,
        ((L : ℝ) + 4) * Real.log x ≤ x ^ (1 / (4 * (D : ℝ))) / 8 := by
      have hpos : (0 : ℝ) < 1 / (8 * ((L : ℝ) + 4)) := by positivity
      filter_upwards [hlo.bound hpos, eventually_gt_atTop (1 : ℝ)] with x hx hx1
      have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1.le
      have hrp0 : 0 ≤ x ^ (1 / (4 * (D : ℝ))) := Real.rpow_nonneg (by linarith) _
      rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hrp0] at hx
      have hmul := mul_le_mul_of_nonneg_left hx (show (0 : ℝ) ≤ (L : ℝ) + 4 by positivity)
      calc ((L : ℝ) + 4) * Real.log x
          ≤ ((L : ℝ) + 4) * (1 / (8 * ((L : ℝ) + 4)) * x ^ (1 / (4 * (D : ℝ)))) := hmul
        _ = x ^ (1 / (4 * (D : ℝ))) / 8 := by field_simp
    filter_upwards [hlog_ge4, hlog_ge100, htend.eventually hbound] with n h1 h2 h3
    exact ⟨h1, h2, h3⟩
  filter_upwards [hev1, eventually_ge_atTop (1000 : ℕ)] with n ⟨hpow4, hlog100, hloglog⟩ hn1000
  let t : ℝ := Real.log (n : ℝ)
  have ht_pos : 0 < t := by linarith
  let k : ℕ := Nat.floor (t ^ (1 / (2 * (D : ℝ))))
  have hk_ge4 : 4 ≤ k := Nat.le_floor (by exact_mod_cast hpow4)
  have hk_ge2 : 2 ≤ k := by omega
  have hk_le : (k : ℝ) ≤ t ^ (1 / (2 * (D : ℝ))) := Nat.floor_le (by positivity)
  have hk_gt : t ^ (1 / (2 * (D : ℝ))) / 2 ≤ (k : ℝ) := by
    have h1 : t ^ (1 / (2 * (D : ℝ))) - 1 < (k : ℝ) := Nat.sub_one_lt_floor _
    linarith
  let l : ℕ := k ^ L + 1
  have hl1 : 1 ≤ l := by omega
  let D0 : ℕ := Nat.ceil (Real.exp ((k : ℝ) ^ D)) + 1
  have hD0_ge1 : 1 ≤ D0 := by omega
  let m : ℕ := Nat.ceil (t ^ (1 + c) / (k : ℝ))
  have hmk_ge : t ^ (1 + c) ≤ ((m * k : ℕ) : ℝ) := by
    push_cast
    have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
    have := Nat.le_ceil (t ^ (1 + c) / (k : ℝ))
    rwa [div_le_iff₀ hkpos] at this
  have hm_le : (m : ℝ) ≤ 3 * t ^ (1 - 1 / (4 * (D : ℝ))) := by
    have hm1 : (m : ℝ) < t ^ (1 + c) / (k : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
    have hdiv : t ^ (1 + c) / (k : ℝ) ≤ 2 * t ^ (1 - 1 / (4 * (D : ℝ))) := by
      have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
      rw [div_le_iff₀ hkpos]
      calc t ^ (1 + c) = t ^ (1 - 1 / (4 * (D : ℝ))) * t ^ (1 / (2 * (D : ℝ))) := by
            rw [← Real.rpow_add ht_pos]; congr 1; dsimp [c]; field_simp; ring
        _ = 2 * t ^ (1 - 1 / (4 * (D : ℝ))) * (t ^ (1 / (2 * (D : ℝ))) / 2) := by ring
        _ ≤ 2 * t ^ (1 - 1 / (4 * (D : ℝ))) * (k : ℝ) := by
            exact mul_le_mul_of_nonneg_left hk_gt (by positivity)
    have h1le : (1 : ℝ) ≤ t ^ (1 - 1 / (4 * (D : ℝ))) := by
      refine Real.one_le_rpow (by linarith) ?_
      have : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
      have : 1 / (4 * (D : ℝ)) ≤ 1 / 4 := by
        apply one_div_le_one_div_of_le (by norm_num); linarith
      linarith
    linarith
  have hkD_le : (k : ℝ) ^ D ≤ t ^ (1 / 2 : ℝ) := by
    calc (k : ℝ) ^ D ≤ (t ^ (1 / (2 * (D : ℝ)))) ^ D := pow_le_pow_left₀ (by positivity) hk_le D
      _ = t ^ ((1 / (2 * (D : ℝ))) * (D : ℝ)) := by rw [← Real.rpow_natCast, ← Real.rpow_mul ht_pos.le]
      _ = t ^ (1 / 2 : ℝ) := by congr 1; field_simp
  have hsqrt_le : t ^ (1 / 2 : ℝ) ≤ t / 10 := by
    have ht10 : (10 : ℝ) ^ 2 ≤ t := by norm_num; linarith
    have hsq : (t ^ (1 / 2 : ℝ)) ^ 2 ≤ (t / 10) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht_pos.le]
      norm_num
      nlinarith
    nlinarith [Real.rpow_nonneg ht_pos.le (1 / 2 : ℝ)]
  have hD0_le : (2 * D0 : ℝ) ≤ Real.exp (t / 4) := by
    have hceil : (D0 : ℝ) < Real.exp ((k : ℝ) ^ D) + 2 := by
      dsimp only [D0]; push_cast
      have := Nat.ceil_lt_add_one (a := Real.exp ((k : ℝ) ^ D)) (Real.exp_pos _).le
      linarith
    have h2 : (2 * D0 : ℝ) ≤ 6 * Real.exp (t / 10) := by
      have hexp1 : (1 : ℝ) ≤ Real.exp (t / 10) := Real.one_le_exp (by linarith)
      have hexp2 : Real.exp ((k : ℝ) ^ D) ≤ Real.exp (t / 10) := Real.exp_le_exp.mpr (hkD_le.trans hsqrt_le)
      linarith
    have h6 : (6 : ℝ) ≤ Real.exp (t * (3 / 20)) := by
      have : (6 : ℝ) ≤ t * (3 / 20) + 1 := by linarith
      exact this.trans (Real.add_one_le_exp _)
    calc (2 * D0 : ℝ) ≤ 6 * Real.exp (t / 10) := h2
      _ ≤ Real.exp (t * (3 / 20)) * Real.exp (t / 10) := mul_le_mul_of_nonneg_right h6 (Real.exp_pos _).le
      _ = Real.exp (t / 4) := by rw [← Real.exp_add]; congr 1; ring
  have hq_log : Real.log ((2 * l * (m * k + 1) : ℕ) : ℝ) ≤ ((L : ℝ) + 4) * Real.log t := by
    have hk_le_t : (k : ℝ) ≤ t := by
      refine hk_le.trans ?_
      calc t ^ (1 / (2 * (D : ℝ))) ≤ t ^ (1 : ℝ) := by
            apply Real.rpow_le_rpow_of_exponent_le (by linarith)
            have : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD1
            rw [div_le_one (by positivity)]; linarith
        _ = t := Real.rpow_one t
    have h2l : (2 * (l : ℝ)) ≤ 4 * t ^ L := by
      have hl_le : (l : ℝ) ≤ (k : ℝ) ^ L + 1 := by dsimp [l]; push_cast; rfl
      have h1 : (k : ℝ) ^ L ≤ t ^ L := pow_le_pow_left₀ (by positivity) hk_le_t L
      have h2 : (1 : ℝ) ≤ t ^ L := one_le_pow₀ (by linarith)
      linarith
    have hmk1 : ((m * k + 1 : ℕ) : ℝ) ≤ 4 * t ^ 2 := by
      push_cast
      have hm_le_t : (m : ℝ) ≤ 3 * t := by
        refine hm_le.trans ?_
        have : t ^ (1 - 1 / (4 * (D : ℝ))) ≤ t ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (sub_le_self 1 (by positivity))
        rw [Real.rpow_one] at this; linarith
      nlinarith
    have hprod : ((2 * l * (m * k + 1) : ℕ) : ℝ) ≤ t ^ (L + 4) := by
      push_cast
      calc 2 * (l : ℝ) * ((m : ℝ) * (k : ℝ) + 1)
          ≤ (4 * t ^ L) * (4 * t ^ 2) := mul_le_mul h2l (by push_cast at hmk1; exact hmk1) (by positivity) (by positivity)
        _ = 16 * t ^ (L + 2) := by rw [pow_add]; ring
        _ ≤ t ^ 2 * t ^ (L + 2) := by gcongr; nlinarith
        _ = t ^ (L + 4) := by rw [← pow_add]; ring_nf
    have hpos_lhs : (0 : ℝ) < ((2 * l * (m * k + 1) : ℕ) : ℝ) := by positivity
    calc Real.log ((2 * l * (m * k + 1) : ℕ) : ℝ)
        ≤ Real.log (t ^ (L + 4)) := Real.log_le_log hpos_lhs hprod
      _ = ((L + 4 : ℕ) : ℝ) * Real.log t := Real.log_pow t (L + 4)
      _ = ((L : ℝ) + 4) * Real.log t := by push_cast; ring
  have hqm_le : (((2 * l * (m * k + 1)) ^ m : ℕ) : ℝ) ≤ Real.exp (t / 2) := by
    have hbase_pos : (0 : ℝ) < ((2 * l * (m * k + 1) : ℕ) : ℝ) := by positivity
    rw [Nat.cast_pow, ← Real.exp_log (pow_pos hbase_pos m), Real.log_pow]
    apply Real.exp_le_exp.mpr
    have hm_log : (m : ℝ) * Real.log ((2 * l * (m * k + 1) : ℕ) : ℝ) ≤
        (3 * t ^ (1 - 1 / (4 * (D : ℝ)))) * (t ^ (1 / (4 * (D : ℝ))) / 8) := by
      have hlog_nonneg : 0 ≤ Real.log ((2 * l * (m * k + 1) : ℕ) : ℝ) :=
        Real.log_nonneg (by exact_mod_cast (Nat.mul_pos (by omega : 0 < 2 * l) (by omega : 0 < m * k + 1)))
      exact mul_le_mul hm_le (hq_log.trans hloglog) hlog_nonneg (by positivity)
    have hprod_t : (3 * t ^ (1 - 1 / (4 * (D : ℝ)))) * (t ^ (1 / (4 * (D : ℝ))) / 8) = (3 / 8) * t := by
      have : t ^ (1 - 1 / (4 * (D : ℝ))) * t ^ (1 / (4 * (D : ℝ))) = t := by
        rw [← Real.rpow_add ht_pos]; simp
      linarith
    linarith
  have hbudget_R : ((2 * D0 * (2 * l * (m * k + 1)) ^ m : ℕ) : ℝ) ≤ ((n - 1) / 2 : ℕ) := by
    have h1 : ((2 * D0 * (2 * l * (m * k + 1)) ^ m : ℕ) : ℝ) ≤ Real.exp (t * (3 / 4)) := by
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
      calc (2 * (D0 : ℝ)) * ((((2 * l * (m * k + 1)) ^ m : ℕ) : ℝ))
          ≤ Real.exp (t / 4) * Real.exp (t / 2) :=
            mul_le_mul hD0_le hqm_le (by positivity) (Real.exp_pos _).le
        _ = Real.exp (t * (3 / 4)) := by rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (t * (3 / 4)) ≤ (n : ℝ) / 4 := by
      have hexp_t : Real.exp t = (n : ℝ) := Real.exp_log (by positivity)
      have h4 : (4 : ℝ) ≤ Real.exp (t / 4) := by
        have : (4 : ℝ) ≤ t / 4 + 1 := by linarith
        exact this.trans (Real.add_one_le_exp _)
      have hmul : 4 * Real.exp (t * (3 / 4)) ≤ Real.exp t := by
        calc 4 * Real.exp (t * (3 / 4)) ≤ Real.exp (t / 4) * Real.exp (t * (3 / 4)) :=
              mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
          _ = Real.exp t := by rw [← Real.exp_add]; congr 1; ring
      linarith
    have h3 : (n : ℝ) / 4 ≤ (((n - 1) / 2 : ℕ) : ℝ) := by
      have hnat : n ≤ 4 * ((n - 1) / 2) := by omega
      have hR : (n : ℝ) ≤ 4 * (((n - 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      linarith
    linarith
  have hbudget : 2 * D0 * (2 * l * (m * k + 1)) ^ m ≤ (n - 1) / 2 := by exact_mod_cast hbudget_R
  have hmk_le_g : m * k ≤ Erdos787.g ℝ n := by
    apply le_g_of_pos_int
    intro A hApos hAcard
    have hAsize : 2 * D0 * (2 * l * (m * k + 1)) ^ m ≤ A.card := hbudget.trans hAcard
    have hP27_inst : ∀ (U V : Finset ℤ), U.Nonempty → U ⊆ V →
        (D0 : ℝ) ≤ (U.card : ℝ) → ((V \ U).card : ℝ) ≤ (1 / (l : ℝ)) * (U.card : ℝ) →
        ∃ S ⊆ U, S.card = k ∧ Disjoint S.restrictedSumset V := by
      intro U V hUne hUV hUD hVU
      by_contra hno
      have hsum : IsSumming k U V := isSumming_iff_no_sumfree.mpr hno
      have hηpos : (0 : ℝ) < 1 / (l : ℝ) := by positivity
      have hη1 : 1 / (l : ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]; exact_mod_cast hl1
      rcases hP27 k (1 / (l : ℝ)) U V hk_ge2 hηpos hη1 hUne hUV hVU hsum with hbad1 | hbad2
      · rw [one_div_one_div] at hbad1
        have hlt : (k : ℝ) ^ L < (l : ℝ) := by dsimp only [l]; push_cast; linarith
        linarith
      · have hlt : Real.exp ((k : ℝ) ^ D) < (D0 : ℝ) := by
          dsimp only [D0]; push_cast
          have := Nat.le_ceil (Real.exp ((k : ℝ) ^ D))
          linarith
        linarith
    obtain ⟨S, hSsub, hSdisj, _, hSfree⟩ := sanders_peel_step hk_ge2 hl1 hD0_ge1 hApos hAsize hP27_inst m le_rfl
    let B := Finset.biUnion Finset.univ S
    refine ⟨B, ?_, ?_, hSfree⟩
    · intro x hx
      obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
      exact (hSsub i).1 hxi
    · have hpw : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint S := fun i _ j _ hne => hSdisj i j hne
      rw [Finset.card_biUnion hpw]
      have : ∑ i : Fin m, (S i).card = m * k := by
        simp [fun i => (hSsub i).2]
      omega
  have hmk_le_gR : ((m * k : ℕ) : ℝ) ≤ (Erdos787.g ℝ n : ℝ) := by exact_mod_cast hmk_le_g
  exact hmk_ge.trans hmk_le_gR

private structure SymNbhd where
  set : Finset ℤ
  zero_mem : (0 : ℤ) ∈ set
  neg_mem : ∀ x ∈ set, -x ∈ set

private lemma SymNbhd.nonempty (Z : SymNbhd) : Z.set.Nonempty := ⟨0, Z.zero_mem⟩

private lemma SymNbhd.card_pos (Z : SymNbhd) : 0 < Z.set.card := Z.nonempty.card_pos

private def scale2Set (m : ℕ) (S : Set ℤ) : Set ℤ :=
  (fun x : ℤ => (2 : ℤ) ^ m * x) '' S

private def scale2Fin (m : ℕ) (S : Finset ℤ) : Finset ℤ :=
  S.image (fun x : ℤ => (2 : ℤ) ^ m * x)

private lemma scale2Fin_card (m : ℕ) (S : Finset ℤ) : (scale2Fin m S).card = S.card := by
  apply Finset.card_image_of_injective
  intro a b h
  have hpow : (2 : ℤ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  exact mul_left_cancel₀ hpow h

private lemma coe_scale2Fin (m : ℕ) (S : Finset ℤ) :
    ((scale2Fin m S : Finset ℤ) : Set ℤ) = scale2Set m (S : Set ℤ) := by
  simp [scale2Fin, scale2Set]

private def SymNbhd.scale2 (m : ℕ) (Z : SymNbhd) : SymNbhd where
  set := scale2Fin m Z.set
  zero_mem := Finset.mem_image.mpr ⟨0, Z.zero_mem, mul_zero _⟩
  neg_mem := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨-y, Z.neg_mem y hy, by ring⟩

private def SymNbhd.add (Z W : SymNbhd) : SymNbhd where
  set := Z.set + W.set
  zero_mem := by simpa using Finset.add_mem_add Z.zero_mem W.zero_mem
  neg_mem := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    have : -(a + b) = -a + -b := by ring
    rw [this]
    exact Finset.add_mem_add (Z.neg_mem a ha) (W.neg_mem b hb)

private def SymNbhd.zero : SymNbhd where
  set := {0}
  zero_mem := by simp
  neg_mem := by intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; simp

private def IsClosedPair (τ : ℝ) (Z W : SymNbhd) : Prop :=
  ∃ Zminus Zplus : SymNbhd,
    Zminus.set + W.set ⊆ Z.set ∧
    Z.set + W.set ⊆ Zplus.set ∧
    (Zplus.set.card : ℝ) ≤ (1 + τ) * (Zminus.set.card : ℝ)

private lemma isClosedPair_mono_right {τ : ℝ} {Z W W' : SymNbhd}
    (h : IsClosedPair τ Z W) (hsub : W'.set ⊆ W.set) : IsClosedPair τ Z W' := by
  obtain ⟨Zm, Zp, h1, h2, h3⟩ := h
  exact ⟨Zm, Zp, (Finset.add_subset_add_left hsub).trans h1,
    (Finset.add_subset_add_left hsub).trans h2, h3⟩

private lemma isClosedPair_mono_tau {τ τ' : ℝ} {Z W : SymNbhd}
    (h : IsClosedPair τ Z W) (hle : τ ≤ τ') : IsClosedPair τ' Z W := by
  obtain ⟨Zm, Zp, h1, h2, h3⟩ := h
  exact ⟨Zm, Zp, h1, h2, h3.trans (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))⟩

private lemma isClosedPair_scale2 {τ : ℝ} {Z W : SymNbhd} (m : ℕ)
    (h : IsClosedPair τ Z W) : IsClosedPair τ (Z.scale2 m) (W.scale2 m) := by
  obtain ⟨Zm, Zp, h1, h2, h3⟩ := h
  refine ⟨Zm.scale2 m, Zp.scale2 m, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨a' + b', h1 (Finset.add_mem_add ha' hb'), by ring⟩
  · intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨a' + b', h2 (Finset.add_mem_add ha' hb'), by ring⟩
  · simpa [SymNbhd.scale2, scale2Fin_card] using h3

private noncomputable def unifMeas (S : Finset ℤ) (x : ℤ) : ℝ :=
  if x ∈ S then (S.card : ℝ)⁻¹ else 0

private lemma unifMeas_nonneg (S : Finset ℤ) (x : ℤ) : 0 ≤ unifMeas S x := by
  unfold unifMeas; split_ifs <;> positivity

private lemma sum_unifMeas (S : Finset ℤ) (hS : S.Nonempty) :
    ∑ x ∈ S, unifMeas S x = 1 := by
  have hpos : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_pos.ne'
  simp [unifMeas, hpos]

private lemma unifMeas_translate (S : Finset ℤ) (z x : ℤ) :
    unifMeas (S.image (· + z)) x = unifMeas S (x - z) := by
  have hcard : (S.image (· + z)).card = S.card :=
    Finset.card_image_of_injective S (add_left_injective z)
  have hmem : x ∈ S.image (· + z) ↔ x - z ∈ S := by
    constructor
    · intro hx; obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      have : x - z = y := by omega
      rwa [this]
    · intro hx; exact Finset.mem_image.mpr ⟨x - z, hx, sub_add_cancel x z⟩
  unfold unifMeas
  by_cases hx : x - z ∈ S
  · rw [if_pos (hmem.mpr hx), if_pos hx, hcard]
  · rw [if_neg (mt hmem.mp hx), if_neg hx]

private lemma isClosedPair_shift_tv {τ : ℝ} {Z W : SymNbhd} (hτ : 0 ≤ τ)
    (h : IsClosedPair τ Z W) {w : ℤ} (hw : w ∈ W.set) :
    ∀ U : Finset ℤ, Z.set ⊆ U → (Z.set.image (· + w)) ⊆ U →
      ∑ x ∈ U, |unifMeas Z.set (x - w) - unifMeas Z.set x| ≤ 2 * τ := by
  obtain ⟨Zm, Zp, h1, h2, h3⟩ := h
  intro U hZU hZwU
  have hZmZ : Zm.set ⊆ Z.set := fun x hx => by
    simpa using h1 (Finset.add_mem_add hx W.zero_mem)
  have hZZp : Z.set ⊆ Zp.set := fun x hx => by
    simpa using h2 (Finset.add_mem_add hx W.zero_mem)
  have hZmZw : Zm.set ⊆ Z.set.image (· + w) := by
    intro x hx
    have hxw : x - w ∈ Z.set := by
      have : x + (-w) ∈ Zm.set + W.set := Finset.add_mem_add hx (W.neg_mem w hw)
      simpa [sub_eq_add_neg] using h1 this
    exact Finset.mem_image.mpr ⟨x - w, hxw, sub_add_cancel x w⟩
  have hinv_nn : (0 : ℝ) ≤ (Z.set.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hterm : ∀ x ∈ U, |unifMeas Z.set (x - w) - unifMeas Z.set x| ≤
      (if x ∈ Z.set \ Zm.set then (Z.set.card : ℝ)⁻¹ else 0) +
      (if x ∈ Z.set.image (· + w) \ Zm.set then (Z.set.card : ℝ)⁻¹ else 0) := by
    intro x _
    have hmem_iff : x - w ∈ Z.set ↔ x ∈ Z.set.image (· + w) := by
      constructor
      · intro hx; exact Finset.mem_image.mpr ⟨x - w, hx, sub_add_cancel x w⟩
      · intro hx; obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
        have : x - w = y := by omega
        rwa [this]
    have hnn1 : 0 ≤ (if x ∈ Z.set \ Zm.set then (Z.set.card : ℝ)⁻¹ else 0) := by
      split_ifs <;> linarith
    have hnn2 : 0 ≤ (if x ∈ Z.set.image (· + w) \ Zm.set then (Z.set.card : ℝ)⁻¹ else 0) := by
      split_ifs <;> linarith
    by_cases hxZm : x ∈ Zm.set
    · have hxZ : x ∈ Z.set := hZmZ hxZm
      have hxw : x - w ∈ Z.set := hmem_iff.mpr (hZmZw hxZm)
      unfold unifMeas
      rw [if_pos hxw, if_pos hxZ, sub_self, abs_zero]
      linarith
    · by_cases hxZ : x ∈ Z.set <;> by_cases hxw : x - w ∈ Z.set
      · unfold unifMeas; rw [if_pos hxw, if_pos hxZ, sub_self, abs_zero]; linarith
      · unfold unifMeas
        rw [if_neg hxw, if_pos hxZ, zero_sub, abs_neg, abs_of_nonneg hinv_nn]
        have hm1 : x ∈ Z.set \ Zm.set := Finset.mem_sdiff.mpr ⟨hxZ, hxZm⟩
        rw [if_pos hm1]; linarith
      · unfold unifMeas
        rw [if_pos hxw, if_neg hxZ, sub_zero, abs_of_nonneg hinv_nn]
        have hm2 : x ∈ Z.set.image (· + w) \ Zm.set := Finset.mem_sdiff.mpr ⟨hmem_iff.mp hxw, hxZm⟩
        rw [if_pos hm2]; linarith
      · unfold unifMeas; rw [if_neg hxw, if_neg hxZ, sub_self, abs_zero]; linarith
  calc ∑ x ∈ U, |unifMeas Z.set (x - w) - unifMeas Z.set x|
      ≤ ∑ x ∈ U, ((if x ∈ Z.set \ Zm.set then (Z.set.card : ℝ)⁻¹ else 0) +
          (if x ∈ Z.set.image (· + w) \ Zm.set then (Z.set.card : ℝ)⁻¹ else 0)) :=
        Finset.sum_le_sum hterm
    _ = ((Z.set \ Zm.set).card : ℝ) * (Z.set.card : ℝ)⁻¹ +
        ((Z.set.image (· + w) \ Zm.set).card : ℝ) * (Z.set.card : ℝ)⁻¹ := by
        rw [Finset.sum_add_distrib]
        have s1 : U.filter (· ∈ Z.set \ Zm.set) = Z.set \ Zm.set :=
          Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (Finset.sdiff_subset.trans hZU))
        have s2 : U.filter (· ∈ Z.set.image (· + w) \ Zm.set) = Z.set.image (· + w) \ Zm.set :=
          Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr (Finset.sdiff_subset.trans hZwU))
        simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, s1, s2, mul_zero, add_zero]
    _ ≤ 2 * τ := by
        have hc1 : (Z.set \ Zm.set).card = Z.set.card - Zm.set.card := Finset.card_sdiff_of_subset hZmZ
        have hc2 : (Z.set.image (· + w) \ Zm.set).card = Z.set.card - Zm.set.card := by
          rw [Finset.card_sdiff_of_subset hZmZw, Finset.card_image_of_injective _ (add_left_injective w)]
        have hZleZp : (Z.set.card : ℝ) ≤ (Zp.set.card : ℝ) := by exact_mod_cast Finset.card_le_card hZZp
        have hZmleZ : (Zm.set.card : ℝ) ≤ (Z.set.card : ℝ) := by exact_mod_cast Finset.card_le_card hZmZ
        have hdiff : ((Z.set.card - Zm.set.card : ℕ) : ℝ) ≤ τ * (Z.set.card : ℝ) := by
          rw [Nat.cast_sub (Finset.card_le_card hZmZ)]
          nlinarith
        have hZpos : (0 : ℝ) < (Z.set.card : ℝ) := by exact_mod_cast Z.card_pos
        rw [hc1, hc2]
        have hdiv : ((Z.set.card - Zm.set.card : ℕ) : ℝ) * (Z.set.card : ℝ)⁻¹ ≤ τ := by
          rw [← div_eq_mul_inv, div_le_iff₀ hZpos]; exact hdiff
        linarith


private noncomputable def covNum {G : Type} [AddCommGroup G] (X Y : Set G) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ T : Finset G, (T.card : ℕ∞) = n ∧ X ⊆ (T : Set G) + Y}

private lemma covNum_le_of_cover {G : Type} [AddCommGroup G] {X Y : Set G}
    (T : Finset G) (h : X ⊆ (T : Set G) + Y) : covNum X Y ≤ T.card :=
  sInf_le ⟨T, rfl, h⟩

private lemma exists_cover_of_covNum_lt_top {G : Type} [AddCommGroup G] {X Y : Set G}
    (h : covNum X Y < ⊤) :
    ∃ T : Finset G, (T.card : ℕ∞) = covNum X Y ∧ X ⊆ (T : Set G) + Y := by
  have hne : {n : ℕ∞ | ∃ T : Finset G, (T.card : ℕ∞) = n ∧ X ⊆ (T : Set G) + Y}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : covNum X Y = ⊤ := by rw [covNum, hemp, sInf_empty]
    exact lt_irrefl ⊤ (this ▸ h)
  exact csInf_mem hne

private lemma covNum_empty_left {G : Type} [AddCommGroup G] (Y : Set G) :
    covNum (∅ : Set G) Y = 0 :=
  le_antisymm (covNum_le_of_cover ∅ (by simp)) bot_le

private lemma covNum_ne_zero_of_nonempty {G : Type} [AddCommGroup G] {X Y : Set G}
    (hX : X.Nonempty) : covNum X Y ≠ 0 := by
  intro h0
  obtain ⟨T, hTc, hT⟩ := exists_cover_of_covNum_lt_top (by rw [h0]; exact ENat.natCast_lt_top 0)
  have hTe : T = ∅ := Finset.card_eq_zero.mp (ENat.natCast_inj.mp (hTc.trans h0))
  rw [hTe, Finset.coe_empty, Set.empty_add] at hT
  exact hX.ne_empty (Set.subset_empty_iff.mp hT)

private lemma covNum_mono {G : Type} [AddCommGroup G] {X' X Y Y' : Set G}
    (hX : X' ⊆ X) (hY : Y ⊆ Y') : covNum X' Y' ≤ covNum X Y := by
  apply le_sInf
  rintro n ⟨T, rfl, hcov⟩
  exact covNum_le_of_cover T (hX.trans (hcov.trans (Set.add_subset_add_left hY)))

private lemma covNum_chain {G : Type} [AddCommGroup G] {X Y Z : Set G}
    (hY : X.Nonempty → Y.Nonempty) :
    covNum X Z ≤ covNum X Y * covNum Y Z := by
  by_cases hXe : X = ∅
  · rw [hXe, covNum_empty_left]; exact bot_le
  have hXne : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hXe
  have hYne : Y.Nonempty := hY hXne
  by_cases h1 : covNum X Y = ⊤
  · rw [h1, ENat.top_mul (covNum_ne_zero_of_nonempty hYne)]; exact le_top
  · by_cases h2 : covNum Y Z = ⊤
    · rw [h2, ENat.mul_top (covNum_ne_zero_of_nonempty hXne)]; exact le_top
    · classical
      obtain ⟨T1, hT1c, hT1⟩ := exists_cover_of_covNum_lt_top (lt_top_iff_ne_top.mpr h1)
      obtain ⟨T2, hT2c, hT2⟩ := exists_cover_of_covNum_lt_top (lt_top_iff_ne_top.mpr h2)
      have hcov : X ⊆ ((T1 + T2 : Finset G) : Set G) + Z := by
        rw [Finset.coe_add, add_assoc]
        exact hT1.trans (Set.add_subset_add_left hT2)
      calc covNum X Z ≤ ((T1 + T2).card : ℕ∞) := covNum_le_of_cover (T1 + T2) hcov
        _ ≤ ((T1.card * T2.card : ℕ) : ℕ∞) := ENat.natCast_le_natCast.mpr Finset.card_add_le
        _ = covNum X Y * covNum Y Z := by rw [Nat.cast_mul, hT1c, hT2c]

private lemma covNum_hom {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (φ : G →+ H) (X Y : Set G) :
    covNum (φ '' X) (φ '' Y) ≤ covNum X Y := by
  classical
  apply le_sInf
  rintro n ⟨T, rfl, hcov⟩
  have hcov' : φ '' X ⊆ ((T.image φ : Finset H) : Set H) + φ '' Y := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, y, hy, rfl⟩ := Set.mem_add.mp (hcov hx)
    rw [map_add]
    exact Set.add_mem_add (Finset.mem_coe.mpr (Finset.mem_image_of_mem φ ht)) ⟨y, hy, rfl⟩
  exact (covNum_le_of_cover (T.image φ) hcov').trans (ENat.natCast_le_natCast.mpr Finset.card_image_le)

private lemma covNum_card_le {G : Type} [AddCommGroup G] [DecidableEq G]
    {X Y : Finset G} (hY : X.Nonempty → Y.Nonempty) :
    (X.card : ℕ∞) ≤ covNum (X : Set G) (Y : Set G) * (Y.card : ℕ∞) := by
  by_cases hXe : X = ∅
  · simp [hXe]
  have hXne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hXe
  have hYne : Y.Nonempty := hY hXne
  by_cases htop : covNum (X : Set G) (Y : Set G) = ⊤
  · rw [htop, ENat.top_mul (Nat.cast_ne_zero.mpr hYne.card_pos.ne')]; exact le_top
  · obtain ⟨T, hTc, hT⟩ := exists_cover_of_covNum_lt_top (lt_top_iff_ne_top.mpr htop)
    have hsub : X ⊆ T + Y := by
      intro x hx
      have hx' : x ∈ ((T + Y : Finset G) : Set G) := by
        rw [Finset.coe_add]; exact hT hx
      exact Finset.mem_coe.mp hx'
    calc (X.card : ℕ∞) ≤ ((T + Y).card : ℕ∞) := ENat.natCast_le_natCast.mpr (Finset.card_le_card hsub)
      _ ≤ ((T.card * Y.card : ℕ) : ℕ∞) := ENat.natCast_le_natCast.mpr Finset.card_add_le
      _ = covNum (X : Set G) (Y : Set G) * (Y.card : ℕ∞) := by rw [Nat.cast_mul, hTc]

private lemma covNum_prod_le {H H' : Type} [AddCommGroup H] [AddCommGroup H']
    (W Z : Set H) (W' Z' : Set H') :
    covNum (W ×ˢ W') (Z ×ˢ Z') ≤ covNum W Z * covNum W' Z' := by
  by_cases hW : W = ∅
  · simp [hW, covNum_empty_left]
  by_cases hW' : W' = ∅
  · simp [hW', covNum_empty_left]
  have hWne : W.Nonempty := Set.nonempty_iff_ne_empty.mpr hW
  have hW'ne : W'.Nonempty := Set.nonempty_iff_ne_empty.mpr hW'
  by_cases h1 : covNum W Z = ⊤
  · rw [h1, ENat.top_mul (covNum_ne_zero_of_nonempty hW'ne)]; exact le_top
  by_cases h2 : covNum W' Z' = ⊤
  · rw [h2, ENat.mul_top (covNum_ne_zero_of_nonempty hWne)]; exact le_top
  classical
  obtain ⟨T1, hT1c, hT1⟩ := exists_cover_of_covNum_lt_top (lt_top_iff_ne_top.mpr h1)
  obtain ⟨T2, hT2c, hT2⟩ := exists_cover_of_covNum_lt_top (lt_top_iff_ne_top.mpr h2)
  have hcov : W ×ˢ W' ⊆ ((T1 ×ˢ T2 : Finset (H × H')) : Set (H × H')) + Z ×ˢ Z' := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    obtain ⟨t1, ht1, z1, hz1, rfl⟩ := Set.mem_add.mp (hT1 ha)
    obtain ⟨t2, ht2, z2, hz2, rfl⟩ := Set.mem_add.mp (hT2 hb)
    exact Set.mem_add.mpr ⟨(t1, t2), Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨ht1, ht2⟩),
      (z1, z2), ⟨hz1, hz2⟩, rfl⟩
  calc covNum (W ×ˢ W') (Z ×ˢ Z')
      ≤ ((T1 ×ˢ T2).card : ℕ∞) := covNum_le_of_cover (T1 ×ˢ T2) hcov
    _ = ((T1.card * T2.card : ℕ) : ℕ∞) := by rw [Finset.card_product]
    _ = covNum W Z * covNum W' Z' := by rw [Nat.cast_mul, hT1c, hT2c]

private lemma covNum_ruzsa_le_of_mul_le {G : Type} [AddCommGroup G] [DecidableEq G]
    {A B : Finset G} (hB : B.Nonempty) {M : ℕ}
    (hM : (A + B).card ≤ M * B.card) :
    covNum (A : Set G) ((B : Set G) - (B : Set G)) ≤ M := by
  have hMR : ((A + B).card : ℝ) ≤ (M : ℝ) * (B.card : ℝ) := by exact_mod_cast hM
  obtain ⟨F, _, hFM, hAF⟩ := Finset.ruzsa_covering_add hB hMR
  have hFM' : F.card ≤ M := by exact_mod_cast hFM
  have hcov : (A : Set G) ⊆ (F : Set G) + ((B : Set G) - (B : Set G)) := by
    intro a ha
    have ha' : a ∈ ((F + (B - B) : Finset G) : Set G) := Finset.mem_coe.mpr (hAF ha)
    simpa [Finset.coe_add, Finset.coe_sub] using ha'
  exact (covNum_le_of_cover F hcov).trans (ENat.natCast_le_natCast.mpr hFM')

private structure FlatData {G : Type} [AddCommGroup G] (X Y : Set G) where
  H : Type
  [instH : AddCommGroup H]
  φ : AddSubgroup.closure X →+ H
  W : Set H
  Z : Set H
  hW : ∀ x : AddSubgroup.closure X, (x : G) ∈ X → φ x ∈ W
  hZ : ∀ x : AddSubgroup.closure X, φ x ∈ Z - Z → (x : G) ∈ Y

private def IsFlatWitness {G : Type} [AddCommGroup G] (X Y : Set G) (n : ℕ∞) : Prop :=
  ∃ d : FlatData X Y, @covNum d.H d.instH d.W d.Z = n

private noncomputable def covFlat {G : Type} [AddCommGroup G] (X Y : Set G) : ℕ∞ :=
  sInf {n : ℕ∞ | IsFlatWitness X Y n}

private lemma covFlat_le {G : Type} [AddCommGroup G] {X Y : Set G}
    (H : Type) [instH : AddCommGroup H] (φ : AddSubgroup.closure X →+ H) (W Z : Set H)
    (hW : ∀ x : AddSubgroup.closure X, (x : G) ∈ X → φ x ∈ W)
    (hZ : ∀ x : AddSubgroup.closure X, φ x ∈ Z - Z → (x : G) ∈ Y) :
    covFlat X Y ≤ covNum W Z := by
  have hmem : covNum W Z ∈ {n : ℕ∞ | IsFlatWitness X Y n} :=
    ⟨@FlatData.mk G _ X Y H instH φ W Z hW hZ, rfl⟩
  exact sInf_le hmem

private lemma exists_witness_of_covFlat_lt_top {G : Type} [AddCommGroup G] {X Y : Set G}
    (h : covFlat X Y < ⊤) : IsFlatWitness X Y (covFlat X Y) := by
  have hne : {n : ℕ∞ | IsFlatWitness X Y n}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : covFlat X Y = ⊤ := by rw [covFlat, hemp, sInf_empty]
    exact lt_irrefl ⊤ (this ▸ h)
  exact csInf_mem hne

private lemma covFlat_mono {G : Type} [AddCommGroup G] {X' X Y Y' : Set G}
    (hX : X' ⊆ X) (hY : Y ⊆ Y') : covFlat X' Y' ≤ covFlat X Y := by
  apply le_sInf
  rintro n ⟨⟨H, φ, W, Z, hW, hZ⟩, rfl⟩
  let ι : AddSubgroup.closure X' →+ AddSubgroup.closure X :=
    AddSubgroup.inclusion (AddSubgroup.closure_mono hX)
  exact covFlat_le H (φ.comp ι) W Z
    (fun x hx => hW (ι x) (hX hx))
    (fun x hx => hY (hZ (ι x) hx))

private lemma covFlat_preimage {K G : Type} [AddCommGroup K] [AddCommGroup G]
    (ψ : K →+ G) (X Y : Set G) :
    covFlat (ψ ⁻¹' X) (ψ ⁻¹' Y) ≤ covFlat X Y := by
  apply le_sInf
  rintro n ⟨⟨H, φ, W, Z, hW, hZ⟩, rfl⟩
  have hle : AddSubgroup.closure (ψ ⁻¹' X) ≤ (AddSubgroup.closure X).comap ψ := by
    rw [AddSubgroup.closure_le]
    intro k hk
    exact AddSubgroup.subset_closure hk
  let ψ' : AddSubgroup.closure (ψ ⁻¹' X) →+ AddSubgroup.closure X :=
    { toFun := fun k => ⟨ψ k.1, hle k.2⟩
      map_zero' := by ext; exact map_zero ψ
      map_add' := fun a b => by ext; exact map_add ψ a.1 b.1 }
  exact covFlat_le H (φ.comp ψ') W Z
    (fun k hk => hW (ψ' k) hk)
    (fun k hk => hZ (ψ' k) hk)

private lemma covFlat_le_covNum {G : Type} [AddCommGroup G] (X Y : Set G) :
    covFlat X (Y - Y) ≤ covNum X Y :=
  covFlat_le G (AddSubgroup.closure X).subtype X Y (fun _ hx => hx) (fun _ hx => hx)

private lemma covNum_le_covFlat {G : Type} [AddCommGroup G] (X Y : Set G) :
    covNum X Y ≤ covFlat X Y := by
  classical
  apply le_sInf
  rintro n ⟨⟨H, φ, W, Z, hW, hZ⟩, rfl⟩
  by_cases htop : covNum W Z = ⊤
  · rw [htop]; exact le_top
  obtain ⟨S, hSc, hS⟩ := exists_cover_of_covNum_lt_top (lt_top_iff_ne_top.mpr htop)
  let P : H → Prop := fun s => ∃ x : AddSubgroup.closure X, φ x ∈ ({s} : Set H) + Z
  let S' : Finset H := S.filter P
  let pick : H → G := fun s =>
    if h : P s then ((Classical.choose h : AddSubgroup.closure X) : G) else 0
  let T : Finset G := S'.image pick
  have hcov : X ⊆ (T : Set G) + Y := by
    intro x hx
    let x' : AddSubgroup.closure X := ⟨x, AddSubgroup.subset_closure hx⟩
    have hφx : φ x' ∈ (S : Set H) + Z := hS (hW x' hx)
    obtain ⟨s, hs, z1, hz1, hxz1⟩ := Set.mem_add.mp hφx
    have hPs : P s := ⟨x', Set.mem_add.mpr ⟨s, rfl, z1, hz1, hxz1⟩⟩
    have hs' : s ∈ S' := Finset.mem_filter.mpr ⟨hs, hPs⟩
    let t' : AddSubgroup.closure X := Classical.choose hPs
    have ht' : φ t' ∈ ({s} : Set H) + Z := Classical.choose_spec hPs
    obtain ⟨s2, hs2, z2, hz2, htz2⟩ := Set.mem_add.mp ht'
    rw [Set.mem_singleton_iff] at hs2
    rw [hs2] at htz2
    have hsub : φ (x' - t') ∈ Z - Z := by
      rw [map_sub, ← hxz1, ← htz2]
      have : (s + z1) - (s + z2) = z1 - z2 := by abel
      rw [this]
      exact Set.sub_mem_sub hz1 hz2
    have hmemY : x - (t' : G) ∈ Y := hZ (x' - t') hsub
    have hmemT : (t' : G) ∈ T := by
      apply Finset.mem_image.mpr
      refine ⟨s, hs', ?_⟩
      simp only [pick, dif_pos hPs, t']
    exact Set.mem_add.mpr ⟨(t' : G), Finset.mem_coe.mpr hmemT, x - (t' : G), hmemY, by abel⟩
  calc covNum X Y ≤ (T.card : ℕ∞) := covNum_le_of_cover T hcov
    _ ≤ (S'.card : ℕ∞) := ENat.natCast_le_natCast.mpr Finset.card_image_le
    _ ≤ (S.card : ℕ∞) := ENat.natCast_le_natCast.mpr (Finset.card_filter_le S P)
    _ = covNum W Z := hSc

private lemma covFlat_empty_left {G : Type} [AddCommGroup G] (Y : Set G) :
    covFlat (∅ : Set G) Y = 0 := by
  apply le_antisymm _ bot_le
  have h := covFlat_le (Y := Y) G (AddSubgroup.closure (∅ : Set G)).subtype ∅ ∅
    (fun _ hx => hx) (fun _ hx => by simp at hx)
  simpa [covNum_empty_left] using h

private lemma covFlat_ne_zero_of_nonempty {G : Type} [AddCommGroup G] {X Y : Set G}
    (hX : X.Nonempty) : covFlat X Y ≠ 0 := by
  intro h0
  have : covNum X Y = 0 := le_antisymm ((covNum_le_covFlat X Y).trans (le_of_eq h0)) bot_le
  exact covNum_ne_zero_of_nonempty hX this

private lemma covFlat_meet {G : Type} [AddCommGroup G] (X X' Y Y' : Set G) :
    covFlat (X ∩ X') (Y ∩ Y') ≤ covFlat X Y * covFlat X' Y' := by
  by_cases hX : X = ∅
  · simp [hX, covFlat_empty_left]
  by_cases hX' : X' = ∅
  · simp [hX', covFlat_empty_left]
  have hXne : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hX
  have hX'ne : X'.Nonempty := Set.nonempty_iff_ne_empty.mpr hX'
  by_cases h1 : covFlat X Y = ⊤
  · rw [h1, ENat.top_mul (covFlat_ne_zero_of_nonempty hX'ne)]; exact le_top
  by_cases h2 : covFlat X' Y' = ⊤
  · rw [h2, ENat.mul_top (covFlat_ne_zero_of_nonempty hXne)]; exact le_top
  obtain ⟨⟨H, φ, W, Z, hW, hZ⟩, hcov1⟩ :=
    exists_witness_of_covFlat_lt_top (lt_top_iff_ne_top.mpr h1)
  obtain ⟨⟨H', ψ, W', Z', hW', hZ'⟩, hcov2⟩ :=
    exists_witness_of_covFlat_lt_top (lt_top_iff_ne_top.mpr h2)
  let ι1 : AddSubgroup.closure (X ∩ X') →+ AddSubgroup.closure X :=
    AddSubgroup.inclusion (AddSubgroup.closure_mono Set.inter_subset_left)
  let ι2 : AddSubgroup.closure (X ∩ X') →+ AddSubgroup.closure X' :=
    AddSubgroup.inclusion (AddSubgroup.closure_mono Set.inter_subset_right)
  let π : AddSubgroup.closure (X ∩ X') →+ H × H' := (φ.comp ι1).prod (ψ.comp ι2)
  have hle : covFlat (X ∩ X') (Y ∩ Y') ≤ covNum (W ×ˢ W') (Z ×ˢ Z') := by
    refine covFlat_le (H × H') π (W ×ˢ W') (Z ×ˢ Z') ?_ ?_
    · intro x hx
      exact ⟨hW (ι1 x) hx.1, hW' (ι2 x) hx.2⟩
    · intro x hx
      obtain ⟨⟨z1, z1'⟩, ⟨hz1, hz1'⟩, ⟨z2, z2'⟩, ⟨hz2, hz2'⟩, heq⟩ := Set.mem_sub.mp hx
      have h1eq : z1 - z2 = φ (ι1 x) := congrArg Prod.fst heq
      have h2eq : z1' - z2' = ψ (ι2 x) := congrArg Prod.snd heq
      exact ⟨hZ (ι1 x) ⟨z1, hz1, z2, hz2, h1eq⟩, hZ' (ι2 x) ⟨z1', hz1', z2', hz2', h2eq⟩⟩
  exact hle.trans ((covNum_prod_le W Z W' Z').trans (by rw [hcov1, hcov2]))

private lemma covFlat_mul_le {c : ℤ} (hc : c ≠ 0) (X Y : Set ℤ) :
    covFlat ((fun x => c * x) '' X) ((fun x => c * x) '' Y) ≤ covFlat X Y := by
  let mulC : ℤ →+ ℤ := AddMonoidHom.mulLeft c
  have hcl : AddSubgroup.closure ((fun x => c * x) '' X) ≤ (AddSubgroup.closure X).map mulC := by
    rw [AddSubgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, AddSubgroup.subset_closure hx, rfl⟩
  have hdiv : ∀ y : AddSubgroup.closure ((fun x => c * x) '' X),
      ∃ x : AddSubgroup.closure X, c * (x : ℤ) = (y : ℤ) := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hcl y.2
    exact ⟨⟨x, hx⟩, hxy⟩
  let f : AddSubgroup.closure ((fun x => c * x) '' X) → AddSubgroup.closure X :=
    fun y => Classical.choose (hdiv y)
  have hf_spec : ∀ y, c * (f y : ℤ) = (y : ℤ) := fun y => Classical.choose_spec (hdiv y)
  let invC : AddSubgroup.closure ((fun x => c * x) '' X) →+ AddSubgroup.closure X :=
    { toFun := f
      map_zero' := by
        apply Subtype.ext
        exact mul_left_cancel₀ hc (by simpa using hf_spec 0)
      map_add' := fun a b => by
        apply Subtype.ext
        apply mul_left_cancel₀ hc
        calc c * (f (a + b) : ℤ)
            = ((a + b : AddSubgroup.closure ((fun x => c * x) '' X)) : ℤ) := hf_spec (a + b)
          _ = (a : ℤ) + (b : ℤ) := rfl
          _ = c * (f a : ℤ) + c * (f b : ℤ) := by rw [hf_spec a, hf_spec b]
          _ = c * ((f a : ℤ) + (f b : ℤ)) := by ring }
  apply le_sInf
  rintro n ⟨⟨H, φ, W, Z, hW, hZ⟩, rfl⟩
  refine covFlat_le H (φ.comp invC) W Z ?_ ?_
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := hy
    have heq : (f y : ℤ) = x := mul_left_cancel₀ hc ((hf_spec y).trans hxy.symm)
    exact hW (invC y) (heq.symm ▸ hx)
  · intro y hy
    exact ⟨(f y : ℤ), hZ (invC y) hy, hf_spec y⟩


private structure Sys where
  set : ℕ → Set ℤ
  zero_mem : ∀ i, (0 : ℤ) ∈ set i
  neg_mem : ∀ i, ∀ x ∈ set i, -x ∈ set i
  add_subset : ∀ i, set (i + 1) + set (i + 1) ⊆ set i

private lemma Sys.nonempty (B : Sys) (i : ℕ) : (B.set i).Nonempty := ⟨0, B.zero_mem i⟩

private lemma Sys.sub_subset (B : Sys) (i : ℕ) :
    B.set (i + 1) - B.set (i + 1) ⊆ B.set i := by
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.mp hx
  rw [sub_eq_add_neg]
  exact B.add_subset i (Set.add_mem_add ha (B.neg_mem (i + 1) b hb))

private lemma Sys.mono_succ (B : Sys) (i : ℕ) : B.set (i + 1) ⊆ B.set i := by
  intro x hx
  simpa using B.add_subset i (Set.add_mem_add hx (B.zero_mem (i + 1)))

private lemma Sys.antitone (B : Sys) {i j : ℕ} (h : i ≤ j) : B.set j ⊆ B.set i := by
  induction h with
  | refl => exact Set.Subset.rfl
  | step _ ih => exact (B.mono_succ _).trans ih

private def Sys.HasDim (B : Sys) (d : ℕ) : Prop :=
  ∀ i : ℕ, covFlat (B.set i) (B.set (i + 1)) ≤ ((2 ^ d : ℕ) : ℕ∞)

private lemma Sys.HasDim.mono {B : Sys} {d d' : ℕ} (h : B.HasDim d) (hle : d ≤ d') :
    B.HasDim d' :=
  fun i => (h i).trans (ENat.natCast_le_natCast.mpr (Nat.pow_le_pow_right (by norm_num) hle))

private def Sys.IsFinite (B : Sys) : Prop := (B.set 0).Finite

private lemma Sys.IsFinite.finite {B : Sys} (h : B.IsFinite) (i : ℕ) : (B.set i).Finite :=
  h.subset (B.antitone (Nat.zero_le i))

private noncomputable def Sys.toSymNbhd (B : Sys) (h : B.IsFinite) (i : ℕ) : SymNbhd where
  set := (h.finite i).toFinset
  zero_mem := (Set.Finite.mem_toFinset _).mpr (B.zero_mem i)
  neg_mem := fun x hx =>
    (Set.Finite.mem_toFinset _).mpr (B.neg_mem i x ((Set.Finite.mem_toFinset _).mp hx))

private lemma Sys.coe_toSymNbhd (B : Sys) (h : B.IsFinite) (i : ℕ) :
    ((B.toSymNbhd h i).set : Set ℤ) = B.set i :=
  Set.Finite.coe_toFinset _

private def Sys.univ : Sys where
  set := fun _ => Set.univ
  zero_mem := fun _ => trivial
  neg_mem := fun _ _ _ => trivial
  add_subset := fun _ _ _ => trivial

private lemma Sys.univ_hasDim : Sys.univ.HasDim 0 := by
  intro i
  change covFlat (Set.univ : Set ℤ) (Set.univ : Set ℤ) ≤ ((2 ^ 0 : ℕ) : ℕ∞)
  have h1 : covFlat (Set.univ : Set ℤ) Set.univ ≤ covNum (Set.univ : Set ℤ) Set.univ := by
    have heq : (Set.univ : Set ℤ) - Set.univ = Set.univ := by
      ext x; exact ⟨fun _ => trivial, fun _ => ⟨x, trivial, 0, trivial, sub_zero x⟩⟩
    have h0 := covFlat_le_covNum (Set.univ : Set ℤ) Set.univ
    rwa [heq] at h0
  have h2 : covNum (Set.univ : Set ℤ) Set.univ ≤ ((1 : ℕ) : ℕ∞) := by
    have hcov : (Set.univ : Set ℤ) ⊆ (({0} : Finset ℤ) : Set ℤ) + (Set.univ : Set ℤ) :=
      fun x _ => Set.mem_add.mpr ⟨0, by simp, x, trivial, zero_add x⟩
    exact (covNum_le_of_cover ({0} : Finset ℤ) hcov).trans (by simp)
  simpa using h1.trans h2

private def Sys.inter (B B' : Sys) : Sys where
  set := fun i => B.set i ∩ B'.set i
  zero_mem := fun i => ⟨B.zero_mem i, B'.zero_mem i⟩
  neg_mem := fun i x hx => ⟨B.neg_mem i x hx.1, B'.neg_mem i x hx.2⟩
  add_subset := fun i x hx => by
    obtain ⟨a, ⟨ha1, ha2⟩, b, ⟨hb1, hb2⟩, rfl⟩ := Set.mem_add.mp hx
    exact ⟨B.add_subset i (Set.add_mem_add ha1 hb1), B'.add_subset i (Set.add_mem_add ha2 hb2)⟩

private lemma Sys.inter_hasDim {B B' : Sys} {d d' : ℕ} (h : B.HasDim d) (h' : B'.HasDim d') :
    (B.inter B').HasDim (d + d') := by
  intro i
  calc covFlat (B.set i ∩ B'.set i) (B.set (i + 1) ∩ B'.set (i + 1))
      ≤ covFlat (B.set i) (B.set (i + 1)) * covFlat (B'.set i) (B'.set (i + 1)) :=
        covFlat_meet _ _ _ _
    _ ≤ ((2 ^ d : ℕ) : ℕ∞) * ((2 ^ d' : ℕ) : ℕ∞) := mul_le_mul' (h i) (h' i)
    _ = ((2 ^ (d + d') : ℕ) : ℕ∞) := by rw [← Nat.cast_mul, ← pow_add]

private lemma Sys.inter_covFlat (B B' : Sys) (S : Set ℤ) :
    covFlat S ((B.inter B').set 0) ≤ covFlat S (B.set 0) * covFlat S (B'.set 0) := by
  simpa [Sys.inter] using covFlat_meet S S (B.set 0) (B'.set 0)

private lemma Sys.inter_isFinite_left {B B' : Sys} (h : B.IsFinite) : (B.inter B').IsFinite :=
  h.subset Set.inter_subset_left

private def Sys.dilate (m : ℕ) (B : Sys) : Sys where
  set := fun i => B.set (i + m)
  zero_mem := fun i => B.zero_mem (i + m)
  neg_mem := fun i => B.neg_mem (i + m)
  add_subset := fun i => by
    have : i + 1 + m = (i + m) + 1 := by omega
    rw [this]; exact B.add_subset (i + m)

private lemma Sys.dilate_hasDim {B : Sys} {d : ℕ} (m : ℕ) (h : B.HasDim d) :
    (B.dilate m).HasDim d := by
  intro i
  have : i + 1 + m = (i + m) + 1 := by omega
  simpa [Sys.dilate, this] using h (i + m)

private lemma Sys.dilate_isFinite {B : Sys} (m : ℕ) (h : B.IsFinite) : (B.dilate m).IsFinite := by
  simpa [Sys.IsFinite, Sys.dilate] using h.finite m

private lemma Sys.covNum_chain_step {B : Sys} {d : ℕ} (h : B.HasDim d) (k : ℕ) :
    covNum (B.set 0) (B.set k) ≤ ((2 ^ (k * d) : ℕ) : ℕ∞) := by
  induction k with
  | zero =>
    have h1 : covNum (B.set 0) (B.set 0) ≤ 1 := by
      simpa using covNum_le_of_cover ({0} : Finset ℤ)
        (fun x hx => ⟨0, by simp, x, hx, zero_add x⟩)
    simpa using h1
  | succ k ih =>
    calc covNum (B.set 0) (B.set (k + 1))
        ≤ covNum (B.set 0) (B.set k) * covNum (B.set k) (B.set (k + 1)) :=
          covNum_chain (fun _ => B.nonempty k)
      _ ≤ ((2 ^ (k * d) : ℕ) : ℕ∞) * ((2 ^ d : ℕ) : ℕ∞) :=
          mul_le_mul' ih ((covNum_le_covFlat _ _).trans (h k))
      _ = ((2 ^ ((k + 1) * d) : ℕ) : ℕ∞) := by
          rw [← Nat.cast_mul, ← pow_add, Nat.add_mul, one_mul]

private lemma Sys.dilate_covFlat {B : Sys} {d : ℕ} (h : B.HasDim d) (m : ℕ) (S : Set ℤ) :
    covFlat S ((B.dilate m).set 0) ≤ covFlat S (B.set 0) * ((2 ^ ((m + 1) * d) : ℕ) : ℕ∞) := by
  simp only [Sys.dilate, zero_add]
  calc covFlat S (B.set m)
      ≤ covFlat S (B.set (m + 1) - B.set (m + 1)) :=
        covFlat_mono Set.Subset.rfl (B.sub_subset m)
    _ ≤ covNum S (B.set (m + 1)) := covFlat_le_covNum S (B.set (m + 1))
    _ ≤ covNum S (B.set 0) * covNum (B.set 0) (B.set (m + 1)) :=
        covNum_chain (fun _ => B.nonempty 0)
    _ ≤ covFlat S (B.set 0) * ((2 ^ ((m + 1) * d) : ℕ) : ℕ∞) :=
        mul_le_mul' (covNum_le_covFlat _ _) (B.covNum_chain_step h (m + 1))

private def Sys.scale2 (m : ℕ) (B : Sys) : Sys where
  set := fun i => scale2Set m (B.set i)
  zero_mem := fun i => ⟨0, B.zero_mem i, mul_zero _⟩
  neg_mem := fun i x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨-y, B.neg_mem i y hy, by ring⟩
  add_subset := fun i x hx => by
    obtain ⟨a, ⟨a', ha', rfl⟩, b, ⟨b', hb', rfl⟩, rfl⟩ := Set.mem_add.mp hx
    exact ⟨a' + b', B.add_subset i (Set.add_mem_add ha' hb'), by ring⟩

private lemma Sys.scale2_hasDim {B : Sys} {d : ℕ} (m : ℕ) (h : B.HasDim d) :
    (B.scale2 m).HasDim d := by
  intro i
  have hne : (2 : ℤ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
  exact (covFlat_mul_le hne (B.set i) (B.set (i + 1))).trans (h i)

private lemma Sys.scale2_isFinite {B : Sys} (m : ℕ) (h : B.IsFinite) : (B.scale2 m).IsFinite :=
  h.image _

private lemma Sys.scale2_covFlat {B : Sys} {d : ℕ} (h : B.HasDim d) (hfin : B.IsFinite)
    (m : ℕ) (S : Set ℤ) :
    covFlat S ((B.scale2 m).set 0) ≤ covFlat S (B.set 0) * ((2 ^ ((2 * m + 1) * d) : ℕ) : ℕ∞) := by
  have hstep : covNum (B.set 1) (scale2Set 1 (B.set 1)) ≤ ((2 ^ (2 * d) : ℕ) : ℕ∞) := by
    let F0 : Finset ℤ := (B.toSymNbhd hfin 0).set
    let F1 : Finset ℤ := (B.toSymNbhd hfin 1).set
    let F2 : Finset ℤ := (B.toSymNbhd hfin 2).set
    let F2s : Finset ℤ := scale2Fin 1 F2
    have hsub1 : F1 + F2s ⊆ F0 := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      have ha' : a ∈ B.set 1 := by simpa [F1, Sys.coe_toSymNbhd] using (Finset.mem_coe.mpr ha)
      have hc' : c ∈ B.set 2 := by simpa [F2, Sys.coe_toSymNbhd] using (Finset.mem_coe.mpr hc)
      have h2c : (2 : ℤ) ^ 1 * c ∈ B.set 1 := by
        have : (2 : ℤ) ^ 1 * c = c + c := by ring
        rw [this]; exact B.add_subset 1 (Set.add_mem_add hc' hc')
      have hmem : a + (2 : ℤ) ^ 1 * c ∈ B.set 0 := B.add_subset 0 (Set.add_mem_add ha' h2c)
      exact (Set.Finite.mem_toFinset _).mpr hmem
    have hcard02 : (F0.card : ℕ∞) ≤ ((2 ^ (2 * d) : ℕ) : ℕ∞) * (F2.card : ℕ∞) := by
      have hc := covNum_card_le (X := F0) (Y := F2) (fun _ => (B.toSymNbhd hfin 2).nonempty)
      have hcov02 : covNum (F0 : Set ℤ) (F2 : Set ℤ) ≤ ((2 ^ (2 * d) : ℕ) : ℕ∞) := by
        simpa [F0, F2, Sys.coe_toSymNbhd] using B.covNum_chain_step h 2
      exact hc.trans (mul_le_mul' hcov02 le_rfl)
    have hcard_mul : (F1 + F2s).card ≤ 2 ^ (2 * d) * F2s.card := by
      have hle1 : ((F1 + F2s).card : ℕ∞) ≤ (F0.card : ℕ∞) :=
        ENat.natCast_le_natCast.mpr (Finset.card_le_card hsub1)
      have hF2s : F2s.card = F2.card := scale2Fin_card 1 F2
      have hle2 : ((F1 + F2s).card : ℕ∞) ≤ ((2 ^ (2 * d) * F2s.card : ℕ) : ℕ∞) := by
        rw [Nat.cast_mul, hF2s]; exact hle1.trans hcard02
      exact ENat.natCast_le_natCast.mp hle2
    have hruz : covNum (F1 : Set ℤ) ((F2s : Set ℤ) - (F2s : Set ℤ)) ≤ ((2 ^ (2 * d) : ℕ) : ℕ∞) :=
      covNum_ruzsa_le_of_mul_le (A := F1) (B := F2s)
        ((B.toSymNbhd hfin 2).scale2 1).nonempty hcard_mul
    have hsub2 : (F2s : Set ℤ) - (F2s : Set ℤ) ⊆ scale2Set 1 (B.set 1) := by
      rw [coe_scale2Fin, Sys.coe_toSymNbhd]
      exact (B.scale2 1).sub_subset 1
    have hF1eq : (F1 : Set ℤ) = B.set 1 := B.coe_toSymNbhd hfin 1
    rw [hF1eq] at hruz
    exact (covNum_mono Set.Subset.rfl hsub2).trans hruz
  have hind : ∀ t : ℕ, covNum (B.set 1) (scale2Set t (B.set 1)) ≤ ((2 ^ (2 * t * d) : ℕ) : ℕ∞) := by
    intro t
    induction t with
    | zero =>
      have heq : scale2Set 0 (B.set 1) = B.set 1 := by ext x; simp [scale2Set]
      rw [heq]
      simpa using covNum_le_of_cover ({0} : Finset ℤ)
        (fun x hx => ⟨0, by simp, x, hx, zero_add x⟩)
    | succ t ih =>
      have hmul : covNum (scale2Set t (B.set 1)) (scale2Set (t + 1) (B.set 1)) ≤
          covNum (B.set 1) (scale2Set 1 (B.set 1)) := by
        let φ : ℤ →+ ℤ :=
          { toFun := fun x => (2 : ℤ) ^ t * x
            map_zero' := mul_zero _
            map_add' := mul_add _ }
        have h1 : scale2Set (t + 1) (B.set 1) = φ '' (scale2Set 1 (B.set 1)) := by
          ext x
          simp only [scale2Set, Set.mem_image, φ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
          constructor
          · rintro ⟨y, hy, rfl⟩
            exact ⟨(2 : ℤ) ^ 1 * y, ⟨y, hy, rfl⟩, by ring⟩
          · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
            exact ⟨y, hy, by ring⟩
        have h2 : scale2Set t (B.set 1) = φ '' (B.set 1) := rfl
        rw [h1, h2]
        exact covNum_hom φ (B.set 1) (scale2Set 1 (B.set 1))
      calc covNum (B.set 1) (scale2Set (t + 1) (B.set 1))
          ≤ covNum (B.set 1) (scale2Set t (B.set 1)) *
            covNum (scale2Set t (B.set 1)) (scale2Set (t + 1) (B.set 1)) :=
            covNum_chain (fun _ => (B.scale2 t).nonempty 1)
        _ ≤ ((2 ^ (2 * t * d) : ℕ) : ℕ∞) * ((2 ^ (2 * d) : ℕ) : ℕ∞) :=
            mul_le_mul' ih (hmul.trans hstep)
        _ = ((2 ^ (2 * (t + 1) * d) : ℕ) : ℕ∞) := by
            rw [← Nat.cast_mul, ← pow_add]
            congr 2; ring
  calc covFlat S ((B.scale2 m).set 0)
      ≤ covFlat S ((B.scale2 m).set 1 - (B.scale2 m).set 1) :=
        covFlat_mono Set.Subset.rfl ((B.scale2 m).sub_subset 0)
    _ ≤ covNum S ((B.scale2 m).set 1) := covFlat_le_covNum S _
    _ ≤ covNum S (B.set 0) * covNum (B.set 0) ((B.scale2 m).set 1) :=
        covNum_chain (fun _ => B.nonempty 0)
    _ ≤ covNum S (B.set 0) * (covNum (B.set 0) (B.set 1) * covNum (B.set 1) ((B.scale2 m).set 1)) :=
        mul_le_mul' le_rfl (covNum_chain (fun _ => B.nonempty 1))
    _ ≤ covFlat S (B.set 0) * (((2 ^ d : ℕ) : ℕ∞) * ((2 ^ (2 * m * d) : ℕ) : ℕ∞)) :=
        mul_le_mul' (covNum_le_covFlat _ _) (mul_le_mul' ((covNum_le_covFlat _ _).trans (h 0)) (hind m))
    _ = covFlat S (B.set 0) * ((2 ^ ((2 * m + 1) * d) : ℕ) : ℕ∞) := by
        rw [← Nat.cast_mul, ← pow_add]
        congr 3; ring


private lemma finset_add_singleton_zero (S : Finset ℤ) : S + ({0} : Finset ℤ) = S := by
  ext x; simp [Finset.mem_add]

private lemma finset_singleton_zero_add (S : Finset ℤ) : ({0} : Finset ℤ) + S = S := by
  ext x; simp [Finset.mem_add]

private def iterAddNbhd (n : ℕ) (W : SymNbhd) : SymNbhd :=
  match n with
  | 0 => SymNbhd.zero
  | n + 1 => (iterAddNbhd n W).add W

private lemma iterAddNbhd_add_set (a b : ℕ) (W : SymNbhd) :
    (iterAddNbhd (a + b) W).set = (iterAddNbhd a W).set + (iterAddNbhd b W).set := by
  induction b with
  | zero =>
    change (iterAddNbhd a W).set = (iterAddNbhd a W).set + {0}
    exact (finset_add_singleton_zero _).symm
  | succ b ih =>
    change (iterAddNbhd (a + b) W).set + W.set = (iterAddNbhd a W).set + ((iterAddNbhd b W).set + W.set)
    rw [ih, add_assoc]

private lemma iterAddNbhd_pow_subset (B : Sys) (hB : B.IsFinite) :
    ∀ k i : ℕ, (iterAddNbhd (2 ^ k) (B.toSymNbhd hB (i + k))).set ⊆ (B.toSymNbhd hB i).set := by
  intro k
  induction k with
  | zero =>
    intro i
    change ({0} : Finset ℤ) + (B.toSymNbhd hB i).set ⊆ (B.toSymNbhd hB i).set
    rw [finset_singleton_zero_add]
  | succ k ih =>
    intro i
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    rw [hpow, iterAddNbhd_add_set]
    have hidx : i + (k + 1) = (i + 1) + k := by omega
    rw [hidx]
    have h1 := ih (i + 1)
    have h2 : (B.toSymNbhd hB (i + 1)).set + (B.toSymNbhd hB (i + 1)).set ⊆ (B.toSymNbhd hB i).set := by
      intro x hx
      have hx' : x ∈ B.set (i + 1) + B.set (i + 1) := by
        simpa [Finset.coe_add, Sys.coe_toSymNbhd] using (Finset.mem_coe.mpr hx)
      exact (Set.Finite.mem_toFinset _).mpr (B.add_subset i hx')
    exact (Finset.add_subset_add h1 h1).trans h2

private lemma lem_ubreg (Z : SymNbhd) (B : Sys) (hB : B.IsFinite)
    {K τ : ℝ} (hτ : 0 < τ)
    (hK : ((Z.set + (B.toSymNbhd hB 0).set).card : ℝ) ≤ K * (Z.set.card : ℝ))
    {m : ℕ} (hm : 1 ≤ m) (hKm : K ≤ (1 + τ) ^ (2 ^ (m - 1))) :
    ∃ Z0 : SymNbhd,
      Z.set ⊆ Z0.set ∧
      Z0.set ⊆ Z.set + (B.toSymNbhd hB 0).set ∧
      IsClosedPair τ Z0 (B.toSymNbhd hB m) := by
  let W : SymNbhd := B.toSymNbhd hB m
  let N : ℕ := 2 ^ (m - 1)
  let c : ℕ → ℝ := fun j => ((Z.add (iterAddNbhd (2 * j) W)).set.card : ℝ)
  have hc_pos : ∀ j, (0 : ℝ) < c j := fun j => by
    dsimp only [c]; exact_mod_cast (Z.add (iterAddNbhd (2 * j) W)).card_pos
  have hc0 : c 0 = (Z.set.card : ℝ) := by
    dsimp only [c]; change ((Z.set + ({0} : Finset ℤ)).card : ℝ) = (Z.set.card : ℝ)
    rw [finset_add_singleton_zero]
  have hcN_le : c N ≤ K * c 0 := by
    rw [hc0]
    have h2N : 2 * N = 2 ^ m := by
      change 2 * 2 ^ (m - 1) = 2 ^ m
      cases m with
      | zero => omega
      | succ m' => simp [pow_succ, mul_comm]
    have hsub : (Z.add (iterAddNbhd (2 * N) W)).set ⊆ Z.set + (B.toSymNbhd hB 0).set := by
      rw [h2N]
      exact Finset.add_subset_add_left (by simpa [W] using iterAddNbhd_pow_subset B hB m 0)
    have hcle : c N ≤ ((Z.set + (B.toSymNbhd hB 0).set).card : ℝ) := by
      dsimp only [c]; exact_mod_cast Finset.card_le_card hsub
    exact hcle.trans hK
  have hex : ∃ j < N, c (j + 1) ≤ (1 + τ) * c j := by
    by_contra hall
    push Not at hall
    have hind : ∀ t ≤ N, (1 + τ) ^ t * c 0 < c t ∨ t = 0 := by
      intro t ht
      induction t with
      | zero => right; rfl
      | succ t ih =>
        left
        have hstep := hall t (by omega)
        rcases ih (by omega) with hlt | rfl
        · have h1p : (0 : ℝ) < 1 + τ := by linarith
          calc (1 + τ) ^ (t + 1) * c 0 = (1 + τ) * ((1 + τ) ^ t * c 0) := by ring
            _ < (1 + τ) * c t := mul_lt_mul_of_pos_left hlt h1p
            _ < c (t + 1) := hstep
        · simpa using hstep
    have hNpos : 0 < N := pow_pos (by norm_num) _
    rcases hind N le_rfl with hlt | h0
    · have h1 : K * c 0 ≤ (1 + τ) ^ N * c 0 :=
        mul_le_mul_of_nonneg_right hKm (le_of_lt (hc_pos 0))
      linarith
    · omega
  obtain ⟨j, hjN, hj⟩ := hex
  let Zm : SymNbhd := Z.add (iterAddNbhd (2 * j) W)
  let Z0 : SymNbhd := Z.add (iterAddNbhd (2 * j + 1) W)
  let Zp : SymNbhd := Z.add (iterAddNbhd (2 * (j + 1)) W)
  have hZm0 : Zm.set + W.set = Z0.set := by
    simp [Zm, Z0, SymNbhd.add, iterAddNbhd, add_assoc]
  have hZ0p : Z0.set + W.set = Zp.set := by
    have : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
    simp [Z0, Zp, this, SymNbhd.add, iterAddNbhd, add_assoc]
  have hsub_Z : Z.set ⊆ Z0.set := fun x hx => by
    simpa [Z0, SymNbhd.add] using Finset.add_mem_add hx (iterAddNbhd (2 * j + 1) W).zero_mem
  have hsub_top : Z0.set ⊆ Z.set + (B.toSymNbhd hB 0).set := by
    have h2N : 2 * N = 2 ^ m := by
      cases m with
      | zero => omega
      | succ m' => simp [N, pow_succ, mul_comm]
    have hle_iter : (iterAddNbhd (2 * j + 1) W).set ⊆ (iterAddNbhd (2 * N) W).set := by
      have hdiff : 2 * N = (2 * j + 1) + (2 * N - (2 * j + 1)) := by omega
      rw [hdiff, iterAddNbhd_add_set (2 * j + 1) (2 * N - (2 * j + 1)) W]
      intro x hx
      have hm := Finset.add_mem_add hx (iterAddNbhd (2 * N - (2 * j + 1)) W).zero_mem
      simpa only [add_zero] using hm
    have hpow := iterAddNbhd_pow_subset B hB m 0
    exact Finset.add_subset_add_left (hle_iter.trans (by simpa [h2N, W] using hpow))
  exact ⟨Z0, hsub_Z, hsub_top, ⟨Zm, Zp, hZm0.subset, hZ0p.subset, hj⟩⟩

private lemma half_le_log_one_add {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    τ / 2 ≤ Real.log (1 + τ) := by
  have h1p : (0 : ℝ) < 1 + τ := by linarith
  have hexp : Real.exp (-(τ / (1 + τ))) ≥ 1 - τ / (1 + τ) := by
    have := Real.add_one_le_exp (-(τ / (1 + τ)))
    linarith
  have hfrac : 1 - τ / (1 + τ) = (1 + τ)⁻¹ := by
    field_simp; ring
  rw [hfrac] at hexp
  have hexp2 : Real.exp (τ / (1 + τ)) ≤ 1 + τ := by
    rw [Real.exp_neg] at hexp
    have hpos : (0 : ℝ) < Real.exp (τ / (1 + τ)) := Real.exp_pos _
    exact (inv_le_inv₀ h1p hpos).mp hexp
  have hlog : τ / (1 + τ) ≤ Real.log (1 + τ) := by
    rw [← Real.log_exp (τ / (1 + τ))]
    exact Real.log_le_log (Real.exp_pos _) hexp2
  have hhalf : τ / 2 ≤ τ / (1 + τ) := by
    rw [div_le_div_iff₀ (by norm_num) h1p]
    nlinarith
  exact hhalf.trans hlog

private lemma lem_cc (B : Sys) (hB : B.IsFinite) {d : ℕ} (hd : B.HasDim d)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {m : ℕ} (hm : 2 ≤ m) (hdm : (2 : ℝ) * (d : ℝ) ≤ (2 ^ (m - 2) : ℝ) * τ) :
    ∃ Z0 : SymNbhd,
      (B.toSymNbhd hB 1).set ⊆ Z0.set ∧
      Z0.set ⊆ (B.toSymNbhd hB 0).set ∧
      IsClosedPair τ Z0 (B.toSymNbhd hB m) := by
  let Z1 : SymNbhd := B.toSymNbhd hB 1
  let B1 : Sys := B.dilate 1
  have hB1 : B1.IsFinite := B.dilate_isFinite 1 hB
  have hB1_0 : (B1.toSymNbhd hB1 0).set = Z1.set := by
    ext x; simp [B1, Z1, Sys.toSymNbhd, Sys.dilate]
  have hB1_m : (B1.toSymNbhd hB1 (m - 1)).set = (B.toSymNbhd hB m).set := by
    ext x
    have : m - 1 + 1 = m := by omega
    simp [B1, Sys.toSymNbhd, Sys.dilate, this]
  have hsub0 : Z1.set + (B1.toSymNbhd hB1 0).set ⊆ (B.toSymNbhd hB 0).set := by
    rw [hB1_0]
    intro x hx
    have hx' : x ∈ B.set 1 + B.set 1 := by
      simpa [Z1, Finset.coe_add, Sys.coe_toSymNbhd] using (Finset.mem_coe.mpr hx)
    exact (Set.Finite.mem_toFinset _).mpr (B.add_subset 0 hx')
  have hK : ((Z1.set + (B1.toSymNbhd hB1 0).set).card : ℝ) ≤
      ((2 : ℝ) ^ d) * (Z1.set.card : ℝ) := by
    have hc1 : ((B.toSymNbhd hB 0).set.card : ℕ∞) ≤ ((2 ^ d : ℕ) : ℕ∞) * (Z1.set.card : ℕ∞) := by
      have hc := covNum_card_le (X := (B.toSymNbhd hB 0).set) (Y := Z1.set) (fun _ => Z1.nonempty)
      have hcov : covNum ((B.toSymNbhd hB 0).set : Set ℤ) (Z1.set : Set ℤ) ≤ ((2 ^ d : ℕ) : ℕ∞) := by
        simpa [Z1, Sys.coe_toSymNbhd] using (covNum_le_covFlat _ _).trans (hd 0)
      exact hc.trans (mul_le_mul' hcov le_rfl)
    have hc2 : (Z1.set + (B1.toSymNbhd hB1 0).set).card ≤ 2 ^ d * Z1.set.card := by
      have : ((Z1.set + (B1.toSymNbhd hB1 0).set).card : ℕ∞) ≤ ((2 ^ d * Z1.set.card : ℕ) : ℕ∞) := by
        rw [Nat.cast_mul]
        exact (ENat.natCast_le_natCast.mpr (Finset.card_le_card hsub0)).trans hc1
      exact ENat.natCast_le_natCast.mp this
    exact_mod_cast hc2
  have hKm : (2 : ℝ) ^ d ≤ (1 + τ) ^ (2 ^ ((m - 1) - 1)) := by
    have hm2 : (m - 1) - 1 = m - 2 := by omega
    rw [hm2]
    have h1p : (0 : ℝ) < 1 + τ := by linarith
    have hlog2 : Real.log 2 ≤ 1 := le_of_lt (lt_trans Real.log_two_lt_d9 (by norm_num))
    have hlog_le : Real.log ((2 : ℝ) ^ d) ≤ Real.log ((1 + τ) ^ (2 ^ (m - 2))) := by
      rw [Real.log_pow, Real.log_pow]
      have hhalf := half_le_log_one_add (le_of_lt hτ) hτ1
      have h1 : (d : ℝ) * Real.log 2 ≤ (d : ℝ) := by
        nlinarith [Nat.cast_nonneg (α := ℝ) d]
      have h2 : (d : ℝ) ≤ (2 ^ (m - 2) : ℝ) * (τ / 2) := by linarith
      have h3 : (2 ^ (m - 2) : ℝ) * (τ / 2) ≤ (2 ^ (m - 2) : ℝ) * Real.log (1 + τ) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      have hpow_cast : ((2 ^ (m - 2) : ℕ) : ℝ) = (2 ^ (m - 2) : ℝ) := by push_cast; rfl
      rw [hpow_cast]
      linarith
    exact (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog_le
  obtain ⟨Z0, hZ1Z0, hZ0top, hclosed⟩ :=
    lem_ubreg Z1 B1 hB1 hτ hK (m := m - 1) (by omega) hKm
  refine ⟨Z0, hZ1Z0, hZ0top.trans hsub0, ?_⟩
  obtain ⟨Zm, Zp, h1, h2, h3⟩ := hclosed
  exact ⟨Zm, Zp, by simpa [hB1_m] using h1, by simpa [hB1_m] using h2, h3⟩

/- ### Part 3A: Balog-Szemerédi-Gowers -/

private lemma addEnergy_eq_sum_sq_rep (A : Finset ℤ) :
    E[A] = ∑ s ∈ A + A, (((A ×ˢ A).filter (fun p => p.1 + p.2 = s)).card) ^ 2 := by
  classical
  let rep : ℤ → Finset (ℤ × ℤ) := fun s => (A ×ˢ A).filter (fun p => p.1 + p.2 = s)
  have h1 : E[A] = (Finset.sigma (A + A) (fun s => rep s ×ˢ rep s)).card := by
    refine Finset.card_bij
      (fun q _ => ⟨q.1.1 + q.2.1, ((q.1.1, q.2.1), (q.1.2, q.2.2))⟩) ?_ ?_ ?_
    · intro q hq
      obtain ⟨hqP, hqEq⟩ := Finset.mem_filter.mp hq
      obtain ⟨h1, h2⟩ := Finset.mem_product.mp hqP
      obtain ⟨ha1, ha2⟩ := Finset.mem_product.mp h1
      obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp h2
      refine Finset.mem_sigma.mpr ⟨Finset.add_mem_add ha1 hb1, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha1, hb1⟩, rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha2, hb2⟩, hqEq.symm⟩
    · intro q₁ _ q₂ _ h
      have hfst : ((q₁.1.1, q₁.2.1), (q₁.1.2, q₁.2.2)) = ((q₂.1.1, q₂.2.1), (q₂.1.2, q₂.2.2)) := by
        exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
      have h11 : q₁.1.1 = q₂.1.1 := congrArg (fun t => t.1.1) hfst
      have h21 : q₁.2.1 = q₂.2.1 := congrArg (fun t => t.1.2) hfst
      have h12 : q₁.1.2 = q₂.1.2 := congrArg (fun t => t.2.1) hfst
      have h22 : q₁.2.2 = q₂.2.2 := congrArg (fun t => t.2.2) hfst
      exact Prod.ext (Prod.ext h11 h12) (Prod.ext h21 h22)
    · rintro ⟨s, ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩⟩ hm
      obtain ⟨_, hp⟩ := Finset.mem_sigma.mp hm
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨hp1A, heq1⟩ := Finset.mem_filter.mp hp1
      obtain ⟨hp2A, heq2⟩ := Finset.mem_filter.mp hp2
      obtain ⟨ha1, hb1⟩ := Finset.mem_product.mp hp1A
      obtain ⟨ha2, hb2⟩ := Finset.mem_product.mp hp2A
      refine ⟨((a1, a2), (b1, b2)), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨ha1, ha2⟩, Finset.mem_product.mpr ⟨hb1, hb2⟩⟩,
          heq1.trans heq2.symm⟩
      · exact Sigma.ext heq1 (heq_of_eq rfl)
  rw [h1, Finset.card_sigma]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.card_product, sq]

private lemma bsg_paths_diff_bound {A Spop NL0 : Finset ℤ} {δ γ : ℝ}
    (hA : A.Nonempty) (hδ : 0 < δ) (hγ : 0 < γ)
    (hNL0_ge : (δ / 2) * (A.card : ℝ) ≤ (NL0.card : ℝ))
    (hY0_le : ∑ a ∈ NL0,
      ((NL0.filter (fun a' =>
        (((A.filter (fun b => a + b ∈ Spop)) ∩ (A.filter (fun b => a' + b ∈ Spop))).card : ℝ) <
          γ * (A.card : ℝ))).card : ℝ) ≤ (1 / 8) * (NL0.card : ℝ) ^ 2) :
    ∃ A' ⊆ NL0, A'.Nonempty ∧
      (δ / 4) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      ((A' - A').card : ℝ) * ((δ / 4) * γ ^ 2 * (A.card : ℝ) ^ 3) ≤ (Spop.card : ℝ) ^ 4 := by
  classical
  let n : ℕ := A.card
  let NR : ℤ → Finset ℤ := fun a => A.filter (fun b => a + b ∈ Spop)
  let bad : ℤ → ℤ → Prop := fun a1 a2 => ((NR a1 ∩ NR a2).card : ℝ) < γ * (n : ℝ)
  have hbad_symm : ∀ a1 a2, bad a1 a2 ↔ bad a2 a1 := fun a1 a2 => by simp only [bad, Finset.inter_comm]
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hNL0_pos : (0 : ℝ) < (NL0.card : ℝ) := by nlinarith
  let A' : Finset ℤ := NL0.filter (fun a => ((NL0.filter (fun a' => bad a a')).card : ℝ) ≤
    (1 / 4) * (NL0.card : ℝ))
  have hA'_sub_NL : A' ⊆ NL0 := Finset.filter_subset _ _
  have hA'_card : (1 / 2) * (NL0.card : ℝ) ≤ (A'.card : ℝ) := by
    let badV : Finset ℤ := NL0 \ A'
    have hbadV_sum : (badV.card : ℝ) * ((1 / 4) * (NL0.card : ℝ)) ≤ (1 / 8) * (NL0.card : ℝ) ^ 2 := by
      calc (badV.card : ℝ) * ((1 / 4) * (NL0.card : ℝ))
          = ∑ _a ∈ badV, ((1 / 4) * (NL0.card : ℝ)) := by simp
        _ ≤ ∑ a ∈ badV, ((NL0.filter (fun a' => bad a a')).card : ℝ) := by
            refine Finset.sum_le_sum fun a ha => ?_
            obtain ⟨haNL, haNot⟩ := Finset.mem_sdiff.mp ha
            by_contra hlt; push Not at hlt
            exact haNot (Finset.mem_filter.mpr ⟨haNL, hlt.le⟩)
        _ ≤ ∑ a ∈ NL0, ((NL0.filter (fun a' => bad a a')).card : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
        _ ≤ (1 / 8) * (NL0.card : ℝ) ^ 2 := hY0_le
    have hbadV_le : (badV.card : ℝ) ≤ (1 / 2) * (NL0.card : ℝ) := by nlinarith
    have hpart : (A'.card : ℝ) + (badV.card : ℝ) = (NL0.card : ℝ) := by
      have hcard : badV.card + A'.card = NL0.card := Finset.card_sdiff_add_card_eq_card hA'_sub_NL
      exact_mod_cast (show A'.card + badV.card = NL0.card by omega)
    linarith
  have hA'_ge_n : (δ / 4) * (n : ℝ) ≤ (A'.card : ℝ) := by linarith
  have hA'_ne : A'.Nonempty := Finset.card_pos.mp (by
    have : (0 : ℝ) < (A'.card : ℝ) := by nlinarith
    exact_mod_cast this)
  let Q4 : Finset ((ℤ × ℤ) × (ℤ × ℤ)) := (Spop ×ˢ Spop) ×ˢ (Spop ×ˢ Spop)
  let fib : ℤ → Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
    fun d => Q4.filter (fun q => q.1.1 - q.1.2 + q.2.1 - q.2.2 = d)
  have hfib_lb : ∀ d ∈ A' - A', (δ / 4) * γ ^ 2 * (n : ℝ) ^ 3 ≤ ((fib d).card : ℝ) := by
    intro d hd
    obtain ⟨a1, ha1, a2, ha2, hda⟩ := Finset.mem_sub.mp hd
    let good3 : Finset ℤ := NL0.filter (fun a3 => ¬ bad a1 a3 ∧ ¬ bad a3 a2)
    have hgood3_card : (1 / 2) * (NL0.card : ℝ) ≤ (good3.card : ℝ) := by
      let B1 : Finset ℤ := NL0.filter (fun a3 => bad a1 a3)
      let B2 : Finset ℤ := NL0.filter (fun a3 => bad a2 a3)
      have hB1 : (B1.card : ℝ) ≤ (1 / 4) * (NL0.card : ℝ) := (Finset.mem_filter.mp ha1).2
      have hB2 : (B2.card : ℝ) ≤ (1 / 4) * (NL0.card : ℝ) := (Finset.mem_filter.mp ha2).2
      have hsub : NL0 \ good3 ⊆ B1 ∪ B2 := by
        intro a3 ha3
        obtain ⟨ha3NL, ha3not⟩ := Finset.mem_sdiff.mp ha3
        simp only [good3, Finset.mem_filter, not_and, not_not] at ha3not
        by_cases h1 : bad a1 a3
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨ha3NL, h1⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ha3NL, (hbad_symm a3 a2).mp (ha3not ha3NL h1)⟩)
      have hdiff_le : ((NL0 \ good3).card : ℝ) ≤ (1 / 2) * (NL0.card : ℝ) := by
        have hnat : (NL0 \ good3).card ≤ B1.card + B2.card :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le B1 B2)
        have hR : ((NL0 \ good3).card : ℝ) ≤ (B1.card : ℝ) + (B2.card : ℝ) := by exact_mod_cast hnat
        linarith
      have hpart : (good3.card : ℝ) + ((NL0 \ good3).card : ℝ) = (NL0.card : ℝ) := by
        have hcard : (NL0 \ good3).card + good3.card = NL0.card :=
          Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ NL0)
        exact_mod_cast (show good3.card + (NL0 \ good3).card = NL0.card by omega)
      linarith
    let paths : Finset (Σ _ : ℤ, ℤ × ℤ) :=
      Finset.sigma good3 (fun a3 => (NR a1 ∩ NR a3) ×ˢ (NR a3 ∩ NR a2))
    have hpaths_card : (δ / 4) * γ ^ 2 * (n : ℝ) ^ 3 ≤ (paths.card : ℝ) := by
      have hpeq : (paths.card : ℝ) =
          ∑ a3 ∈ good3, (((NR a1 ∩ NR a3).card : ℝ) * ((NR a3 ∩ NR a2).card : ℝ)) := by
        rw [Finset.card_sigma]; push_cast
        refine Finset.sum_congr rfl fun a3 _ => ?_
        rw [Finset.card_product]; push_cast; rfl
      rw [hpeq]
      calc (δ / 4) * γ ^ 2 * (n : ℝ) ^ 3
          ≤ (good3.card : ℝ) * (γ * (n : ℝ) * (γ * (n : ℝ))) := by
            have hg : (δ / 4) * (n : ℝ) ≤ (good3.card : ℝ) := by linarith
            have h1 : (δ / 4) * (n : ℝ) * (γ ^ 2 * (n : ℝ) ^ 2) ≤ (good3.card : ℝ) * (γ ^ 2 * (n : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right hg (mul_nonneg (sq_nonneg γ) (sq_nonneg _))
            linarith
        _ = ∑ _a3 ∈ good3, ((γ * (n : ℝ)) * (γ * (n : ℝ))) := by simp
        _ ≤ ∑ a3 ∈ good3, (((NR a1 ∩ NR a3).card : ℝ) * ((NR a3 ∩ NR a2).card : ℝ)) := by
            refine Finset.sum_le_sum fun a3 ha3 => ?_
            obtain ⟨_, hnb1, hnb2⟩ := Finset.mem_filter.mp ha3
            have h1 : γ * (n : ℝ) ≤ ((NR a1 ∩ NR a3).card : ℝ) := not_lt.mp hnb1
            have h2 : γ * (n : ℝ) ≤ ((NR a3 ∩ NR a2).card : ℝ) := not_lt.mp hnb2
            exact mul_le_mul h1 h2 (mul_nonneg hγ.le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hinj : paths.card ≤ (fib d).card := by
      refine Finset.card_le_card_of_injOn
        (fun t => ((a1 + t.2.1, t.1 + t.2.1), (t.1 + t.2.2, a2 + t.2.2))) ?_ ?_
      · intro t ht
        rw [Finset.mem_coe] at ht ⊢
        obtain ⟨_, hp⟩ := Finset.mem_sigma.mp ht
        obtain ⟨hb1, hb2⟩ := Finset.mem_product.mp hp
        obtain ⟨h11, h13⟩ := Finset.mem_inter.mp hb1
        obtain ⟨h32, h22⟩ := Finset.mem_inter.mp hb2
        have hs1 : a1 + t.2.1 ∈ Spop := (Finset.mem_filter.mp h11).2
        have hs2 : t.1 + t.2.1 ∈ Spop := (Finset.mem_filter.mp h13).2
        have hs3 : t.1 + t.2.2 ∈ Spop := (Finset.mem_filter.mp h32).2
        have hs4 : a2 + t.2.2 ∈ Spop := (Finset.mem_filter.mp h22).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr ⟨hs1, hs2⟩, Finset.mem_product.mpr ⟨hs3, hs4⟩⟩, ?_⟩
        dsimp only; omega
      · intro t1 _ t2 _ h
        dsimp only at h
        have e1 : a1 + t1.2.1 = a1 + t2.2.1 := congrArg (fun q => q.1.1) h
        have e2 : t1.1 + t1.2.1 = t2.1 + t2.2.1 := congrArg (fun q => q.1.2) h
        have e4 : a2 + t1.2.2 = a2 + t2.2.2 := congrArg (fun q => q.2.2) h
        have hb1 : t1.2.1 = t2.2.1 := by omega
        have ha3 : t1.1 = t2.1 := by omega
        have hb2 : t1.2.2 = t2.2.2 := by omega
        cases t1; cases t2
        dsimp only at ha3 hb1 hb2
        subst ha3
        congr 1
        exact Prod.ext hb1 hb2
    exact hpaths_card.trans (by exact_mod_cast hinj)
  have hsum_fib : ∑ d ∈ A' - A', ((fib d).card : ℝ) ≤ (Spop.card : ℝ) ^ 4 := by
    have hdisj : ((A' - A' : Finset ℤ) : Set ℤ).PairwiseDisjoint fib := by
      intro d1 _ d2 _ hne
      change Disjoint _ _
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      exact hne ((Finset.mem_filter.mp hq1).2.symm.trans (Finset.mem_filter.mp hq2).2)
    have hsub : (A' - A').biUnion fib ⊆ Q4 := by
      intro q hq
      obtain ⟨_, _, hqf⟩ := Finset.mem_biUnion.mp hq
      exact (Finset.mem_filter.mp hqf).1
    have hnat : ∑ d ∈ A' - A', (fib d).card ≤ Q4.card := by
      rw [← Finset.card_biUnion hdisj]
      exact Finset.card_le_card hsub
    have hQ4 : Q4.card = Spop.card ^ 4 := by
      simp only [Q4, Finset.card_product]; ring
    rw [hQ4] at hnat
    exact_mod_cast hnat
  refine ⟨A', hA'_sub_NL, hA'_ne, hA'_ge_n, ?_⟩
  calc ((A' - A').card : ℝ) * ((δ / 4) * γ ^ 2 * (n : ℝ) ^ 3)
      = ∑ _d ∈ A' - A', ((δ / 4) * γ ^ 2 * (n : ℝ) ^ 3) := by simp
    _ ≤ ∑ d ∈ A' - A', ((fib d).card : ℝ) := Finset.sum_le_sum hfib_lb
    _ ≤ (Spop.card : ℝ) ^ 4 := hsum_fib

private lemma balog_szemeredi_gowers {A : Finset ℤ} {c : ℝ}
    (hA : A.Nonempty) (hc0 : 0 < c) (hE : c * (A.card : ℝ) ^ 3 ≤ (E[A] : ℝ)) :
    ∃ A' ⊆ A, A'.Nonempty ∧
      (c / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      ((A' - A').card : ℝ) ≤ (4194304 / c ^ 10) * (A'.card : ℝ) := by
  classical
  let n : ℕ := A.card
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hA.card_pos
  let rep : ℤ → Finset (ℤ × ℤ) := fun s => (A ×ˢ A).filter (fun p => p.1 + p.2 = s)
  have hrep_le : ∀ s, (rep s).card ≤ n := by
    intro s
    refine Finset.card_le_card_of_injOn Prod.fst (fun p hp => ?_) (fun p1 hp1 p2 hp2 h => ?_)
    · exact Finset.mem_coe.mpr (Finset.mem_product.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).1).1
    · have e1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp1)).2
      have e2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hp2)).2
      exact Prod.ext h (by omega)
  have hsum_rep : ∑ s ∈ A + A, (rep s).card = n ^ 2 := by
    have h1 : (A ×ˢ A).card = ∑ s ∈ A + A, (rep s).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext p
        simp only [Finset.mem_biUnion, rep, Finset.mem_filter]
        constructor
        · intro hp
          obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp
          exact ⟨p.1 + p.2, Finset.add_mem_add ha hb, hp, rfl⟩
        · rintro ⟨_, _, hp, _⟩; exact hp
      · intro s1 _ s2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact hne ((Finset.mem_filter.mp hp1).2.symm.trans (Finset.mem_filter.mp hp2).2)
    rw [← h1, Finset.card_product, sq]
  let δ : ℝ := c / 2
  have hδ_pos : 0 < δ := by positivity
  let Spop : Finset ℤ := (A + A).filter (fun s => δ * (n : ℝ) ≤ ((rep s).card : ℝ))
  have hE_eq : (E[A] : ℝ) = ∑ s ∈ A + A, ((rep s).card : ℝ) ^ 2 := by
    rw [addEnergy_eq_sum_sq_rep]; push_cast; rfl
  have hnonpop : ∑ s ∈ (A + A) \ Spop, ((rep s).card : ℝ) ^ 2 ≤ δ * (n : ℝ) ^ 3 := by
    calc ∑ s ∈ (A + A) \ Spop, ((rep s).card : ℝ) ^ 2
        ≤ ∑ s ∈ (A + A) \ Spop, (δ * (n : ℝ)) * ((rep s).card : ℝ) := by
          refine Finset.sum_le_sum fun s hs => ?_
          obtain ⟨hsA, hsnot⟩ := Finset.mem_sdiff.mp hs
          have hlt : ((rep s).card : ℝ) < δ * (n : ℝ) := by
            by_contra hge
            push Not at hge
            exact hsnot (Finset.mem_filter.mpr ⟨hsA, hge⟩)
          rw [sq]
          exact mul_le_mul_of_nonneg_right hlt.le (Nat.cast_nonneg _)
      _ = δ * (n : ℝ) * ∑ s ∈ (A + A) \ Spop, ((rep s).card : ℝ) := by rw [← Finset.mul_sum]
      _ ≤ δ * (n : ℝ) * ∑ s ∈ A + A, ((rep s).card : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
      _ = δ * (n : ℝ) ^ 3 := by
          have : ∑ s ∈ A + A, ((rep s).card : ℝ) = (n : ℝ) ^ 2 := by exact_mod_cast hsum_rep
          rw [this]; ring
  have hpop_sq : δ * (n : ℝ) ^ 3 ≤ ∑ s ∈ Spop, ((rep s).card : ℝ) ^ 2 := by
    have hsplit : ∑ s ∈ (A + A) \ Spop, ((rep s).card : ℝ) ^ 2 + ∑ s ∈ Spop, ((rep s).card : ℝ) ^ 2 =
        ∑ s ∈ A + A, ((rep s).card : ℝ) ^ 2 :=
      Finset.sum_sdiff (Finset.filter_subset (fun s => δ * (n : ℝ) ≤ ((rep s).card : ℝ)) (A + A))
    dsimp only [δ] at hnonpop ⊢
    linarith
  have hpop_sum : δ * (n : ℝ) ^ 2 ≤ ∑ s ∈ Spop, ((rep s).card : ℝ) := by
    have h1 : ∑ s ∈ Spop, ((rep s).card : ℝ) ^ 2 ≤ (n : ℝ) * ∑ s ∈ Spop, ((rep s).card : ℝ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun s _ => ?_
      rw [sq]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hrep_le s) (Nat.cast_nonneg _)
    nlinarith
  have hSpop_card : (Spop.card : ℝ) * δ ≤ (n : ℝ) := by
    have h1 : (Spop.card : ℝ) * (δ * (n : ℝ)) ≤ ∑ s ∈ Spop, ((rep s).card : ℝ) := by
      calc (Spop.card : ℝ) * (δ * (n : ℝ)) = ∑ _s ∈ Spop, (δ * (n : ℝ)) := by simp
        _ ≤ ∑ s ∈ Spop, ((rep s).card : ℝ) :=
            Finset.sum_le_sum fun s hs => (Finset.mem_filter.mp hs).2
    have h2 : ∑ s ∈ Spop, ((rep s).card : ℝ) ≤ (n : ℝ) ^ 2 := by
      calc ∑ s ∈ Spop, ((rep s).card : ℝ) ≤ ∑ s ∈ A + A, ((rep s).card : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
        _ = (n : ℝ) ^ 2 := by exact_mod_cast hsum_rep
    nlinarith
  let G : Finset (ℤ × ℤ) := (A ×ˢ A).filter (fun p => p.1 + p.2 ∈ Spop)
  have hG_card : δ * (n : ℝ) ^ 2 ≤ (G.card : ℝ) := by
    have hG_eq : G.card = ∑ s ∈ Spop, (rep s).card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext p
        simp only [G, rep, Finset.mem_biUnion, Finset.mem_filter]
        constructor
        · rintro ⟨hp, hs⟩; exact ⟨p.1 + p.2, hs, hp, rfl⟩
        · rintro ⟨s, hs, hp, hpeq⟩; exact ⟨hp, hpeq ▸ hs⟩
      · intro s1 _ s2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro p hp1 hp2
        exact hne ((Finset.mem_filter.mp hp1).2.symm.trans (Finset.mem_filter.mp hp2).2)
    have hG_eqR : (G.card : ℝ) = ∑ s ∈ Spop, ((rep s).card : ℝ) := by exact_mod_cast hG_eq
    linarith
  let NL : ℤ → Finset ℤ := fun b => A.filter (fun a => (a, b) ∈ G)
  let NR : ℤ → Finset ℤ := fun a => A.filter (fun b => (a, b) ∈ G)
  have hsum_NL : ∑ b ∈ A, ((NL b).card : ℝ) = (G.card : ℝ) := by
    have hnat : G.card = ∑ b ∈ A, (NL b).card := by
      simp only [G, NL, Finset.card_filter, Finset.sum_product_right]
      refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
      simp [Finset.mem_filter, Finset.mem_product, ha, hb]
    exact_mod_cast hnat.symm
  have hsum_NL_sq : δ ^ 2 * (n : ℝ) ^ 3 ≤ ∑ b ∈ A, ((NL b).card : ℝ) ^ 2 := by
    have hcs : (∑ b ∈ A, ((NL b).card : ℝ)) ^ 2 ≤ (n : ℝ) * ∑ b ∈ A, ((NL b).card : ℝ) ^ 2 := by
      have hnn : 0 ≤ ∑ a ∈ A, ∑ b ∈ A, (((NL a).card : ℝ) - ((NL b).card : ℝ)) ^ 2 :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hexp : ∑ a ∈ A, ∑ b ∈ A, (((NL a).card : ℝ) - ((NL b).card : ℝ)) ^ 2 =
          2 * (n : ℝ) * ∑ a ∈ A, ((NL a).card : ℝ) ^ 2 - 2 * (∑ a ∈ A, ((NL a).card : ℝ)) ^ 2 := by
        have hsq : ∀ a b : ℤ, (((NL a).card : ℝ) - ((NL b).card : ℝ)) ^ 2 =
            ((NL a).card : ℝ) ^ 2 - 2 * ((NL a).card : ℝ) * ((NL b).card : ℝ) + ((NL b).card : ℝ) ^ 2 :=
          fun _ _ => by ring
        simp_rw [hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        have hcross : ∑ a ∈ A, ∑ b ∈ A, 2 * ((NL a).card : ℝ) * ((NL b).card : ℝ) =
            2 * (∑ a ∈ A, ((NL a).card : ℝ)) ^ 2 := by
          have : ∑ a ∈ A, ∑ b ∈ A, 2 * ((NL a).card : ℝ) * ((NL b).card : ℝ) =
              2 * ∑ a ∈ A, ((NL a).card : ℝ) * ∑ b ∈ A, ((NL b).card : ℝ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun b _ => by ring
          rw [this, ← Finset.sum_mul, sq]
        rw [hcross, ← Finset.mul_sum]
        dsimp only [n]
        ring
      linarith
    have h1 : (δ * (n : ℝ) ^ 2) ^ 2 ≤ (n : ℝ) * ∑ b ∈ A, ((NL b).card : ℝ) ^ 2 := by
      calc (δ * (n : ℝ) ^ 2) ^ 2 ≤ (G.card : ℝ) ^ 2 := by gcongr
        _ = (∑ b ∈ A, ((NL b).card : ℝ)) ^ 2 := by rw [hsum_NL]
        _ ≤ (n : ℝ) * ∑ b ∈ A, ((NL b).card : ℝ) ^ 2 := hcs
    nlinarith
  let γ : ℝ := δ ^ 2 / 16
  have hγ_pos : 0 < γ := by positivity
  let bad : ℤ → ℤ → Prop := fun a a' => (((NR a ∩ NR a').card : ℝ)) < γ * (n : ℝ)
  have hbad_symm : ∀ a a', bad a a' ↔ bad a' a := fun a a' => by
    simp only [bad, Finset.inter_comm]
  let Y : ℤ → ℕ := fun b => ((NL b ×ˢ NL b).filter (fun p => bad p.1 p.2)).card
  have hsum_Y : ∑ b ∈ A, (Y b : ℝ) ≤ γ * (n : ℝ) ^ 3 := by
    have hswap : ∑ b ∈ A, Y b = ∑ p ∈ (A ×ˢ A).filter (fun p => bad p.1 p.2), (NR p.1 ∩ NR p.2).card := by
      have h1 : ∀ b ∈ A, Y b = ∑ p ∈ A ×ˢ A, if bad p.1 p.2 ∧ (p.1, b) ∈ G ∧ (p.2, b) ∈ G then 1 else 0 := by
        intro b _
        have heq : (NL b ×ˢ NL b).filter (fun p => bad p.1 p.2) =
            (A ×ˢ A).filter (fun p => bad p.1 p.2 ∧ (p.1, b) ∈ G ∧ (p.2, b) ∈ G) := by
          ext ⟨a1, a2⟩
          simp only [NL, Finset.mem_filter, Finset.mem_product]
          tauto
        dsimp only [Y]
        rw [heq, Finset.card_filter]
      rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hb : bad p.1 p.2
      · simp only [hb, true_and, ↓reduceIte]
        have heq2 : NR p.1 ∩ NR p.2 = A.filter (fun b => (p.1, b) ∈ G ∧ (p.2, b) ∈ G) := by
          ext b
          simp only [NR, Finset.mem_inter, Finset.mem_filter]
          tauto
        rw [heq2, Finset.card_filter]
      · simp only [hb, false_and, ↓reduceIte, Finset.sum_const_zero]
    have hswapR : ∑ b ∈ A, (Y b : ℝ) =
        ∑ p ∈ (A ×ˢ A).filter (fun p => bad p.1 p.2), ((NR p.1 ∩ NR p.2).card : ℝ) := by
      exact_mod_cast hswap
    rw [hswapR]
    calc ∑ p ∈ (A ×ˢ A).filter (fun p => bad p.1 p.2), ((NR p.1 ∩ NR p.2).card : ℝ)
        ≤ ∑ _p ∈ (A ×ˢ A).filter (fun p => bad p.1 p.2), (γ * (n : ℝ)) :=
          Finset.sum_le_sum fun p hp => (Finset.mem_filter.mp hp).2.le
      _ = (((A ×ˢ A).filter (fun p => bad p.1 p.2)).card : ℝ) * (γ * (n : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((A ×ˢ A).card : ℝ) * (γ * (n : ℝ)) := by
          have hγn : 0 ≤ γ * (n : ℝ) := mul_nonneg (by dsimp only [γ]; positivity) (Nat.cast_nonneg n)
          exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_filter_le _ _)) hγn
      _ = γ * (n : ℝ) ^ 3 := by
          rw [Finset.card_product]; push_cast; ring
  have hex_b0 : ∃ b0 ∈ A, (1 / 16) * δ ^ 2 * (n : ℝ) ^ 2 ≤ (1 / 8) * ((NL b0).card : ℝ) ^ 2 - (Y b0 : ℝ) := by
    by_contra hall
    push Not at hall
    have hlt : ∑ b ∈ A, ((1 / 8) * ((NL b).card : ℝ) ^ 2 - (Y b : ℝ)) <
        ∑ _b ∈ A, ((1 / 16) * δ ^ 2 * (n : ℝ) ^ 2) :=
      Finset.sum_lt_sum_of_nonempty hA hall
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hlt
    dsimp only [γ] at hsum_Y
    linarith
  obtain ⟨b0, hb0A, hb0⟩ := hex_b0
  have hNL0_sq : (1 / 2) * δ ^ 2 * (n : ℝ) ^ 2 ≤ ((NL b0).card : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ (Y b0 : ℝ) := Nat.cast_nonneg _
    linarith
  have hNL0_ge : (δ / 2) * (n : ℝ) ≤ ((NL b0).card : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (NL b0).card]
  have hNL0_pos : (0 : ℝ) < ((NL b0).card : ℝ) := by nlinarith
  have hY0_le : (Y b0 : ℝ) ≤ (1 / 8) * ((NL b0).card : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ (1 / 16) * δ ^ 2 * (n : ℝ) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg δ)) (sq_nonneg _)
    linarith
  have hY_sum : ∑ a ∈ NL b0,
      (((NL b0).filter (fun a' =>
        (((A.filter (fun b => a + b ∈ Spop)) ∩ (A.filter (fun b => a' + b ∈ Spop))).card : ℝ) <
          γ * (A.card : ℝ))).card : ℝ) ≤ (1 / 8) * ((NL b0).card : ℝ) ^ 2 := by
    have hY_eq : Y b0 = ∑ a ∈ NL b0, ((NL b0).filter (fun a' => bad a a')).card := by
      simp only [Y, Finset.card_filter, Finset.sum_product]
    have hY_eqR : (Y b0 : ℝ) = ∑ a ∈ NL b0, (((NL b0).filter (fun a' => bad a a')).card : ℝ) := by
      exact_mod_cast hY_eq
    have hNR_eq : ∀ a ∈ NL b0, NR a = A.filter (fun b => a + b ∈ Spop) := fun a ha => by
      have haA : a ∈ A := (Finset.mem_filter.mp ha).1
      ext b; simp [NR, G, haA, Finset.mem_filter, Finset.mem_product]
    have hbad_eq : ∀ a ∈ NL b0, ∀ a' ∈ NL b0, bad a a' ↔
        (((A.filter (fun b => a + b ∈ Spop)) ∩ (A.filter (fun b => a' + b ∈ Spop))).card : ℝ) <
          γ * (A.card : ℝ) := fun a ha a' ha' => by simp only [bad, hNR_eq a ha, hNR_eq a' ha', n]
    have hcongr : ∑ a ∈ NL b0, (((NL b0).filter (fun a' => bad a a')).card : ℝ) =
        ∑ a ∈ NL b0, (((NL b0).filter (fun a' =>
          (((A.filter (fun b => a + b ∈ Spop)) ∩ (A.filter (fun b => a' + b ∈ Spop))).card : ℝ) <
            γ * (A.card : ℝ))).card : ℝ) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      congr 2; ext a'; simp only [Finset.mem_filter]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (hbad_eq a ha a' h1).mp h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (hbad_eq a ha a' h1).mpr h2⟩⟩
    linarith
  obtain ⟨A', hA'_sub_NL, hA'_ne, hA'_ge_n, hdiff_bound⟩ :=
    bsg_paths_diff_bound hA hδ_pos hγ_pos hNL0_ge hY_sum
  have hA'_sub_A : A' ⊆ A := hA'_sub_NL.trans (Finset.filter_subset _ _)
  have hSpop4 : (Spop.card : ℝ) ^ 4 * δ ^ 4 ≤ (n : ℝ) ^ 4 := by
    calc (Spop.card : ℝ) ^ 4 * δ ^ 4 = ((Spop.card : ℝ) * δ) ^ 4 := by ring
      _ ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hδ_pos.le) hSpop_card 4
  have hfinal_diff : ((A' - A').card : ℝ) ≤ (4194304 / c ^ 10) * (A'.card : ℝ) := by
    have h1 : ((A' - A').card : ℝ) * (δ ^ 9 / 1024) * (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by
      have hmul := mul_le_mul_of_nonneg_right hdiff_bound (pow_nonneg hδ_pos.le 4)
      have hlhs : ((A' - A').card : ℝ) * ((δ / 4) * γ ^ 2 * (n : ℝ) ^ 3) * δ ^ 4 =
          ((A' - A').card : ℝ) * (δ ^ 9 / 1024) * (n : ℝ) ^ 3 := by
        dsimp only [γ]; ring
      linarith
    have h2 : ((A' - A').card : ℝ) * (δ ^ 9 / 1024) ≤ (n : ℝ) := by
      have hpos3 : (0 : ℝ) < (n : ℝ) ^ 3 := pow_pos hn_pos 3
      have : ((A' - A').card : ℝ) * (δ ^ 9 / 1024) * (n : ℝ) ^ 3 ≤ (n : ℝ) * (n : ℝ) ^ 3 := by
        linarith
      exact le_of_mul_le_mul_right this hpos3
    have h3 : ((A' - A').card : ℝ) * (δ ^ 10 / 4096) ≤ (A'.card : ℝ) := by
      calc ((A' - A').card : ℝ) * (δ ^ 10 / 4096)
          = (δ / 4) * (((A' - A').card : ℝ) * (δ ^ 9 / 1024)) := by ring
        _ ≤ (δ / 4) * (n : ℝ) := mul_le_mul_of_nonneg_left h2 (div_nonneg hδ_pos.le (by norm_num))
        _ ≤ (A'.card : ℝ) := hA'_ge_n
    have heq : δ ^ 10 / 4096 = c ^ 10 / 4194304 := by dsimp only [δ]; ring
    rw [heq] at h3
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hc0 10)]
    linarith
  refine ⟨A', hA'_sub_A, hA'_ne, ?_, hfinal_diff⟩
  dsimp only [δ] at hA'_ge_n
  linarith

/- ### Part 3B: Ruzsa Modeling Lemma (s = 6) -/

private def IsFreiman6Iso {H : Type} [AddCommGroup H] (A : Finset ℤ) (φ : ℤ → H) : Prop :=
  ∀ a1 ∈ A, ∀ a2 ∈ A, ∀ a3 ∈ A, ∀ a4 ∈ A, ∀ a5 ∈ A, ∀ a6 ∈ A,
  ∀ b1 ∈ A, ∀ b2 ∈ A, ∀ b3 ∈ A, ∀ b4 ∈ A, ∀ b5 ∈ A, ∀ b6 ∈ A,
    a1 + a2 + a3 + a4 + a5 + a6 = b1 + b2 + b3 + b4 + b5 + b6 ↔
    φ a1 + φ a2 + φ a3 + φ a4 + φ a5 + φ a6 = φ b1 + φ b2 + φ b3 + φ b4 + φ b5 + φ b6

private lemma ruzsa_modeling_6 {A' : Finset ℤ} (hA' : A'.Nonempty) :
    ∃ (P : ℕ), P.Prime ∧
      12 * (6 • A' - 6 • A').card < P ∧ P ≤ 24 * (6 • A' - 6 • A').card ∧
      ∃ (A'' : Finset ℤ) (φ : ℤ → ZMod P),
        A'' ⊆ A' ∧ A''.Nonempty ∧
        A'.card ≤ 7 * A''.card ∧
        IsFreiman6Iso A'' φ := by
  classical
  let D : Finset ℤ := 6 • A' - 6 • A'
  have hD_ne : D.Nonempty := by
    obtain ⟨a0, ha0⟩ := hA'
    have h6 : 6 * a0 ∈ 6 • A' := by
      have : 6 • A' = A' + A' + A' + A' + A' + A' := by
        simp only [succ_nsmul, zero_nsmul, zero_add]
      rw [this]
      have h2 := Finset.add_mem_add ha0 ha0
      have h3 := Finset.add_mem_add h2 ha0
      have h4 := Finset.add_mem_add h3 ha0
      have h5 := Finset.add_mem_add h4 ha0
      have h6' := Finset.add_mem_add h5 ha0
      have : a0 + a0 + a0 + a0 + a0 + a0 = 6 * a0 := by ring
      rwa [this] at h6'
    exact ⟨0, Finset.mem_sub.mpr ⟨6 * a0, h6, 6 * a0, h6, sub_self _⟩⟩
  have h12D_ne : 12 * D.card ≠ 0 := Nat.mul_ne_zero (by norm_num) hD_ne.card_pos.ne'
  obtain ⟨P, hP_prime, hP_gt, hP_le⟩ := Nat.exists_prime_lt_and_le_two_mul (12 * D.card) h12D_ne
  have hP_pos : 0 < P := hP_prime.pos
  let Bmax : ℕ := (D.image Int.natAbs).sup id
  obtain ⟨Q, hQ_ge, hQ_prime⟩ := Nat.exists_infinite_primes (max (max Bmax P) 100 + 1)
  have hQ_gt_B : Bmax < Q := by omega
  have hQ_gt_P : P < Q := by omega
  have hQ_gt_100 : 100 < Q := by omega
  have : Fact Q.Prime := ⟨hQ_prime⟩
  have : NeZero Q := ⟨hQ_prime.ne_zero⟩
  have : NeZero P := ⟨hP_prime.ne_zero⟩
  have hd_nz : ∀ d ∈ D, d ≠ 0 → (d : ZMod Q) ≠ 0 := by
    intro d hd hd0 hzero
    have hdvd : (Q : ℤ) ∣ d := (ZMod.intCast_zmod_eq_zero_iff_dvd d Q).mp hzero
    have hnat_dvd : Q ∣ d.natAbs := Int.natCast_dvd.mp hdvd
    have hle_B : d.natAbs ≤ Bmax := Finset.le_sup (f := id) (Finset.mem_image_of_mem Int.natAbs hd)
    have hd_pos : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
    have hQ_le : Q ≤ d.natAbs := Nat.le_of_dvd hd_pos hnat_dvd
    omega
  let mQP : ℕ := Q / P
  let Kset : Finset ℤ := (Finset.Icc (1 : ℤ) (mQP : ℤ)) ∪ (Finset.Icc (-(mQP : ℤ)) (-1))
  have hKset_card : Kset.card ≤ 2 * mQP := by
    have h1 := Finset.card_union_le (Finset.Icc (1 : ℤ) (mQP : ℤ))
      (Finset.Icc (-(mQP : ℤ)) (-1))
    have hc1 : (Finset.Icc (1 : ℤ) (mQP : ℤ)).card = mQP := by
      rw [Int.card_Icc]
      have h : (mQP : ℤ) + 1 - 1 = (mQP : ℤ) := by ring
      rw [h, Int.toNat_natCast]
    have hc2 : (Finset.Icc (-(mQP : ℤ)) (-1)).card = mQP := by
      rw [Int.card_Icc]
      have h : (-1 : ℤ) + 1 - -(mQP : ℤ) = (mQP : ℤ) := by ring
      rw [h, Int.toNat_natCast]
    dsimp only [Kset]
    omega
  let badXi : Finset (ZMod Q) :=
    (D.erase 0).biUnion fun d => Kset.image fun k => ((k * (P : ℤ) : ℤ) : ZMod Q) * ((d : ZMod Q))⁻¹
  have hbadXi_lt : badXi.card < Q - 1 := by
    have h1 : badXi.card ≤ (D.erase 0).card * Kset.card := by
      calc badXi.card ≤ ∑ d ∈ D.erase 0, (Kset.image fun k => ((k * (P : ℤ) : ℤ) : ZMod Q) * ((d : ZMod Q))⁻¹).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ _d ∈ D.erase 0, Kset.card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
        _ = (D.erase 0).card * Kset.card := by simp
    have hDe : (D.erase 0).card ≤ D.card := Finset.card_erase_le
    have h2 : badXi.card ≤ D.card * (2 * mQP) :=
      h1.trans (Nat.mul_le_mul hDe hKset_card)
    have h3 : (2 * D.card) * mQP * P ≤ (2 * D.card) * Q := by
      have := Nat.div_mul_le_self Q P
      calc (2 * D.card) * mQP * P = (2 * D.card) * (mQP * P) := by ring
        _ ≤ (2 * D.card) * Q := Nat.mul_le_mul_left _ this
    have h4 : badXi.card * P < (Q - 1) * P := by
      have hmul : badXi.card * P ≤ 2 * D.card * Q := by
        calc badXi.card * P ≤ (D.card * (2 * mQP)) * P := Nat.mul_le_mul_right P h2
          _ = (2 * D.card) * mQP * P := by ring
          _ ≤ (2 * D.card) * Q := h3
      have hbig : 2 * D.card * Q < (Q - 1) * P := by
        have h2Q : 2 * Q ≤ 12 * (Q - 1) := by omega
        calc 2 * D.card * Q = D.card * (2 * Q) := by ring
          _ ≤ D.card * (12 * (Q - 1)) := Nat.mul_le_mul_left _ h2Q
          _ = (12 * D.card) * (Q - 1) := by ring
          _ < P * (Q - 1) := Nat.mul_lt_mul_of_pos_right hP_gt (by omega)
          _ = (Q - 1) * P := by ring
      omega
    exact Nat.lt_of_mul_lt_mul_right h4
  have hex_xi : ∃ ξ : ZMod Q, ξ ≠ 0 ∧ ξ ∉ badXi := by
    have hcard : ((Finset.univ : Finset (ZMod Q)).erase 0).card = Q - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have hsub : ¬ ((Finset.univ : Finset (ZMod Q)).erase 0 ⊆ badXi) := fun h => by
      have := Finset.card_le_card h
      omega
    obtain ⟨ξ, hξ1, hξ2⟩ := Finset.not_subset.mp hsub
    exact ⟨ξ, (Finset.mem_erase.mp hξ1).1, hξ2⟩
  obtain ⟨ξ, hξ_nz, hξ_good⟩ := hex_xi
  let bucket : ℤ → Fin 7 := fun a =>
    ⟨(7 * (ξ * (a : ZMod Q)).val) / Q, by
      have hlt : (ξ * (a : ZMod Q)).val < Q := ZMod.val_lt _
      exact Nat.div_lt_of_lt_mul (by omega)⟩
  have hex_j : ∃ j : Fin 7, A'.card ≤ 7 * (A'.filter (fun a => bucket a = j)).card := by
    by_contra hall
    push Not at hall
    have hpart : ∑ j : Fin 7, (A'.filter (fun a => bucket a = j)).card = A'.card := by
      rw [← Finset.card_biUnion]
      · congr 1
        ext a
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
        exact ⟨fun ⟨_, ha, _⟩ => ha, fun ha => ⟨bucket a, ha, rfl⟩⟩
      · intro j1 _ j2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro a ha1 ha2
        exact hne ((Finset.mem_filter.mp ha1).2.symm.trans (Finset.mem_filter.mp ha2).2)
    have hsum_lt : 7 * ∑ j : Fin 7, (A'.filter (fun a => bucket a = j)).card < 7 * A'.card := by
      rw [Finset.mul_sum]
      calc ∑ j : Fin 7, 7 * (A'.filter (fun a => bucket a = j)).card
          < ∑ _j : Fin 7, A'.card := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hall j)
        _ = 7 * A'.card := by simp
    omega
  obtain ⟨j0, hj0⟩ := hex_j
  let A'' : Finset ℤ := A'.filter (fun a => bucket a = j0)
  have hA''_sub : A'' ⊆ A' := Finset.filter_subset _ _
  have hA''_ne : A''.Nonempty := Finset.card_pos.mp (by have := hA'.card_pos; dsimp only [A'']; omega)
  let φ : ℤ → ZMod P := fun a => (((ξ * (a : ZMod Q)).val : ℤ) : ZMod P)
  refine ⟨P, hP_prime, hP_gt, by dsimp only [D] at hP_le; omega, A'', φ, hA''_sub, hA''_ne, hj0, ?_⟩
  intro a1 ha1 a2 ha2 a3 ha3 a4 ha4 a5 ha5 a6 ha6 b1 hb1 b2 hb2 b3 hb3 b4 hb4 b5 hb5 b6 hb6
  let u : ℤ → ℤ := fun x => ((ξ * (x : ZMod Q)).val : ℤ)
  have hu_modQ : ∀ x : ℤ, (u x : ZMod Q) = ξ * (x : ZMod Q) := fun x => by
    simp [u]
  have hu_diff : ∀ x ∈ A'', ∀ y ∈ A'', |u x - u y| * 7 < (Q : ℤ) := by
    intro x hx y hy
    have hbx : (7 * (ξ * (x : ZMod Q)).val) / Q = j0.val :=
      congrArg Fin.val (Finset.mem_filter.mp hx).2
    have hby : (7 * (ξ * (y : ZMod Q)).val) / Q = j0.val :=
      congrArg Fin.val (Finset.mem_filter.mp hy).2
    have h1 := Nat.div_add_mod (7 * (ξ * (x : ZMod Q)).val) Q
    have h2 := Nat.div_add_mod (7 * (ξ * (y : ZMod Q)).val) Q
    have hm1 := Nat.mod_lt (7 * (ξ * (x : ZMod Q)).val) hQ_prime.pos
    have hm2 := Nat.mod_lt (7 * (ξ * (y : ZMod Q)).val) hQ_prime.pos
    rw [hbx] at h1
    rw [hby] at h2
    dsimp only [u]
    have h7 : |7 * (((ξ * (x : ZMod Q)).val : ℤ) - ((ξ * (y : ZMod Q)).val : ℤ))| < (Q : ℤ) := by
      rw [abs_lt]; omega
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 7)] at h7
    linarith
  let W : ℤ := (u a1 + u a2 + u a3 + u a4 + u a5 + u a6) - (u b1 + u b2 + u b3 + u b4 + u b5 + u b6)
  have hW_lt : |W| < (Q : ℤ) := by
    have d1 := hu_diff a1 ha1 b1 hb1
    have d2 := hu_diff a2 ha2 b2 hb2
    have d3 := hu_diff a3 ha3 b3 hb3
    have d4 := hu_diff a4 ha4 b4 hb4
    have d5 := hu_diff a5 ha5 b5 hb5
    have d6 := hu_diff a6 ha6 b6 hb6
    have hW_eq : W = (u a1 - u b1) + (u a2 - u b2) + (u a3 - u b3) +
        (u a4 - u b4) + (u a5 - u b5) + (u a6 - u b6) := by dsimp [W]; ring
    rw [hW_eq]
    have htri : |(u a1 - u b1) + (u a2 - u b2) + (u a3 - u b3) +
        (u a4 - u b4) + (u a5 - u b5) + (u a6 - u b6)| ≤
        |u a1 - u b1| + |u a2 - u b2| + |u a3 - u b3| +
        |u a4 - u b4| + |u a5 - u b5| + |u a6 - u b6| := by
      linarith [abs_add_le ((u a1 - u b1) + (u a2 - u b2) + (u a3 - u b3) + (u a4 - u b4) + (u a5 - u b5)) (u a6 - u b6),
        abs_add_le ((u a1 - u b1) + (u a2 - u b2) + (u a3 - u b3) + (u a4 - u b4)) (u a5 - u b5),
        abs_add_le ((u a1 - u b1) + (u a2 - u b2) + (u a3 - u b3)) (u a4 - u b4),
        abs_add_le ((u a1 - u b1) + (u a2 - u b2)) (u a3 - u b3),
        abs_add_le (u a1 - u b1) (u a2 - u b2)]
    omega
  let d : ℤ := (a1 + a2 + a3 + a4 + a5 + a6) - (b1 + b2 + b3 + b4 + b5 + b6)
  have hW_modQ : (W : ZMod Q) = ξ * (d : ZMod Q) := by
    dsimp only [W, d]
    push_cast
    rw [hu_modQ, hu_modQ, hu_modQ, hu_modQ, hu_modQ, hu_modQ,
        hu_modQ, hu_modQ, hu_modQ, hu_modQ, hu_modQ, hu_modQ]
    ring
  have hW_modP : (W : ZMod P) =
      (φ a1 + φ a2 + φ a3 + φ a4 + φ a5 + φ a6) - (φ b1 + φ b2 + φ b3 + φ b4 + φ b5 + φ b6) := by
    dsimp only [W, φ, u]; push_cast; ring
  constructor
  · intro heq
    have hd0 : d = 0 := sub_eq_zero.mpr heq
    have hWQ0 : (W : ZMod Q) = 0 := by rw [hW_modQ, hd0, Int.cast_zero, mul_zero]
    have hdvdQ : (Q : ℤ) ∣ W := (ZMod.intCast_zmod_eq_zero_iff_dvd W Q).mp hWQ0
    have hW0 : W = 0 := by
      rcases hdvdQ with ⟨k, hk⟩
      have hk0 : k = 0 := by
        by_contra hkne
        have : (1 : ℤ) ≤ |k| := Int.one_le_abs hkne
        have : (Q : ℤ) ≤ |W| := by
          rw [hk, abs_mul, abs_of_pos (by exact_mod_cast hQ_prime.pos : (0 : ℤ) < Q)]
          nlinarith
        omega
      simp [hk, hk0]
    have hWP0 : (W : ZMod P) = 0 := by rw [hW0, Int.cast_zero]
    rw [hW_modP] at hWP0
    exact sub_eq_zero.mp hWP0
  · intro heqP
    by_contra hne
    have hd_nz_int : d ≠ 0 := sub_ne_zero.mpr hne
    have h6_mem : ∀ x1 ∈ A'', ∀ x2 ∈ A'', ∀ x3 ∈ A'', ∀ x4 ∈ A'', ∀ x5 ∈ A'', ∀ x6 ∈ A'',
        x1 + x2 + x3 + x4 + x5 + x6 ∈ 6 • A' := by
      intro x1 h1 x2 h2 x3 h3 x4 h4 x5 h5 x6 h6
      have h6eq : 6 • A' = A' + A' + A' + A' + A' + A' := by
        simp only [succ_nsmul, zero_nsmul, zero_add]
      rw [h6eq]
      exact Finset.add_mem_add (Finset.add_mem_add (Finset.add_mem_add (Finset.add_mem_add
        (Finset.add_mem_add (hA''_sub h1) (hA''_sub h2)) (hA''_sub h3)) (hA''_sub h4)) (hA''_sub h5)) (hA''_sub h6)
    have hd_mem : d ∈ D := Finset.mem_sub.mpr
      ⟨_, h6_mem a1 ha1 a2 ha2 a3 ha3 a4 ha4 a5 ha5 a6 ha6,
       _, h6_mem b1 hb1 b2 hb2 b3 hb3 b4 hb4 b5 hb5 b6 hb6, rfl⟩
    have hd_modQ_nz : (d : ZMod Q) ≠ 0 := hd_nz d hd_mem hd_nz_int
    have hW_nz : W ≠ 0 := by
      intro hW0
      rw [hW0, Int.cast_zero] at hW_modQ
      rcases mul_eq_zero.mp hW_modQ.symm with h1 | h2
      · exact hξ_nz h1
      · exact hd_modQ_nz h2
    have hWP0 : (W : ZMod P) = 0 := by rw [hW_modP, heqP, sub_self]
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd W P).mp hWP0
    have hk_nz : k ≠ 0 := by intro hk0; apply hW_nz; simp [hk, hk0]
    have hk_abs : |k| ≤ ((Q / P : ℕ) : ℤ) := by
      have h1 : |k| * (P : ℤ) < (Q : ℤ) := by
        have : |W| = (P : ℤ) * |k| := by
          rw [hk, abs_mul, abs_of_pos (by exact_mod_cast hP_pos : (0 : ℤ) < P)]
        linarith
      have hnat : k.natAbs * P < Q := by
        have h1' : (k.natAbs : ℤ) * (P : ℤ) < (Q : ℤ) := by simpa [Int.natCast_natAbs] using h1
        exact_mod_cast h1'
      have hdiv : k.natAbs ≤ Q / P := by
        exact (Nat.le_div_iff_mul_le hP_pos).mpr (by omega)
      have : (k.natAbs : ℤ) ≤ ((Q / P : ℕ) : ℤ) := by exact_mod_cast hdiv
      simpa [Int.natCast_natAbs] using this
    have hk_mem : k ∈ Kset := by
      rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
      rcases lt_or_gt_of_ne hk_nz with hlt | hgt
      · right; rw [abs_of_neg hlt] at hk_abs; omega
      · left; rw [abs_of_pos hgt] at hk_abs; omega
    have hξ_eq : ξ = ((k * (P : ℤ) : ℤ) : ZMod Q) * ((d : ZMod Q))⁻¹ := by
      have h1 : (W : ZMod Q) = ((k * (P : ℤ) : ℤ) : ZMod Q) := by rw [hk]; push_cast; ring
      rw [h1] at hW_modQ
      calc ξ = ξ * ((d : ZMod Q) * ((d : ZMod Q))⁻¹) := by rw [mul_inv_cancel₀ hd_modQ_nz, mul_one]
        _ = (ξ * (d : ZMod Q)) * ((d : ZMod Q))⁻¹ := by ring
        _ = ((k * (P : ℤ) : ℤ) : ZMod Q) * ((d : ZMod Q))⁻¹ := by rw [← hW_modQ]
    apply hξ_good
    refine Finset.mem_biUnion.mpr ⟨d, Finset.mem_erase.mpr ⟨hd_nz_int, hd_mem⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨k, hk_mem, hξ_eq.symm⟩

/- ### Part 3C: Classical Bogolyubov in `ZMod P` -/

private noncomputable def zmodChar (P : ℕ) (r x : ZMod P) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (((r * x).val : ℝ) / (P : ℝ)))

private lemma zmodChar_zero_right (P : ℕ) (r : ZMod P) : zmodChar P r 0 = 1 := by
  simp [zmodChar]

private lemma zmodChar_zero_left (P : ℕ) (x : ZMod P) : zmodChar P 0 x = 1 := by
  simp [zmodChar]

private lemma zmodChar_norm (P : ℕ) (r x : ZMod P) : ‖zmodChar P r x‖ = 1 := by
  unfold zmodChar
  have : 2 * Real.pi * Complex.I * (((r * x).val : ℝ) / (P : ℝ)) =
      ((2 * Real.pi * (((r * x).val : ℝ) / (P : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma zmodChar_add (P : ℕ) [NeZero P] (r x y : ZMod P) :
    zmodChar P r (x + y) = zmodChar P r x * zmodChar P r y := by
  unfold zmodChar
  rw [← Complex.exp_add]
  have hP_pos : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr (NeZero.pos P)
  have hval : (r * (x + y)).val = ((r * x).val + (r * y).val) % P := by
    rw [mul_add, ZMod.val_add]
  have hdiv : ((r * x).val + (r * y).val : ℕ) = P * (((r * x).val + (r * y).val) / P) + (r * (x + y)).val := by
    rw [hval]; exact (Nat.div_add_mod _ P).symm
  let q : ℕ := ((r * x).val + (r * y).val) / P
  have hqR : (((r * x).val : ℝ) + ((r * y).val : ℝ)) / (P : ℝ) =
      (((r * (x + y)).val : ℝ) / (P : ℝ)) + (q : ℝ) := by
    have hdivR : ((r * x).val : ℝ) + ((r * y).val : ℝ) = (P : ℝ) * (q : ℝ) + ((r * (x + y)).val : ℝ) := by
      exact_mod_cast hdiv
    field_simp
    linarith
  have hexp_diff : 2 * Real.pi * Complex.I * (((r * x).val : ℝ) / (P : ℝ)) +
      2 * Real.pi * Complex.I * (((r * y).val : ℝ) / (P : ℝ)) =
      2 * Real.pi * Complex.I * (((r * (x + y)).val : ℝ) / (P : ℝ)) + (q : ℂ) * (2 * Real.pi * Complex.I) := by
    have h1 : (((r * x).val : ℂ) / (P : ℂ)) + (((r * y).val : ℂ) / (P : ℂ)) =
        (((r * (x + y)).val : ℂ) / (P : ℂ)) + (q : ℂ) := by
      rw [add_div] at hqR
      have := congrArg Complex.ofReal hqR
      simpa only [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_natCast] using this
    linear_combination (2 * Real.pi * Complex.I) * h1
  rw [hexp_diff, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

private lemma zmodChar_neg (P : ℕ) [NeZero P] (r x : ZMod P) :
    zmodChar P r (-x) = starRingEnd ℂ (zmodChar P r x) := by
  have hmul : zmodChar P r (-x) * zmodChar P r x = 1 := by
    rw [← zmodChar_add, neg_add_cancel, zmodChar_zero_right]
  have hnorm : zmodChar P r x * starRingEnd ℂ (zmodChar P r x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, zmodChar_norm]
    norm_num
  have hnz : zmodChar P r x ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hmul; exact zero_ne_one hmul
  exact mul_right_cancel₀ hnz (hmul.trans (by rw [mul_comm, hnorm]))

private lemma zmodChar_comm (P : ℕ) (r x : ZMod P) : zmodChar P r x = zmodChar P x r := by
  simp only [zmodChar, mul_comm]

private lemma sum_zmodChar (P : ℕ) [NeZero P] (r : ZMod P) :
    ∑ x : ZMod P, zmodChar P r x = if r = 0 then (P : ℂ) else 0 := by
  by_cases hr : r = 0
  · subst hr
    simp [zmodChar_zero_left, ZMod.card]
  · rw [if_neg hr]
    have hshift : zmodChar P r 1 * ∑ x : ZMod P, zmodChar P r x = ∑ x : ZMod P, zmodChar P r x := by
      rw [Finset.mul_sum]
      conv_lhs =>
        arg 2; ext x
        rw [← zmodChar_add]
      exact Fintype.sum_equiv (Equiv.addLeft (1 : ZMod P)) _ _ (fun _ => rfl)
    have hne1 : zmodChar P r 1 ≠ 1 := by
      intro h1
      have hP_pos : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr (NeZero.pos P)
      have hr_pos : 0 < r.val := Nat.pos_of_ne_zero (fun h0 => hr ((ZMod.val_eq_zero r).mp h0))
      have hr_lt : r.val < P := ZMod.val_lt r
      have hval1 : (r * (1 : ZMod P)).val = r.val := by rw [mul_one]
      rw [zmodChar, hval1] at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have hk_eq : ((r.val : ℝ) / (P : ℝ) : ℂ) = (k : ℂ) := by
        have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
          simp [Real.pi_ne_zero, Complex.I_ne_zero]
        apply mul_left_cancel₀ hpi
        linear_combination hk
      have hkR : (r.val : ℝ) / (P : ℝ) = (k : ℝ) := by exact_mod_cast hk_eq
      have h0lt : (0 : ℝ) < (k : ℝ) := by rw [← hkR]; positivity
      have hlt1 : (k : ℝ) < 1 := by
        rw [← hkR, div_lt_one hP_pos]; exact_mod_cast hr_lt
      have hk0 : (0 : ℤ) < k := by exact_mod_cast h0lt
      have hk1 : k < 1 := by exact_mod_cast hlt1
      omega
    have hzero : (zmodChar P r 1 - 1) * ∑ x : ZMod P, zmodChar P r x = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne1)

private def zmodSval (P : ℕ) (y : ZMod P) : ℤ :=
  if 2 * y.val ≤ P then (y.val : ℤ) else (y.val : ℤ) - (P : ℤ)

private lemma zmodSval_cast (P : ℕ) [NeZero P] (y : ZMod P) :
    ((zmodSval P y : ℤ) : ZMod P) = y := by
  unfold zmodSval
  split_ifs <;> simp

private lemma zmodSval_abs_eq (P : ℕ) [NeZero P] (y : ZMod P) :
    |zmodSval P y| = ((min y.val (P - y.val) : ℕ) : ℤ) := by
  have hlt : y.val < P := ZMod.val_lt y
  unfold zmodSval
  split_ifs with h
  · rw [abs_of_nonneg (Nat.cast_nonneg _), min_eq_left (by omega)]
  · rw [abs_of_neg (by omega), min_eq_right (by omega)]; omega

private lemma zmodSval_abs_le_of_cast {P : ℕ} [NeZero P] (k : ℤ) :
    |zmodSval P (k : ZMod P)| ≤ |k| := by
  rw [zmodSval_abs_eq]
  have hP : 0 < P := NeZero.pos P
  have hlt : (k : ZMod P).val < P := ZMod.val_lt _
  have hval : ((k : ZMod P).val : ℤ) = k % (P : ℤ) := by
    rw [ZMod.val_intCast]
  have hdiv : ((k : ZMod P).val : ℤ) + (P : ℤ) * (k / (P : ℤ)) = k := by
    rw [hval]; exact Int.emod_add_mul_ediv k (P : ℤ)
  have hmin : ((min (k : ZMod P).val (P - (k : ZMod P).val) : ℕ) : ℤ) =
      min ((k : ZMod P).val : ℤ) ((P : ℤ) - ((k : ZMod P).val : ℤ)) := by
    omega
  rw [hmin]
  set q := k / (P : ℤ)
  set v := ((k : ZMod P).val : ℤ)
  have hv0 : 0 ≤ v := Nat.cast_nonneg _
  have hvP : v < (P : ℤ) := by dsimp only [v]; exact_mod_cast hlt
  by_cases hq0 : q = 0
  · rw [hq0, mul_zero, add_zero] at hdiv
    rw [← hdiv, abs_of_nonneg hv0]; exact min_le_left _ _
  · by_cases hqpos : 0 < q
    · have : (P : ℤ) ≤ k := by nlinarith
      rw [abs_of_nonneg (by omega)]; exact le_trans (min_le_left _ _) (by omega)
    · by_cases hqm1 : q = -1
      · rw [hqm1] at hdiv
        have hk_eq : k = v - (P : ℤ) := by linarith
        rw [hk_eq, abs_of_neg (by omega)]
        have : -(v - (P : ℤ)) = (P : ℤ) - v := by ring
        rw [this]; exact min_le_right _ _
      · have hqle : q ≤ -2 := by omega
        have : k ≤ -(P : ℤ) := by nlinarith
        rw [abs_of_neg (by omega)]
        exact le_trans (min_le_left _ _) (by omega)

private noncomputable def zmodDist (P : ℕ) (y : ZMod P) : ℝ :=
  ((min y.val (P - y.val) : ℕ) : ℝ) / (P : ℝ)

private lemma zmodDist_eq_sval (P : ℕ) [NeZero P] (y : ZMod P) :
    zmodDist P y = (|zmodSval P y| : ℝ) / (P : ℝ) := by
  unfold zmodDist
  congr 1
  exact_mod_cast (zmodSval_abs_eq P y).symm

private lemma zmodDist_zero (P : ℕ) : zmodDist P 0 = 0 := by simp [zmodDist]

private lemma zmodDist_neg (P : ℕ) [NeZero P] (y : ZMod P) : zmodDist P (-y) = zmodDist P y := by
  rw [zmodDist_eq_sval, zmodDist_eq_sval]
  congr 1
  have h1 : |zmodSval P (-y)| ≤ |zmodSval P y| := by
    have : (-y : ZMod P) = ((-(zmodSval P y) : ℤ) : ZMod P) := by
      rw [Int.cast_neg, zmodSval_cast]
    rw [this]
    simpa [abs_neg] using zmodSval_abs_le_of_cast (P := P) (-(zmodSval P y))
  have h2 : |zmodSval P y| ≤ |zmodSval P (-y)| := by
    have hcast : y = ((-(zmodSval P (-y)) : ℤ) : ZMod P) := by
      rw [Int.cast_neg, zmodSval_cast, neg_neg]
    have h2' := zmodSval_abs_le_of_cast (P := P) (-(zmodSval P (-y)))
    rw [← hcast, abs_neg] at h2'
    exact h2'
  exact_mod_cast le_antisymm h1 h2

private lemma zmodDist_add_le (P : ℕ) [NeZero P] (a b : ZMod P) :
    zmodDist P (a + b) ≤ zmodDist P a + zmodDist P b := by
  rw [zmodDist_eq_sval, zmodDist_eq_sval, zmodDist_eq_sval, ← add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hcast : a + b = (((zmodSval P a + zmodSval P b : ℤ)) : ZMod P) := by
    rw [Int.cast_add, zmodSval_cast, zmodSval_cast]
  have h1 : |zmodSval P (a + b)| ≤ |zmodSval P a + zmodSval P b| := by
    rw [hcast]; exact zmodSval_abs_le_of_cast _
  have h2 : |zmodSval P a + zmodSval P b| ≤ |zmodSval P a| + |zmodSval P b| := abs_add_le _ _
  exact_mod_cast h1.trans h2

private lemma norm_exp_I_mul_sub_one_le (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
  have hsq : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * Real.sin (t / 2)) ^ 2 := by
    rw [Complex.exp_mul_I, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.cos_ofReal_re, Complex.mul_re,
      Complex.sin_ofReal_re, Complex.I_re, mul_zero, Complex.sin_ofReal_im, Complex.I_im,
      mul_one, sub_zero, add_zero, Complex.one_re, Complex.sub_im, Complex.add_im,
      Complex.cos_ofReal_im, Complex.mul_im, zero_add, Complex.one_im]
    have hcos : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
      have := Real.cos_two_mul (t / 2)
      have h1 : 2 * (t / 2) = t := by ring
      rw [h1] at this
      have hsc := Real.sin_sq_add_cos_sq (t / 2)
      linarith
    have hsin : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
      have := Real.sin_two_mul (t / 2)
      have h1 : 2 * (t / 2) = t := by ring
      rwa [h1] at this
    rw [hcos, hsin]
    have hsc := Real.sin_sq_add_cos_sq (t / 2)
    nlinarith
  have hle : |2 * Real.sin (t / 2)| ≤ |t| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hsin := Real.abs_sin_le_abs (x := t / 2)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hsin
    linarith
  have hsq2 : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ^ 2 ≤ |t| ^ 2 := by
    rw [hsq, ← sq_abs (2 * Real.sin (t / 2))]
    exact pow_le_pow_left₀ (abs_nonneg _) hle 2
  nlinarith [norm_nonneg (Complex.exp ((t : ℂ) * Complex.I) - 1), abs_nonneg t]

private lemma zmodChar_sub_one_le (P : ℕ) [NeZero P] (r x : ZMod P) :
    ‖zmodChar P r x - 1‖ ≤ 8 * zmodDist P (r * x) := by
  have hP_pos : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr (NeZero.pos P)
  have hlt : (r * x).val < P := ZMod.val_lt _
  unfold zmodChar zmodDist
  by_cases h : (r * x).val ≤ P - (r * x).val
  · rw [min_eq_left h]
    have hre : 2 * Real.pi * Complex.I * (((r * x).val : ℝ) / (P : ℝ)) =
        ((2 * Real.pi * (((r * x).val : ℝ) / (P : ℝ)) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hre]
    calc ‖Complex.exp (((2 * Real.pi * (((r * x).val : ℝ) / (P : ℝ)) : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ |2 * Real.pi * (((r * x).val : ℝ) / (P : ℝ))| := norm_exp_I_mul_sub_one_le _
      _ = 2 * Real.pi * (((r * x).val : ℝ) / (P : ℝ)) := abs_of_nonneg (by positivity)
      _ ≤ 8 * (((r * x).val : ℝ) / (P : ℝ)) := by
          have := Real.pi_lt_four
          nlinarith [div_nonneg (Nat.cast_nonneg (α := ℝ) (r * x).val) hP_pos.le]
  · rw [min_eq_right (by omega)]
    have hexp : Complex.exp (2 * Real.pi * Complex.I * (((r * x).val : ℝ) / (P : ℝ))) =
        Complex.exp (((-(2 * Real.pi * (((P - (r * x).val : ℕ) : ℝ) / (P : ℝ))) : ℝ) : ℂ) * Complex.I) := by
      have hsub : (((r * x).val : ℝ) / (P : ℝ)) = 1 - (((P - (r * x).val : ℕ) : ℝ) / (P : ℝ)) := by
        rw [Nat.cast_sub hlt.le]; field_simp; ring
      have harg : 2 * Real.pi * Complex.I * (((r * x).val : ℝ) / (P : ℝ)) =
          2 * Real.pi * Complex.I +
          ((-(2 * Real.pi * (((P - (r * x).val : ℕ) : ℝ) / (P : ℝ))) : ℝ) : ℂ) * Complex.I := by
        have hsubC : (((r * x).val : ℂ) / (P : ℂ)) = 1 - (((P - (r * x).val : ℕ) : ℂ) / (P : ℂ)) := by
          have := congrArg Complex.ofReal hsub
          simpa only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_natCast] using this
        push_cast
        linear_combination (2 * Real.pi * Complex.I) * hsubC
      rw [harg, Complex.exp_add, Complex.exp_two_pi_mul_I, one_mul]
    rw [hexp]
    calc ‖Complex.exp (((-(2 * Real.pi * (((P - (r * x).val : ℕ) : ℝ) / (P : ℝ))) : ℝ) : ℂ) * Complex.I) - 1‖
        ≤ |-(2 * Real.pi * (((P - (r * x).val : ℕ) : ℝ) / (P : ℝ)))| := norm_exp_I_mul_sub_one_le _
      _ = 2 * Real.pi * (((P - (r * x).val : ℕ) : ℝ) / (P : ℝ)) := by
          rw [abs_neg, abs_of_nonneg (by positivity)]
      _ ≤ 8 * (((P - (r * x).val : ℕ) : ℝ) / (P : ℝ)) := by
          have := Real.pi_lt_four
          nlinarith [div_nonneg (Nat.cast_nonneg (α := ℝ) (P - (r * x).val)) hP_pos.le]

private lemma bogolyubov_zmod {P : ℕ} [NeZero P] {S0 : Finset (ZMod P)} (hS0 : S0.Nonempty) :
    let α : ℝ := (S0.card : ℝ) / (P : ℝ)
    ∃ Γ : Finset (ZMod P),
      (Γ.card : ℝ) ≤ 4 / α ^ 2 ∧
      let W : ℕ → Finset (ZMod P) := fun i =>
        Finset.univ.filter (fun x => ∀ r ∈ Γ, zmodDist P (r * x) < 1 / (16 * (2 : ℝ) ^ i))
      (∀ i, (0 : ZMod P) ∈ W i) ∧
      (∀ i, ∀ x ∈ W i, -x ∈ W i) ∧
      (∀ i, W (i + 1) + W (i + 1) ⊆ W i) ∧
      (W 0 ⊆ (S0 + S0) - (S0 + S0)) ∧
      ((P : ℝ) ≤ (16 : ℝ) ^ Γ.card * ((W 0).card : ℝ)) ∧
      (∀ i, ∃ T ⊆ W i, T.card ≤ 8 ^ Γ.card ∧ W i ⊆ T + W (i + 2)) := by
  classical
  intro α
  have hP_pos : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr (NeZero.pos P)
  have hS0_pos : (0 : ℝ) < (S0.card : ℝ) := Nat.cast_pos.mpr hS0.card_pos
  have hα_pos : 0 < α := div_pos hS0_pos hP_pos
  let fhat : ZMod P → ℂ := fun r => ∑ x ∈ S0, zmodChar P r x
  have hfhat_zero : fhat 0 = (S0.card : ℂ) := by
    simp [fhat, zmodChar_zero_left]
  have hparseval : ∑ r : ZMod P, ‖fhat r‖ ^ 2 = (P : ℝ) * (S0.card : ℝ) := by
    have hC : (∑ r : ZMod P, ((‖fhat r‖ ^ 2 : ℝ) : ℂ)) = ((P : ℂ) * (S0.card : ℂ)) := by
      have hterm : ∀ r : ZMod P, ((‖fhat r‖ ^ 2 : ℝ) : ℂ) =
          ∑ x ∈ S0, ∑ y ∈ S0, zmodChar P r (x - y) := by
        intro r
        have hsq : ((‖fhat r‖ ^ 2 : ℝ) : ℂ) = fhat r * starRingEnd ℂ (fhat r) := by
          rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
        rw [hsq]
        dsimp only [fhat]
        rw [map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← zmodChar_neg, ← zmodChar_add, sub_eq_add_neg]
      simp_rw [hterm]
      rw [Finset.sum_comm]
      calc ∑ x ∈ S0, ∑ r : ZMod P, ∑ y ∈ S0, zmodChar P r (x - y)
          = ∑ x ∈ S0, ∑ y ∈ S0, ∑ r : ZMod P, zmodChar P r (x - y) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ x ∈ S0, ∑ y ∈ S0, (if x - y = 0 then (P : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
            simp_rw [zmodChar_comm P _ (x - y)]
            exact sum_zmodChar P (x - y)
        _ = ∑ x ∈ S0, (P : ℂ) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            have : ∑ y ∈ S0, (if x - y = 0 then (P : ℂ) else 0) =
                ∑ y ∈ S0, (if y = x then (P : ℂ) else 0) := by
              refine Finset.sum_congr rfl fun y _ => ?_
              simp [sub_eq_zero, eq_comm]
            rw [this, Finset.sum_ite_eq' S0 x, if_pos hx]
        _ = (P : ℂ) * (S0.card : ℂ) := by simp [mul_comm]
    have hre := congrArg Complex.re hC
    rw [Complex.re_sum] at hre
    simpa only [Complex.ofReal_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      mul_zero, sub_zero] using hre
  let Γ : Finset (ZMod P) :=
    Finset.univ.filter (fun r => r ≠ 0 ∧ (1 / 4) * α ^ 3 * (P : ℝ) ^ 2 ≤ ‖fhat r‖ ^ 2)
  have hΓ_card : (Γ.card : ℝ) ≤ 4 / α ^ 2 := by
    have h1 : (Γ.card : ℝ) * ((1 / 4) * α ^ 3 * (P : ℝ) ^ 2) ≤ (P : ℝ) * (S0.card : ℝ) := by
      calc (Γ.card : ℝ) * ((1 / 4) * α ^ 3 * (P : ℝ) ^ 2)
          = ∑ _r ∈ Γ, ((1 / 4) * α ^ 3 * (P : ℝ) ^ 2) := by simp
        _ ≤ ∑ r ∈ Γ, ‖fhat r‖ ^ 2 := Finset.sum_le_sum fun r hr => (Finset.mem_filter.mp hr).2.2
        _ ≤ ∑ r : ZMod P, ‖fhat r‖ ^ 2 :=
            Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
        _ = (P : ℝ) * (S0.card : ℝ) := hparseval
    have hPS : (P : ℝ) * (S0.card : ℝ) = α * (P : ℝ) ^ 2 := by
      dsimp only [α]; field_simp
    rw [hPS] at h1
    rw [le_div_iff₀ (by positivity)]
    have hP2 : (0 : ℝ) < (P : ℝ) ^ 2 := by positivity
    have : (Γ.card : ℝ) * α ^ 2 * (α * (P : ℝ) ^ 2) ≤ 4 * (α * (P : ℝ) ^ 2) := by linarith
    exact le_of_mul_le_mul_right this (mul_pos hα_pos hP2)
  let W : ℕ → Finset (ZMod P) := fun i =>
    Finset.univ.filter (fun x => ∀ r ∈ Γ, zmodDist P (r * x) < 1 / (16 * (2 : ℝ) ^ i))
  refine ⟨Γ, hΓ_card, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 0 ∈ W i
    intro i
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r _ => ?_⟩
    rw [mul_zero, zmodDist_zero]; positivity
  · -- -x ∈ W i
    intro i x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
    rw [mul_neg, zmodDist_neg]
    exact (Finset.mem_filter.mp hx).2 r hr
  · -- W (i + 1) + W (i + 1) ⊆ W i
    intro i x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
    have ha' := (Finset.mem_filter.mp ha).2 r hr
    have hb' := (Finset.mem_filter.mp hb).2 r hr
    have htri : zmodDist P (r * (a + b)) ≤ zmodDist P (r * a) + zmodDist P (r * b) := by
      rw [mul_add]; exact zmodDist_add_le P _ _
    have hhalf : 1 / (16 * (2 : ℝ) ^ (i + 1)) + 1 / (16 * (2 : ℝ) ^ (i + 1)) = 1 / (16 * (2 : ℝ) ^ i) := by
      rw [pow_succ]; field_simp; ring
    linarith
  · -- W 0 ⊆ (S0 + S0) - (S0 + S0) via Fourier inversion!
    intro x hx
    have hxΓ : ∀ r ∈ Γ, zmodDist P (r * x) < 1 / 16 := by
      intro r hr; simpa using (Finset.mem_filter.mp hx).2 r hr
    have hsum_pos : (0 : ℝ) < (∑ r : ZMod P, ((‖fhat r‖ ^ 4 : ℝ) : ℂ) * zmodChar P r (-x)).re := by
      rw [Complex.re_sum]
      have hterm_re : ∀ r : ZMod P, (((‖fhat r‖ ^ 4 : ℝ) : ℂ) * zmodChar P r (-x)).re =
          ‖fhat r‖ ^ 4 * (zmodChar P r (-x)).re := by
        intro r
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      simp_rw [hterm_re]
      let rest : Finset (ZMod P) := (Finset.univ.erase 0) \ Γ
      have hsplit : ∑ r : ZMod P, ‖fhat r‖ ^ 4 * (zmodChar P r (-x)).re =
          (S0.card : ℝ) ^ 4 +
          ∑ r ∈ Γ, ‖fhat r‖ ^ 4 * (zmodChar P r (-x)).re +
          ∑ r ∈ rest, ‖fhat r‖ ^ 4 * (zmodChar P r (-x)).re := by
        have h0 : ‖fhat 0‖ ^ 4 * (zmodChar P 0 (-x)).re = (S0.card : ℝ) ^ 4 := by
          simp [hfhat_zero, zmodChar_zero_left]
        have hΓsub : Γ ⊆ Finset.univ.erase 0 := fun r hr =>
          Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hr).2.1, Finset.mem_univ _⟩
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod P)), h0]
        rw [← Finset.sum_sdiff hΓsub]
        ring
      rw [hsplit]
      have hΓ_nn : 0 ≤ ∑ r ∈ Γ, ‖fhat r‖ ^ 4 * (zmodChar P r (-x)).re := by
        refine Finset.sum_nonneg fun r hr => mul_nonneg (by positivity) ?_
        have h1 : ‖zmodChar P r (-x) - 1‖ ≤ 1 / 2 := by
          have := zmodChar_sub_one_le P r (-x)
          rw [mul_neg, zmodDist_neg] at this
          linarith [hxΓ r hr]
        have h2 : |(zmodChar P r (-x)).re - 1| ≤ ‖zmodChar P r (-x) - 1‖ := by
          have := Complex.abs_re_le_norm (zmodChar P r (-x) - 1)
          simpa using this
        have := abs_le.mp (h2.trans h1)
        linarith
      have hrest_ge : -(1 / 4) * (S0.card : ℝ) ^ 4 ≤ ∑ r ∈ rest, ‖fhat r‖ ^ 4 * (zmodChar P r (-x)).re := by
        have hneg : ∑ r ∈ rest, -(‖fhat r‖ ^ 4) ≤ ∑ r ∈ rest, ‖fhat r‖ ^ 4 * (zmodChar P r (-x)).re := by
          refine Finset.sum_le_sum fun r _ => ?_
          have hre : -1 ≤ (zmodChar P r (-x)).re := by
            have h1 := Complex.abs_re_le_norm (zmodChar P r (-x))
            rw [zmodChar_norm] at h1
            exact (abs_le.mp h1).1
          nlinarith [pow_nonneg (norm_nonneg (fhat r)) 4]
        have hub : ∑ r ∈ rest, ‖fhat r‖ ^ 4 ≤ (1 / 4) * (S0.card : ℝ) ^ 4 := by
          calc ∑ r ∈ rest, ‖fhat r‖ ^ 4
              ≤ ∑ r ∈ rest, ((1 / 4) * α ^ 3 * (P : ℝ) ^ 2) * ‖fhat r‖ ^ 2 := by
                refine Finset.sum_le_sum fun r hr => ?_
                obtain ⟨hr0, hrnot⟩ := Finset.mem_sdiff.mp hr
                have hlt : ‖fhat r‖ ^ 2 < (1 / 4) * α ^ 3 * (P : ℝ) ^ 2 := by
                  by_contra hge; push Not at hge
                  exact hrnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_erase.mp hr0).1, hge⟩)
                have : ‖fhat r‖ ^ 4 = ‖fhat r‖ ^ 2 * ‖fhat r‖ ^ 2 := by ring
                rw [this]
                exact mul_le_mul_of_nonneg_right hlt.le (sq_nonneg _)
            _ = ((1 / 4) * α ^ 3 * (P : ℝ) ^ 2) * ∑ r ∈ rest, ‖fhat r‖ ^ 2 := by rw [← Finset.mul_sum]
            _ ≤ ((1 / 4) * α ^ 3 * (P : ℝ) ^ 2) * ∑ r : ZMod P, ‖fhat r‖ ^ 2 := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
            _ = (1 / 4) * (S0.card : ℝ) ^ 4 := by
                rw [hparseval]; dsimp only [α]; field_simp
        rw [Finset.sum_neg_distrib] at hneg
        linarith
      have hS4 : (0 : ℝ) < (S0.card : ℝ) ^ 4 := by positivity
      linarith
    have hexpand : ∑ r : ZMod P, ((‖fhat r‖ ^ 4 : ℝ) : ℂ) * zmodChar P r (-x) =
        ∑ a ∈ S0, ∑ b ∈ S0, ∑ c ∈ S0, ∑ d ∈ S0,
          if a + b - c - d - x = 0 then (P : ℂ) else 0 := by
      have hterm' : ∀ r : ZMod P, ((‖fhat r‖ ^ 4 : ℝ) : ℂ) * zmodChar P r (-x) =
          ∑ a ∈ S0, ∑ b ∈ S0, ∑ c ∈ S0, ∑ d ∈ S0, zmodChar P r (a + b - c - d - x) := by
        intro r
        have hsq : ((‖fhat r‖ ^ 2 : ℝ) : ℂ) = fhat r * starRingEnd ℂ (fhat r) := by
          rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
        have h4 : ((‖fhat r‖ ^ 4 : ℝ) : ℂ) =
            (fhat r * fhat r) * (starRingEnd ℂ (fhat r) * starRingEnd ℂ (fhat r)) := by
          have : ((‖fhat r‖ ^ 4 : ℝ) : ℂ) = ((‖fhat r‖ ^ 2 : ℝ) : ℂ) * ((‖fhat r‖ ^ 2 : ℝ) : ℂ) := by
            push_cast; ring
          rw [this, hsq]; ring
        rw [h4]
        calc ((fhat r * fhat r) * (starRingEnd ℂ (fhat r) * starRingEnd ℂ (fhat r))) * zmodChar P r (-x)
            = (∑ a ∈ S0, zmodChar P r a) *
              ((∑ b ∈ S0, zmodChar P r b) *
               ((∑ c ∈ S0, zmodChar P r (-c)) *
                ((∑ d ∈ S0, zmodChar P r (-d)) * zmodChar P r (-x)))) := by
                have hc : starRingEnd ℂ (fhat r) = ∑ c ∈ S0, zmodChar P r (-c) := by
                  simp only [fhat, map_sum, ← zmodChar_neg]
                rw [hc]; dsimp only [fhat]; ring
          _ = ∑ a ∈ S0, ∑ b ∈ S0, ∑ c ∈ S0, ∑ d ∈ S0, zmodChar P r (a + b - c - d - x) := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun a _ => ?_
                rw [Finset.sum_mul, Finset.mul_sum]
                refine Finset.sum_congr rfl fun b _ => ?_
                rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun c _ => ?_
                rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
                refine Finset.sum_congr rfl fun d _ => ?_
                simp only [← zmodChar_add]
                congr 1; abel
      simp_rw [hterm']
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp_rw [zmodChar_comm P _ (a + b - c - d - x)]
      exact sum_zmodChar P (a + b - c - d - x)
    rw [hexpand] at hsum_pos
    by_contra hnot
    have hzero : (∑ a ∈ S0, ∑ b ∈ S0, ∑ c ∈ S0, ∑ d ∈ S0,
        if a + b - c - d - x = 0 then (P : ℂ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb =>
        Finset.sum_eq_zero fun c hc => Finset.sum_eq_zero fun d hd => ?_
      rw [if_neg]
      intro heq
      apply hnot
      have hx_eq : (a + b) - (c + d) = x := by
        have := sub_eq_zero.mp heq
        abel_nf at this ⊢
        exact this
      exact Finset.mem_sub.mpr ⟨a + b, Finset.add_mem_add ha hb, c + d, Finset.add_mem_add hc hd, hx_eq⟩
    rw [hzero, Complex.zero_re] at hsum_pos
    exact lt_irrefl 0 hsum_pos
  · -- Lower bound |W 0| ≥ P / 16^|Γ| via torus box pigeonhole!
    let box : ZMod P → (Γ → Fin 16) := fun x r =>
      ⟨(16 * (r.1 * x).val) / P, by
        have hlt := ZMod.val_lt (r.1 * x)
        exact Nat.div_lt_of_lt_mul (by omega)⟩
    have hcard_cod : Fintype.card (Γ → Fin 16) = 16 ^ Γ.card := by
      simp [Fintype.card_fin]
    have hex_b : ∃ b : Γ → Fin 16, P ≤ 16 ^ Γ.card * (Finset.univ.filter (fun x => box x = b)).card := by
      by_contra hall
      push Not at hall
      have hpart : ∑ b : Γ → Fin 16, (Finset.univ.filter (fun x => box x = b)).card = P := by
        rw [← Finset.card_biUnion]
        · have : Finset.univ.biUnion (fun b : Γ → Fin 16 => Finset.univ.filter (fun x => box x = b)) =
              (Finset.univ : Finset (ZMod P)) := by
            ext x; simp
          rw [this, Finset.card_univ, ZMod.card]
        · intro b1 _ b2 _ hne
          change Disjoint _ _
          rw [Finset.disjoint_left]
          intro x hx1 hx2
          exact hne ((Finset.mem_filter.mp hx1).2.symm.trans (Finset.mem_filter.mp hx2).2)
      have hlt : 16 ^ Γ.card * ∑ b : Γ → Fin 16, (Finset.univ.filter (fun x => box x = b)).card <
          16 ^ Γ.card * P := by
        rw [Finset.mul_sum]
        calc ∑ b : Γ → Fin 16, 16 ^ Γ.card * (Finset.univ.filter (fun x => box x = b)).card
            < ∑ _b : Γ → Fin 16, P :=
              Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun b _ => hall b)
          _ = 16 ^ Γ.card * P := by simp [hcard_cod]
      rw [hpart] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨b0, hb0⟩ := hex_b
    let F := Finset.univ.filter (fun x : ZMod P => box x = b0)
    have hF_ne : F.Nonempty := Finset.card_pos.mp (by
      have hP0 := NeZero.pos P
      have h16 : 0 < 16 ^ Γ.card := by positivity
      by_contra h0
      have : F.card = 0 := by omega
      rw [this, mul_zero] at hb0; omega)
    obtain ⟨x0, hx0⟩ := hF_ne
    have hF_le_W0 : F.card ≤ (W 0).card := by
      refine Finset.card_le_card_of_injOn (fun x => x - x0) ?_ ?_
      · intro x hx
        rw [Finset.mem_coe] at hx ⊢
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
        have hbx : (16 * (r * x).val) / P = (b0 ⟨r, hr⟩).val :=
          congrArg (fun f => (f ⟨r, hr⟩).val) (Finset.mem_filter.mp hx).2
        have hbx0 : (16 * (r * x0).val) / P = (b0 ⟨r, hr⟩).val :=
          congrArg (fun f => (f ⟨r, hr⟩).val) (Finset.mem_filter.mp hx0).2
        have h1 := Nat.div_add_mod (16 * (r * x).val) P
        have h2 := Nat.div_add_mod (16 * (r * x0).val) P
        have hm1 := Nat.mod_lt (16 * (r * x).val) (NeZero.pos P)
        have hm2 := Nat.mod_lt (16 * (r * x0).val) (NeZero.pos P)
        rw [hbx] at h1; rw [hbx0] at h2
        have hdiff : |((r * x).val : ℤ) - ((r * x0).val : ℤ)| * 16 < (P : ℤ) := by
          have h16 : |16 * (((r * x).val : ℤ) - ((r * x0).val : ℤ))| < (P : ℤ) := by
            rw [abs_lt]; omega
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℤ) < 16)] at h16
          linarith
        set dZ : ℤ := ((r * x).val : ℤ) - ((r * x0).val : ℤ)
        have hcast : r * (x - x0) = (dZ : ZMod P) := by
          dsimp only [dZ]
          rw [mul_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
            ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
        have hle := zmodSval_abs_le_of_cast (P := P) dZ
        rw [← hcast] at hle
        dsimp only [dZ] at hle
        dsimp only
        rw [zmodDist_eq_sval]
        simp only [pow_zero, mul_one]
        rw [div_lt_div_iff₀ hP_pos (by norm_num)]
        have hdiffR : (|zmodSval P (r * (x - x0))| : ℝ) * 16 < (P : ℝ) := by
          exact_mod_cast (show |zmodSval P (r * (x - x0))| * 16 < (P : ℤ) by nlinarith)
        linarith
      · intro x1 _ x2 _ h
        exact sub_left_inj.mp h
    have hnat : P ≤ 16 ^ Γ.card * (W 0).card := hb0.trans (Nat.mul_le_mul_left _ hF_le_W0)
    change (P : ℝ) ≤ (16 : ℝ) ^ Γ.card * ((W 0).card : ℝ)
    exact_mod_cast hnat
  · -- Covering W i by ≤ 8^|Γ| translates in W i of W (i + 2)!
    intro i
    let L : ℕ := 64 * 2 ^ i
    let bkt : ZMod P → (Γ → ℤ) := fun x r => ((L : ℤ) * zmodSval P (r.1 * x)) / (P : ℤ)
    let cod : Finset (Γ → ℤ) := Fintype.piFinset (fun _ : Γ => Finset.Ico (-4 : ℤ) 4)
    have hcod_card : cod.card = 8 ^ Γ.card := by
      simp [cod, Fintype.card_piFinset]
    have hbkt_mem : ∀ x ∈ W i, bkt x ∈ cod := by
      intro x hx
      refine Fintype.mem_piFinset.mpr fun r => ?_
      have hdist := (Finset.mem_filter.mp hx).2 r.1 r.2
      rw [zmodDist_eq_sval] at hdist
      have hL_lt : (L : ℝ) * (|zmodSval P (r.1 * x)| : ℝ) < 4 * (P : ℝ) := by
        have h1 : (|zmodSval P (r.1 * x)| : ℝ) < (P : ℝ) / (16 * (2 : ℝ) ^ i) := by
          rw [div_lt_iff₀ hP_pos] at hdist
          linarith [show (1 / (16 * (2 : ℝ) ^ i)) * (P : ℝ) = (P : ℝ) / (16 * (2 : ℝ) ^ i) by ring]
        have hL_eq : (L : ℝ) = 4 * (16 * (2 : ℝ) ^ i) := by dsimp [L]; push_cast; ring
        rw [hL_eq]
        have hpos : (0 : ℝ) < 16 * (2 : ℝ) ^ i := by positivity
        have hmul : (16 * (2 : ℝ) ^ i) * (|zmodSval P (r.1 * x)| : ℝ) < (P : ℝ) := by
          rwa [lt_div_iff₀' hpos] at h1
        linarith
      have hL_int : |(L : ℤ) * zmodSval P (r.1 * x)| < 4 * (P : ℤ) := by
        have h1 : ((L : ℤ) * |zmodSval P (r.1 * x)| : ℤ) < 4 * (P : ℤ) := by exact_mod_cast hL_lt
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        exact h1
      have hdiv_bounds : -4 ≤ Int.ediv ((L : ℤ) * zmodSval P (r.1 * x)) (P : ℤ) ∧
          Int.ediv ((L : ℤ) * zmodSval P (r.1 * x)) (P : ℤ) < 4 := by
        have hPposZ : (0 : ℤ) < (P : ℤ) := by exact_mod_cast NeZero.pos P
        have hlo : -4 * (P : ℤ) ≤ (L : ℤ) * zmodSval P (r.1 * x) := (abs_lt.mp hL_int).1.le
        have hhi : (L : ℤ) * zmodSval P (r.1 * x) < 4 * (P : ℤ) := (abs_lt.mp hL_int).2
        constructor
        · exact (Int.le_ediv_iff_mul_le hPposZ).mpr hlo
        · exact (Int.ediv_lt_iff_lt_mul hPposZ).mpr hhi
      exact Finset.mem_Ico.mpr hdiv_bounds
    let used : Finset (Γ → ℤ) := (W i).image bkt
    have hused_sub : used ⊆ cod := by
      intro f hf
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hf
      exact hbkt_mem x hx
    have hpick : ∀ f ∈ used, ∃ t ∈ W i, bkt t = f := fun f hf => Finset.mem_image.mp hf
    let pick : (Γ → ℤ) → ZMod P := fun f =>
      if hf : f ∈ used then Classical.choose (hpick f hf) else 0
    let T : Finset (ZMod P) := used.image pick
    refine ⟨T, ?_, ?_, ?_⟩
    · intro t ht
      obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ht
      simp only [pick, dif_pos hf]
      exact (Classical.choose_spec (hpick f hf)).1
    · calc T.card ≤ used.card := Finset.card_image_le
        _ ≤ cod.card := Finset.card_le_card hused_sub
        _ = 8 ^ Γ.card := hcod_card
    · intro x hx
      have hfx : bkt x ∈ used := Finset.mem_image_of_mem bkt hx
      let t := pick (bkt x)
      have htT : t ∈ T := Finset.mem_image_of_mem pick hfx
      have hbt : bkt t = bkt x := by
        simp only [t, pick, dif_pos hfx]
        exact (Classical.choose_spec (hpick (bkt x) hfx)).2
      have hdiff_mem : x - t ∈ W (i + 2) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun r hr => ?_⟩
        have hbe := congrFun hbt ⟨r, hr⟩
        dsimp only [bkt] at hbe
        have hPposZ : (0 : ℤ) < (P : ℤ) := by exact_mod_cast NeZero.pos P
        have h1 := Int.emod_add_mul_ediv ((L : ℤ) * zmodSval P (r * t)) (P : ℤ)
        have h2 := Int.emod_add_mul_ediv ((L : ℤ) * zmodSval P (r * x)) (P : ℤ)
        have hm10 := Int.emod_nonneg ((L : ℤ) * zmodSval P (r * t)) hPposZ.ne'
        have hm20 := Int.emod_nonneg ((L : ℤ) * zmodSval P (r * x)) hPposZ.ne'
        have hm1 := Int.emod_lt_of_pos ((L : ℤ) * zmodSval P (r * t)) hPposZ
        have hm2 := Int.emod_lt_of_pos ((L : ℤ) * zmodSval P (r * x)) hPposZ
        rw [hbe] at h1
        have hdiff_Z : |(L : ℤ) * (zmodSval P (r * x) - zmodSval P (r * t))| < (P : ℤ) := by
          have : (L : ℤ) * (zmodSval P (r * x) - zmodSval P (r * t)) =
              (L : ℤ) * zmodSval P (r * x) - (L : ℤ) * zmodSval P (r * t) := by ring
          rw [this, abs_lt]; omega
        have hcast : r * (x - t) = ((zmodSval P (r * x) - zmodSval P (r * t) : ℤ) : ZMod P) := by
          rw [mul_sub, Int.cast_sub, zmodSval_cast, zmodSval_cast]
        have hle := zmodSval_abs_le_of_cast (P := P) (zmodSval P (r * x) - zmodSval P (r * t))
        rw [← hcast] at hle
        rw [zmodDist_eq_sval]
        have hL_eq : (16 * (2 : ℝ) ^ (i + 2)) = (L : ℝ) := by dsimp [L]; push_cast; ring
        rw [hL_eq, div_lt_div_iff₀ hP_pos (by positivity)]
        have hLposZ : (0 : ℤ) ≤ (L : ℤ) := Nat.cast_nonneg _
        have hle2 : |zmodSval P (r * (x - t))| * (L : ℤ) < (P : ℤ) := by
          rw [abs_mul, abs_of_nonneg hLposZ] at hdiff_Z
          nlinarith
        have hle2R : (|zmodSval P (r * (x - t))| : ℝ) * (L : ℝ) < (P : ℝ) := by exact_mod_cast hle2
        linarith
      exact Finset.mem_add.mpr ⟨t, htT, x - t, hdiff_mem, by abel⟩

/- ### Module 4: Finite Fourier on `ZMod M`, `lem_inv`, `lem_bohr`, `lem_pars`, `lem_increment` -/

private noncomputable def fourierFin (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) (r : ZMod M) : ℂ :=
  ∑ x ∈ S, f x * zmodChar M r (-(x : ZMod M))

private noncomputable def unifHat (M : ℕ) (Z : SymNbhd) (r : ZMod M) : ℂ :=
  fourierFin M Z.set (fun x => ((unifMeas Z.set x : ℝ) : ℂ)) r

private lemma norm_unifHat_le_one (M : ℕ) (Z : SymNbhd) (r : ZMod M) :
    ‖unifHat M Z r‖ ≤ 1 := by
  unfold unifHat fourierFin
  calc ‖∑ x ∈ Z.set, ((unifMeas Z.set x : ℝ) : ℂ) * zmodChar M r (-(x : ZMod M))‖
      ≤ ∑ x ∈ Z.set, ‖((unifMeas Z.set x : ℝ) : ℂ) * zmodChar M r (-(x : ZMod M))‖ :=
        norm_sum_le _ _
    _ = ∑ x ∈ Z.set, unifMeas Z.set x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (unifMeas_nonneg _ _),
          zmodChar_norm, mul_one]
    _ = 1 := sum_unifMeas Z.set Z.nonempty

private lemma unifHat_zero (M : ℕ) (Z : SymNbhd) : unifHat M Z 0 = 1 := by
  unfold unifHat fourierFin
  simp only [zmodChar_zero_left, mul_one]
  have h := sum_unifMeas Z.set Z.nonempty
  have hC := congrArg Complex.ofReal h
  simpa [Complex.ofReal_sum] using hC

private lemma plancherel_fin {M : ℕ} [NeZero M] (S : Finset ℤ) (f : ℤ → ℂ)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, |x - y| < (M : ℤ)) :
    (∑ r : ZMod M, ‖fourierFin M S f r‖ ^ 2) = (M : ℝ) * ∑ x ∈ S, ‖f x‖ ^ 2 := by
  have hC : (∑ r : ZMod M, ((‖fourierFin M S f r‖ ^ 2 : ℝ) : ℂ)) =
      (M : ℂ) * ∑ x ∈ S, ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    have hterm : ∀ r : ZMod M, ((‖fourierFin M S f r‖ ^ 2 : ℝ) : ℂ) =
        ∑ x ∈ S, ∑ y ∈ S, (f x * starRingEnd ℂ (f y)) * zmodChar M r (((y - x : ℤ) : ZMod M)) := by
      intro r
      have hsq : ((‖fourierFin M S f r‖ ^ 2 : ℝ) : ℂ) =
          fourierFin M S f r * starRingEnd ℂ (fourierFin M S f r) := by
        rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
      rw [hsq]
      unfold fourierFin
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [map_mul, ← zmodChar_neg, neg_neg]
      have hmul : (f x * zmodChar M r (-(x : ZMod M))) *
          (starRingEnd ℂ (f y) * zmodChar M r (y : ZMod M)) =
          (f x * starRingEnd ℂ (f y)) * (zmodChar M r (y : ZMod M) * zmodChar M r (-(x : ZMod M))) := by
        ring
      rw [hmul, ← zmodChar_add]
      congr 2; push_cast; ring
    simp_rw [hterm]
    rw [Finset.sum_comm]
    calc ∑ x ∈ S, ∑ r : ZMod M, ∑ y ∈ S, (f x * starRingEnd ℂ (f y)) * zmodChar M r (((y - x : ℤ) : ZMod M))
        = ∑ x ∈ S, ∑ y ∈ S, (f x * starRingEnd ℂ (f y)) * ∑ r : ZMod M, zmodChar M r (((y - x : ℤ) : ZMod M)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [← Finset.mul_sum]
      _ = ∑ x ∈ S, ∑ y ∈ S, (f x * starRingEnd ℂ (f y)) * (if ((y - x : ℤ) : ZMod M) = 0 then (M : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          congr 1
          simp_rw [zmodChar_comm M _ ((y - x : ℤ) : ZMod M)]
          exact sum_zmodChar M _
      _ = ∑ x ∈ S, (M : ℂ) * ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          have hiff : ∀ y ∈ S, (((y - x : ℤ) : ZMod M) = 0 ↔ y = x) := by
            intro y hy
            constructor
            · intro h0
              obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (y - x) M).mp h0
              have hlt := hdiam y hy x hx
              have hk0 : k = 0 := by
                by_contra hkne
                have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hkne
                have hMpos : (0 : ℤ) < (M : ℤ) := by exact_mod_cast NeZero.pos M
                have : (M : ℤ) ≤ |y - x| := by
                  rw [hk, abs_mul, abs_of_pos hMpos]; nlinarith
                omega
              have : y - x = 0 := by simp [hk, hk0]
              omega
            · intro heq; subst heq; simp
          have hsum_y : ∑ y ∈ S, (f x * starRingEnd ℂ (f y)) * (if ((y - x : ℤ) : ZMod M) = 0 then (M : ℂ) else 0) =
              ∑ y ∈ S, if y = x then (f x * starRingEnd ℂ (f y)) * (M : ℂ) else 0 := by
            refine Finset.sum_congr rfl fun y hy => ?_
            by_cases hyx : y = x
            · rw [if_pos ((hiff y hy).mpr hyx), if_pos hyx]
            · rw [if_neg (mt (hiff y hy).mp hyx), if_neg hyx, mul_zero]
          rw [hsum_y, Finset.sum_ite_eq' S x, if_pos hx]
          rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj, mul_comm]
      _ = (M : ℂ) * ∑ x ∈ S, ((‖f x‖ ^ 2 : ℝ) : ℂ) := by rw [← Finset.mul_sum]
  have hre := congrArg Complex.re hC
  rw [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, Complex.re_sum] at hre
  simpa only [Complex.ofReal_re] using hre

private noncomputable def convZ (S2 : Finset ℤ) (f g : ℤ → ℝ) (x : ℤ) : ℝ :=
  ∑ y ∈ S2, f (x - y) * g y

private lemma fourierFin_convZ {M : ℕ} [NeZero M] (S1 S2 : Finset ℤ) (f g : ℤ → ℝ)
    (hf : ∀ x, x ∉ S1 → f x = 0) (r : ZMod M) :
    fourierFin M (S1 + S2) (fun x => ((convZ S2 f g x : ℝ) : ℂ)) r =
    fourierFin M S1 (fun x => ((f x : ℝ) : ℂ)) r * fourierFin M S2 (fun y => ((g y : ℝ) : ℂ)) r := by
  unfold fourierFin convZ
  simp only [Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.sum_mul]
  calc ∑ x ∈ S1 + S2, (∑ y ∈ S2, ((f (x - y) : ℝ) : ℂ) * ((g y : ℝ) : ℂ)) * zmodChar M r (-(x : ZMod M))
      = ∑ y ∈ S2, ∑ x ∈ S1 + S2, (((f (x - y) : ℝ) : ℂ) * ((g y : ℝ) : ℂ)) * zmodChar M r (-(x : ZMod M)) := by
        simp_rw [Finset.sum_mul]
        exact Finset.sum_comm
    _ = ∑ y ∈ S2, ∑ u ∈ S1, (((f u : ℝ) : ℂ) * ((g y : ℝ) : ℂ)) * zmodChar M r (-((u + y : ℤ) : ZMod M)) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        have hsub : S1.image (· + y) ⊆ S1 + S2 := by
          intro x hx
          obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
          exact Finset.add_mem_add hu hy
        rw [← Finset.sum_subset hsub]
        · rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
          refine Finset.sum_congr rfl fun u _ => by simp [add_sub_cancel_right]
        · intro x _ hxnot
          have hnotS1 : x - y ∉ S1 := fun h =>
            hxnot (Finset.mem_image.mpr ⟨x - y, h, sub_add_cancel x y⟩)
          simp [hf (x - y) hnotS1]
    _ = ∑ u ∈ S1, ((f u : ℝ) : ℂ) * zmodChar M r (-(u : ZMod M)) *
          ∑ y ∈ S2, ((g y : ℝ) : ℂ) * zmodChar M r (-(y : ZMod M)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        have hch : zmodChar M r (-((u + y : ℤ) : ZMod M)) =
            zmodChar M r (-(u : ZMod M)) * zmodChar M r (-(y : ZMod M)) := by
          rw [← zmodChar_add]; congr 1; push_cast; ring
        rw [hch]; ring

private lemma lem_inv {M : ℕ} [NeZero M] {τ κ : ℝ} {Z W : SymNbhd}
    (hτ : 0 ≤ τ) (hκ : 0 < κ) (hZW : IsClosedPair τ Z W)
    {r : ZMod M} (hr : κ < ‖unifHat M Z r‖) :
    ∀ w ∈ W.set, ‖zmodChar M r (w : ZMod M) - 1‖ ≤ 2 * τ / κ := by
  intro w hw
  let U : Finset ℤ := Z.set ∪ Z.set.image (· + w)
  have hshift : (zmodChar M r (-(w : ZMod M)) - 1) * unifHat M Z r =
      ∑ x ∈ U, (((unifMeas Z.set (x - w) - unifMeas Z.set x : ℝ) : ℂ)) * zmodChar M r (-(x : ZMod M)) := by
    have h1 : zmodChar M r (-(w : ZMod M)) * unifHat M Z r =
        ∑ x ∈ U, ((unifMeas Z.set (x - w) : ℝ) : ℂ) * zmodChar M r (-(x : ZMod M)) := by
      unfold unifHat fourierFin
      rw [Finset.mul_sum]
      have hsub : Z.set.image (· + w) ⊆ U := Finset.subset_union_right
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [add_sub_cancel_right]
        have hch : zmodChar M r (-(w : ZMod M)) * zmodChar M r (-(y : ZMod M)) =
            zmodChar M r (-((y + w : ℤ) : ZMod M)) := by
          rw [← zmodChar_add]; congr 1; push_cast; ring
        calc zmodChar M r (-(w : ZMod M)) * (((unifMeas Z.set y : ℝ) : ℂ) * zmodChar M r (-(y : ZMod M)))
            = ((unifMeas Z.set y : ℝ) : ℂ) * (zmodChar M r (-(w : ZMod M)) * zmodChar M r (-(y : ZMod M))) := by ring
          _ = ((unifMeas Z.set y : ℝ) : ℂ) * zmodChar M r (-((y + w : ℤ) : ZMod M)) := by rw [hch]
      · intro x _ hxnot
        have hnot : x - w ∉ Z.set := fun h =>
          hxnot (Finset.mem_image.mpr ⟨x - w, h, sub_add_cancel x w⟩)
        simp [unifMeas, hnot]
    have h2 : unifHat M Z r =
        ∑ x ∈ U, ((unifMeas Z.set x : ℝ) : ℂ) * zmodChar M r (-(x : ZMod M)) := by
      unfold unifHat fourierFin
      have hsubL : Z.set ⊆ U := Finset.subset_union_left
      exact Finset.sum_subset hsubL fun x _ hxnot => by simp [unifMeas, hxnot]
    rw [sub_mul, one_mul, h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    push_cast; ring
  have hnorm_neg : ‖zmodChar M r (-(w : ZMod M)) - 1‖ = ‖zmodChar M r (w : ZMod M) - 1‖ := by
    rw [zmodChar_neg]
    have : starRingEnd ℂ (zmodChar M r (w : ZMod M) - 1) = starRingEnd ℂ (zmodChar M r (w : ZMod M)) - 1 := by
      simp
    rw [← this, Complex.norm_conj]
  have hbound : ‖zmodChar M r (w : ZMod M) - 1‖ * ‖unifHat M Z r‖ ≤ 2 * τ := by
    rw [← hnorm_neg, ← norm_mul, hshift]
    calc ‖∑ x ∈ U, (((unifMeas Z.set (x - w) - unifMeas Z.set x : ℝ) : ℂ)) * zmodChar M r (-(x : ZMod M))‖
        ≤ ∑ x ∈ U, ‖(((unifMeas Z.set (x - w) - unifMeas Z.set x : ℝ) : ℂ)) * zmodChar M r (-(x : ZMod M))‖ :=
          norm_sum_le _ _
      _ = ∑ x ∈ U, |unifMeas Z.set (x - w) - unifMeas Z.set x| := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, zmodChar_norm, mul_one]
      _ ≤ 2 * τ := isClosedPair_shift_tv hτ hZW hw U Finset.subset_union_left Finset.subset_union_right
  rw [le_div_iff₀ hκ]
  have h1 : ‖zmodChar M r (w : ZMod M) - 1‖ * κ ≤ ‖zmodChar M r (w : ZMod M) - 1‖ * ‖unifHat M Z r‖ :=
    mul_le_mul_of_nonneg_left hr.le (norm_nonneg _)
  exact h1.trans hbound

private lemma lem_bohr {M : ℕ} [NeZero M] (r : ZMod M) {ρ : ℝ} (hρ : 0 < ρ) :
    let m : ℕ := Nat.clog 2 (Nat.ceil (8 / ρ)) + 1
    ∃ B : Sys,
      B.HasDim 3 ∧
      covFlat (Set.univ : Set ℤ) (B.set 0) ≤ ((2 ^ (3 * (m + 1)) : ℕ) : ℕ∞) ∧
      ∀ x : ℤ, x ∈ B.set 0 → ‖zmodChar M r (x : ZMod M) - 1‖ < ρ := by
  classical
  intro m
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  let A : ℕ → Set (ZMod M) := fun i => {y : ZMod M | zmodDist M y < 1 / (2 : ℝ) ^ i}
  let ψ : ℤ →+ ZMod M :=
    { toFun := fun x => r * (x : ZMod M)
      map_zero' := by simp
      map_add' := fun a b => by push_cast; ring }
  let B' : Sys :=
    { set := fun i => ψ ⁻¹' (A i)
      zero_mem := fun i => by
        simp only [Set.mem_preimage, map_zero, A, Set.mem_ofPred_eq, zmodDist_zero]
        positivity
      neg_mem := fun i x hx => by
        simp only [Set.mem_preimage, map_neg, A, Set.mem_ofPred_eq, zmodDist_neg]
        exact hx
      add_subset := fun i x hx => by
        obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hx
        simp only [Set.mem_preimage, map_add, A, Set.mem_ofPred_eq]
        have htri : zmodDist M (ψ a + ψ b) ≤ zmodDist M (ψ a) + zmodDist M (ψ b) :=
          zmodDist_add_le M _ _
        have hhalf : 1 / (2 : ℝ) ^ (i + 1) + 1 / (2 : ℝ) ^ (i + 1) = 1 / (2 : ℝ) ^ i := by
          rw [pow_succ]; field_simp; ring
        have ha' : zmodDist M (ψ a) < 1 / (2 : ℝ) ^ (i + 1) := ha
        have hb' : zmodDist M (ψ b) < 1 / (2 : ℝ) ^ (i + 1) := hb
        linarith }
  have hB'_dim : B'.HasDim 3 := by
    intro i
    have hAsub : A (i + 2) - A (i + 2) ⊆ A (i + 1) := by
      intro y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.mp hy
      change zmodDist M (a - b) < 1 / (2 : ℝ) ^ (i + 1)
      have htri : zmodDist M (a - b) ≤ zmodDist M a + zmodDist M b := by
        rw [sub_eq_add_neg]; exact (zmodDist_add_le M a (-b)).trans (by rw [zmodDist_neg])
      have hhalf : 1 / (2 : ℝ) ^ (i + 2) + 1 / (2 : ℝ) ^ (i + 2) = 1 / (2 : ℝ) ^ (i + 1) := by
        rw [pow_succ]; field_simp; ring
      have ha' : zmodDist M a < 1 / (2 : ℝ) ^ (i + 2) := ha
      have hb' : zmodDist M b < 1 / (2 : ℝ) ^ (i + 2) := hb
      linarith
    have hcovA : covNum (A i) (A (i + 2)) ≤ ((8 : ℕ) : ℕ∞) := by
      let L : ℕ := 2 ^ (i + 2)
      let bkt : ZMod M → ℤ := fun y => ((L : ℤ) * zmodSval M y) / (M : ℤ)
      let Af : Finset (ZMod M) := Finset.univ.filter (fun y => y ∈ A i)
      let used : Finset ℤ := Af.image bkt
      have hused_sub : used ⊆ Finset.Ico (-4 : ℤ) 4 := by
        intro k hk
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hk
        have hyA : zmodDist M y < 1 / (2 : ℝ) ^ i := (Finset.mem_filter.mp hy).2
        rw [zmodDist_eq_sval] at hyA
        have hL_lt : (L : ℝ) * (|zmodSval M y| : ℝ) < 4 * (M : ℝ) := by
          have h1 : (|zmodSval M y| : ℝ) < (M : ℝ) / (2 : ℝ) ^ i := by
            rw [div_lt_iff₀ hM_pos] at hyA
            linarith [show (1 / (2 : ℝ) ^ i) * (M : ℝ) = (M : ℝ) / (2 : ℝ) ^ i by ring]
          have hL_eq : (L : ℝ) = 4 * (2 : ℝ) ^ i := by dsimp [L]; push_cast; ring
          rw [hL_eq]
          have hmul : (2 : ℝ) ^ i * (|zmodSval M y| : ℝ) < (M : ℝ) := by
            rwa [lt_div_iff₀' (by positivity : (0 : ℝ) < (2 : ℝ) ^ i)] at h1
          linarith
        have hL_int : |(L : ℤ) * zmodSval M y| < 4 * (M : ℤ) := by
          have h1 : ((L : ℤ) * |zmodSval M y| : ℤ) < 4 * (M : ℤ) := by exact_mod_cast hL_lt
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]; exact h1
        have hMposZ : (0 : ℤ) < (M : ℤ) := by exact_mod_cast NeZero.pos M
        exact Finset.mem_Ico.mpr
          ⟨(Int.le_ediv_iff_mul_le hMposZ).mpr (abs_lt.mp hL_int).1.le,
           (Int.ediv_lt_iff_lt_mul hMposZ).mpr (abs_lt.mp hL_int).2⟩
      have hpick : ∀ k ∈ used, ∃ t ∈ Af, bkt t = k := fun k hk => Finset.mem_image.mp hk
      let pick : ℤ → ZMod M := fun k => if hk : k ∈ used then Classical.choose (hpick k hk) else 0
      let T : Finset (ZMod M) := used.image pick
      have hTcard : T.card ≤ 8 := by
        calc T.card ≤ used.card := Finset.card_image_le
          _ ≤ (Finset.Ico (-4 : ℤ) 4).card := Finset.card_le_card hused_sub
          _ = 8 := by rw [Int.card_Ico]; decide
      have hTcov : A i ⊆ (T : Set (ZMod M)) + A (i + 2) := by
        intro y hy
        have hyAf : y ∈ Af := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
        have hky : bkt y ∈ used := Finset.mem_image_of_mem bkt hyAf
        let t := pick (bkt y)
        have htT : t ∈ T := Finset.mem_image_of_mem pick hky
        have hbt : bkt t = bkt y := by
          simp only [t, pick, dif_pos hky]
          exact (Classical.choose_spec (hpick (bkt y) hky)).2
        have hdiff : y - t ∈ A (i + 2) := by
          change zmodDist M (y - t) < 1 / (2 : ℝ) ^ (i + 2)
          have hMposZ : (0 : ℤ) < (M : ℤ) := by exact_mod_cast NeZero.pos M
          have h1 := Int.emod_add_mul_ediv ((L : ℤ) * zmodSval M t) (M : ℤ)
          have h2 := Int.emod_add_mul_ediv ((L : ℤ) * zmodSval M y) (M : ℤ)
          have hm10 := Int.emod_nonneg ((L : ℤ) * zmodSval M t) hMposZ.ne'
          have hm20 := Int.emod_nonneg ((L : ℤ) * zmodSval M y) hMposZ.ne'
          have hm1 := Int.emod_lt_of_pos ((L : ℤ) * zmodSval M t) hMposZ
          have hm2 := Int.emod_lt_of_pos ((L : ℤ) * zmodSval M y) hMposZ
          dsimp only [bkt] at hbt
          rw [hbt] at h1
          have hdiff_Z : |(L : ℤ) * (zmodSval M y - zmodSval M t)| < (M : ℤ) := by
            have : (L : ℤ) * (zmodSval M y - zmodSval M t) =
                (L : ℤ) * zmodSval M y - (L : ℤ) * zmodSval M t := by ring
            rw [this, abs_lt]; omega
          have hcast : y - t = ((zmodSval M y - zmodSval M t : ℤ) : ZMod M) := by
            rw [Int.cast_sub, zmodSval_cast, zmodSval_cast]
          have hle := zmodSval_abs_le_of_cast (P := M) (zmodSval M y - zmodSval M t)
          rw [← hcast] at hle
          rw [zmodDist_eq_sval]
          have hL_eq : ((2 : ℝ) ^ (i + 2)) = (L : ℝ) := by dsimp [L]; push_cast; rfl
          rw [hL_eq, div_lt_div_iff₀ hM_pos (by positivity)]
          have hle2 : |zmodSval M (y - t)| * (L : ℤ) < (M : ℤ) := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)] at hdiff_Z; nlinarith
          have hle2R : (|zmodSval M (y - t)| : ℝ) * (L : ℝ) < (M : ℝ) := by exact_mod_cast hle2
          linarith
        exact Set.mem_add.mpr ⟨t, Finset.mem_coe.mpr htT, y - t, hdiff, by abel⟩
      exact (covNum_le_of_cover T hTcov).trans (ENat.natCast_le_natCast.mpr hTcard)
    calc covFlat (B'.set i) (B'.set (i + 1))
        ≤ covFlat (A i) (A (i + 1)) := covFlat_preimage ψ (A i) (A (i + 1))
      _ ≤ covFlat (A i) (A (i + 2) - A (i + 2)) := covFlat_mono Set.Subset.rfl hAsub
      _ ≤ covNum (A i) (A (i + 2)) := covFlat_le_covNum _ _
      _ ≤ ((2 ^ 3 : ℕ) : ℕ∞) := hcovA
  have hB'_0 : B'.set 0 = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true, B', Set.mem_preimage, ψ, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, A, Set.mem_ofPred_eq]
    unfold zmodDist
    simp only [pow_zero, div_one]
    rw [div_lt_one hM_pos]
    have hlt : (r * (x : ZMod M)).val < M := ZMod.val_lt _
    have : min (r * (x : ZMod M)).val (M - (r * (x : ZMod M)).val) < M :=
      lt_of_le_of_lt (min_le_left _ _) hlt
    exact_mod_cast this
  let B : Sys := B'.dilate m
  refine ⟨B, B'.dilate_hasDim m hB'_dim, ?_, ?_⟩
  · have hcov0 : covFlat (Set.univ : Set ℤ) (B'.set 0) ≤ 1 := by
      rw [hB'_0]
      have hu := Sys.univ_hasDim 0
      dsimp only [Sys.univ] at hu
      simpa using hu
    calc covFlat (Set.univ : Set ℤ) (B.set 0)
        ≤ covFlat (Set.univ : Set ℤ) (B'.set 0) * ((2 ^ ((m + 1) * 3) : ℕ) : ℕ∞) :=
          B'.dilate_covFlat hB'_dim m Set.univ
      _ ≤ 1 * ((2 ^ ((m + 1) * 3) : ℕ) : ℕ∞) := mul_le_mul' hcov0 le_rfl
      _ = ((2 ^ (3 * (m + 1)) : ℕ) : ℕ∞) := by rw [one_mul, mul_comm]
  · intro x hx
    have hx' : zmodDist M (r * (x : ZMod M)) < 1 / (2 : ℝ) ^ m := by
      simpa [B, Sys.dilate, B', ψ, A] using hx
    have h2m : (8 : ℝ) / ρ ≤ (2 : ℝ) ^ m := by
      have hceil : (8 : ℝ) / ρ ≤ (Nat.ceil (8 / ρ) : ℝ) := Nat.le_ceil _
      have hclog : Nat.ceil (8 / ρ) ≤ 2 ^ Nat.clog 2 (Nat.ceil (8 / ρ)) :=
        Nat.le_pow_clog (by norm_num) _
      have hclog2 : 2 ^ Nat.clog 2 (Nat.ceil (8 / ρ)) ≤ 2 ^ m :=
        Nat.pow_le_pow_right (by norm_num) (by dsimp [m]; omega)
      have hR : (Nat.ceil (8 / ρ) : ℝ) ≤ (2 : ℝ) ^ m := by exact_mod_cast hclog.trans hclog2
      exact hceil.trans hR
    have hlt_rho : 8 * zmodDist M (r * (x : ZMod M)) < ρ := by
      have h1 : 8 * (1 / (2 : ℝ) ^ m) ≤ ρ := by
        rw [mul_one_div, div_le_iff₀ (by positivity)]
        have : 8 ≤ ρ * (2 : ℝ) ^ m := (div_le_iff₀ hρ).mp h2m |>.trans_eq (mul_comm _ _)
        linarith
      linarith
    exact (zmodChar_sub_one_le M r (x : ZMod M)).trans_lt hlt_rho

private lemma sys_inter_finset {ι : Type} (s : Finset ι) (F : ι → Sys)
    (d0 : ℕ) (D0 : ℕ)
    (hd : ∀ i ∈ s, (F i).HasDim d0)
    (hD : ∀ i ∈ s, covFlat (Set.univ : Set ℤ) ((F i).set 0) ≤ (D0 : ℕ∞)) :
    ∃ B : Sys,
      B.HasDim (s.card * d0) ∧
      covFlat (Set.univ : Set ℤ) (B.set 0) ≤ ((D0 ^ s.card : ℕ) : ℕ∞) ∧
      ∀ i ∈ s, B.set 0 ⊆ (F i).set 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Sys.univ, by simpa using Sys.univ_hasDim, ?_, by simp⟩
    have hu := Sys.univ_hasDim 0
    simpa [Sys.univ] using hu
  | @insert a s ha ih =>
    obtain ⟨B0, hB0d, hB0D, hB0sub⟩ := ih
      (fun i hi => hd i (Finset.mem_insert_of_mem hi))
      (fun i hi => hD i (Finset.mem_insert_of_mem hi))
    refine ⟨(F a).inter B0, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem ha, add_mul, one_mul, add_comm]
      exact Sys.inter_hasDim (hd a (Finset.mem_insert_self a s)) hB0d
    · rw [Finset.card_insert_of_notMem ha, pow_succ', Nat.cast_mul]
      exact ((F a).inter_covFlat B0 Set.univ).trans
        (mul_le_mul' (hD a (Finset.mem_insert_self a s)) hB0D)
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact Set.inter_subset_left
      · exact Set.inter_subset_right.trans (hB0sub i hi')

private lemma lem_pars {M : ℕ} [NeZero M] {τ ε δ : ℝ} {Z W : SymNbhd}
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hδ : 0 < δ)
    (hZW : IsClosedPair τ Z W)
    (f : ℤ → ℝ) (hf : ∀ x ∈ Z.set, |f x| ≤ 1) :
    let m : ℕ := Nat.clog 2 (Nat.ceil (8 / δ)) + 1
    let N : ℕ := Nat.floor (2 / ε ^ 2)
    ∃ B : Sys,
      B.HasDim (3 * N) ∧
      covFlat (Set.univ : Set ℤ) (B.set 0) ≤ ((2 ^ (3 * (m + 1) * N) : ℕ) : ℕ∞) ∧
      ∀ r : ZMod M,
        ε < ‖fourierFin M Z.set (fun x => ((f x * unifMeas Z.set x : ℝ) : ℂ)) r‖ →
        ∀ x : ℤ, x ∈ B.set 0 → x ∈ W.set →
          ‖zmodChar M r (x : ZMod M) - 1‖ ≤ 4 * τ / ε ^ 2 + δ := by
  classical
  intro m N
  let ghat : ZMod M → ℂ := fun r =>
    fourierFin M Z.set (fun x => ((f x * unifMeas Z.set x : ℝ) : ℂ)) r
  let Spec : Finset (ZMod M) := Finset.univ.filter (fun r => ε < ‖ghat r‖)
  let η0 : ℝ := 4 * τ / ε ^ 2
  let Ann : ZMod M → Prop := fun r => ∀ w ∈ W.set, ‖zmodChar M r (w : ZMod M) - 1‖ ≤ η0
  have hAnn_symm : ∀ r : ZMod M, Ann (-r) ↔ Ann r := by
    intro r
    constructor <;> intro h w hw
    · have := h w hw
      rw [show zmodChar M (-r) (w : ZMod M) = zmodChar M r (-(w : ZMod M)) by simp [zmodChar],
        zmodChar_neg] at this
      have heq : starRingEnd ℂ (zmodChar M r (w : ZMod M) - 1) =
          starRingEnd ℂ (zmodChar M r (w : ZMod M)) - 1 := by simp
      rwa [← heq, Complex.norm_conj] at this
    · have := h w hw
      rw [show zmodChar M (-r) (w : ZMod M) = zmodChar M r (-(w : ZMod M)) by simp [zmodChar],
        zmodChar_neg]
      have heq : starRingEnd ℂ (zmodChar M r (w : ZMod M) - 1) =
          starRingEnd ℂ (zmodChar M r (w : ZMod M)) - 1 := by simp
      rwa [← heq, Complex.norm_conj]
  let Sep : Finset (ZMod M) → Prop := fun L =>
    ∀ r1 ∈ L, ∀ r2 ∈ L, r1 ≠ r2 → ¬ Ann (r1 - r2)
  let Cands : Finset (Finset (ZMod M)) := Spec.powerset.filter Sep
  have hCands_ne : Cands.Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, fun _ h => (Finset.notMem_empty _ h).elim⟩⟩
  obtain ⟨Λ, hΛmax⟩ := Cands.exists_maximal hCands_ne
  obtain ⟨hΛ_pow, hΛ_sep⟩ := Finset.mem_filter.mp hΛmax.1
  have hΛ_sub : Λ ⊆ Spec := Finset.mem_powerset.mp hΛ_pow
  have hΛ_cov : ∀ r ∈ Spec, ∃ l ∈ Λ, Ann (r - l) := by
    intro r hr
    by_cases hrL : r ∈ Λ
    · refine ⟨r, hrL, fun w _ => ?_⟩
      rw [sub_self, zmodChar_zero_left, sub_self, norm_zero]
      dsimp only [η0]; positivity
    · by_contra hno
      push Not at hno
      have hsep_ins : Sep (insert r Λ) := by
        intro r1 h1 r2 h2 hne
        rcases Finset.mem_insert.mp h1 with rfl | h1' <;>
        rcases Finset.mem_insert.mp h2 with rfl | h2'
        · exact (hne rfl).elim
        · exact hno r2 h2'
        · intro hAnn; exact hno r1 h1' ((hAnn_symm _).mp (by simpa [neg_sub] using hAnn))
        · exact hΛ_sep r1 h1' r2 h2' hne
      have hins_mem : insert r Λ ∈ Cands :=
        Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset_iff.mpr ⟨hr, hΛ_sub⟩), hsep_ins⟩
      exact hΛmax.not_gt hins_mem (Finset.ssubset_insert hrL)
  have hΛ_card_le : (Λ.card : ℝ) ≤ 2 / ε ^ 2 := by
    by_cases hΛ0 : Λ.card = 0
    · simp [hΛ0]; positivity
    have hΛ_pos : (0 : ℝ) < (Λ.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hΛ0)
    let σ : ZMod M → ℂ := fun l => starRingEnd ℂ (ghat l) / ((‖ghat l‖ : ℝ) : ℂ)
    have hσ_norm : ∀ l ∈ Λ, ‖σ l‖ = 1 := by
      intro l hl
      have hpos : 0 < ‖ghat l‖ := hε.trans (Finset.mem_filter.mp (hΛ_sub hl)).2
      simp only [σ, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hpos, div_self hpos.ne']
    have hσ_mul : ∀ l ∈ Λ, σ l * ghat l = ((‖ghat l‖ : ℝ) : ℂ) := by
      intro l hl
      have hpos : 0 < ‖ghat l‖ := hε.trans (Finset.mem_filter.mp (hΛ_sub hl)).2
      have hposC : ((‖ghat l‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
      dsimp only [σ]
      rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, sq]
      push_cast
      exact mul_div_cancel_right₀ _ hposC
    let Fsum : ℤ → ℂ := fun x => ∑ l ∈ Λ, σ l * zmodChar M l (-(x : ZMod M))
    have hinner : ((∑ l ∈ Λ, ‖ghat l‖ : ℝ) : ℂ) =
        ∑ x ∈ Z.set, ((f x * unifMeas Z.set x : ℝ) : ℂ) * Fsum x := by
      rw [Complex.ofReal_sum]
      calc ∑ l ∈ Λ, ((‖ghat l‖ : ℝ) : ℂ)
          = ∑ l ∈ Λ, σ l * ghat l := Finset.sum_congr rfl fun l hl => (hσ_mul l hl).symm
        _ = ∑ l ∈ Λ, ∑ x ∈ Z.set, ((f x * unifMeas Z.set x : ℝ) : ℂ) * (σ l * zmodChar M l (-(x : ZMod M))) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            unfold ghat fourierFin
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => by ring
        _ = ∑ x ∈ Z.set, ((f x * unifMeas Z.set x : ℝ) : ℂ) * Fsum x := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x _ => ?_
            dsimp only [Fsum]; rw [Finset.mul_sum]
    have hcs_step : (∑ l ∈ Λ, ‖ghat l‖) ^ 2 ≤ ∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖ ^ 2 := by
      have htri : ∑ l ∈ Λ, ‖ghat l‖ ≤ ∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖ := by
        have h1 : ∑ l ∈ Λ, ‖ghat l‖ = ‖((∑ l ∈ Λ, ‖ghat l‖ : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        rw [h1, hinner]
        calc ‖∑ x ∈ Z.set, ((f x * unifMeas Z.set x : ℝ) : ℂ) * Fsum x‖
            ≤ ∑ x ∈ Z.set, ‖((f x * unifMeas Z.set x : ℝ) : ℂ) * Fsum x‖ := norm_sum_le _ _
          _ ≤ ∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖ := by
              refine Finset.sum_le_sum fun x hx => ?_
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
                abs_of_nonneg (unifMeas_nonneg _ _)]
              have hfx : |f x| ≤ 1 := hf x hx
              calc |f x| * unifMeas Z.set x * ‖Fsum x‖
                  ≤ 1 * unifMeas Z.set x * ‖Fsum x‖ :=
                    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfx (unifMeas_nonneg _ _)) (norm_nonneg _)
                _ = unifMeas Z.set x * ‖Fsum x‖ := by ring
      have hwcs : (∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖) ^ 2 ≤
          ∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖ ^ 2 := by
        have hnn : 0 ≤ ∑ x ∈ Z.set, ∑ y ∈ Z.set,
            unifMeas Z.set x * unifMeas Z.set y * (‖Fsum x‖ - ‖Fsum y‖) ^ 2 :=
          Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ =>
            mul_nonneg (mul_nonneg (unifMeas_nonneg _ _) (unifMeas_nonneg _ _)) (sq_nonneg _)
        have hexp : ∑ x ∈ Z.set, ∑ y ∈ Z.set,
            unifMeas Z.set x * unifMeas Z.set y * (‖Fsum x‖ - ‖Fsum y‖) ^ 2 =
            2 * (∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖ ^ 2) -
            2 * (∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖) ^ 2 := by
          have hsq : ∀ x y : ℤ, unifMeas Z.set x * unifMeas Z.set y * (‖Fsum x‖ - ‖Fsum y‖) ^ 2 =
              (unifMeas Z.set x * ‖Fsum x‖ ^ 2) * unifMeas Z.set y -
              2 * (unifMeas Z.set x * ‖Fsum x‖) * (unifMeas Z.set y * ‖Fsum y‖) +
              unifMeas Z.set x * (unifMeas Z.set y * ‖Fsum y‖ ^ 2) := fun _ _ => by ring
          simp_rw [hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
          have hs1 : ∑ x ∈ Z.set, ∑ y ∈ Z.set, (unifMeas Z.set x * ‖Fsum x‖ ^ 2) * unifMeas Z.set y =
              ∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖ ^ 2 := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [← Finset.mul_sum, sum_unifMeas Z.set Z.nonempty, mul_one]
          have hs3 : ∑ x ∈ Z.set, ∑ y ∈ Z.set, unifMeas Z.set x * (unifMeas Z.set y * ‖Fsum y‖ ^ 2) =
              ∑ y ∈ Z.set, unifMeas Z.set y * ‖Fsum y‖ ^ 2 := by
            simp_rw [← Finset.mul_sum, ← Finset.sum_mul, sum_unifMeas Z.set Z.nonempty, one_mul]
          have hs2 : ∑ x ∈ Z.set, ∑ y ∈ Z.set, 2 * (unifMeas Z.set x * ‖Fsum x‖) * (unifMeas Z.set y * ‖Fsum y‖) =
              2 * (∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖) ^ 2 := by
            have : ∑ x ∈ Z.set, ∑ y ∈ Z.set, 2 * (unifMeas Z.set x * ‖Fsum x‖) * (unifMeas Z.set y * ‖Fsum y‖) =
                2 * ∑ x ∈ Z.set, (unifMeas Z.set x * ‖Fsum x‖) * ∑ y ∈ Z.set, (unifMeas Z.set y * ‖Fsum y‖) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => by ring
            rw [this, ← Finset.sum_mul, sq]
          rw [hs1, hs2, hs3]; ring
        linarith
      exact (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) htri 2).trans hwcs
    have hF_expand : ((∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖ ^ 2 : ℝ) : ℂ) =
        ∑ l1 ∈ Λ, ∑ l2 ∈ Λ, (σ l1 * starRingEnd ℂ (σ l2)) * unifHat M Z (l1 - l2) := by
      rw [Complex.ofReal_sum]
      have hterm : ∀ x ∈ Z.set, ((unifMeas Z.set x * ‖Fsum x‖ ^ 2 : ℝ) : ℂ) =
          ∑ l1 ∈ Λ, ∑ l2 ∈ Λ, (σ l1 * starRingEnd ℂ (σ l2)) *
            (((unifMeas Z.set x : ℝ) : ℂ) * zmodChar M (l1 - l2) (-(x : ZMod M))) := by
        intro x _
        rw [Complex.ofReal_mul]
        have hsq : ((‖Fsum x‖ ^ 2 : ℝ) : ℂ) = Fsum x * starRingEnd ℂ (Fsum x) := by
          rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
        rw [hsq]
        dsimp only [Fsum]
        rw [map_sum, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l1 _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l2 _ => ?_
        rw [map_mul, ← zmodChar_neg]
        have hch' : zmodChar M l1 (-(x : ZMod M)) * zmodChar M l2 (-(-(x : ZMod M))) =
            zmodChar M (l1 - l2) (-(x : ZMod M)) := by
          rw [neg_neg, zmodChar_comm M l1, zmodChar_comm M l2, zmodChar_comm M (l1 - l2)]
          have h2 : zmodChar M (x : ZMod M) l2 = zmodChar M (-(x : ZMod M)) (-l2) := by
            simp [zmodChar]
          rw [h2, ← zmodChar_add, sub_eq_add_neg]
        rw [← hch']; ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_comm]
      refine Finset.sum_congr rfl fun l1 _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l2 _ => ?_
      rw [← Finset.mul_sum]; rfl
    have hF_ub : ∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖ ^ 2 ≤
        (Λ.card : ℝ) + (ε ^ 2 / 2) * (Λ.card : ℝ) ^ 2 := by
      have h1 : ∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖ ^ 2 =
          ‖((∑ x ∈ Z.set, unifMeas Z.set x * ‖Fsum x‖ ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (unifMeas_nonneg _ _) (sq_nonneg _))]
      rw [h1, hF_expand]
      calc ‖∑ l1 ∈ Λ, ∑ l2 ∈ Λ, (σ l1 * starRingEnd ℂ (σ l2)) * unifHat M Z (l1 - l2)‖
          ≤ ∑ l1 ∈ Λ, ∑ l2 ∈ Λ, ‖(σ l1 * starRingEnd ℂ (σ l2)) * unifHat M Z (l1 - l2)‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
        _ ≤ ∑ l1 ∈ Λ, ∑ l2 ∈ Λ, (if l1 = l2 then (1 : ℝ) else ε ^ 2 / 2) := by
            refine Finset.sum_le_sum fun l1 hl1 => Finset.sum_le_sum fun l2 hl2 => ?_
            rw [norm_mul, norm_mul, hσ_norm l1 hl1, Complex.norm_conj, hσ_norm l2 hl2, mul_one, one_mul]
            by_cases heq : l1 = l2
            · rw [if_pos heq, heq, sub_self, unifHat_zero, norm_one]
            · rw [if_neg heq]
              by_contra hgt
              push Not at hgt
              have hAnn := lem_inv hτ (by positivity : 0 < ε ^ 2 / 2) hZW hgt
              have hηeq : 2 * τ / (ε ^ 2 / 2) = η0 := by dsimp only [η0]; field_simp; ring
              rw [hηeq] at hAnn
              exact hΛ_sep l1 hl1 l2 hl2 heq hAnn
        _ ≤ ∑ l1 ∈ Λ, ∑ l2 ∈ Λ, ((if l1 = l2 then (1 : ℝ) else 0) + ε ^ 2 / 2) := by
            refine Finset.sum_le_sum fun l1 _ => Finset.sum_le_sum fun l2 _ => ?_
            split_ifs <;> linarith [sq_nonneg ε]
        _ = (Λ.card : ℝ) + (ε ^ 2 / 2) * (Λ.card : ℝ) ^ 2 := by
            simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
            have hdiag : ∑ l1 ∈ Λ, ∑ l2 ∈ Λ, (if l1 = l2 then (1 : ℝ) else 0) = (Λ.card : ℝ) := by
              have : ∀ l1 ∈ Λ, ∑ l2 ∈ Λ, (if l1 = l2 then (1 : ℝ) else 0) = 1 := fun l1 hl1 => by
                have : ∀ l2 ∈ Λ, (if l1 = l2 then (1 : ℝ) else 0) = if l2 = l1 then 1 else 0 :=
                  fun l2 _ => by simp [eq_comm]
                rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' Λ l1, if_pos hl1]
              rw [Finset.sum_congr rfl this]; simp
            rw [hdiag]; ring
    have hlb : (Λ.card : ℝ) * ε ≤ ∑ l ∈ Λ, ‖ghat l‖ := by
      calc (Λ.card : ℝ) * ε = ∑ _l ∈ Λ, ε := by simp
        _ ≤ ∑ l ∈ Λ, ‖ghat l‖ := Finset.sum_le_sum fun l hl => (Finset.mem_filter.mp (hΛ_sub hl)).2.le
    have hsq_lb : ((Λ.card : ℝ) * ε) ^ 2 ≤ (Λ.card : ℝ) + (ε ^ 2 / 2) * (Λ.card : ℝ) ^ 2 :=
      (pow_le_pow_left₀ (by positivity) hlb 2).trans (hcs_step.trans hF_ub)
    rw [le_div_iff₀ (by positivity)]
    have : (Λ.card : ℝ) * ε ^ 2 * (Λ.card : ℝ) ≤ 2 * (Λ.card : ℝ) := by nlinarith
    exact le_of_mul_le_mul_right this hΛ_pos
  have hΛ_le_N : Λ.card ≤ N := Nat.le_floor hΛ_card_le
  have hbohr_all : ∀ l : ZMod M, ∃ B : Sys,
      B.HasDim 3 ∧
      covFlat (Set.univ : Set ℤ) (B.set 0) ≤ ((2 ^ (3 * (m + 1)) : ℕ) : ℕ∞) ∧
      ∀ x : ℤ, x ∈ B.set 0 → ‖zmodChar M l (x : ZMod M) - 1‖ < δ :=
    fun l => lem_bohr l hδ
  choose FB hFBd hFBD hFBann using hbohr_all
  obtain ⟨B, hBd, hBD, hBsub⟩ := sys_inter_finset Λ FB 3 (2 ^ (3 * (m + 1)))
    (fun l _ => hFBd l) (fun l _ => hFBD l)
  refine ⟨B, hBd.mono (by rw [mul_comm]; exact Nat.mul_le_mul_left 3 hΛ_le_N), ?_, ?_⟩
  · calc covFlat (Set.univ : Set ℤ) (B.set 0)
        ≤ (((2 ^ (3 * (m + 1))) ^ Λ.card : ℕ) : ℕ∞) := hBD
      _ = ((2 ^ (3 * (m + 1) * Λ.card) : ℕ) : ℕ∞) := by rw [← pow_mul]
      _ ≤ ((2 ^ (3 * (m + 1) * N) : ℕ) : ℕ∞) :=
          ENat.natCast_le_natCast.mpr (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hΛ_le_N))
  · intro r hr x hxB hxW
    have hrSpec : r ∈ Spec := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩
    obtain ⟨l, hlΛ, hAnn⟩ := hΛ_cov r hrSpec
    have h1 : ‖zmodChar M (r - l) (x : ZMod M) - 1‖ ≤ η0 := hAnn x hxW
    have h2 : ‖zmodChar M l (x : ZMod M) - 1‖ < δ := hFBann l x (hBsub l hlΛ hxB)
    have hprod : zmodChar M r (x : ZMod M) = zmodChar M (r - l) (x : ZMod M) * zmodChar M l (x : ZMod M) := by
      rw [zmodChar_comm M r, zmodChar_comm M (r - l), zmodChar_comm M l, ← zmodChar_add, sub_add_cancel]
    have htri : ‖zmodChar M r (x : ZMod M) - 1‖ ≤
        ‖zmodChar M (r - l) (x : ZMod M) - 1‖ + ‖zmodChar M l (x : ZMod M) - 1‖ := by
      rw [hprod]
      have hdecomp : zmodChar M (r - l) (x : ZMod M) * zmodChar M l (x : ZMod M) - 1 =
          (zmodChar M (r - l) (x : ZMod M) - 1) * zmodChar M l (x : ZMod M) + (zmodChar M l (x : ZMod M) - 1) := by
        ring
      rw [hdecomp]
      calc ‖(zmodChar M (r - l) (x : ZMod M) - 1) * zmodChar M l (x : ZMod M) + (zmodChar M l (x : ZMod M) - 1)‖
          ≤ ‖(zmodChar M (r - l) (x : ZMod M) - 1) * zmodChar M l (x : ZMod M)‖ + ‖zmodChar M l (x : ZMod M) - 1‖ :=
            norm_add_le _ _
        _ = ‖zmodChar M (r - l) (x : ZMod M) - 1‖ + ‖zmodChar M l (x : ZMod M) - 1‖ := by
            rw [norm_mul, zmodChar_norm, mul_one]
    linarith

private noncomputable def locDens (Z : SymNbhd) (A : Finset ℤ) : ℝ :=
  ((A ∩ Z.set).card : ℝ) / (Z.set.card : ℝ)

private lemma locDens_nonneg (Z : SymNbhd) (A : Finset ℤ) : 0 ≤ locDens Z A := by
  unfold locDens; positivity

private lemma locDens_le_one (Z : SymNbhd) (A : Finset ℤ) : locDens Z A ≤ 1 := by
  unfold locDens
  rw [div_le_one (Nat.cast_pos.mpr Z.card_pos)]
  exact_mod_cast Finset.card_le_card Finset.inter_subset_right

private noncomputable def convInd (S T : Finset ℤ) (U : SymNbhd) (x : ℤ) : ℝ :=
  convZ U.set (fun u => if u ∈ S then 1 else 0) (fun y => (if y ∈ T then 1 else 0) * unifMeas U.set y) x

private lemma convInd_nonneg (S T : Finset ℤ) (U : SymNbhd) (x : ℤ) : 0 ≤ convInd S T U x := by
  unfold convInd convZ
  dsimp only
  refine Finset.sum_nonneg fun y _ => mul_nonneg (by split_ifs <;> norm_num)
    (mul_nonneg (by split_ifs <;> norm_num) (unifMeas_nonneg _ _))

private lemma convInd_le_one (S T : Finset ℤ) (U : SymNbhd) (x : ℤ) : convInd S T U x ≤ 1 := by
  unfold convInd convZ
  calc ∑ y ∈ U.set, (if x - y ∈ S then (1 : ℝ) else 0) * ((if y ∈ T then 1 else 0) * unifMeas U.set y)
      ≤ ∑ y ∈ U.set, unifMeas U.set y := by
        refine Finset.sum_le_sum fun y _ => ?_
        have hu := unifMeas_nonneg U.set y
        split_ifs <;> linarith
    _ = 1 := sum_unifMeas U.set U.nonempty

private lemma lem_increment_stepA {A : Finset ℤ} {Z0 Z1 Z0m : SymNbhd} {τ α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hZ0m_sub : Z0m.set + Z1.set ⊆ Z0.set)
    (hZ0_inner_sdiff : ((Z0.set \ Z0m.set).card : ℝ) ≤ τ * (Z0.set.card : ℝ)) :
    let g : ℤ → ℝ := fun x => (if x ∈ A ∩ Z0.set then 1 else 0) - α * (if x ∈ Z0.set then 1 else 0)
    let h : ℤ → ℝ := fun y => (if y ∈ A then 1 else 0) * unifMeas Z1.set y
    ∑ x ∈ Z0.set, (convInd (A ∩ Z0.set) A Z1 x - α ^ 2) ^ 2 ≤
      ∑ x ∈ Z0.set, (convZ Z1.set g h x) ^ 2 +
      (2 * |locDens Z1 A - α| + 2 * τ) * (Z0.set.card : ℝ) := by
  classical
  intro g h
  have hg_abs : ∀ x, |g x| ≤ 1 := by
    intro x
    dsimp only [g]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hgh_eq : ∀ x, convZ Z1.set g h x = convInd (A ∩ Z0.set) A Z1 x - α * convInd Z0.set A Z1 x := by
    intro x
    unfold convInd convZ
    dsimp only [g, h]
    simp_rw [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  have hconvZ0_on_m : ∀ x ∈ Z0m.set, convInd Z0.set A Z1 x = locDens Z1 A := by
    intro x hx
    unfold convInd convZ locDens
    have hmem : ∀ y ∈ Z1.set, x - y ∈ Z0.set := fun y hy => by
      rw [sub_eq_add_neg]; exact hZ0m_sub (Finset.add_mem_add hx (Z1.neg_mem y hy))
    have hsum : ∑ y ∈ Z1.set, (if x - y ∈ Z0.set then (1 : ℝ) else 0) *
        ((if y ∈ A then 1 else 0) * unifMeas Z1.set y) =
        ∑ y ∈ Z1.set, if y ∈ A then (Z1.set.card : ℝ)⁻¹ else 0 := by
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [if_pos (hmem y hy), one_mul]
      unfold unifMeas; rw [if_pos hy]
      split_ifs <;> ring
    rw [hsum, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Finset.sum_const_zero, add_zero]
    have hfilt : Z1.set.filter (· ∈ A) = A ∩ Z1.set := by
      ext y; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
    rw [hfilt, div_eq_mul_inv]
  have hpt : ∀ x ∈ Z0.set, (convInd (A ∩ Z0.set) A Z1 x - α ^ 2) ^ 2 ≤
      (convZ Z1.set g h x) ^ 2 +
      (if x ∈ Z0m.set then 2 * |locDens Z1 A - α| else 2) := by
    intro x _
    set u := convInd (A ∩ Z0.set) A Z1 x - α ^ 2
    set v := convZ Z1.set g h x
    have hu_abs : |u| ≤ 1 := by
      have h0 := convInd_nonneg (A ∩ Z0.set) A Z1 x
      have h1 := convInd_le_one (A ∩ Z0.set) A Z1 x
      rw [abs_le]; constructor <;> nlinarith
    have hv_abs : |v| ≤ 1 := by
      dsimp only [v]
      calc |convZ Z1.set g h x|
          ≤ ∑ y ∈ Z1.set, |g (x - y) * h y| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ y ∈ Z1.set, unifMeas Z1.set y := by
            refine Finset.sum_le_sum fun y _ => ?_
            rw [abs_mul]
            have hhy : |h y| ≤ unifMeas Z1.set y := by
              dsimp only [h]; rw [abs_mul, abs_of_nonneg (unifMeas_nonneg _ _)]
              split_ifs <;> simp [unifMeas_nonneg]
            nlinarith [hg_abs (x - y), abs_nonneg (h y), unifMeas_nonneg Z1.set y]
        _ = 1 := sum_unifMeas Z1.set Z1.nonempty
    have hdiff : u - v = α * (convInd Z0.set A Z1 x - α) := by
      dsimp only [u, v]; rw [hgh_eq x]; ring
    have hsq_diff : u ^ 2 - v ^ 2 ≤ 2 * |u - v| := by
      have : u ^ 2 - v ^ 2 = (u + v) * (u - v) := by ring
      rw [this]
      have habs : |u + v| ≤ 2 := by linarith [abs_add_le u v]
      have h1 : (u + v) * (u - v) ≤ |u + v| * |u - v| := by
        rw [← abs_mul]; exact le_abs_self _
      nlinarith [abs_nonneg (u - v)]
    by_cases hxm : x ∈ Z0m.set
    · rw [if_pos hxm]
      have : |u - v| ≤ |locDens Z1 A - α| := by
        rw [hdiff, hconvZ0_on_m x hxm, abs_mul, abs_of_nonneg hα0]
        nlinarith [abs_nonneg (locDens Z1 A - α)]
      linarith
    · rw [if_neg hxm]
      have h0 := convInd_nonneg Z0.set A Z1 x
      have h1 := convInd_le_one Z0.set A Z1 x
      have : |u - v| ≤ 1 := by
        rw [hdiff, abs_mul, abs_of_nonneg hα0]
        have : |convInd Z0.set A Z1 x - α| ≤ 1 := by rw [abs_le]; constructor <;> linarith
        nlinarith
      linarith
  calc ∑ x ∈ Z0.set, (convInd (A ∩ Z0.set) A Z1 x - α ^ 2) ^ 2
      ≤ ∑ x ∈ Z0.set, ((convZ Z1.set g h x) ^ 2 + (if x ∈ Z0m.set then 2 * |locDens Z1 A - α| else 2)) :=
        Finset.sum_le_sum hpt
    _ = ∑ x ∈ Z0.set, (convZ Z1.set g h x) ^ 2 +
        ∑ x ∈ Z0.set, (if x ∈ Z0m.set then 2 * |locDens Z1 A - α| else 2) := Finset.sum_add_distrib
    _ ≤ ∑ x ∈ Z0.set, (convZ Z1.set g h x) ^ 2 +
        (2 * |locDens Z1 A - α| + 2 * τ) * (Z0.set.card : ℝ) := by
        have hsum_err : ∑ x ∈ Z0.set, (if x ∈ Z0m.set then 2 * |locDens Z1 A - α| else 2) ≤
            (2 * |locDens Z1 A - α| + 2 * τ) * (Z0.set.card : ℝ) := by
          have h1 : ∀ x ∈ Z0.set, (if x ∈ Z0m.set then 2 * |locDens Z1 A - α| else 2) ≤
              2 * |locDens Z1 A - α| + (if x ∉ Z0m.set then 2 else 0) := by
            intro x _; split_ifs <;> linarith [abs_nonneg (locDens Z1 A - α)]
          calc ∑ x ∈ Z0.set, (if x ∈ Z0m.set then 2 * |locDens Z1 A - α| else 2)
              ≤ ∑ x ∈ Z0.set, (2 * |locDens Z1 A - α| + (if x ∉ Z0m.set then 2 else 0)) :=
                Finset.sum_le_sum h1
            _ = (Z0.set.card : ℝ) * (2 * |locDens Z1 A - α|) +
                ((Z0.set \ Z0m.set).card : ℝ) * 2 := by
                rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_ite,
                  Finset.sum_const, nsmul_eq_mul, Finset.sum_const_zero, add_zero]
                have hf : Z0.set.filter (· ∉ Z0m.set) = Z0.set \ Z0m.set := by
                  ext x; simp [Finset.mem_sdiff]
                rw [hf]
            _ ≤ (2 * |locDens Z1 A - α| + 2 * τ) * (Z0.set.card : ℝ) := by nlinarith
        linarith

private lemma lem_increment_stepE {M : ℕ} [NeZero M] {A : Finset ℤ}
    {Z0 Z1 Z0m Z0p Z' : SymNbhd} {τ α : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hZ0m_sub : Z0m.set + Z1.set ⊆ Z0.set)
    (hZ0p_sub : Z0.set + Z1.set ⊆ Z0p.set)
    (hZ0mZ0 : Z0m.set ⊆ Z0.set)
    (hZ0_sdiff : ((Z0p.set \ Z0m.set).card : ℝ) ≤ τ * (Z0.set.card : ℝ))
    (hZ'1 : Z'.set ⊆ Z1.set)
    (hdiam_01 : ∀ x ∈ Z0.set + Z1.set, ∀ y ∈ Z0.set + Z1.set, |x - y| < (M : ℤ)) :
    let g : ℤ → ℝ := fun x => (if x ∈ A ∩ Z0.set then 1 else 0) - α * (if x ∈ Z0.set then 1 else 0)
    let ghat : ZMod M → ℂ := fourierFin M Z0.set (fun x => ((g x : ℝ) : ℂ))
    (M : ℝ)⁻¹ * ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖unifHat M Z' r‖ ^ 2 ≤
      ∑ x ∈ Z0.set, (convInd A Z'.set Z' x - α) ^ 2 + τ * (Z0.set.card : ℝ) := by
  classical
  intro g ghat
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  have hg_supp : ∀ x, x ∉ Z0.set → g x = 0 := fun x hx => by
    have hnot : x ∉ A ∩ Z0.set := fun h => hx (Finset.mem_inter.mp h).2
    simp [g, hx]
  have hg_abs : ∀ x, |g x| ≤ 1 := fun x => by
    dsimp only [g]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  have hsub01 : Z0.set + Z'.set ⊆ Z0.set + Z1.set := Finset.add_subset_add_left hZ'1
  have hdiam' : ∀ x ∈ Z0.set + Z'.set, ∀ y ∈ Z0.set + Z'.set, |x - y| < (M : ℤ) :=
    fun x hx y hy => hdiam_01 x (hsub01 hx) y (hsub01 hy)
  have hp := plancherel_fin (Z0.set + Z'.set)
    (fun x => ((convZ Z'.set g (unifMeas Z'.set) x : ℝ) : ℂ)) hdiam'
  have hconv : ∀ r : ZMod M, ‖fourierFin M (Z0.set + Z'.set)
      (fun x => ((convZ Z'.set g (unifMeas Z'.set) x : ℝ) : ℂ)) r‖ ^ 2 =
      ‖ghat r‖ ^ 2 * ‖unifHat M Z' r‖ ^ 2 := fun r => by
    rw [fourierFin_convZ Z0.set Z'.set g (unifMeas Z'.set) hg_supp r, norm_mul, mul_pow]
    rfl
  simp_rw [hconv] at hp
  have hphys : (M : ℝ)⁻¹ * ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖unifHat M Z' r‖ ^ 2 =
      ∑ x ∈ Z0.set + Z'.set, (convZ Z'.set g (unifMeas Z'.set) x) ^ 2 := by
    rw [hp, ← mul_assoc, inv_mul_cancel₀ hM_pos.ne', one_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hphys]
  have hZ0m_sub' : Z0m.set ⊆ Z0.set + Z'.set := fun x hx => by
    simpa using Finset.add_mem_add (hZ0mZ0 hx) Z'.zero_mem
  have hsplit_eq : ∑ x ∈ Z0.set + Z'.set, (convZ Z'.set g (unifMeas Z'.set) x) ^ 2 =
      ∑ x ∈ Z0m.set, (convZ Z'.set g (unifMeas Z'.set) x) ^ 2 +
      ∑ x ∈ (Z0.set + Z'.set) \ Z0m.set, (convZ Z'.set g (unifMeas Z'.set) x) ^ 2 :=
    (Finset.sum_sdiff hZ0m_sub').symm.trans (add_comm _ _)
  rw [hsplit_eq]
  have hinner_eq : ∑ x ∈ Z0m.set, (convZ Z'.set g (unifMeas Z'.set) x) ^ 2 ≤
      ∑ x ∈ Z0.set, (convInd A Z'.set Z' x - α) ^ 2 := by
    have heq_on : ∀ x ∈ Z0m.set, convZ Z'.set g (unifMeas Z'.set) x = convInd A Z'.set Z' x - α := by
      intro x hx
      unfold convInd convZ
      have hmem : ∀ y ∈ Z'.set, x - y ∈ Z0.set := fun y hy => by
        rw [sub_eq_add_neg]; exact hZ0m_sub (Finset.add_mem_add hx (hZ'1 (Z'.neg_mem y hy)))
      have h1 : ∑ y ∈ Z'.set, g (x - y) * unifMeas Z'.set y =
          ∑ y ∈ Z'.set, ((if x - y ∈ A then (1 : ℝ) else 0) * ((if y ∈ Z'.set then 1 else 0) * unifMeas Z'.set y) -
            α * unifMeas Z'.set y) := by
        refine Finset.sum_congr rfl fun y hy => ?_
        dsimp only [g]
        have hx0 := hmem y hy
        rw [if_pos hx0, if_pos hy, one_mul]
        by_cases hxA : x - y ∈ A
        · rw [if_pos (Finset.mem_inter.mpr ⟨hxA, hx0⟩), if_pos hxA]; ring
        · rw [if_neg (fun h => hxA (Finset.mem_inter.mp h).1), if_neg hxA]; ring
      rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_unifMeas Z'.set Z'.nonempty, mul_one]
    calc ∑ x ∈ Z0m.set, (convZ Z'.set g (unifMeas Z'.set) x) ^ 2
        = ∑ x ∈ Z0m.set, (convInd A Z'.set Z' x - α) ^ 2 :=
          Finset.sum_congr rfl fun x hx => by rw [heq_on x hx]
      _ ≤ ∑ x ∈ Z0.set, (convInd A Z'.set Z' x - α) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hZ0mZ0 (fun _ _ _ => sq_nonneg _)
  have houter_le : ∑ x ∈ (Z0.set + Z'.set) \ Z0m.set, (convZ Z'.set g (unifMeas Z'.set) x) ^ 2 ≤
      τ * (Z0.set.card : ℝ) := by
    have hterm_le : ∀ x ∈ (Z0.set + Z'.set) \ Z0m.set, (convZ Z'.set g (unifMeas Z'.set) x) ^ 2 ≤ 1 := by
      intro x _
      have habs : |convZ Z'.set g (unifMeas Z'.set) x| ≤ 1 := by
        calc |convZ Z'.set g (unifMeas Z'.set) x|
            ≤ ∑ y ∈ Z'.set, |g (x - y) * unifMeas Z'.set y| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ y ∈ Z'.set, unifMeas Z'.set y := by
              refine Finset.sum_le_sum fun y _ => ?_
              rw [abs_mul, abs_of_nonneg (unifMeas_nonneg _ _)]
              nlinarith [hg_abs (x - y), unifMeas_nonneg Z'.set y]
          _ = 1 := sum_unifMeas Z'.set Z'.nonempty
      nlinarith [sq_abs (convZ Z'.set g (unifMeas Z'.set) x), abs_nonneg (convZ Z'.set g (unifMeas Z'.set) x)]
    have hsub_outer : (Z0.set + Z'.set) \ Z0m.set ⊆ Z0p.set \ Z0m.set :=
      Finset.sdiff_subset_sdiff (hsub01.trans hZ0p_sub) Subset.rfl
    calc ∑ x ∈ (Z0.set + Z'.set) \ Z0m.set, (convZ Z'.set g (unifMeas Z'.set) x) ^ 2
        ≤ ∑ _x ∈ (Z0.set + Z'.set) \ Z0m.set, (1 : ℝ) := Finset.sum_le_sum hterm_le
      _ = (((Z0.set + Z'.set) \ Z0m.set).card : ℝ) := by simp
      _ ≤ ((Z0p.set \ Z0m.set).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub_outer
      _ ≤ τ * (Z0.set.card : ℝ) := hZ0_sdiff
  linarith

private lemma lem_increment {A : Finset ℤ} {Z0 Z1 Z2 : SymNbhd} {τ α ε δ : ℝ}
    (hτ : 0 ≤ τ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hZ21 : Z2.set ⊆ Z1.set)
    (h01 : IsClosedPair τ Z0 Z1) (h12 : IsClosedPair τ Z1 Z2) :
    let m : ℕ := Nat.clog 2 (Nat.ceil (8 / δ)) + 1
    let N : ℕ := Nat.floor (2 / ε ^ 2)
    ∃ B : Sys,
      B.HasDim (3 * N) ∧
      covFlat (Set.univ : Set ℤ) (B.set 0) ≤ ((2 ^ (3 * (m + 1) * N) : ℕ) : ℕ∞) ∧
      ∀ Z' : SymNbhd, Z'.set ⊆ Z2.set → (Z'.set : Set ℤ) ⊆ B.set 0 →
        (Z0.set.card : ℝ)⁻¹ * ∑ x ∈ Z0.set, (convInd A Z'.set Z' x - α) ^ 2 ≥
        (Z0.set.card : ℝ)⁻¹ * ∑ x ∈ Z0.set, (convInd (A ∩ Z0.set) A Z1 x - α ^ 2) ^ 2 -
          (ε ^ 2 + 8 * τ / ε ^ 2 + 2 * δ + 3 * τ + 2 * |locDens Z1 A - α|) := by
  classical
  intro m N
  obtain ⟨Z0m, Z0p, hZ0m_sub, hZ0p_sub, hZ0_card⟩ := h01
  have hZ0mZ0 : Z0m.set ⊆ Z0.set := fun x hx => by
    simpa using hZ0m_sub (Finset.add_mem_add hx Z1.zero_mem)
  have hZ0Z0p : Z0.set ⊆ Z0p.set := fun x hx => by
    simpa using hZ0p_sub (Finset.add_mem_add hx Z1.zero_mem)
  have hZ0_pos : (0 : ℝ) < (Z0.set.card : ℝ) := Nat.cast_pos.mpr Z0.card_pos
  have hZ0_sdiff : ((Z0p.set \ Z0m.set).card : ℝ) ≤ τ * (Z0.set.card : ℝ) := by
    have hle : Z0m.set ⊆ Z0p.set := hZ0mZ0.trans hZ0Z0p
    have hc : (Z0p.set \ Z0m.set).card = Z0p.set.card - Z0m.set.card := Finset.card_sdiff_of_subset hle
    have hR : ((Z0p.set \ Z0m.set).card : ℝ) = (Z0p.set.card : ℝ) - (Z0m.set.card : ℝ) := by
      rw [hc, Nat.cast_sub (Finset.card_le_card hle)]
    have hZmZ0 : (Z0m.set.card : ℝ) ≤ (Z0.set.card : ℝ) := by exact_mod_cast Finset.card_le_card hZ0mZ0
    nlinarith
  have hZ0_inner_sdiff : ((Z0.set \ Z0m.set).card : ℝ) ≤ τ * (Z0.set.card : ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card (Finset.sdiff_subset_sdiff hZ0Z0p Subset.rfl))).trans hZ0_sdiff
  let R : ℕ := ((Z0.set ∪ Z1.set).image Int.natAbs).sup id + 1
  let M : ℕ := 8 * R + 1
  have : NeZero M := ⟨by dsimp [M]; omega⟩
  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (NeZero.pos M)
  have hdiam_01 : ∀ x ∈ Z0.set + Z1.set, ∀ y ∈ Z0.set + Z1.set, |x - y| < (M : ℤ) := by
    intro x hx y hy
    have hbound : ∀ z ∈ Z0.set + Z1.set, |z| ≤ 2 * (R : ℤ) := by
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hz
      have haR : a.natAbs ≤ R :=
        (Finset.le_sup (f := id) (Finset.mem_image_of_mem Int.natAbs (Finset.mem_union_left Z1.set ha))).trans (by dsimp [R]; omega)
      have hbR : b.natAbs ≤ R :=
        (Finset.le_sup (f := id) (Finset.mem_image_of_mem Int.natAbs (Finset.mem_union_right Z0.set hb))).trans (by dsimp [R]; omega)
      have haZ : |a| ≤ (R : ℤ) := by simpa [Int.natCast_natAbs] using (show (a.natAbs : ℤ) ≤ (R : ℤ) by exact_mod_cast haR)
      have hbZ : |b| ≤ (R : ℤ) := by simpa [Int.natCast_natAbs] using (show (b.natAbs : ℤ) ≤ (R : ℤ) by exact_mod_cast hbR)
      linarith [abs_add_le a b]
    have hxR := hbound x hx
    have hyR := hbound y hy
    have : |x - y| ≤ |x| + |y| := abs_sub x y
    dsimp only [M]; omega
  have hdiam_0 : ∀ x ∈ Z0.set, ∀ y ∈ Z0.set, |x - y| < (M : ℤ) := fun x hx y hy =>
    hdiam_01 x (by simpa using Finset.add_mem_add hx Z1.zero_mem)
      y (by simpa using Finset.add_mem_add hy Z1.zero_mem)
  let g : ℤ → ℝ := fun x => (if x ∈ A ∩ Z0.set then 1 else 0) - α * (if x ∈ Z0.set then 1 else 0)
  have hg_supp : ∀ x, x ∉ Z0.set → g x = 0 := fun x hx => by
    simp [g, hx]
  have hg_abs : ∀ x, |g x| ≤ 1 := fun x => by
    dsimp only [g]
    split_ifs <;> rw [abs_le] <;> constructor <;> linarith
  let h : ℤ → ℝ := fun y => (if y ∈ A then 1 else 0) * unifMeas Z1.set y
  have hstepA : ∑ x ∈ Z0.set, (convInd (A ∩ Z0.set) A Z1 x - α ^ 2) ^ 2 ≤
      ∑ x ∈ Z0.set, (convZ Z1.set g h x) ^ 2 +
      (2 * |locDens Z1 A - α| + 2 * τ) * (Z0.set.card : ℝ) :=
    lem_increment_stepA hα0 hα1 hZ0m_sub hZ0_inner_sdiff
  let ghat : ZMod M → ℂ := fourierFin M Z0.set (fun x => ((g x : ℝ) : ℂ))
  let hhat : ZMod M → ℂ := fourierFin M Z1.set (fun y => ((h y : ℝ) : ℂ))
  have hg_L2 : (M : ℝ)⁻¹ * ∑ r : ZMod M, ‖ghat r‖ ^ 2 ≤ (Z0.set.card : ℝ) := by
    have hp := plancherel_fin Z0.set (fun x => ((g x : ℝ) : ℂ)) hdiam_0
    have hnorm : ∑ x ∈ Z0.set, ‖((g x : ℝ) : ℂ)‖ ^ 2 ≤ (Z0.set.card : ℝ) := by
      calc ∑ x ∈ Z0.set, ‖((g x : ℝ) : ℂ)‖ ^ 2
          = ∑ x ∈ Z0.set, |g x| ^ 2 := Finset.sum_congr rfl fun x _ => by rw [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ∑ _x ∈ Z0.set, (1 : ℝ) := Finset.sum_le_sum fun x _ => by nlinarith [hg_abs x, abs_nonneg (g x)]
        _ = (Z0.set.card : ℝ) := by simp
    dsimp only [ghat]
    rw [hp, ← mul_assoc, inv_mul_cancel₀ hM_pos.ne', one_mul]
    exact hnorm
  have hh_norm_le : ∀ r : ZMod M, ‖hhat r‖ ≤ 1 := by
    intro r
    unfold hhat fourierFin
    calc ‖∑ y ∈ Z1.set, ((h y : ℝ) : ℂ) * zmodChar M r (-(y : ZMod M))‖
        ≤ ∑ y ∈ Z1.set, ‖((h y : ℝ) : ℂ) * zmodChar M r (-(y : ZMod M))‖ := norm_sum_le _ _
      _ ≤ ∑ y ∈ Z1.set, unifMeas Z1.set y := by
          refine Finset.sum_le_sum fun y _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, zmodChar_norm, mul_one]
          dsimp only [h]; rw [abs_mul, abs_of_nonneg (unifMeas_nonneg _ _)]
          split_ifs <;> simp [unifMeas_nonneg]
      _ = 1 := sum_unifMeas Z1.set Z1.nonempty
  let Spec : Finset (ZMod M) := Finset.univ.filter (fun r => ε < ‖hhat r‖)
  have hstepBC : ∑ x ∈ Z0.set, (convZ Z1.set g h x) ^ 2 ≤
      (M : ℝ)⁻¹ * ∑ r ∈ Spec, ‖ghat r‖ ^ 2 + ε ^ 2 * (Z0.set.card : ℝ) := by
    have hsub0 : Z0.set ⊆ Z0.set + Z1.set := fun x hx => by
      simpa using Finset.add_mem_add hx Z1.zero_mem
    have h1 : ∑ x ∈ Z0.set, (convZ Z1.set g h x) ^ 2 ≤
        (M : ℝ)⁻¹ * ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖hhat r‖ ^ 2 := by
      have hp := plancherel_fin (Z0.set + Z1.set) (fun x => ((convZ Z1.set g h x : ℝ) : ℂ)) hdiam_01
      have hconv : ∀ r : ZMod M, ‖fourierFin M (Z0.set + Z1.set) (fun x => ((convZ Z1.set g h x : ℝ) : ℂ)) r‖ ^ 2 =
          ‖ghat r‖ ^ 2 * ‖hhat r‖ ^ 2 := fun r => by
        rw [fourierFin_convZ Z0.set Z1.set g h hg_supp r, norm_mul, mul_pow]
      simp_rw [hconv] at hp
      have h2 : ∑ x ∈ Z0.set, (convZ Z1.set g h x) ^ 2 ≤
          ∑ x ∈ Z0.set + Z1.set, ‖((convZ Z1.set g h x : ℝ) : ℂ)‖ ^ 2 := by
        refine (Finset.sum_le_sum_of_subset_of_nonneg hsub0 (fun _ _ _ => sq_nonneg _)).trans_eq ?_
        refine Finset.sum_congr rfl fun x _ => by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      calc ∑ x ∈ Z0.set, (convZ Z1.set g h x) ^ 2
          ≤ ∑ x ∈ Z0.set + Z1.set, ‖((convZ Z1.set g h x : ℝ) : ℂ)‖ ^ 2 := h2
        _ = (M : ℝ)⁻¹ * ((M : ℝ) * ∑ x ∈ Z0.set + Z1.set, ‖((convZ Z1.set g h x : ℝ) : ℂ)‖ ^ 2) := by
            rw [← mul_assoc, inv_mul_cancel₀ hM_pos.ne', one_mul]
        _ = (M : ℝ)⁻¹ * ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖hhat r‖ ^ 2 := by rw [← hp]
    have hsplit : ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖hhat r‖ ^ 2 ≤
        ∑ r ∈ Spec, ‖ghat r‖ ^ 2 + ε ^ 2 * ∑ r : ZMod M, ‖ghat r‖ ^ 2 := by
      have hpt : ∀ r : ZMod M, ‖ghat r‖ ^ 2 * ‖hhat r‖ ^ 2 ≤
          (if r ∈ Spec then ‖ghat r‖ ^ 2 else 0) + ε ^ 2 * ‖ghat r‖ ^ 2 := by
        intro r
        by_cases hr : r ∈ Spec
        · rw [if_pos hr]
          have h1 := hh_norm_le r
          have hsq : ‖hhat r‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (hhat r)]
          nlinarith [sq_nonneg ‖ghat r‖, sq_nonneg ε]
        · rw [if_neg hr, zero_add]
          have hle : ‖hhat r‖ ≤ ε := by
            by_contra hgt; push Not at hgt
            exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
          have hsq : ‖hhat r‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
          nlinarith [sq_nonneg ‖ghat r‖]
      calc ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖hhat r‖ ^ 2
          ≤ ∑ r : ZMod M, ((if r ∈ Spec then ‖ghat r‖ ^ 2 else 0) + ε ^ 2 * ‖ghat r‖ ^ 2) :=
            Finset.sum_le_sum fun r _ => hpt r
        _ = ∑ r ∈ Spec, ‖ghat r‖ ^ 2 + ε ^ 2 * ∑ r : ZMod M, ‖ghat r‖ ^ 2 := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_mem, Finset.univ_inter]
    calc ∑ x ∈ Z0.set, (convZ Z1.set g h x) ^ 2
        ≤ (M : ℝ)⁻¹ * ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖hhat r‖ ^ 2 := h1
      _ ≤ (M : ℝ)⁻¹ * (∑ r ∈ Spec, ‖ghat r‖ ^ 2 + ε ^ 2 * ∑ r : ZMod M, ‖ghat r‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsplit (inv_nonneg.mpr hM_pos.le)
      _ = (M : ℝ)⁻¹ * ∑ r ∈ Spec, ‖ghat r‖ ^ 2 + ε ^ 2 * ((M : ℝ)⁻¹ * ∑ r : ZMod M, ‖ghat r‖ ^ 2) := by ring
      _ ≤ (M : ℝ)⁻¹ * ∑ r ∈ Spec, ‖ghat r‖ ^ 2 + ε ^ 2 * (Z0.set.card : ℝ) := by gcongr
  let indA : ℤ → ℝ := fun y => if y ∈ A then 1 else 0
  have hindA : ∀ y ∈ Z1.set, |indA y| ≤ 1 := fun y _ => by dsimp [indA]; split_ifs <;> norm_num
  obtain ⟨B, hBd, hBD, hBann⟩ := lem_pars (M := M) hτ hε hδ h12 indA hindA
  refine ⟨B, hBd, hBD, ?_⟩
  intro Z' hZ'2 hZ'B
  have hspec_ann : ∀ r ∈ Spec, 1 - (8 * τ / ε ^ 2 + 2 * δ) ≤ ‖unifHat M Z' r‖ ^ 2 := by
    intro r hr
    have hr' : ε < ‖fourierFin M Z1.set (fun y => ((indA y * unifMeas Z1.set y : ℝ) : ℂ)) r‖ :=
      (Finset.mem_filter.mp hr).2
    have hdiff : ‖unifHat M Z' r - 1‖ ≤ 4 * τ / ε ^ 2 + δ := by
      have heq : unifHat M Z' r - 1 =
          ∑ y ∈ Z'.set, ((unifMeas Z'.set y : ℝ) : ℂ) * (zmodChar M r (-(y : ZMod M)) - 1) := by
        unfold unifHat fourierFin
        have h1 : (1 : ℂ) = ∑ y ∈ Z'.set, ((unifMeas Z'.set y : ℝ) : ℂ) := by
          have := congrArg Complex.ofReal (sum_unifMeas Z'.set Z'.nonempty)
          simpa [Complex.ofReal_sum] using this.symm
        conv_lhs => rw [h1]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun y _ => by ring
      rw [heq]
      calc ‖∑ y ∈ Z'.set, ((unifMeas Z'.set y : ℝ) : ℂ) * (zmodChar M r (-(y : ZMod M)) - 1)‖
          ≤ ∑ y ∈ Z'.set, ‖((unifMeas Z'.set y : ℝ) : ℂ) * (zmodChar M r (-(y : ZMod M)) - 1)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ y ∈ Z'.set, unifMeas Z'.set y * (4 * τ / ε ^ 2 + δ) := by
            refine Finset.sum_le_sum fun y hy => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (unifMeas_nonneg _ _)]
            have hneg : ‖zmodChar M r (-(y : ZMod M)) - 1‖ = ‖zmodChar M r (y : ZMod M) - 1‖ := by
              rw [zmodChar_neg]
              have : starRingEnd ℂ (zmodChar M r (y : ZMod M) - 1) =
                  starRingEnd ℂ (zmodChar M r (y : ZMod M)) - 1 := by simp
              rw [← this, Complex.norm_conj]
            rw [hneg]
            exact mul_le_mul_of_nonneg_left (hBann r hr' y (hZ'B hy) (hZ'2 hy)) (unifMeas_nonneg _ _)
        _ = 4 * τ / ε ^ 2 + δ := by
            rw [← Finset.sum_mul, sum_unifMeas Z'.set Z'.nonempty, one_mul]
    have htri : 1 - ‖unifHat M Z' r‖ ≤ ‖unifHat M Z' r - 1‖ := by
      have := norm_sub_norm_le (1 : ℂ) (unifHat M Z' r)
      rw [norm_one, norm_sub_rev] at this
      exact this
    have hle1 := norm_unifHat_le_one M Z' r
    have hnn := norm_nonneg (unifHat M Z' r)
    have hsq_le : 1 - ‖unifHat M Z' r‖ ^ 2 ≤ 2 * (1 - ‖unifHat M Z' r‖) := by nlinarith
    have h2eq : 2 * (4 * τ / ε ^ 2 + δ) = 8 * τ / ε ^ 2 + 2 * δ := by ring
    linarith
  have hstepD : (M : ℝ)⁻¹ * ∑ r ∈ Spec, ‖ghat r‖ ^ 2 - (8 * τ / ε ^ 2 + 2 * δ) * (Z0.set.card : ℝ) ≤
      (M : ℝ)⁻¹ * ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖unifHat M Z' r‖ ^ 2 := by
    have h1 : ∑ r ∈ Spec, ‖ghat r‖ ^ 2 - (8 * τ / ε ^ 2 + 2 * δ) * ∑ r : ZMod M, ‖ghat r‖ ^ 2 ≤
        ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖unifHat M Z' r‖ ^ 2 := by
      have hSpec_le : ∑ r ∈ Spec, ‖ghat r‖ ^ 2 * ‖unifHat M Z' r‖ ^ 2 ≤
          ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖unifHat M Z' r‖ ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      have hSpec_lb : ∑ r ∈ Spec, ‖ghat r‖ ^ 2 - (8 * τ / ε ^ 2 + 2 * δ) * ∑ r ∈ Spec, ‖ghat r‖ ^ 2 ≤
          ∑ r ∈ Spec, ‖ghat r‖ ^ 2 * ‖unifHat M Z' r‖ ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_le_sum fun r hr => ?_
        have hs := hspec_ann r hr
        nlinarith [sq_nonneg ‖ghat r‖]
      have hall : ∑ r ∈ Spec, ‖ghat r‖ ^ 2 ≤ ∑ r : ZMod M, ‖ghat r‖ ^ 2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
      have hpos : 0 ≤ 8 * τ / ε ^ 2 + 2 * δ := by positivity
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hM_pos.le)
    have hpos : 0 ≤ 8 * τ / ε ^ 2 + 2 * δ := by positivity
    nlinarith
  have hstepE : (M : ℝ)⁻¹ * ∑ r : ZMod M, ‖ghat r‖ ^ 2 * ‖unifHat M Z' r‖ ^ 2 ≤
      ∑ x ∈ Z0.set, (convInd A Z'.set Z' x - α) ^ 2 + τ * (Z0.set.card : ℝ) :=
    lem_increment_stepE hα0 hα1 hZ0m_sub hZ0p_sub hZ0mZ0 hZ0_sdiff (hZ'2.trans hZ21) hdiam_01
  have hcomb : ∑ x ∈ Z0.set, (convInd (A ∩ Z0.set) A Z1 x - α ^ 2) ^ 2 -
      (ε ^ 2 + 8 * τ / ε ^ 2 + 2 * δ + 3 * τ + 2 * |locDens Z1 A - α|) * (Z0.set.card : ℝ) ≤
      ∑ x ∈ Z0.set, (convInd A Z'.set Z' x - α) ^ 2 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hcomb (inv_nonneg.mpr hZ0_pos.le)
  have hrhs : (Z0.set.card : ℝ)⁻¹ * (∑ x ∈ Z0.set, (convInd (A ∩ Z0.set) A Z1 x - α ^ 2) ^ 2 -
      (ε ^ 2 + 8 * τ / ε ^ 2 + 2 * δ + 3 * τ + 2 * |locDens Z1 A - α|) * (Z0.set.card : ℝ)) =
      (Z0.set.card : ℝ)⁻¹ * ∑ x ∈ Z0.set, (convInd (A ∩ Z0.set) A Z1 x - α ^ 2) ^ 2 -
      (ε ^ 2 + 8 * τ / ε ^ 2 + 2 * δ + 3 * τ + 2 * |locDens Z1 A - α|) := by
    rw [mul_sub, mul_comm _ (Z0.set.card : ℝ), ← mul_assoc, inv_mul_cancel₀ hZ0_pos.ne', one_mul]
  linarith

/- ### Module 5A: Finite probability spaces `FinProb`, `tvLe`, and `lem_newprob` -/

private structure FinProb where
  N : ℕ
  w : Fin N → ℝ
  w_nonneg : ∀ i, 0 ≤ w i
  sum_w : ∑ i : Fin N, w i = 1

private noncomputable def FinProb.expect (P : FinProb) (f : Fin P.N → ℝ) : ℝ :=
  ∑ i : Fin P.N, P.w i * f i

private lemma FinProb.expect_const (P : FinProb) (c : ℝ) : P.expect (fun _ => c) = c := by
  unfold FinProb.expect
  rw [← Finset.sum_mul, P.sum_w, one_mul]

private lemma FinProb.expect_add (P : FinProb) (f g : Fin P.N → ℝ) :
    P.expect (fun i => f i + g i) = P.expect f + P.expect g := by
  unfold FinProb.expect
  simp_rw [mul_add, Finset.sum_add_distrib]

private lemma FinProb.expect_sub (P : FinProb) (f g : Fin P.N → ℝ) :
    P.expect (fun i => f i - g i) = P.expect f - P.expect g := by
  unfold FinProb.expect
  simp_rw [mul_sub, Finset.sum_sub_distrib]

private lemma FinProb.expect_mul_const (P : FinProb) (c : ℝ) (f : Fin P.N → ℝ) :
    P.expect (fun i => c * f i) = c * P.expect f := by
  unfold FinProb.expect
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private lemma FinProb.expect_nonneg (P : FinProb) {f : Fin P.N → ℝ} (hf : ∀ i, 0 ≤ f i) :
    0 ≤ P.expect f :=
  Finset.sum_nonneg fun i _ => mul_nonneg (P.w_nonneg i) (hf i)

private lemma FinProb.expect_mono (P : FinProb) {f g : Fin P.N → ℝ} (h : ∀ i, f i ≤ g i) :
    P.expect f ≤ P.expect g :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (P.w_nonneg i)

private lemma FinProb.sq_expect_le (P : FinProb) (f : Fin P.N → ℝ) :
    (P.expect f) ^ 2 ≤ P.expect (fun i => (f i) ^ 2) := by
  have hnn : 0 ≤ ∑ i : Fin P.N, ∑ j : Fin P.N, P.w i * P.w j * (f i - f j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (P.w_nonneg i) (P.w_nonneg j)) (sq_nonneg _)
  have hexp : ∑ i : Fin P.N, ∑ j : Fin P.N, P.w i * P.w j * (f i - f j) ^ 2 =
      2 * P.expect (fun i => (f i) ^ 2) - 2 * (P.expect f) ^ 2 := by
    have hsq : ∀ i j : Fin P.N, P.w i * P.w j * (f i - f j) ^ 2 =
        (P.w i * (f i) ^ 2) * P.w j - 2 * (P.w i * f i) * (P.w j * f j) +
        P.w i * (P.w j * (f j) ^ 2) := fun _ _ => by ring
    simp_rw [hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have h1 : ∑ i : Fin P.N, ∑ j : Fin P.N, (P.w i * (f i) ^ 2) * P.w j =
        P.expect (fun i => (f i) ^ 2) := by
      unfold FinProb.expect
      refine Finset.sum_congr rfl fun i _ => by rw [← Finset.mul_sum, P.sum_w, mul_one]
    have h3 : ∑ i : Fin P.N, ∑ j : Fin P.N, P.w i * (P.w j * (f j) ^ 2) =
        P.expect (fun j => (f j) ^ 2) := by
      unfold FinProb.expect
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul, P.sum_w, one_mul]
    have h2 : ∑ i : Fin P.N, ∑ j : Fin P.N, 2 * (P.w i * f i) * (P.w j * f j) =
        2 * (P.expect f) ^ 2 := by
      unfold FinProb.expect
      have : ∑ i : Fin P.N, ∑ j : Fin P.N, 2 * (P.w i * f i) * (P.w j * f j) =
          2 * ∑ i : Fin P.N, (P.w i * f i) * ∑ j : Fin P.N, (P.w j * f j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [this, ← Finset.sum_mul, sq]
    rw [h1, h2, h3]; ring
  linarith

private lemma FinProb.expect_abs_le_sqrt (P : FinProb) (f : Fin P.N → ℝ) :
    P.expect (fun i => |f i|) ≤ Real.sqrt (P.expect (fun i => (f i) ^ 2)) := by
  have h1 := P.sq_expect_le (fun i => |f i|)
  simp_rw [sq_abs] at h1
  have hnn : 0 ≤ P.expect (fun i => |f i|) := P.expect_nonneg fun _ => abs_nonneg _
  rw [← Real.sqrt_sq hnn]
  exact Real.sqrt_le_sqrt h1

private noncomputable def FinProb.unifFinset (S : Finset ℤ) (hS : S.Nonempty) :
    Σ P : FinProb, (Fin P.N → ℤ) := by
  let e : S ≃ Fin S.card := S.equivFin
  let P : FinProb :=
    { N := S.card
      w := fun _ => (S.card : ℝ)⁻¹
      w_nonneg := fun _ => inv_nonneg.mpr (Nat.cast_nonneg _)
      sum_w := by
        have hpos : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS.card_pos.ne'
        simp [hpos] }
  exact ⟨P, fun i => (e.symm i).1⟩

private lemma FinProb.unifFinset_expect (S : Finset ℤ) (hS : S.Nonempty) (F : ℤ → ℝ) :
    (FinProb.unifFinset S hS).1.expect (fun i => F ((FinProb.unifFinset S hS).2 i)) =
    (S.card : ℝ)⁻¹ * ∑ x ∈ S, F x := by
  dsimp only [FinProb.unifFinset, FinProb.expect]
  rw [← Finset.mul_sum]
  congr 1
  have h1 : ∑ i : Fin S.card, F (S.equivFin.symm i).1 = ∑ x : S, F x.1 :=
    Fintype.sum_equiv S.equivFin.symm _ _ (fun _ => rfl)
  rw [h1, Finset.univ_eq_attach, Finset.sum_attach S F]

private noncomputable def FinProb.extend (P : FinProb) (Z : Fin P.N → SymNbhd) :
    Σ P' : FinProb, (Fin P'.N → Fin P.N) × (Fin P'.N → ℤ) := by
  let S : Finset (Σ _ : Fin P.N, ℤ) := Finset.univ.sigma (fun i => (Z i).set)
  let e : S ≃ Fin S.card := S.equivFin
  let proj : Fin S.card → Fin P.N := fun j => (e.symm j).1.1
  let shift : Fin S.card → ℤ := fun j => (e.symm j).1.2
  let w' : Fin S.card → ℝ := fun j => P.w (proj j) * ((Z (proj j)).set.card : ℝ)⁻¹
  have hw'_nn : ∀ j, 0 ≤ w' j := fun j =>
    mul_nonneg (P.w_nonneg _) (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hsum_w' : ∑ j : Fin S.card, w' j = 1 := by
    have h1 : ∑ j : Fin S.card, w' j = ∑ p : S, P.w p.1.1 * ((Z p.1.1).set.card : ℝ)⁻¹ :=
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    rw [h1, Finset.univ_eq_attach, Finset.sum_attach S (fun p => P.w p.1 * ((Z p.1).set.card : ℝ)⁻¹),
      Finset.sum_sigma]
    calc ∑ i : Fin P.N, ∑ _z ∈ (Z i).set, P.w i * ((Z i).set.card : ℝ)⁻¹
        = ∑ i : Fin P.N, P.w i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hpos : ((Z i).set.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Z i).card_pos.ne'
          simp only [Finset.sum_const, nsmul_eq_mul]
          field_simp
      _ = 1 := P.sum_w
  exact ⟨⟨S.card, w', hw'_nn, hsum_w'⟩, (proj, shift)⟩

private lemma FinProb.extend_shift_mem (P : FinProb) (Z : Fin P.N → SymNbhd)
    (j : Fin (P.extend Z).1.N) :
    (P.extend Z).2.2 j ∈ (Z ((P.extend Z).2.1 j)).set := by
  dsimp only [FinProb.extend]
  let S : Finset (Σ _ : Fin P.N, ℤ) := Finset.univ.sigma (fun i => (Z i).set)
  have hm := (S.equivFin.symm j).2
  exact (Finset.mem_sigma.mp hm).2

private lemma FinProb.extend_expect (P : FinProb) (Z : Fin P.N → SymNbhd)
    (F : Fin P.N → ℤ → ℝ) :
    (P.extend Z).1.expect (fun j => F ((P.extend Z).2.1 j) ((P.extend Z).2.2 j)) =
    P.expect (fun i => ((Z i).set.card : ℝ)⁻¹ * ∑ x ∈ (Z i).set, F i x) := by
  dsimp only [FinProb.extend, FinProb.expect]
  let S : Finset (Σ _ : Fin P.N, ℤ) := Finset.univ.sigma (fun i => (Z i).set)
  have h1 : ∑ j : Fin S.card,
      P.w (S.equivFin.symm j).1.1 * ((Z (S.equivFin.symm j).1.1).set.card : ℝ)⁻¹ *
        F (S.equivFin.symm j).1.1 (S.equivFin.symm j).1.2 =
      ∑ p : S, P.w p.1.1 * ((Z p.1.1).set.card : ℝ)⁻¹ * F p.1.1 p.1.2 :=
    Fintype.sum_equiv S.equivFin.symm _ _ (fun _ => rfl)
  rw [h1, Finset.univ_eq_attach,
    Finset.sum_attach S (fun p => P.w p.1 * ((Z p.1).set.card : ℝ)⁻¹ * F p.1 p.2),
    Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => by ring

private lemma FinProb.extend_pullback (P : FinProb) (Z : Fin P.N → SymNbhd) (f : Fin P.N → ℝ) :
    (P.extend Z).1.expect (fun j => f ((P.extend Z).2.1 j)) = P.expect f := by
  have h := P.extend_expect Z (fun i _ => f i)
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpos : ((Z i).set.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Z i).card_pos.ne'
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp

/- Total variation distance bound `tvLe` -/

private def tvLe (μ₁ μ₂ : ℤ → ℝ) (ε : ℝ) : Prop :=
  ∀ U : Finset ℤ, ∑ x ∈ U, |μ₁ x - μ₂ x| ≤ ε

private lemma tvLe_refl (μ : ℤ → ℝ) {ε : ℝ} (hε : 0 ≤ ε) : tvLe μ μ ε := fun U => by
  simp [hε]

private lemma tvLe_mono {μ₁ μ₂ : ℤ → ℝ} {ε₁ ε₂ : ℝ} (h : tvLe μ₁ μ₂ ε₁) (hle : ε₁ ≤ ε₂) :
    tvLe μ₁ μ₂ ε₂ := fun U => (h U).trans hle

private lemma tvLe_trans {μ₁ μ₂ μ₃ : ℤ → ℝ} {ε₁ ε₂ : ℝ}
    (h1 : tvLe μ₁ μ₂ ε₁) (h2 : tvLe μ₂ μ₃ ε₂) : tvLe μ₁ μ₃ (ε₁ + ε₂) := fun U => by
  calc ∑ x ∈ U, |μ₁ x - μ₃ x|
      ≤ ∑ x ∈ U, (|μ₁ x - μ₂ x| + |μ₂ x - μ₃ x|) :=
        Finset.sum_le_sum fun x _ => abs_sub_le (μ₁ x) (μ₂ x) (μ₃ x)
    _ = ∑ x ∈ U, |μ₁ x - μ₂ x| + ∑ x ∈ U, |μ₂ x - μ₃ x| := Finset.sum_add_distrib
    _ ≤ ε₁ + ε₂ := add_le_add (h1 U) (h2 U)

private lemma tvLe_eval {μ₁ μ₂ : ℤ → ℝ} {ε : ℝ} (h : tvLe μ₁ μ₂ ε) (A : Finset ℤ) :
    |∑ x ∈ A, μ₁ x - ∑ x ∈ A, μ₂ x| ≤ ε := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (h A)

private lemma tvLe_of_closed_shift {τ : ℝ} {Z W : SymNbhd} (hτ : 0 ≤ τ)
    (h : IsClosedPair τ Z W) {w : ℤ} (hw : w ∈ W.set) :
    tvLe (fun x => unifMeas Z.set (x - w)) (unifMeas Z.set) (2 * τ) := by
  intro U
  let U' : Finset ℤ := U ∪ Z.set ∪ Z.set.image (· + w)
  have hsub1 : U ⊆ U' := Finset.subset_union_left.trans Finset.subset_union_left
  have hsub2 : Z.set ⊆ U' := Finset.subset_union_right.trans Finset.subset_union_left
  have hsub3 : Z.set.image (· + w) ⊆ U' := Finset.subset_union_right
  calc ∑ x ∈ U, |unifMeas Z.set (x - w) - unifMeas Z.set x|
      ≤ ∑ x ∈ U', |unifMeas Z.set (x - w) - unifMeas Z.set x| :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun _ _ _ => abs_nonneg _)
    _ ≤ 2 * τ := isClosedPair_shift_tv hτ h hw U' hsub2 hsub3

private lemma tvLe_translate {μ₁ μ₂ : ℤ → ℝ} {ε : ℝ} (h : tvLe μ₁ μ₂ ε) (a : ℤ) :
    tvLe (fun x => μ₁ (x - a)) (fun x => μ₂ (x - a)) ε := fun U => by
  have heq : ∑ x ∈ U, |μ₁ (x - a) - μ₂ (x - a)| = ∑ y ∈ U.image (· - a), |μ₁ y - μ₂ y| := by
    rw [Finset.sum_image (fun _ _ _ _ h => sub_left_inj.mp h)]
  rw [heq]
  exact h _

private noncomputable def pushScale2 (s : ℕ) (μ : ℤ → ℝ) (x : ℤ) : ℝ :=
  if ((2 : ℤ) ^ s) ∣ x then μ (x / (2 : ℤ) ^ s) else 0

private lemma unifMeas_scale2Fin (s : ℕ) (S : Finset ℤ) (x : ℤ) :
    unifMeas (scale2Fin s S) x = pushScale2 s (unifMeas S) x := by
  have hpow : (2 : ℤ) ^ s ≠ 0 := pow_ne_zero s (by norm_num)
  simp only [unifMeas, pushScale2, scale2Fin_card]
  by_cases hdvd : (2 : ℤ) ^ s ∣ x
  · rw [if_pos hdvd]
    obtain ⟨q, rfl⟩ := hdvd
    rw [Int.mul_ediv_cancel_left q hpow]
    have hiff : (2 : ℤ) ^ s * q ∈ scale2Fin s S ↔ q ∈ S := by
      simp only [scale2Fin, Finset.mem_image]
      constructor
      · rintro ⟨y, hy, heq⟩; rwa [← mul_left_cancel₀ hpow heq]
      · intro hq; exact ⟨q, hq, rfl⟩
    by_cases hq : q ∈ S
    · rw [if_pos (hiff.mpr hq), if_pos hq]
    · rw [if_neg (mt hiff.mp hq), if_neg hq]
  · rw [if_neg hdvd]
    have hnot : x ∉ scale2Fin s S := by
      intro hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact hdvd ⟨y, rfl⟩
    rw [if_neg hnot]

private lemma tvLe_pushScale2 (s : ℕ) {μ₁ μ₂ : ℤ → ℝ} {ε : ℝ} (h : tvLe μ₁ μ₂ ε) :
    tvLe (pushScale2 s μ₁) (pushScale2 s μ₂) ε := by
  classical
  intro U
  have hpow : (2 : ℤ) ^ s ≠ 0 := pow_ne_zero s (by norm_num)
  let Udiv : Finset ℤ := U.filter (fun x => (2 : ℤ) ^ s ∣ x)
  have h1 : ∑ x ∈ U, |pushScale2 s μ₁ x - pushScale2 s μ₂ x| =
      ∑ x ∈ Udiv, |μ₁ (x / (2 : ℤ) ^ s) - μ₂ (x / (2 : ℤ) ^ s)| := by
    rw [← Finset.sum_subset (Finset.filter_subset (fun x => (2 : ℤ) ^ s ∣ x) U)]
    · refine Finset.sum_congr rfl fun x hx => ?_
      have hd := (Finset.mem_filter.mp hx).2
      simp only [pushScale2, if_pos hd]
    · intro x hx hnot
      have hnd : ¬ ((2 : ℤ) ^ s ∣ x) := fun hd => hnot (Finset.mem_filter.mpr ⟨hx, hd⟩)
      simp only [pushScale2, if_neg hnd, sub_self, abs_zero]
  rw [h1]
  have hinj : Set.InjOn (fun x : ℤ => x / (2 : ℤ) ^ s) (Udiv : Set ℤ) := by
    intro x1 hx1 x2 hx2 heq
    dsimp only at heq
    obtain ⟨q1, rfl⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hx1)).2
    obtain ⟨q2, rfl⟩ := (Finset.mem_filter.mp (Finset.mem_coe.mp hx2)).2
    rw [Int.mul_ediv_cancel_left q1 hpow, Int.mul_ediv_cancel_left q2 hpow] at heq
    rw [heq]
  have h2 : ∑ y ∈ Udiv.image (fun x : ℤ => x / (2 : ℤ) ^ s), |μ₁ y - μ₂ y| =
      ∑ x ∈ Udiv, |μ₁ (x / (2 : ℤ) ^ s) - μ₂ (x / (2 : ℤ) ^ s)| :=
    Finset.sum_image hinj
  rw [← h2]
  exact h _

private def coset (a : ℤ) (U : SymNbhd) : Finset ℤ := U.set.image (· + a)

private lemma coset_card (a : ℤ) (U : SymNbhd) : (coset a U).card = U.set.card :=
  Finset.card_image_of_injective _ (add_left_injective a)

private lemma scale2Fin_coset (s : ℕ) (a : ℤ) (U : SymNbhd) :
    scale2Fin s (coset a U) = coset ((2 : ℤ) ^ s * a) (U.scale2 s) := by
  ext x
  simp only [scale2Fin, coset, SymNbhd.scale2, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨(2 : ℤ) ^ s * y, ⟨y, hy, rfl⟩, by ring⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y + a, ⟨y, hy, rfl⟩, by ring⟩

private noncomputable def cosetDens (a : ℤ) (U : SymNbhd) (A : Finset ℤ) : ℝ :=
  ((A ∩ coset a U).card : ℝ) / (U.set.card : ℝ)

private lemma cosetDens_eq_sum (a : ℤ) (U : SymNbhd) (A : Finset ℤ) :
    cosetDens a U A = ∑ x ∈ A, unifMeas (coset a U) x := by
  unfold cosetDens unifMeas
  rw [coset_card, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Finset.sum_const_zero, add_zero,
    div_eq_mul_inv]
  have hfilt : A.filter (· ∈ coset a U) = A ∩ coset a U := by
    ext x; simp [Finset.mem_filter, Finset.mem_inter]
  rw [hfilt]

private lemma cosetDens_nonneg (a : ℤ) (U : SymNbhd) (A : Finset ℤ) : 0 ≤ cosetDens a U A := by
  unfold cosetDens; positivity

private lemma cosetDens_le_one (a : ℤ) (U : SymNbhd) (A : Finset ℤ) : cosetDens a U A ≤ 1 := by
  unfold cosetDens
  rw [div_le_one (Nat.cast_pos.mpr U.card_pos)]
  have : (A ∩ coset a U).card ≤ (coset a U).card := Finset.card_le_card Finset.inter_subset_right
  rw [coset_card] at this
  exact_mod_cast this

private lemma cosetDens_eq_convInd (a : ℤ) (U : SymNbhd) (A : Finset ℤ) :
    cosetDens a U A = convInd A U.set U a := by
  unfold convInd convZ
  rw [cosetDens_eq_sum]
  have h1 : ∑ x ∈ A, unifMeas (coset a U) x =
      (U.set.card : ℝ)⁻¹ * ∑ y ∈ U.set, if a - y ∈ A then (1 : ℝ) else 0 := by
    have hcard : (A ∩ coset a U).card = (U.set.filter (fun y => a - y ∈ A)).card := by
      refine Finset.card_bij (fun x _ => a - x) ?_ ?_ ?_
      · intro x hx
        obtain ⟨hxA, hxC⟩ := Finset.mem_inter.mp hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxC
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · have : a - (y + a) = -y := by ring
          rw [this]; exact U.neg_mem y hy
        · have : a - (a - (y + a)) = y + a := by ring
          rwa [this]
      · intro x1 _ x2 _ h; omega
      · intro y hy
        obtain ⟨hyU, hayA⟩ := Finset.mem_filter.mp hy
        refine ⟨a - y, Finset.mem_inter.mpr ⟨hayA, ?_⟩, by ring⟩
        exact Finset.mem_image.mpr ⟨-y, U.neg_mem y hyU, by ring⟩
    rw [← cosetDens_eq_sum, cosetDens, hcard, Finset.card_filter, Nat.cast_sum, div_eq_inv_mul]
    congr 1; refine Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
  rw [h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  dsimp only [unifMeas]; rw [if_pos hy, if_pos hy, one_mul]; ring

private lemma avg_coset_tvLe {τ : ℝ} {Z W : SymNbhd} (hτ : 0 ≤ τ)
    (hZW : IsClosedPair τ Z W) (a : ℤ) :
    tvLe
      (fun x => (Z.set.card : ℝ)⁻¹ * ∑ z ∈ Z.set, unifMeas (coset (a + z) W) x)
      (fun x => unifMeas (coset a Z) x) (2 * τ) := by
  have havg_eq : ∀ x : ℤ,
      (Z.set.card : ℝ)⁻¹ * ∑ z ∈ Z.set, unifMeas (coset (a + z) W) x =
      (W.set.card : ℝ)⁻¹ * ∑ w ∈ W.set, unifMeas (coset a Z) (x - w) := by
    intro x
    have hcount : ((Z.set.filter (fun z => x - (a + z) ∈ W.set)).card : ℝ) =
        ((W.set.filter (fun w => x - w - a ∈ Z.set)).card : ℝ) := by
      congr 1
      refine Finset.card_bij (fun z _ => x - a - z) ?_ ?_ ?_
      · intro z hz
        obtain ⟨hzZ, hmem⟩ := Finset.mem_filter.mp hz
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · have : x - a - z = x - (a + z) := by ring
          rwa [this]
        · have : x - (x - a - z) - a = z := by ring
          rwa [this]
      · intro z1 _ z2 _ h; omega
      · intro w hw
        obtain ⟨hwW, hmem⟩ := Finset.mem_filter.mp hw
        refine ⟨x - w - a, Finset.mem_filter.mpr ⟨hmem, ?_⟩, by ring⟩
        have : x - (a + (x - w - a)) = w := by ring
        rwa [this]
    have hL : (Z.set.card : ℝ)⁻¹ * ∑ z ∈ Z.set, unifMeas (coset (a + z) W) x =
        (Z.set.card : ℝ)⁻¹ * ((W.set.card : ℝ)⁻¹ * ((Z.set.filter (fun z => x - (a + z) ∈ W.set)).card : ℝ)) := by
      congr 1
      have : ∀ z ∈ Z.set, unifMeas (coset (a + z) W) x =
          if x - (a + z) ∈ W.set then (W.set.card : ℝ)⁻¹ else 0 := fun z _ => by
        rw [coset, unifMeas_translate]; rfl
      rw [Finset.sum_congr rfl this, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_const_zero, add_zero, mul_comm]
    have hR : (W.set.card : ℝ)⁻¹ * ∑ w ∈ W.set, unifMeas (coset a Z) (x - w) =
        (W.set.card : ℝ)⁻¹ * ((Z.set.card : ℝ)⁻¹ * ((W.set.filter (fun w => x - w - a ∈ Z.set)).card : ℝ)) := by
      congr 1
      have : ∀ w ∈ W.set, unifMeas (coset a Z) (x - w) =
          if x - w - a ∈ Z.set then (Z.set.card : ℝ)⁻¹ else 0 := fun w _ => by
        rw [coset, unifMeas_translate]; rfl
      rw [Finset.sum_congr rfl this, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul,
        Finset.sum_const_zero, add_zero, mul_comm]
    rw [hL, hR, hcount]; ring
  intro U
  simp_rw [havg_eq]
  have h1 : ∀ x ∈ U, |(W.set.card : ℝ)⁻¹ * ∑ w ∈ W.set, unifMeas (coset a Z) (x - w) - unifMeas (coset a Z) x| ≤
      (W.set.card : ℝ)⁻¹ * ∑ w ∈ W.set, |unifMeas (coset a Z) (x - w) - unifMeas (coset a Z) x| := by
    intro x _
    have hWpos : (0 : ℝ) < (W.set.card : ℝ) := Nat.cast_pos.mpr W.card_pos
    have heq : (W.set.card : ℝ)⁻¹ * ∑ w ∈ W.set, unifMeas (coset a Z) (x - w) - unifMeas (coset a Z) x =
        (W.set.card : ℝ)⁻¹ * ∑ w ∈ W.set, (unifMeas (coset a Z) (x - w) - unifMeas (coset a Z) x) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_sub]
      congr 1; field_simp
    rw [heq, abs_mul, abs_of_nonneg (inv_nonneg.mpr hWpos.le)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hWpos.le)
  calc ∑ x ∈ U, |(W.set.card : ℝ)⁻¹ * ∑ w ∈ W.set, unifMeas (coset a Z) (x - w) - unifMeas (coset a Z) x|
      ≤ ∑ x ∈ U, (W.set.card : ℝ)⁻¹ * ∑ w ∈ W.set, |unifMeas (coset a Z) (x - w) - unifMeas (coset a Z) x| :=
        Finset.sum_le_sum h1
    _ = (W.set.card : ℝ)⁻¹ * ∑ w ∈ W.set, ∑ x ∈ U, |unifMeas (coset a Z) (x - w) - unifMeas (coset a Z) x| := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (W.set.card : ℝ)⁻¹ * ∑ _w ∈ W.set, (2 * τ) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        refine Finset.sum_le_sum fun w hw => ?_
        have htr := tvLe_translate (tvLe_of_closed_shift hτ hZW hw) a U
        refine le_trans ?_ htr
        refine le_of_eq (Finset.sum_congr rfl fun x _ => ?_)
        rw [coset, unifMeas_translate, unifMeas_translate]
        have : x - w - a = x - a - w := by ring
        rw [this]
    _ = 2 * τ := by
        have hWpos : ((W.set.card : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr W.card_pos.ne'
        simp only [Finset.sum_const, nsmul_eq_mul]; field_simp

private lemma lem_newprob_kkj (P : FinProb) (z : Fin P.N → ℤ) (Z W : Fin P.N → SymNbhd)
    (A : Finset ℤ) (s r : ℕ) :
    let ext := P.extend Z
    let z' : Fin ext.1.N → ℤ := fun j => z (ext.2.1 j) + ext.2.2 j
    P.expect (fun i =>
      ((Z i).set.card : ℝ)⁻¹ *
        ∑ x ∈ coset ((2 : ℤ) ^ s * z i) ((Z i).scale2 s),
          (convInd A ((W i).scale2 r).set ((W i).scale2 r) x -
            cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A) ^ 2) =
    ext.1.expect (fun j =>
      (cosetDens ((2 : ℤ) ^ s * z' j) ((W (ext.2.1 j)).scale2 r) A -
        cosetDens ((2 : ℤ) ^ s * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s) A) ^ 2) := by
  intro ext z'
  symm
  have h1 := P.extend_expect Z (fun i y =>
    (cosetDens ((2 : ℤ) ^ s * (z i + y)) ((W i).scale2 r) A -
      cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A) ^ 2)
  change ext.1.expect (fun j =>
    (cosetDens ((2 : ℤ) ^ s * (z (ext.2.1 j) + ext.2.2 j)) ((W (ext.2.1 j)).scale2 r) A -
      cosetDens ((2 : ℤ) ^ s * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s) A) ^ 2) = _
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  congr 2
  have hinj : Function.Injective (fun y : ℤ => (2 : ℤ) ^ s * (z i + y)) := by
    intro y1 y2 h
    have hpow : (2 : ℤ) ^ s ≠ 0 := pow_ne_zero s (by norm_num)
    have := mul_left_cancel₀ hpow h
    omega
  have himg : (Z i).set.image (fun y => (2 : ℤ) ^ s * (z i + y)) =
      coset ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) := by
    ext x
    simp only [coset, SymNbhd.scale2, scale2Fin, Finset.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨(2 : ℤ) ^ s * y, ⟨y, hy, rfl⟩, by ring⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, by ring⟩
  rw [← himg, Finset.sum_image (fun _ _ _ _ h => hinj h)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [cosetDens_eq_convInd]

private lemma lem_newprob_ifr (P : FinProb) (z : Fin P.N → ℤ) (Z W : Fin P.N → SymNbhd)
    {τ : ℝ} (hτ : 0 ≤ τ) (hZW : ∀ i, IsClosedPair τ (Z i) (W i)) :
    let ext := P.extend Z
    let z' : Fin ext.1.N → ℤ := fun j => z (ext.2.1 j) + ext.2.2 j
    tvLe
      (fun x => ext.1.expect (fun j => unifMeas (coset (z' j) (W (ext.2.1 j))) x))
      (fun x => P.expect (fun i => unifMeas (coset (z i) (Z i)) x)) (2 * τ) := by
  intro ext z' U
  have hex : ∀ x : ℤ,
      ext.1.expect (fun j => unifMeas (coset (z' j) (W (ext.2.1 j))) x) =
      P.expect (fun i => ((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, unifMeas (coset (z i + y) (W i)) x) :=
    fun x => P.extend_expect Z (fun i y => unifMeas (coset (z i + y) (W i)) x)
  simp_rw [hex]
  calc ∑ x ∈ U, |P.expect (fun i => ((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, unifMeas (coset (z i + y) (W i)) x) -
          P.expect (fun i => unifMeas (coset (z i) (Z i)) x)|
      ≤ ∑ x ∈ U, P.expect (fun i =>
          |((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, unifMeas (coset (z i + y) (W i)) x -
            unifMeas (coset (z i) (Z i)) x|) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [← P.expect_sub]
        unfold FinProb.expect
        calc |∑ i : Fin P.N, P.w i * (((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, unifMeas (coset (z i + y) (W i)) x -
                unifMeas (coset (z i) (Z i)) x)|
            ≤ ∑ i : Fin P.N, |P.w i * (((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, unifMeas (coset (z i + y) (W i)) x -
                unifMeas (coset (z i) (Z i)) x)| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i : Fin P.N, P.w i * |((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, unifMeas (coset (z i + y) (W i)) x -
                unifMeas (coset (z i) (Z i)) x| := by
              refine Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg (P.w_nonneg i)]
    _ = P.expect (fun i => ∑ x ∈ U,
          |((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, unifMeas (coset (z i + y) (W i)) x -
            unifMeas (coset (z i) (Z i)) x|) := by
        unfold FinProb.expect
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
    _ ≤ P.expect (fun _ => 2 * τ) := P.expect_mono fun i => avg_coset_tvLe hτ (hZW i) (z i) U
    _ = 2 * τ := P.expect_const (2 * τ)

private lemma lem_newprob_irf (P : FinProb) (z : Fin P.N → ℤ) (Z W : Fin P.N → SymNbhd)
    (A : Finset ℤ) {r s0 : ℕ} (hs0 : s0 ≤ r) {τ' : ℝ} (hτ' : 0 ≤ τ')
    (hZW : ∀ i, IsClosedPair τ' (Z i) ((W i).scale2 (r - s0))) :
    let ext := P.extend Z
    let z' : Fin ext.1.N → ℤ := fun j => z (ext.2.1 j) + ext.2.2 j
    let W' : Fin P.N → SymNbhd := fun i => (W i).scale2 (r - s0)
    ∑ s ∈ Finset.range (r + 1),
        ext.1.expect (fun j => (cosetDens ((2 : ℤ) ^ s * z' j) ((W' (ext.2.1 j)).scale2 s) A) ^ 2) ≥
      ∑ s ∈ Finset.range (r + 1),
        P.expect (fun i => (cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A) ^ 2) +
      ext.1.expect (fun j =>
        (cosetDens ((2 : ℤ) ^ s0 * z' j) ((W (ext.2.1 j)).scale2 r) A -
          cosetDens ((2 : ℤ) ^ s0 * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s0) A) ^ 2) -
      4 * τ' * ((r + 1 : ℕ) : ℝ) := by
  intro ext z' W'
  have hstep : ∀ s : ℕ,
      ext.1.expect (fun j => (cosetDens ((2 : ℤ) ^ s * z' j) ((W' (ext.2.1 j)).scale2 s) A) ^ 2) ≥
      P.expect (fun i => (cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A) ^ 2) +
      ext.1.expect (fun j =>
        (cosetDens ((2 : ℤ) ^ s * z' j) ((W' (ext.2.1 j)).scale2 s) A -
          cosetDens ((2 : ℤ) ^ s * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s) A) ^ 2) -
      4 * τ' := by
    intro s
    have hmean_diff : ∀ i : Fin P.N,
        |((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, cosetDens ((2 : ℤ) ^ s * (z i + y)) ((W' i).scale2 s) A -
          cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A| ≤ 2 * τ' := by
      intro i
      have htv := tvLe_pushScale2 s (avg_coset_tvLe hτ' (hZW i) (z i))
      have heval := tvLe_eval htv A
      have hL : ∑ x ∈ A, pushScale2 s (fun x => ((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, unifMeas (coset (z i + y) (W' i)) x) x =
          ((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, cosetDens ((2 : ℤ) ^ s * (z i + y)) ((W' i).scale2 s) A := by
        have hpush_lin : ∀ x, pushScale2 s (fun u => ((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, unifMeas (coset (z i + y) (W' i)) u) x =
            ((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, pushScale2 s (unifMeas (coset (z i + y) (W' i))) x := by
          intro x; unfold pushScale2; split_ifs <;> simp
        simp_rw [hpush_lin, ← unifMeas_scale2Fin, scale2Fin_coset]
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun y _ => (cosetDens_eq_sum _ _ A).symm
      have hR : ∑ x ∈ A, pushScale2 s (fun x => unifMeas (coset (z i) (Z i)) x) x =
          cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A := by
        simp_rw [← unifMeas_scale2Fin, scale2Fin_coset]
        exact (cosetDens_eq_sum _ _ A).symm
      rwa [hL, hR] at heval
    have hvar : ext.1.expect (fun j =>
        (cosetDens ((2 : ℤ) ^ s * z' j) ((W' (ext.2.1 j)).scale2 s) A -
          cosetDens ((2 : ℤ) ^ s * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s) A) ^ 2) =
        ext.1.expect (fun j => (cosetDens ((2 : ℤ) ^ s * z' j) ((W' (ext.2.1 j)).scale2 s) A) ^ 2) -
        P.expect (fun i => (cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A) ^ 2) +
        P.expect (fun i => 2 * cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A *
          (cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A -
            ((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, cosetDens ((2 : ℤ) ^ s * (z i + y)) ((W' i).scale2 s) A)) := by
      have h1 := P.extend_expect Z (fun i y =>
        (cosetDens ((2 : ℤ) ^ s * (z i + y)) ((W' i).scale2 s) A -
          cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A) ^ 2)
      have h2 := P.extend_expect Z (fun i y =>
        (cosetDens ((2 : ℤ) ^ s * (z i + y)) ((W' i).scale2 s) A) ^ 2)
      change ext.1.expect (fun j =>
        (cosetDens ((2 : ℤ) ^ s * (z (ext.2.1 j) + ext.2.2 j)) ((W' (ext.2.1 j)).scale2 s) A -
          cosetDens ((2 : ℤ) ^ s * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s) A) ^ 2) = _
      rw [h1]
      change _ = ext.1.expect (fun j =>
        (cosetDens ((2 : ℤ) ^ s * (z (ext.2.1 j) + ext.2.2 j)) ((W' (ext.2.1 j)).scale2 s) A) ^ 2) - _ + _
      rw [h2, ← P.expect_sub, ← P.expect_add]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      congr 1
      set μ := cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A
      set f : ℤ → ℝ := fun y => cosetDens ((2 : ℤ) ^ s * (z i + y)) ((W' i).scale2 s) A
      have hZpos : ((Z i).set.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Z i).card_pos.ne'
      have hsq : ∀ y ∈ (Z i).set, (f y - μ) ^ 2 = (f y) ^ 2 - 2 * μ * f y + μ ^ 2 := fun _ _ => by ring
      rw [Finset.sum_congr rfl hsq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      field_simp; ring
    have herr : P.expect (fun i => 2 * cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A *
        (cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A -
          ((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, cosetDens ((2 : ℤ) ^ s * (z i + y)) ((W' i).scale2 s) A)) ≤
        4 * τ' := by
      calc P.expect _
          ≤ P.expect (fun _ => 4 * τ') := P.expect_mono fun i => by
            have h0 := cosetDens_nonneg ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A
            have h1 := cosetDens_le_one ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A
            have hd := hmean_diff i
            have hd' : cosetDens ((2 : ℤ) ^ s * z i) ((Z i).scale2 s) A -
                ((Z i).set.card : ℝ)⁻¹ * ∑ y ∈ (Z i).set, cosetDens ((2 : ℤ) ^ s * (z i + y)) ((W' i).scale2 s) A ≤ 2 * τ' := by
              rw [abs_sub_comm] at hd; exact (le_abs_self _).trans hd
            nlinarith
        _ = 4 * τ' := P.expect_const (4 * τ')
    linarith
  have hsum_all := Finset.sum_le_sum (s := Finset.range (r + 1)) (fun s _ => hstep s)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_all
  have hs0_mem : s0 ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
  have hvar_ge : ext.1.expect (fun j =>
      (cosetDens ((2 : ℤ) ^ s0 * z' j) ((W (ext.2.1 j)).scale2 r) A -
        cosetDens ((2 : ℤ) ^ s0 * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s0) A) ^ 2) ≤
      ∑ s ∈ Finset.range (r + 1), ext.1.expect (fun j =>
        (cosetDens ((2 : ℤ) ^ s * z' j) ((W' (ext.2.1 j)).scale2 s) A -
          cosetDens ((2 : ℤ) ^ s * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s) A) ^ 2) := by
    have hscale_eq : ∀ i, (W' i).scale2 s0 = (W i).scale2 r := fun i => by
      dsimp only [W', SymNbhd.scale2]
      congr 1
      ext x
      simp only [scale2Fin, Finset.mem_image]
      constructor
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        refine ⟨y, hy, ?_⟩
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hs0]
      · rintro ⟨y, hy, rfl⟩
        refine ⟨(2 : ℤ) ^ (r - s0) * y, ⟨y, hy, rfl⟩, ?_⟩
        rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hs0]
    have hterm_eq : ext.1.expect (fun j =>
        (cosetDens ((2 : ℤ) ^ s0 * z' j) ((W (ext.2.1 j)).scale2 r) A -
          cosetDens ((2 : ℤ) ^ s0 * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s0) A) ^ 2) =
        ext.1.expect (fun j =>
          (cosetDens ((2 : ℤ) ^ s0 * z' j) ((W' (ext.2.1 j)).scale2 s0) A -
            cosetDens ((2 : ℤ) ^ s0 * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s0) A) ^ 2) := by
      unfold FinProb.expect
      refine Finset.sum_congr rfl fun j _ => by dsimp only; rw [hscale_eq]
    rw [hterm_eq]
    exact Finset.single_le_sum
      (f := fun s => ext.1.expect (fun j =>
        (cosetDens ((2 : ℤ) ^ s * z' j) ((W' (ext.2.1 j)).scale2 s) A -
          cosetDens ((2 : ℤ) ^ s * z (ext.2.1 j)) ((Z (ext.2.1 j)).scale2 s) A) ^ 2))
      (fun s _ => ext.1.expect_nonneg fun _ => sq_nonneg _) hs0_mem
  linarith

/- ### Module 3D: Plünnecke bound, Bogolyubov pullback system, and `lem_gs` -/

private lemma pluennecke_sub_bound {A : Finset ℤ} {K : ℝ} (hA : A.Nonempty)
    (hdbl : ((A - A).card : ℝ) ≤ K * (A.card : ℝ)) (m n : ℕ) :
    (((m • A - n • A).card : ℝ)) ≤ K ^ (m + n) * (A.card : ℝ) := by
  have hpr := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hA A m n
  have hR : (((m • A - n • A).card : ℝ)) ≤
      (((A - A).card : ℝ) / (A.card : ℝ)) ^ (m + n) * (A.card : ℝ) := by
    have hcast := (NNRat.cast_le (K := ℝ)).mpr hpr
    simpa [NNRat.cast_mul, NNRat.cast_pow, NNRat.cast_div, NNRat.cast_natCast] using hcast
  have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
  have hdiv : ((A - A).card : ℝ) / (A.card : ℝ) ≤ K := (div_le_iff₀ hApos).mpr hdbl
  have hpow : (((A - A).card : ℝ) / (A.card : ℝ)) ^ (m + n) ≤ K ^ (m + n) :=
    pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hApos.le) hdiv (m + n)
  exact hR.trans (mul_le_mul_of_nonneg_right hpow hApos.le)

private lemma bogolyubov_pullback_system {P : ℕ} [NeZero P] {A'' : Finset ℤ} {φ : ℤ → ZMod P}
    (hA'' : A''.Nonempty) (hiso : IsFreiman6Iso A'' φ) :
    let α : ℝ := (A''.card : ℝ) / (P : ℝ)
    ∃ (B : Sys) (hB : B.IsFinite) (gcard : ℕ),
      (gcard : ℝ) ≤ 4 / α ^ 2 ∧
      B.HasDim (3 * gcard) ∧
      (B.toSymNbhd hB 0).set ⊆ (A'' + A'') - (A'' + A'') ∧
      (P : ℝ) ≤ (16 : ℝ) ^ gcard * ((B.toSymNbhd hB 0).set.card : ℝ) := by
  classical
  intro α
  obtain ⟨a0, ha0⟩ := hA''
  have hφ_inj : Set.InjOn φ (A'' : Set ℤ) := by
    intro x hx y hy hxy
    have hx' : x ∈ A'' := Finset.mem_coe.mp hx
    have hy' : y ∈ A'' := Finset.mem_coe.mp hy
    have hsum6 : φ x + φ x + φ x + φ x + φ x + φ x = φ y + φ y + φ y + φ y + φ y + φ y := by
      simp [hxy]
    have h6 := (hiso x hx' x hx' x hx' x hx' x hx' x hx' y hy' y hy' y hy' y hy' y hy' y hy').mpr hsum6
    omega
  let S0 : Finset (ZMod P) := A''.image φ
  have hS0_card : S0.card = A''.card := Finset.card_image_of_injOn hφ_inj
  have hS0_ne : S0.Nonempty := ⟨φ a0, Finset.mem_image_of_mem φ ha0⟩
  obtain ⟨Γ, hΓ_card, hW0, hWneg, hWadd, hWsub, hWsize, hWcov⟩ := bogolyubov_zmod hS0_ne
  let W : ℕ → Finset (ZMod P) := fun i =>
    Finset.univ.filter (fun x => ∀ r ∈ Γ, zmodDist P (r * x) < 1 / (16 * (2 : ℝ) ^ i))
  have hΓ_card' : (Γ.card : ℝ) ≤ 4 / α ^ 2 := by
    simpa only [α, hS0_card] using hΓ_card
  let Φ2 : Finset ℤ := (A'' + A'') - (A'' + A'')
  have hΦ2_rep : ∀ x ∈ Φ2, ∃ a1 ∈ A'', ∃ a2 ∈ A'', ∃ a3 ∈ A'', ∃ a4 ∈ A'',
      x = (a1 + a2) - (a3 + a4) := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hx
    obtain ⟨a1, h1, a2, h2, rfl⟩ := Finset.mem_add.mp hu
    obtain ⟨a3, h3, a4, h4, rfl⟩ := Finset.mem_add.mp hv
    exact ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩
  let φ2 : ℤ → ZMod P := fun x =>
    if hx : x ∈ Φ2 then
      let a1 := Classical.choose (hΦ2_rep x hx)
      let h1 := Classical.choose_spec (hΦ2_rep x hx)
      let a2 := Classical.choose h1.2
      let h2 := Classical.choose_spec h1.2
      let a3 := Classical.choose h2.2
      let h3 := Classical.choose_spec h2.2
      let a4 := Classical.choose h3.2
      (φ a1 + φ a2) - (φ a3 + φ a4)
    else 0
  have hφ2_eq : ∀ {x a1 a2 a3 a4 : ℤ}, a1 ∈ A'' → a2 ∈ A'' → a3 ∈ A'' → a4 ∈ A'' →
      x = (a1 + a2) - (a3 + a4) → φ2 x = (φ a1 + φ a2) - (φ a3 + φ a4) := by
    intro x a1 a2 a3 a4 h1 h2 h3 h4 hxeq
    have hx : x ∈ Φ2 := Finset.mem_sub.mpr
      ⟨a1 + a2, Finset.add_mem_add h1 h2, a3 + a4, Finset.add_mem_add h3 h4, hxeq.symm⟩
    simp only [φ2, dif_pos hx]
    set b1 := Classical.choose (hΦ2_rep x hx)
    set hb1 := Classical.choose_spec (hΦ2_rep x hx)
    set b2 := Classical.choose hb1.2
    set hb2 := Classical.choose_spec hb1.2
    set b3 := Classical.choose hb2.2
    set hb3 := Classical.choose_spec hb2.2
    set b4 := Classical.choose hb3.2
    set hb4 := Classical.choose_spec hb3.2
    have h6Z : b1 + b2 + a3 + a4 + a0 + a0 = a1 + a2 + b3 + b4 + a0 + a0 := by
      have e1 := hb4.2; omega
    have h6M := (hiso b1 hb1.1 b2 hb2.1 a3 h3 a4 h4 a0 ha0 a0 ha0
      a1 h1 a2 h2 b3 hb3.1 b4 hb4.1 a0 ha0 a0 ha0).mp h6Z
    have hcancel : φ b1 + φ b2 + φ a3 + φ a4 = φ a1 + φ a2 + φ b3 + φ b4 := by
      linear_combination h6M
    linear_combination hcancel
  have hΦ2_zero : (0 : ℤ) ∈ Φ2 :=
    Finset.mem_sub.mpr ⟨a0 + a0, Finset.add_mem_add ha0 ha0, a0 + a0, Finset.add_mem_add ha0 ha0, sub_self _⟩
  have hφ2_zero : φ2 0 = 0 := by
    rw [hφ2_eq ha0 ha0 ha0 ha0 (by ring)]; ring
  have hΦ2_neg : ∀ x ∈ Φ2, -x ∈ Φ2 := by
    intro x hx
    obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩ := hΦ2_rep x hx
    exact Finset.mem_sub.mpr ⟨a3 + a4, Finset.add_mem_add h3 h4, a1 + a2, Finset.add_mem_add h1 h2, by ring⟩
  have hφ2_neg : ∀ x ∈ Φ2, φ2 (-x) = -φ2 x := by
    intro x hx
    obtain ⟨a1, h1, a2, h2, a3, h3, a4, h4, rfl⟩ := hΦ2_rep x hx
    rw [hφ2_eq h3 h4 h1 h2 (by ring), hφ2_eq h1 h2 h3 h4 rfl]; ring
  have hφ2_sum_iff : ∀ x ∈ Φ2, ∀ y ∈ Φ2, ∀ z ∈ Φ2,
      x + y = z ↔ φ2 x + φ2 y = φ2 z := by
    intro x hx y hy z hz
    obtain ⟨a1, ha1, a2, ha2, a3, ha3, a4, ha4, rfl⟩ := hΦ2_rep x hx
    obtain ⟨b1, hb1, b2, hb2, b3, hb3, b4, hb4, rfl⟩ := hΦ2_rep y hy
    obtain ⟨c1, hc1, c2, hc2, c3, hc3, c4, hc4, rfl⟩ := hΦ2_rep z hz
    rw [hφ2_eq ha1 ha2 ha3 ha4 rfl, hφ2_eq hb1 hb2 hb3 hb4 rfl, hφ2_eq hc1 hc2 hc3 hc4 rfl]
    have hZiff : (a1 + a2 - (a3 + a4)) + (b1 + b2 - (b3 + b4)) = c1 + c2 - (c3 + c4) ↔
        a1 + a2 + b1 + b2 + c3 + c4 = c1 + c2 + a3 + a4 + b3 + b4 := by omega
    have hMiff : (φ a1 + φ a2 - (φ a3 + φ a4)) + (φ b1 + φ b2 - (φ b3 + φ b4)) =
        φ c1 + φ c2 - (φ c3 + φ c4) ↔
        φ a1 + φ a2 + φ b1 + φ b2 + φ c3 + φ c4 =
        φ c1 + φ c2 + φ a3 + φ a4 + φ b3 + φ b4 := by
      constructor <;> intro h <;> linear_combination h
    rw [hZiff, hMiff]
    exact hiso a1 ha1 a2 ha2 b1 hb1 b2 hb2 c3 hc3 c4 hc4
      c1 hc1 c2 hc2 a3 ha3 a4 ha4 b3 hb3 b4 hb4
  have hφ2_inj : Set.InjOn φ2 (Φ2 : Set ℤ) := by
    intro x hx y hy hxy
    have hx' : x ∈ Φ2 := Finset.mem_coe.mp hx
    have hy' : y ∈ Φ2 := Finset.mem_coe.mp hy
    have h := (hφ2_sum_iff x hx' 0 hΦ2_zero y hy').mpr (by rw [hφ2_zero, add_zero, hxy])
    omega
  have hφ2_surj : ∀ w ∈ (S0 + S0) - (S0 + S0), ∃ x ∈ Φ2, φ2 x = w := by
    intro w hw
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hw
    obtain ⟨u1, hu1, u2, hu2, rfl⟩ := Finset.mem_add.mp hu
    obtain ⟨v1, hv1, v2, hv2, rfl⟩ := Finset.mem_add.mp hv
    obtain ⟨a1, ha1, rfl⟩ := Finset.mem_image.mp hu1
    obtain ⟨a2, ha2, rfl⟩ := Finset.mem_image.mp hu2
    obtain ⟨a3, ha3, rfl⟩ := Finset.mem_image.mp hv1
    obtain ⟨a4, ha4, rfl⟩ := Finset.mem_image.mp hv2
    refine ⟨(a1 + a2) - (a3 + a4),
      Finset.mem_sub.mpr ⟨a1 + a2, Finset.add_mem_add ha1 ha2, a3 + a4, Finset.add_mem_add ha3 ha4, rfl⟩,
      hφ2_eq ha1 ha2 ha3 ha4 rfl⟩
  have hW_mono : ∀ i : ℕ, W (i + 1) ⊆ W i := by
    intro i x hx
    exact hWadd i (by simpa [W] using Finset.add_mem_add hx (hW0 (i + 1)))
  have hW_sub0 : ∀ i : ℕ, W i ⊆ W 0 := by
    intro i
    induction i with
    | zero => exact Subset.rfl
    | succ i ih => exact (hW_mono i).trans ih
  let Bf : ℕ → Finset ℤ := fun i => Φ2.filter (fun x => φ2 x ∈ W i)
  have hBf_zero : ∀ i, (0 : ℤ) ∈ Bf i := fun i =>
    Finset.mem_filter.mpr ⟨hΦ2_zero, by rw [hφ2_zero]; exact hW0 i⟩
  have hBf_neg : ∀ i, ∀ x ∈ Bf i, -x ∈ Bf i := fun i x hx => by
    obtain ⟨hxΦ, hxW⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hΦ2_neg x hxΦ, by rw [hφ2_neg x hxΦ]; exact hWneg i _ hxW⟩
  have hBf_add : ∀ i, Bf (i + 1) + Bf (i + 1) ⊆ Bf i := by
    intro i s hs
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨hxΦ, hxW⟩ := Finset.mem_filter.mp hx
    obtain ⟨hyΦ, hyW⟩ := Finset.mem_filter.mp hy
    have hsumW : φ2 x + φ2 y ∈ W i := hWadd i (Finset.add_mem_add hxW hyW)
    obtain ⟨z, hzΦ, hzEq⟩ := hφ2_surj (φ2 x + φ2 y) (hWsub (hW_sub0 i hsumW))
    have hxyz : x + y = z := (hφ2_sum_iff x hxΦ y hyΦ z hzΦ).mpr hzEq.symm
    rw [hxyz]
    exact Finset.mem_filter.mpr ⟨hzΦ, by rwa [hzEq]⟩
  let B : Sys :=
    { set := fun i => (Bf i : Set ℤ)
      zero_mem := fun i => Finset.mem_coe.mpr (hBf_zero i)
      neg_mem := fun i x hx => Finset.mem_coe.mpr (hBf_neg i x (Finset.mem_coe.mp hx))
      add_subset := fun i x hx => by
        rw [← Finset.coe_add] at hx
        exact Finset.mem_coe.mpr (hBf_add i (Finset.mem_coe.mp hx)) }
  have hB : B.IsFinite := (Bf 0).finite_toSet
  have hB_dim : B.HasDim (3 * Γ.card) := by
    intro i
    obtain ⟨T, hTW, hTcard, hTcov⟩ := hWcov i
    let Tlift : Finset ℤ := Φ2.filter (fun x => φ2 x ∈ T)
    have hTlift_card : Tlift.card ≤ 2 ^ (3 * Γ.card) := by
      have hle : Tlift.card ≤ T.card := by
        refine Finset.card_le_card_of_injOn φ2 (fun x hx => ?_) (fun x1 h1 x2 h2 h => ?_)
        · exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
        · exact hφ2_inj (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).1)
            (Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).1) h
      calc Tlift.card ≤ T.card := hle
        _ ≤ 8 ^ Γ.card := hTcard
        _ = 2 ^ (3 * Γ.card) := by rw [pow_mul]; norm_num
    have hTlift_cov : B.set i ⊆ (Tlift : Set ℤ) + B.set (i + 2) := by
      intro x hx
      obtain ⟨hxΦ, hxW⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      obtain ⟨tm, htm, wm, hwm, hsum⟩ := Finset.mem_add.mp (hTcov hxW)
      obtain ⟨t, htΦ, htEq⟩ := hφ2_surj tm (hWsub (hW_sub0 i (hTW htm)))
      obtain ⟨w, hwΦ, hwEq⟩ := hφ2_surj wm (hWsub (hW_sub0 (i + 2) hwm))
      have htwx : t + w = x := (hφ2_sum_iff t htΦ w hwΦ x hxΦ).mpr (by rw [htEq, hwEq, hsum])
      exact Set.mem_add.mpr ⟨t, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨htΦ, by rwa [htEq]⟩),
        w, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hwΦ, by rwa [hwEq]⟩), htwx⟩
    have hsub_diff : B.set (i + 2) - B.set (i + 2) ⊆ B.set (i + 1) := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.mp hx
      have hnb : -b ∈ B.set (i + 2) := B.neg_mem (i + 2) b hb
      rw [sub_eq_add_neg]
      exact B.add_subset (i + 1) (Set.mem_add.mpr ⟨a, ha, -b, hnb, rfl⟩)
    calc covFlat (B.set i) (B.set (i + 1))
        ≤ covFlat (B.set i) (B.set (i + 2) - B.set (i + 2)) := covFlat_mono Set.Subset.rfl hsub_diff
      _ ≤ covNum (B.set i) (B.set (i + 2)) := covFlat_le_covNum _ _
      _ ≤ (Tlift.card : ℕ∞) := covNum_le_of_cover Tlift hTlift_cov
      _ ≤ ((2 ^ (3 * Γ.card) : ℕ) : ℕ∞) := ENat.natCast_le_natCast.mpr hTlift_card
  have hB0_eq : (B.toSymNbhd hB 0).set = Bf 0 := by
    ext x; simp [Sys.toSymNbhd, B]
  have hB0_card : (Bf 0).card = (W 0).card := by
    refine Finset.card_bij (fun x _ => φ2 x) ?_ ?_ ?_
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x1 h1 x2 h2 h
      exact hφ2_inj (Finset.mem_coe.mpr (Finset.mem_filter.mp h1).1)
        (Finset.mem_coe.mpr (Finset.mem_filter.mp h2).1) h
    · intro w hw
      obtain ⟨x, hxΦ, hxEq⟩ := hφ2_surj w (hWsub hw)
      exact ⟨x, Finset.mem_filter.mpr ⟨hxΦ, by rwa [hxEq]⟩, hxEq⟩
  refine ⟨B, hB, Γ.card, hΓ_card', hB_dim, ?_, ?_⟩
  · rw [hB0_eq]; exact Finset.filter_subset _ _
  · rw [hB0_eq, hB0_card]; exact hWsize

private lemma lem_gs_cov_bound {k gcard m m' Pmod : ℕ} {A' A'' S0_set S : Finset ℤ}
    {B : Sys} (hB : B.IsFinite) {τ : ℝ} {a0 : ℤ}
    (hk : 2 ≤ k) (hτ0 : 0 < τ) (hA'ne : A'.Nonempty)
    (hA'diff_k : ((A' - A').card : ℝ) ≤ (k : ℝ) ^ 92 * (A'.card : ℝ))
    (hA''card : A'.card ≤ 7 * A''.card)
    (hA''_le_P : (A''.card : ℝ) ≤ (Pmod : ℝ))
    (hP_B0 : (Pmod : ℝ) ≤ (16 : ℝ) ^ gcard * ((B.toSymNbhd hB 0).set.card : ℝ))
    (hgcard_k : gcard ≤ k ^ 2226)
    (hBdim : B.HasDim (3 * gcard))
    (hB0_sub22 : (B.toSymNbhd hB 0).set ⊆ 2 • A' - 2 • A')
    (hS0_sub33 : S0_set ⊆ 3 • A' - 3 • A')
    (hS_eq : S = S0_set.image (· + a0))
    (hm_def : m = Nat.clog 2 (Nat.ceil (2208 * (k : ℝ) / τ)) + 1)
    (hm'_def : m' = Nat.clog 2 (Nat.ceil (2 * ((3 * gcard : ℕ) : ℝ) / τ)) + 2) :
    ∃ D : ℕ,
      D ≤ k ^ 2242 * (Nat.clog 2 (Nat.ceil (1 / τ)) + 10) ∧
      covFlat (S : Set ℤ) ((B.dilate (m + 2 + m')).set 0) ≤ ((2 ^ D : ℕ) : ℕ∞) := by
  classical
  let d : ℕ := 3 * gcard
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hd_le : d ≤ k ^ 2228 := by
    have h34 : 3 ≤ k ^ 2 := by nlinarith
    calc d = 3 * gcard := rfl
      _ ≤ k ^ 2 * k ^ 2226 := Nat.mul_le_mul h34 hgcard_k
      _ = k ^ 2228 := by rw [← pow_add]
  let B2sys : Sys := B.dilate 2
  have hB2fin : B2sys.IsFinite := B.dilate_isFinite 2 hB
  let B2nb : SymNbhd := B2sys.toSymNbhd hB2fin 0
  have hB2_sub0 : B2nb.set ⊆ (B.toSymNbhd hB 0).set := by
    intro x hx
    have hx' : x ∈ B.set 2 := by simpa [B2nb, B2sys, Sys.toSymNbhd, Sys.dilate] using hx
    exact (Set.Finite.mem_toFinset _).mpr (B.antitone (by omega) hx')
  have hB2_card_lb : ((B.toSymNbhd hB 0).set.card : ℝ) ≤ (2 : ℝ) ^ (2 * d) * (B2nb.set.card : ℝ) := by
    have hc1 : covNum (B.set 0) (B.set 1) ≤ ((2 ^ d : ℕ) : ℕ∞) := (covNum_le_covFlat _ _).trans (hBdim 0)
    have hc2 : covNum (B.set 1) (B.set 2) ≤ ((2 ^ d : ℕ) : ℕ∞) := (covNum_le_covFlat _ _).trans (hBdim 1)
    have hc02 : covNum (B.set 0) (B.set 2) ≤ ((2 ^ (2 * d) : ℕ) : ℕ∞) := by
      calc covNum (B.set 0) (B.set 2)
          ≤ covNum (B.set 0) (B.set 1) * covNum (B.set 1) (B.set 2) := covNum_chain (fun _ => B.nonempty 1)
        _ ≤ ((2 ^ d : ℕ) : ℕ∞) * ((2 ^ d : ℕ) : ℕ∞) := mul_le_mul' hc1 hc2
        _ = ((2 ^ (2 * d) : ℕ) : ℕ∞) := by rw [← Nat.cast_mul, ← pow_add, two_mul]
    have hcard_enat : ((B.toSymNbhd hB 0).set.card : ℕ∞) ≤ ((2 ^ (2 * d) * B2nb.set.card : ℕ) : ℕ∞) := by
      have h1 := covNum_card_le (X := (B.toSymNbhd hB 0).set) (Y := B2nb.set) (fun _ => B2nb.nonempty)
      have hB2coe : (B2nb.set : Set ℤ) = B.set 2 := by
        simpa [B2nb, B2sys, Sys.dilate] using B2sys.coe_toSymNbhd hB2fin 0
      rw [B.coe_toSymNbhd hB 0, hB2coe] at h1
      rw [Nat.cast_mul]
      exact h1.trans (mul_le_mul' hc02 le_rfl)
    exact_mod_cast ENat.natCast_le_natCast.mp hcard_enat
  have hS_B2_le : ((S + B2nb.set).card : ℝ) ≤ 7 * (k : ℝ) ^ 920 * (2 : ℝ) ^ (10 * gcard) * (B2nb.set.card : ℝ) := by
    have hSB2_eq : (S + B2nb.set).card = (S0_set + B2nb.set).card := by
      refine Finset.card_bij (fun x _ => x - a0) ?_ ?_ ?_
      · intro x hx
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
        rw [hS_eq] at hu
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
        have : u' + a0 + v - a0 = u' + v := by ring
        rw [this]; exact Finset.add_mem_add hu' hv
      · intro _ _ _ _ h; omega
      · intro y hy
        obtain ⟨u', hu', v, hv, rfl⟩ := Finset.mem_add.mp hy
        exact ⟨(u' + a0) + v, Finset.add_mem_add (by rw [hS_eq]; exact Finset.mem_image_of_mem _ hu') hv, by ring⟩
    have hS0B2_sub : S0_set + B2nb.set ⊆ 5 • A' - 5 • A' := by
      intro x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨p1, hp1, q1, hq1, rfl⟩ := Finset.mem_sub.mp (hS0_sub33 hu)
      obtain ⟨p2, hp2, q2, hq2, rfl⟩ := Finset.mem_sub.mp (hB0_sub22 (hB2_sub0 hv))
      have h5eq : 5 • A' = 3 • A' + 2 • A' := by rw [← add_nsmul]
      rw [h5eq]
      exact Finset.mem_sub.mpr ⟨p1 + p2, Finset.add_mem_add hp1 hp2, q1 + q2, Finset.add_mem_add hq1 hq2, by ring⟩
    have h55 := pluennecke_sub_bound hA'ne hA'diff_k 5 5
    have hA'_le_B2 : (A'.card : ℝ) ≤ 7 * (2 : ℝ) ^ (10 * gcard) * (B2nb.set.card : ℝ) := by
      have hA'7 : (A'.card : ℝ) ≤ 7 * (A''.card : ℝ) := by exact_mod_cast hA''card
      have h16eq : (16 : ℝ) ^ gcard * (2 : ℝ) ^ (2 * d) = (2 : ℝ) ^ (10 * gcard) := by
        dsimp only [d]
        have h16 : (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
        rw [h16, ← pow_mul, ← pow_add]; congr 1; omega
      calc (A'.card : ℝ) ≤ 7 * (A''.card : ℝ) := hA'7
        _ ≤ 7 * (Pmod : ℝ) := by linarith
        _ ≤ 7 * ((16 : ℝ) ^ gcard * ((B.toSymNbhd hB 0).set.card : ℝ)) := by linarith
        _ ≤ 7 * ((16 : ℝ) ^ gcard * ((2 : ℝ) ^ (2 * d) * (B2nb.set.card : ℝ))) := by gcongr
        _ = 7 * ((16 : ℝ) ^ gcard * (2 : ℝ) ^ (2 * d)) * (B2nb.set.card : ℝ) := by ring
        _ = 7 * (2 : ℝ) ^ (10 * gcard) * (B2nb.set.card : ℝ) := by rw [h16eq]
    rw [hSB2_eq]
    calc ((S0_set + B2nb.set).card : ℝ) ≤ ((5 • A' - 5 • A').card : ℝ) := by
          exact_mod_cast Finset.card_le_card hS0B2_sub
      _ ≤ ((k : ℝ) ^ 92) ^ (5 + 5) * (A'.card : ℝ) := h55
      _ = (k : ℝ) ^ 920 * (A'.card : ℝ) := by ring
      _ ≤ (k : ℝ) ^ 920 * (7 * (2 : ℝ) ^ (10 * gcard) * (B2nb.set.card : ℝ)) := by gcongr
      _ = 7 * (k : ℝ) ^ 920 * (2 : ℝ) ^ (10 * gcard) * (B2nb.set.card : ℝ) := by ring
  let D0 : ℕ := 3 + 920 * k + 10 * gcard
  have hcov_B0 : covFlat (S : Set ℤ) (B.set 0) ≤ ((2 ^ D0 : ℕ) : ℕ∞) := by
    have h7k : 7 * (k : ℝ) ^ 920 * (2 : ℝ) ^ (10 * gcard) ≤ (2 : ℝ) ^ D0 := by
      have hk2k : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
      have h7 : (7 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
      have h920 : (k : ℝ) ^ 920 ≤ (2 : ℝ) ^ (920 * k) := by
        calc (k : ℝ) ^ 920 ≤ ((2 : ℝ) ^ k) ^ 920 := pow_le_pow_left₀ hk_pos.le hk2k 920
          _ = (2 : ℝ) ^ (920 * k) := by rw [← pow_mul, mul_comm]
      calc 7 * (k : ℝ) ^ 920 * (2 : ℝ) ^ (10 * gcard)
          ≤ (2 : ℝ) ^ 3 * (2 : ℝ) ^ (920 * k) * (2 : ℝ) ^ (10 * gcard) := by gcongr
        _ = (2 : ℝ) ^ D0 := by dsimp only [D0]; rw [← pow_add, ← pow_add]
    have hnat_mul : (S + B2nb.set).card ≤ 2 ^ D0 * B2nb.set.card := by
      have hR : ((S + B2nb.set).card : ℝ) ≤ ((2 ^ D0 * B2nb.set.card : ℕ) : ℝ) := by
        push_cast
        exact hS_B2_le.trans (mul_le_mul_of_nonneg_right h7k (Nat.cast_nonneg _))
      exact_mod_cast hR
    have hruzsa : covNum (S : Set ℤ) ((B2nb.set - B2nb.set : Finset ℤ) : Set ℤ) ≤ ((2 ^ D0 : ℕ) : ℕ∞) := by
      rw [Finset.coe_sub]
      exact covNum_ruzsa_le_of_mul_le B2nb.nonempty hnat_mul
    have hB2_4 : ((B2nb.set - B2nb.set : Finset ℤ) : Set ℤ) - ((B2nb.set - B2nb.set : Finset ℤ) : Set ℤ) ⊆ B.set 0 := by
      have hB2_1 : ((B2nb.set - B2nb.set : Finset ℤ) : Set ℤ) ⊆ B.set 1 := by
        intro x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp (Finset.mem_coe.mp hx)
        have ha2 : a ∈ B.set 2 := by simpa [B2nb, B2sys, Sys.toSymNbhd, Sys.dilate] using ha
        have hb2 : -b ∈ B.set 2 := B.neg_mem 2 b (by simpa [B2nb, B2sys, Sys.toSymNbhd, Sys.dilate] using hb)
        rw [sub_eq_add_neg]
        exact B.add_subset 1 (Set.mem_add.mpr ⟨a, ha2, -b, hb2, rfl⟩)
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_sub.mp hx
      have ha1 := hB2_1 ha
      have hb1 := B.neg_mem 1 b (hB2_1 hb)
      rw [sub_eq_add_neg]
      exact B.add_subset 0 (Set.mem_add.mpr ⟨a, ha1, -b, hb1, rfl⟩)
    calc covFlat (S : Set ℤ) (B.set 0)
        ≤ covFlat (S : Set ℤ) (((B2nb.set - B2nb.set : Finset ℤ) : Set ℤ) - ((B2nb.set - B2nb.set : Finset ℤ) : Set ℤ)) :=
          covFlat_mono Set.Subset.rfl hB2_4
      _ ≤ covNum (S : Set ℤ) ((B2nb.set - B2nb.set : Finset ℤ) : Set ℤ) := covFlat_le_covNum _ _
      _ ≤ ((2 ^ D0 : ℕ) : ℕ∞) := hruzsa
  let D : ℕ := D0 + (m + 2 + m' + 1) * d
  refine ⟨D, ?_, ?_⟩
  · let Lτ : ℕ := Nat.clog 2 (Nat.ceil (1 / τ))
    have hceil_inv : (1 : ℝ) / τ ≤ (2 : ℝ) ^ Lτ := by
      have h1 : (1 : ℝ) / τ ≤ (Nat.ceil (1 / τ) : ℝ) := Nat.le_ceil _
      have h2 : Nat.ceil (1 / τ) ≤ 2 ^ Lτ := Nat.le_pow_clog (by norm_num) _
      exact h1.trans (by exact_mod_cast h2)
    have hm_le : m ≤ 20 * k + Lτ + 2 := by
      have hceil_le : Nat.ceil (2208 * (k : ℝ) / τ) ≤ 2 ^ (20 * k + Lτ) := by
        apply Nat.ceil_le.mpr
        have h2208 : 2208 * (k : ℝ) ≤ (2 : ℝ) ^ (20 * k) := by
          have hk2k : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
          have h22 : (2208 : ℝ) ≤ (2 : ℝ) ^ 12 := by norm_num
          have h12k : 12 + k ≤ 20 * k := by omega
          calc 2208 * (k : ℝ) ≤ (2 : ℝ) ^ 12 * (2 : ℝ) ^ k := mul_le_mul h22 hk2k hk_pos.le (by positivity)
            _ = (2 : ℝ) ^ (12 + k) := by rw [← pow_add]
            _ ≤ (2 : ℝ) ^ (20 * k) := pow_le_pow_right₀ (by norm_num) h12k
        have hmul : 2208 * (k : ℝ) / τ = (2208 * (k : ℝ)) * (1 / τ) := by ring
        rw [hmul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
        exact mul_le_mul h2208 hceil_inv (by positivity) (by positivity)
      have hclog := Nat.clog_le_of_le_pow hceil_le
      omega
    have hm'_le : m' ≤ 2300 * k + Lτ + 3 := by
      have hceil_le : Nat.ceil (2 * (d : ℝ) / τ) ≤ 2 ^ (2300 * k + Lτ) := by
        apply Nat.ceil_le.mpr
        have h2d : 2 * (d : ℝ) ≤ (2 : ℝ) ^ (2300 * k) := by
          have hdR : (d : ℝ) ≤ (k : ℝ) ^ 2228 := by exact_mod_cast hd_le
          have hk2k : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
          have h2228 : (k : ℝ) ^ 2228 ≤ (2 : ℝ) ^ (2228 * k) := by
            calc (k : ℝ) ^ 2228 ≤ ((2 : ℝ) ^ k) ^ 2228 := pow_le_pow_left₀ hk_pos.le hk2k 2228
              _ = (2 : ℝ) ^ (2228 * k) := by rw [← pow_mul, mul_comm]
          have hidx : 1 + 2228 * k ≤ 2300 * k := by omega
          calc 2 * (d : ℝ) ≤ (2 : ℝ) ^ 1 * (2 : ℝ) ^ (2228 * k) := by
                have : 2 * (d : ℝ) ≤ 2 * (k : ℝ) ^ 2228 := by linarith
                linarith [mul_le_mul_of_nonneg_left h2228 (by norm_num : (0 : ℝ) ≤ 2)]
            _ = (2 : ℝ) ^ (1 + 2228 * k) := by rw [← pow_add]
            _ ≤ (2 : ℝ) ^ (2300 * k) := pow_le_pow_right₀ (by norm_num) hidx
        have hmul : 2 * (d : ℝ) / τ = (2 * (d : ℝ)) * (1 / τ) := by ring
        rw [hmul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
        exact mul_le_mul h2d hceil_inv (by positivity) (by positivity)
      have hclog := Nat.clog_le_of_le_pow hceil_le
      dsimp only [d] at hclog
      omega
    have hD0_le : D0 ≤ 1000 * k ^ 2226 := by
      have hk0 : 0 < k := Nat.lt_of_lt_of_le (by decide : 0 < 2) hk
      have h1 : 3 ≤ 3 * k ^ 2226 := Nat.le_mul_of_pos_right 3 (Nat.pow_pos hk0)
      have hk1 : 920 * k ≤ 920 * k ^ 2226 :=
        Nat.mul_le_mul_left 920 (by simpa using Nat.pow_le_pow_right hk0 (show 1 ≤ 2226 by decide))
      have h10g : 10 * gcard ≤ 10 * k ^ 2226 := Nat.mul_le_mul_left 10 hgcard_k
      dsimp only [D0]
      calc 3 + 920 * k + 10 * gcard
          ≤ 3 * k ^ 2226 + 920 * k ^ 2226 + 10 * k ^ 2226 := Nat.add_le_add (Nat.add_le_add h1 hk1) h10g
        _ = 933 * k ^ 2226 := by ring
        _ ≤ 1000 * k ^ 2226 := Nat.mul_le_mul_right _ (by omega)
    have hsum_m : m + 2 + m' + 1 ≤ 2320 * k + 2 * Lτ + 8 := by omega
    have h2320 : 2320 * k + 2 * Lτ + 8 ≤ 2320 * k * (Lτ + 10) := by
      have : 1 ≤ k := by omega
      nlinarith
    have hmul_md : (m + 2 + m' + 1) * d ≤ 2320 * k ^ 2229 * (Lτ + 10) := by
      calc (m + 2 + m' + 1) * d
          ≤ (2320 * k * (Lτ + 10)) * k ^ 2228 := Nat.mul_le_mul (hsum_m.trans h2320) hd_le
        _ = 2320 * (k * k ^ 2228) * (Lτ + 10) := by ring
        _ = 2320 * k ^ 2229 * (Lτ + 10) := by rw [← pow_succ']
    have hD0_term : D0 ≤ 1000 * k ^ 2229 * (Lτ + 10) := by
      have hkpow : k ^ 2226 ≤ k ^ 2229 := Nat.pow_le_pow_right (by omega) (by omega)
      have h1 : D0 ≤ 1000 * k ^ 2229 := hD0_le.trans (Nat.mul_le_mul_left 1000 hkpow)
      exact h1.trans (Nat.le_mul_of_pos_right _ (by omega))
    have h3320 : 3320 ≤ k ^ 12 := (show 3320 ≤ 2 ^ 12 by norm_num).trans (Nat.pow_le_pow_left hk 12)
    have hD_sum : D ≤ 3320 * k ^ 2229 * (Lτ + 10) := by
      dsimp only [D]
      calc D0 + (m + 2 + m' + 1) * d
          ≤ 1000 * k ^ 2229 * (Lτ + 10) + 2320 * k ^ 2229 * (Lτ + 10) := Nat.add_le_add hD0_term hmul_md
        _ = 3320 * k ^ 2229 * (Lτ + 10) := by ring
    calc D ≤ 3320 * k ^ 2229 * (Lτ + 10) := hD_sum
      _ ≤ (k ^ 12 * k ^ 2229) * (Lτ + 10) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3320)
      _ = k ^ 2241 * (Lτ + 10) := by rw [← pow_add]
      _ ≤ k ^ 2242 * (Lτ + 10) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
  · calc covFlat (S : Set ℤ) ((B.dilate (m + 2 + m')).set 0)
        ≤ covFlat (S : Set ℤ) (B.set 0) * ((2 ^ ((m + 2 + m' + 1) * d) : ℕ) : ℕ∞) :=
          B.dilate_covFlat hBdim (m + 2 + m') (S : Set ℤ)
      _ ≤ ((2 ^ D0 : ℕ) : ℕ∞) * ((2 ^ ((m + 2 + m' + 1) * d) : ℕ) : ℕ∞) := mul_le_mul' hcov_B0 le_rfl
      _ = ((2 ^ D : ℕ) : ℕ∞) := by dsimp only [D]; rw [← Nat.cast_mul, ← pow_add]

private lemma lem_gs {k : ℕ} {A X : Finset ℤ} {τ : ℝ}
    (hk : 2 ≤ k) (hA : A.Nonempty)
    (hX : (X.card : ℝ) ≤ 2 * (A.card : ℝ))
    (hsum : IsSumming k A X)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2) :
    ∃ (S : Finset ℤ) (P : FinProb) (z : Fin P.N → ℤ)
      (Z : Fin P.N → SymNbhd) (T : Fin P.N → Sys) (hT : ∀ i, (T i).IsFinite)
      (d D : ℕ),
      S.Nonempty ∧
      HereditarilyEnergetic (1 / (k : ℝ) ^ 1104) S ∧
      (A.card : ℝ) ≤ (k : ℝ) ^ 10 * (S.card : ℝ) ∧
      (S.card : ℝ) ≤ (k : ℝ) ^ 552 * (A.card : ℝ) ∧
      (S.card : ℝ) ≤ (k : ℝ) ^ 552 * ((A ∩ S).card : ℝ) ∧
      tvLe (fun x => P.expect (fun i => unifMeas (coset (z i) (Z i)) x)) (unifMeas S) τ ∧
      d ≤ k ^ 2228 ∧
      D ≤ k ^ 2242 * (Nat.clog 2 (Nat.ceil (1 / τ)) + 10) ∧
      (∀ i, IsClosedPair τ (Z i) ((T i).toSymNbhd (hT i) 0)) ∧
      (∀ i, (T i).HasDim d) ∧
      (∀ i, covFlat (S : Set ℤ) ((T i).set 0) ≤ ((2 ^ D : ℕ) : ℕ∞)) := by
  classical
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have h2pow : ∀ n : ℕ, (2 : ℝ) ^ n ≤ (k : ℝ) ^ n := fun n => pow_le_pow_left₀ (by norm_num) hk2 n
  have hHE_A := hereditarilyEnergetic_of_summing hk (by norm_num : (1 : ℝ) ≤ 2) hX hsum
  have hE_A : (1 / (8 * (k : ℝ) ^ 4)) * (A.card : ℝ) ^ 3 ≤ (E[A] : ℝ) := by
    have h := hHE_A A Subset.rfl
    have hApos : (0 : ℝ) < (A.card : ℝ) := Nat.cast_pos.mpr hA.card_pos
    have : (1 / (8 * (k : ℝ) ^ 4)) * (A.card : ℝ) ^ 3 * (A.card : ℝ) ≤ (E[A] : ℝ) * (A.card : ℝ) := by
      have : (4 : ℝ) * 2 * (k : ℝ) ^ 4 = 8 * (k : ℝ) ^ 4 := by ring
      rw [this] at h
      linarith [show (A.card : ℝ) ^ 4 = (A.card : ℝ) ^ 3 * (A.card : ℝ) by ring]
    exact le_of_mul_le_mul_right this hApos
  obtain ⟨A', hA'A, hA'ne, hA'card, hA'diff⟩ :=
    balog_szemeredi_gowers hA (by positivity : (0 : ℝ) < 1 / (8 * (k : ℝ) ^ 4)) hE_A
  have hA'card_k : (A.card : ℝ) ≤ (k : ℝ) ^ 10 * (A'.card : ℝ) := by
    have h64 : (64 : ℝ) * (k : ℝ) ^ 4 ≤ (k : ℝ) ^ 10 := by
      calc (64 : ℝ) * (k : ℝ) ^ 4 = (2 : ℝ) ^ 6 * (k : ℝ) ^ 4 := by norm_num
        _ ≤ (k : ℝ) ^ 6 * (k : ℝ) ^ 4 := mul_le_mul_of_nonneg_right (h2pow 6) (by positivity)
        _ = (k : ℝ) ^ 10 := by ring
    have h1 : (A.card : ℝ) ≤ (64 * (k : ℝ) ^ 4) * (A'.card : ℝ) := by
      have : (1 / (8 * (k : ℝ) ^ 4)) / 8 = (64 * (k : ℝ) ^ 4)⁻¹ := by field_simp; ring
      rw [this, inv_mul_le_iff₀ (by positivity)] at hA'card
      linarith
    exact h1.trans (mul_le_mul_of_nonneg_right h64 (Nat.cast_nonneg _))
  have hA'diff_k : ((A' - A').card : ℝ) ≤ (k : ℝ) ^ 92 * (A'.card : ℝ) := by
    have hC : 4194304 / (1 / (8 * (k : ℝ) ^ 4)) ^ 10 ≤ (k : ℝ) ^ 92 := by
      have heq : 4194304 / (1 / (8 * (k : ℝ) ^ 4)) ^ 10 = (2 : ℝ) ^ 52 * (k : ℝ) ^ 40 := by
        field_simp; ring
      rw [heq]
      calc (2 : ℝ) ^ 52 * (k : ℝ) ^ 40 ≤ (k : ℝ) ^ 52 * (k : ℝ) ^ 40 :=
            mul_le_mul_of_nonneg_right (h2pow 52) (by positivity)
        _ = (k : ℝ) ^ 92 := by ring
    exact hA'diff.trans (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _))
  obtain ⟨Pmod, hPprime, _, hPle, A'', φ, hA''sub, hA''ne, hA''card, hiso⟩ := ruzsa_modeling_6 hA'ne
  have : NeZero Pmod := ⟨hPprime.ne_zero⟩
  have hPmod_le : (Pmod : ℝ) ≤ (k : ℝ) ^ 1112 * (A''.card : ℝ) := by
    have h66 := pluennecke_sub_bound hA'ne hA'diff_k 6 6
    have hP1 : (Pmod : ℝ) ≤ 24 * ((6 • A' - 6 • A').card : ℝ) := by exact_mod_cast hPle
    have hA'7 : (A'.card : ℝ) ≤ 7 * (A''.card : ℝ) := by exact_mod_cast hA''card
    have h168 : (168 : ℝ) ≤ (k : ℝ) ^ 8 := (by norm_num : (168 : ℝ) ≤ (2 : ℝ) ^ 8).trans (h2pow 8)
    calc (Pmod : ℝ) ≤ 24 * ((6 • A' - 6 • A').card : ℝ) := hP1
      _ ≤ 24 * (((k : ℝ) ^ 92) ^ (6 + 6) * (A'.card : ℝ)) := mul_le_mul_of_nonneg_left h66 (by norm_num)
      _ ≤ 24 * (((k : ℝ) ^ 92) ^ 12 * (7 * (A''.card : ℝ))) := by gcongr
      _ = 168 * (k : ℝ) ^ 1104 * (A''.card : ℝ) := by ring
      _ ≤ (k : ℝ) ^ 8 * (k : ℝ) ^ 1104 * (A''.card : ℝ) := by gcongr
      _ = (k : ℝ) ^ 1112 * (A''.card : ℝ) := by ring
  obtain ⟨B, hB, gcard, hgcard_le, hBdim, hB0sub, hP_B0⟩ := bogolyubov_pullback_system hA''ne hiso
  have hgcard_k : gcard ≤ k ^ 2226 := by
    have hA''pos : (0 : ℝ) < (A''.card : ℝ) := Nat.cast_pos.mpr hA''ne.card_pos
    have hinvα : (Pmod : ℝ) / (A''.card : ℝ) ≤ (k : ℝ) ^ 1112 := (div_le_iff₀ hA''pos).mpr hPmod_le
    have h4 : (gcard : ℝ) ≤ (k : ℝ) ^ 2226 := by
      have h1 : 4 / ((A''.card : ℝ) / (Pmod : ℝ)) ^ 2 = 4 * ((Pmod : ℝ) / (A''.card : ℝ)) ^ 2 := by field_simp
      rw [h1] at hgcard_le
      have hsq : ((Pmod : ℝ) / (A''.card : ℝ)) ^ 2 ≤ ((k : ℝ) ^ 1112) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinvα 2
      have h4k : (4 : ℝ) ≤ (k : ℝ) ^ 2 := (by norm_num : (4 : ℝ) = (2 : ℝ) ^ 2).le.trans (h2pow 2)
      calc (gcard : ℝ) ≤ 4 * ((Pmod : ℝ) / (A''.card : ℝ)) ^ 2 := hgcard_le
        _ ≤ (k : ℝ) ^ 2 * ((k : ℝ) ^ 1112) ^ 2 := mul_le_mul h4k hsq (by positivity) (by positivity)
        _ = (k : ℝ) ^ 2226 := by ring
    exact_mod_cast h4
  let d : ℕ := 3 * gcard
  have hd_le : d ≤ k ^ 2228 := by
    have h34 : 3 ≤ k ^ 2 := by nlinarith
    calc d = 3 * gcard := rfl
      _ ≤ k ^ 2 * k ^ 2226 := Nat.mul_le_mul h34 hgcard_k
      _ = k ^ 2228 := by rw [← pow_add]
  have hB0_sub22 : (B.toSymNbhd hB 0).set ⊆ 2 • A' - 2 • A' := by
    refine hB0sub.trans ?_
    have h2eq : 2 • A' = A' + A' := by simp only [two_nsmul]
    rw [h2eq]
    exact Finset.sub_subset_sub (Finset.add_subset_add hA''sub hA''sub)
      (Finset.add_subset_add hA''sub hA''sub)
  let Zdiff : SymNbhd :=
    { set := A' - A'
      zero_mem := by obtain ⟨a, ha⟩ := hA'ne; exact Finset.mem_sub.mpr ⟨a, ha, a, ha, sub_self a⟩
      neg_mem := fun x hx => by
        obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
        exact Finset.mem_sub.mpr ⟨b, hb, a, ha, by ring⟩ }
  let B2sys : Sys := B.dilate 2
  have hB2fin : B2sys.IsFinite := B.dilate_isFinite 2 hB
  have hB2_sub0 : (B2sys.toSymNbhd hB2fin 0).set ⊆ (B.toSymNbhd hB 0).set := by
    intro x hx
    have hx' : x ∈ B.set 2 := by simpa [B2sys, Sys.toSymNbhd, Sys.dilate] using hx
    exact (Set.Finite.mem_toFinset _).mpr (B.antitone (by omega) hx')
  have hZdiff_add_sub : Zdiff.set + (B2sys.toSymNbhd hB2fin 0).set ⊆ 3 • A' - 3 • A' := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
    have hv22 := hB0_sub22 (hB2_sub0 hv)
    obtain ⟨a1, h1, b1, hb1, rfl⟩ := Finset.mem_sub.mp hu
    obtain ⟨u2, hu2, v2, hv2, rfl⟩ := Finset.mem_sub.mp hv22
    have h3eq : 3 • A' = A' + 2 • A' := by rw [show (3 : ℕ) = 1 + 2 by rfl, add_nsmul, one_nsmul]
    rw [h3eq]
    exact Finset.mem_sub.mpr ⟨a1 + u2, Finset.add_mem_add h1 hu2, b1 + v2, Finset.add_mem_add hb1 hv2, by ring⟩
  have hA'_le_Zdiff : (A'.card : ℝ) ≤ (Zdiff.set.card : ℝ) := by
    let a0 := hA'ne.choose
    have ha0 : a0 ∈ A' := hA'ne.choose_spec
    have hcard : A'.card ≤ (A' - A').card := by
      refine Finset.card_le_card_of_injOn (fun a => a - a0) (fun a ha => ?_) (fun a1 _ a2 _ h => ?_)
      · exact Finset.mem_coe.mpr (Finset.mem_sub.mpr ⟨a, Finset.mem_coe.mp ha, a0, ha0, rfl⟩)
      · exact sub_left_inj.mp h
    exact_mod_cast hcard
  have hZdiff_dbl : ((Zdiff.set + (B2sys.toSymNbhd hB2fin 0).set).card : ℝ) ≤
      (k : ℝ) ^ 552 * (Zdiff.set.card : ℝ) := by
    have h33 := pluennecke_sub_bound hA'ne hA'diff_k 3 3
    have hsubR : ((Zdiff.set + (B2sys.toSymNbhd hB2fin 0).set).card : ℝ) ≤ ((3 • A' - 3 • A').card : ℝ) := by
      exact_mod_cast Finset.card_le_card hZdiff_add_sub
    calc ((Zdiff.set + (B2sys.toSymNbhd hB2fin 0).set).card : ℝ)
        ≤ ((3 • A' - 3 • A').card : ℝ) := hsubR
      _ ≤ ((k : ℝ) ^ 92) ^ (3 + 3) * (A'.card : ℝ) := h33
      _ = (k : ℝ) ^ 552 * (A'.card : ℝ) := by ring
      _ ≤ (k : ℝ) ^ 552 * (Zdiff.set.card : ℝ) := mul_le_mul_of_nonneg_left hA'_le_Zdiff (by positivity)
  let m : ℕ := Nat.clog 2 (Nat.ceil (2208 * (k : ℝ) / τ)) + 1
  have hm1 : 1 ≤ m := by dsimp [m]; omega
  have hKm : (k : ℝ) ^ 552 ≤ (1 + τ / 2) ^ (2 ^ (m - 1)) := by
    have h1p : (0 : ℝ) < 1 + τ / 2 := by linarith
    have hlog_le : Real.log ((k : ℝ) ^ 552) ≤ Real.log ((1 + τ / 2) ^ (2 ^ (m - 1))) := by
      rw [Real.log_pow, Real.log_pow]
      have hlogk : Real.log (k : ℝ) ≤ (k : ℝ) := (Real.log_le_sub_one_of_pos hk_pos).trans (by linarith)
      have hhalf : τ / 4 ≤ Real.log (1 + τ / 2) := by
        have := half_le_log_one_add (by linarith : (0 : ℝ) ≤ τ / 2) (by linarith : τ / 2 ≤ 1)
        linarith
      have hpow_ge : 2208 * (k : ℝ) / τ ≤ (2 : ℝ) ^ (m - 1) := by
        have h1 : 2208 * (k : ℝ) / τ ≤ (Nat.ceil (2208 * (k : ℝ) / τ) : ℝ) := Nat.le_ceil _
        have h2 : Nat.ceil (2208 * (k : ℝ) / τ) ≤ 2 ^ (m - 1) := by
          have hm_sub : m - 1 = Nat.clog 2 (Nat.ceil (2208 * (k : ℝ) / τ)) := Nat.add_sub_cancel _ 1
          rw [hm_sub]; exact Nat.le_pow_clog (by norm_num) _
        exact h1.trans (by exact_mod_cast h2)
      have hmul : 552 * (k : ℝ) ≤ (2 : ℝ) ^ (m - 1) * (τ / 4) := by
        have := (div_le_iff₀ hτ0).mp hpow_ge
        linarith
      have hcast : ((2 ^ (m - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (m - 1) := by push_cast; rfl
      rw [hcast]
      have hstep1 : (552 : ℝ) * Real.log (k : ℝ) ≤ 552 * (k : ℝ) := by linarith
      have hstep2 : (2 : ℝ) ^ (m - 1) * (τ / 4) ≤ (2 : ℝ) ^ (m - 1) * Real.log (1 + τ / 2) :=
        mul_le_mul_of_nonneg_left hhalf (by positivity)
      linarith
    exact (Real.log_le_log_iff (by positivity) (pow_pos h1p _)).mp hlog_le
  obtain ⟨S0, hZdiff_S0, hS0_top, hS0_closed⟩ :=
    lem_ubreg Zdiff B2sys hB2fin (by linarith : 0 < τ / 2) hZdiff_dbl hm1 hKm
  let Bm : Sys := B.dilate (m + 2)
  have hBmfin : Bm.IsFinite := B.dilate_isFinite (m + 2) hB
  have hBmdim : Bm.HasDim d := B.dilate_hasDim (m + 2) hBdim
  let m' : ℕ := Nat.clog 2 (Nat.ceil (2 * (d : ℝ) / τ)) + 2
  have hm'2 : 2 ≤ m' := by dsimp [m']; omega
  have hdm' : (2 : ℝ) * (d : ℝ) ≤ (2 ^ (m' - 2) : ℝ) * τ := by
    have h1 : 2 * (d : ℝ) / τ ≤ (Nat.ceil (2 * (d : ℝ) / τ) : ℝ) := Nat.le_ceil _
    have h2 : Nat.ceil (2 * (d : ℝ) / τ) ≤ 2 ^ (m' - 2) := by
      have hm'_sub : m' - 2 = Nat.clog 2 (Nat.ceil (2 * (d : ℝ) / τ)) := by dsimp [m']; omega
      rw [hm'_sub]; exact Nat.le_pow_clog (by norm_num) _
    exact (div_le_iff₀ hτ0).mp (h1.trans (by exact_mod_cast h2))
  obtain ⟨Zstar, _, hZstar_sub, hZstar_closed⟩ :=
    lem_cc Bm hBmfin hBmdim hτ0 (by linarith) hm'2 hdm'
  let a0 : ℤ := hA'ne.choose
  have ha0 : a0 ∈ A' := hA'ne.choose_spec
  let S : Finset ℤ := coset a0 S0
  have hS_ne : S.Nonempty := ⟨a0, Finset.mem_image.mpr ⟨0, S0.zero_mem, by ring⟩⟩
  have hS_card : S.card = S0.set.card := coset_card a0 S0
  have hS0_sub33 : S0.set ⊆ 3 • A' - 3 • A' := hS0_top.trans hZdiff_add_sub
  have hA'_sub_S : A' ⊆ S := by
    intro a ha
    have hdiff : a - a0 ∈ S0.set := hZdiff_S0 (Finset.mem_sub.mpr ⟨a, ha, a0, ha0, rfl⟩)
    exact Finset.mem_image.mpr ⟨a - a0, hdiff, by ring⟩
  have hA'_sub_AS : A' ⊆ A ∩ S := Finset.subset_inter hA'A hA'_sub_S
  have hS_le_552A' : (S.card : ℝ) ≤ (k : ℝ) ^ 552 * (A'.card : ℝ) := by
    have h33 := pluennecke_sub_bound hA'ne hA'diff_k 3 3
    rw [hS_card]
    calc (S0.set.card : ℝ) ≤ ((3 • A' - 3 • A').card : ℝ) := by exact_mod_cast Finset.card_le_card hS0_sub33
      _ ≤ ((k : ℝ) ^ 92) ^ (3 + 3) * (A'.card : ℝ) := h33
      _ = (k : ℝ) ^ 552 * (A'.card : ℝ) := by ring
  have hA'_le_S : (A'.card : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_le_card hA'_sub_S
  have hA'_le_A : (A'.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hA'A
  have hA'_le_AS : (A'.card : ℝ) ≤ ((A ∩ S).card : ℝ) := by exact_mod_cast Finset.card_le_card hA'_sub_AS
  have hHE_S : HereditarilyEnergetic (1 / (k : ℝ) ^ 1104) S := by
    have hSS_card : (S + S).card = (S0.set + S0.set).card := by
      refine Finset.card_bij (fun x _ => x - 2 * a0) ?_ ?_ ?_
      · intro x hx
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
        obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
        have : u' + a0 + (v' + a0) - 2 * a0 = u' + v' := by ring
        rw [this]; exact Finset.add_mem_add hu' hv'
      · intro _ _ _ _ h; omega
      · intro y hy
        obtain ⟨u', hu', v', hv', rfl⟩ := Finset.mem_add.mp hy
        refine ⟨(u' + a0) + (v' + a0), Finset.add_mem_add (Finset.mem_image_of_mem _ hu')
          (Finset.mem_image_of_mem _ hv'), by ring⟩
    have hS0S0_sub : S0.set + S0.set ⊆ 6 • A' - 6 • A' := by
      intro x hx
      obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hx
      obtain ⟨p1, hp1, q1, hq1, rfl⟩ := Finset.mem_sub.mp (hS0_sub33 hu)
      obtain ⟨p2, hp2, q2, hq2, rfl⟩ := Finset.mem_sub.mp (hS0_sub33 hv)
      have h6eq : 6 • A' = 3 • A' + 3 • A' := by rw [← add_nsmul]
      rw [h6eq]
      exact Finset.mem_sub.mpr ⟨p1 + p2, Finset.add_mem_add hp1 hp2, q1 + q2, Finset.add_mem_add hq1 hq2, by ring⟩
    have hdbl_S : ((S + S).card : ℝ) ≤ (k : ℝ) ^ 1104 * (S.card : ℝ) := by
      have h66 := pluennecke_sub_bound hA'ne hA'diff_k 6 6
      rw [hSS_card]
      calc ((S0.set + S0.set).card : ℝ) ≤ ((6 • A' - 6 • A').card : ℝ) := by
            exact_mod_cast Finset.card_le_card hS0S0_sub
        _ ≤ ((k : ℝ) ^ 92) ^ (6 + 6) * (A'.card : ℝ) := h66
        _ = (k : ℝ) ^ 1104 * (A'.card : ℝ) := by ring
        _ ≤ (k : ℝ) ^ 1104 * (S.card : ℝ) := mul_le_mul_of_nonneg_left hA'_le_S (by positivity)
    simpa [one_div] using hereditarilyEnergetic_of_doubling (by positivity : (0 : ℝ) < (k : ℝ) ^ 1104) hdbl_S
  let unif := FinProb.unifFinset S hS_ne
  let Tstar : Sys := B.dilate (m + 2 + m')
  have hTstar_fin : Tstar.IsFinite := B.dilate_isFinite (m + 2 + m') hB
  have hTstar_dim : Tstar.HasDim d := B.dilate_hasDim (m + 2 + m') hBdim
  have hTstar_0_eq : (Tstar.toSymNbhd hTstar_fin 0).set = (Bm.toSymNbhd hBmfin m').set := by
    ext x
    have hidx : 0 + (m + 2 + m') = m' + (m + 2) := by omega
    simp [Tstar, Bm, Sys.toSymNbhd, Sys.dilate, hidx]
  have hZstar_Tstar : IsClosedPair τ Zstar (Tstar.toSymNbhd hTstar_fin 0) := by
    obtain ⟨Zm, Zp, h1, h2, h3⟩ := hZstar_closed
    exact ⟨Zm, Zp, by rwa [hTstar_0_eq], by rwa [hTstar_0_eq], h3⟩
  have htv : tvLe (fun x => unif.1.expect (fun i => unifMeas (coset (unif.2 i) Zstar) x)) (unifMeas S) τ := by
    have hZstar_B2m : Zstar.set ⊆ (B2sys.toSymNbhd hB2fin m).set := by
      refine hZstar_sub.trans ?_
      intro x hx
      have hidx : 0 + (m + 2) = m + 2 := by omega
      simpa [Bm, B2sys, Sys.toSymNbhd, Sys.dilate, hidx] using hx
    have hS0_Zstar : IsClosedPair (τ / 2) S0 Zstar := isClosedPair_mono_right hS0_closed hZstar_B2m
    have havg := avg_coset_tvLe (by linarith : (0 : ℝ) ≤ τ / 2) hS0_Zstar a0
    have h2tau : 2 * (τ / 2) = τ := by ring
    rw [h2tau] at havg
    have heq : ∀ x : ℤ, unif.1.expect (fun i => unifMeas (coset (unif.2 i) Zstar) x) =
        (S0.set.card : ℝ)⁻¹ * ∑ u ∈ S0.set, unifMeas (coset (a0 + u) Zstar) x := by
      intro x
      have hexp := FinProb.unifFinset_expect S hS_ne (fun y => unifMeas (coset y Zstar) x)
      dsimp only [unif]
      rw [hexp, hS_card]
      congr 1
      dsimp only [S, coset]
      rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
      refine Finset.sum_congr rfl fun u _ => by rw [add_comm]
    intro U
    simpa only [heq] using havg U
  have hA''_le_P : (A''.card : ℝ) ≤ (Pmod : ℝ) := by
    have h1 : A''.card ≤ Pmod := by
      have hinj : Set.InjOn φ (A'' : Set ℤ) := fun x hx y hy hxy => by
        have h6 := (hiso x (Finset.mem_coe.mp hx) x (Finset.mem_coe.mp hx) x (Finset.mem_coe.mp hx)
          x (Finset.mem_coe.mp hx) x (Finset.mem_coe.mp hx) x (Finset.mem_coe.mp hx)
          y (Finset.mem_coe.mp hy) y (Finset.mem_coe.mp hy) y (Finset.mem_coe.mp hy)
          y (Finset.mem_coe.mp hy) y (Finset.mem_coe.mp hy) y (Finset.mem_coe.mp hy)).mpr (by simp [hxy])
        omega
      calc A''.card = (A''.image φ).card := (Finset.card_image_of_injOn hinj).symm
        _ ≤ Fintype.card (ZMod Pmod) := Finset.card_le_univ _
        _ = Pmod := ZMod.card Pmod
    exact_mod_cast h1
  obtain ⟨D, hD_le, hcov_Tstar⟩ :=
    lem_gs_cov_bound hB hk hτ0 hA'ne hA'diff_k hA''card hA''_le_P hP_B0 hgcard_k hBdim hB0_sub22
      hS0_sub33 rfl rfl rfl
  refine ⟨S, unif.1, unif.2, fun _ => Zstar, fun _ => Tstar, fun _ => hTstar_fin, d, D,
    hS_ne, hHE_S, ?_, ?_, ?_, htv, hd_le, hD_le, fun _ => hZstar_Tstar, fun _ => hTstar_dim, fun _ => hcov_Tstar⟩
  · exact hA'card_k.trans (mul_le_mul_of_nonneg_left hA'_le_S (by positivity))
  · exact hS_le_552A'.trans (mul_le_mul_of_nonneg_left hA'_le_A (by positivity))
  · exact hS_le_552A'.trans (mul_le_mul_of_nonneg_left hA'_le_AS (by positivity))

/- ### Module 6A: Counting lemma (`lem.c`) -/

private noncomputable def cosetConvInd (a : ℤ) (Zi Zj : SymNbhd) (A : Finset ℤ) (u : ℤ) : ℝ :=
  (Zj.set.card : ℝ)⁻¹ * ∑ y ∈ Zj.set,
    (if u - (y + a) ∈ A ∩ coset a Zi then (1 : ℝ) else 0) * (if y + a ∈ A then 1 else 0)

private lemma cosetConvInd_shift (a : ℤ) (Zi Zj : SymNbhd) (A : Finset ℤ) (x : ℤ) :
    cosetConvInd a Zi Zj A (x + 2 * a) =
    convInd (A.image (· - a) ∩ Zi.set) (A.image (· - a)) Zj x := by
  unfold cosetConvInd convInd convZ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  dsimp only [unifMeas]
  rw [if_pos hy]
  have h1 : x + 2 * a - (y + a) ∈ A ∩ coset a Zi ↔ x - y ∈ A.image (· - a) ∩ Zi.set := by
    simp only [Finset.mem_inter, coset, Finset.mem_image]
    constructor
    · rintro ⟨hA, ⟨z, hz, hzeq⟩⟩
      refine ⟨⟨x + 2 * a - (y + a), hA, by ring⟩, ?_⟩
      have : x - y = z := by omega
      rwa [this]
    · rintro ⟨⟨u, huA, hueq⟩, hxyZ⟩
      refine ⟨?_, ⟨x - y, hxyZ, by ring⟩⟩
      have : x + 2 * a - (y + a) = u := by omega
      rwa [this]
  have h2 : y + a ∈ A ↔ y ∈ A.image (· - a) := by
    simp only [Finset.mem_image]
    constructor
    · intro h; exact ⟨y + a, h, by ring⟩
    · rintro ⟨u, hu, heq⟩
      have hyu : y + a = u := by omega
      rwa [hyu]
  by_cases c1 : x - y ∈ A.image (· - a) ∩ Zi.set <;>
  by_cases c2 : y ∈ A.image (· - a)
  · rw [if_pos (h1.mpr c1), if_pos (h2.mpr c2), if_pos c1, if_pos c2]; ring
  · rw [if_pos (h1.mpr c1), if_neg (mt h2.mp c2), if_pos c1, if_neg c2]; ring
  · rw [if_neg (mt h1.mp c1), if_pos (h2.mpr c2), if_neg c1, if_pos c2]; ring
  · rw [if_neg (mt h1.mp c1), if_neg (mt h2.mp c2), if_neg c1, if_neg c2]; ring

private lemma one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ e ∈ s, 0 ≤ x e) (hx1 : ∀ e ∈ s, x e ≤ 1) :
    1 - ∑ e ∈ s, x e ≤ ∏ e ∈ s, (1 - x e) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have hih := ih (fun e he => hx0 e (Finset.mem_insert_of_mem he))
      (fun e he => hx1 e (Finset.mem_insert_of_mem he))
    have ha0 := hx0 a (Finset.mem_insert_self a s)
    have ha1 := hx1 a (Finset.mem_insert_self a s)
    have hsum_nn : 0 ≤ ∑ e ∈ s, x e := Finset.sum_nonneg fun e he => hx0 e (Finset.mem_insert_of_mem he)
    have hprod_nn : 0 ≤ ∏ e ∈ s, (1 - x e) := Finset.prod_nonneg fun e he => by
      linarith [hx1 e (Finset.mem_insert_of_mem he)]
    have h1 : (1 - x a) * (1 - ∑ e ∈ s, x e) ≤ (1 - x a) * ∏ e ∈ s, (1 - x e) :=
      mul_le_mul_of_nonneg_left hih (by linarith)
    nlinarith

private lemma pow_sub_ge_three_quarters {k : ℕ} {α τ : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (h : 8 * (k : ℝ) * τ ≤ α) :
    (3 / 4 : ℝ) * α ^ k ≤ (α - 2 * τ) ^ k := by
  by_cases hk0 : k = 0
  · subst hk0; norm_num
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0
  have hratio : 2 * τ / α ≤ 1 / (4 * (k : ℝ)) := by
    rw [div_le_div_iff₀ hα (by positivity)]; linarith
  have h1 : (1 - 2 * τ / α) ^ k ≥ 1 - (k : ℝ) * (2 * τ / α) := by
    have hprod := one_sub_sum_le_prod_one_sub (Finset.univ : Finset (Fin k))
      (fun _ => 2 * τ / α)
      (fun _ _ => by positivity)
      (fun _ _ => hratio.trans (by rw [div_le_one (by positivity)]; linarith))
    simpa [Finset.prod_const, Finset.sum_const] using hprod
  have h2 : (3 / 4 : ℝ) ≤ (1 - 2 * τ / α) ^ k := by
    have hmul : (k : ℝ) * (2 * τ / α) ≤ 1 / 4 := by
      calc (k : ℝ) * (2 * τ / α) ≤ (k : ℝ) * (1 / (4 * (k : ℝ))) :=
            mul_le_mul_of_nonneg_left hratio hk_pos.le
        _ = 1 / 4 := by field_simp
    linarith
  have heq : α - 2 * τ = α * (1 - 2 * τ / α) := by field_simp
  rw [heq, mul_pow]
  have hmul2 := mul_le_mul_of_nonneg_left h2 (pow_nonneg hα.le k)
  linarith

private lemma pow_add_le_two {k : ℕ} {α τ : ℝ}
    (hα : 0 < α) (hτ : 0 ≤ τ) (h : 8 * (k : ℝ) * τ ≤ α) :
    (α + τ) ^ (k - 2) ≤ 2 * α ^ (k - 2) := by
  by_cases hk2 : k ≤ 2
  · have : k - 2 = 0 := by omega
    rw [this]; norm_num
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hratio : τ / α ≤ 1 / (8 * (k : ℝ)) := by
    rw [div_le_div_iff₀ hα (by positivity)]; linarith
  have h1 : (1 + τ / α) ^ (k - 2) ≤ Real.exp (((k - 2 : ℕ) : ℝ) * (τ / α)) := by
    calc (1 + τ / α) ^ (k - 2) ≤ (Real.exp (τ / α)) ^ (k - 2) :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (τ / α)]) _
      _ = Real.exp (((k - 2 : ℕ) : ℝ) * (τ / α)) := by rw [← Real.exp_nat_mul]
  have h2 : (((k - 2 : ℕ) : ℝ) * (τ / α)) ≤ 1 / 8 := by
    have hksub : ((k - 2 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 2
    calc ((k - 2 : ℕ) : ℝ) * (τ / α) ≤ (k : ℝ) * (1 / (8 * (k : ℝ))) :=
          mul_le_mul hksub hratio (by positivity) hk_pos.le
      _ = 1 / 8 := by field_simp
  have h3 : Real.exp (1 / 8 : ℝ) ≤ 2 := by
    have hexp : Real.exp (-(1 / 8 : ℝ)) ≥ 1 - 1 / 8 := by
      have := Real.add_one_le_exp (-(1 / 8 : ℝ)); linarith
    rw [Real.exp_neg] at hexp
    have hinv : Real.exp (1 / 8 : ℝ) ≤ (1 - 1 / 8 : ℝ)⁻¹ :=
      (le_inv_comm₀ (Real.exp_pos _) (by norm_num)).mpr hexp
    have hnum : (1 - 1 / 8 : ℝ)⁻¹ ≤ 2 := by norm_num
    linarith
  have heq : α + τ = α * (1 + τ / α) := by field_simp
  rw [heq, mul_pow]
  have hle : (1 + τ / α) ^ (k - 2) ≤ 2 := h1.trans ((Real.exp_le_exp.mpr h2).trans h3)
  have hmul2 := mul_le_mul_of_nonneg_left hle (pow_nonneg hα.le (k - 2))
  linarith

private lemma lem_c_pair_err {k : ℕ} {A' X' : Finset ℤ} {Z : Fin k → SymNbhd}
    {α τ ε δ : ℝ} (hα0 : 0 < α) (hτ : 0 ≤ τ) (_hε0 : 0 ≤ ε) (_hδ : 0 ≤ δ)
    (hdens' : ∀ i : Fin k, |locDens (Z i) A' - α| ≤ τ)
    (hX' : ∀ i : Fin k, locDens (Z i) X' ≤ ε)
    (hU2' : ∀ i j : Fin k, i < j →
      ((Z i).set.card : ℝ)⁻¹ * ∑ x ∈ (Z i).set,
        (convInd (A' ∩ (Z i).set) A' (Z j) x - α ^ 2) ^ 2 ≤ δ)
    {p : Fin k × Fin k} (hlt : p.1 < p.2) :
    let T : Finset (Fin k → ℤ) := Fintype.piFinset (fun i => (Z i).set)
    let Wprod : ℝ := (∏ i : Fin k, ((Z i).set.card : ℝ))⁻¹
    Wprod * ∑ z ∈ T,
      (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
      (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) ≤
    (α + τ) ^ (k - 2) * (ε * α ^ 2 + Real.sqrt δ) := by
  classical
  intro T Wprod
  have hne : p.1 ≠ p.2 := ne_of_lt hlt
  let rest : Finset (Fin k) := Finset.univ \ {p.1, p.2}
  have hrest_card : rest.card = k - 2 := by
    dsimp only [rest]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_pair hne]
  let Trest := rest.pi (fun i => (Z i).set)
  have hsum_split : ∑ z ∈ T,
      (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
      (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) =
      (∑ x ∈ (Z p.1).set, ∑ y ∈ (Z p.2).set,
        (if x + y ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
        (if x ∈ A' then (1 : ℝ) else 0) * (if y ∈ A' then (1 : ℝ) else 0)) *
      (∏ i ∈ rest, ((A' ∩ (Z i).set).card : ℝ)) := by
    have hbij : ∑ z ∈ T,
        (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
        (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) =
        ∑ q ∈ ((Z p.1).set ×ˢ (Z p.2).set) ×ˢ Trest,
          ((if q.1.1 + q.1.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
           (if q.1.1 ∈ A' then (1 : ℝ) else 0) * (if q.1.2 ∈ A' then (1 : ℝ) else 0)) *
          (∏ i ∈ rest.attach, if q.2 i.1 i.2 ∈ A' then (1 : ℝ) else 0) := by
      refine Finset.sum_bij (fun z _ => ((z p.1, z p.2), fun i _ => z i)) ?_ ?_ ?_ ?_
      · intro z hz
        exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
          ⟨Fintype.mem_piFinset.mp hz p.1, Fintype.mem_piFinset.mp hz p.2⟩,
          Finset.mem_pi.mpr fun i _ => Fintype.mem_piFinset.mp hz i⟩
      · intro z1 _ z2 _ h
        have h1 : z1 p.1 = z2 p.1 := congrArg (fun q => q.1.1) h
        have h2 : z1 p.2 = z2 p.2 := congrArg (fun q => q.1.2) h
        have h3 := congrArg Prod.snd h
        funext i
        by_cases hi1 : i = p.1
        · subst hi1; exact h1
        · by_cases hi2 : i = p.2
          · subst hi2; exact h2
          · have hirest : i ∈ rest := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hi1, hi2]⟩
            exact congrFun (congrFun h3 i) hirest
      · rintro ⟨⟨x, y⟩, g⟩ hq
        obtain ⟨hxy, hg⟩ := Finset.mem_product.mp hq
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
        let z : Fin k → ℤ := fun i =>
          if hi1 : i = p.1 then x
          else if hi2 : i = p.2 then y
          else g i (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hi1, hi2]⟩)
        refine ⟨z, Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
        · by_cases hi1 : i = p.1
          · subst hi1; simpa [z] using hx
          · by_cases hi2 : i = p.2
            · subst hi2; simpa [z, hne.symm] using hy
            · simp only [z, dif_neg hi1, dif_neg hi2]
              exact Finset.mem_pi.mp hg i _
        · refine Prod.ext (Prod.ext (by simp [z]) (by simp [z, hne.symm])) ?_
          funext i hi
          have hi1 : i ≠ p.1 := fun h => by
            have := (Finset.mem_sdiff.mp hi).2; simp [h] at this
          have hi2 : i ≠ p.2 := fun h => by
            have := (Finset.mem_sdiff.mp hi).2; simp [h] at this
          simp [z, hi1, hi2]
      · intro z _
        have hprod_split : (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) =
            (if z p.1 ∈ A' then (1 : ℝ) else 0) * (if z p.2 ∈ A' then (1 : ℝ) else 0) *
            ∏ i ∈ rest.attach, if z i.1 ∈ A' then (1 : ℝ) else 0 := by
          have hu : (Finset.univ : Finset (Fin k)) = {p.1, p.2} ∪ rest := by
            ext i; simp only [rest, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]; tauto
          have hdisj : Disjoint ({p.1, p.2} : Finset (Fin k)) rest := Finset.disjoint_sdiff
          rw [hu, Finset.prod_union hdisj, Finset.prod_pair hne]
          congr 1
          exact (Finset.prod_attach rest (fun i => if z i ∈ A' then (1 : ℝ) else 0)).symm
        rw [hprod_split]; ring
    rw [hbij, Finset.sum_product]
    have hfac : ∀ x ∈ (Z p.1).set ×ˢ (Z p.2).set,
        ∑ y ∈ Trest,
          ((if x.1 + x.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
           (if x.1 ∈ A' then (1 : ℝ) else 0) * (if x.2 ∈ A' then (1 : ℝ) else 0)) *
          (∏ i ∈ rest.attach, if y i.1 i.2 ∈ A' then (1 : ℝ) else 0) =
        ((if x.1 + x.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
         (if x.1 ∈ A' then (1 : ℝ) else 0) * (if x.2 ∈ A' then (1 : ℝ) else 0)) *
        ∑ y ∈ Trest, (∏ i ∈ rest.attach, if y i.1 i.2 ∈ A' then (1 : ℝ) else 0) :=
      fun x _ => (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl hfac, ← Finset.sum_mul, Finset.sum_product]
    congr 1
    have hTrest_sum : ∑ g ∈ Trest, ∏ i ∈ rest.attach, (if g i.1 i.2 ∈ A' then (1 : ℝ) else 0) =
        ∏ i ∈ rest, ∑ x ∈ (Z i).set, (if x ∈ A' then (1 : ℝ) else 0) := by
      dsimp only [Trest]; rw [Finset.prod_sum]
    rw [hTrest_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.inter_comm]
  have hW_split : Wprod = (((Z p.1).set.card : ℝ)⁻¹ * ((Z p.2).set.card : ℝ)⁻¹) *
      ∏ i ∈ rest, (((Z i).set.card : ℝ))⁻¹ := by
    dsimp only [Wprod]
    have hu : (Finset.univ : Finset (Fin k)) = {p.1, p.2} ∪ rest := by
      ext i; simp only [rest, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]; tauto
    rw [hu, Finset.prod_union Finset.disjoint_sdiff, Finset.prod_pair hne, mul_inv, mul_inv,
      Finset.prod_inv_distrib]
  rw [hsum_split, hW_split]
  have hrest_le : (∏ i ∈ rest, (((Z i).set.card : ℝ))⁻¹) * (∏ i ∈ rest, ((A' ∩ (Z i).set).card : ℝ)) ≤
      (α + τ) ^ (k - 2) := by
    rw [← Finset.prod_mul_distrib]
    calc ∏ i ∈ rest, (((Z i).set.card : ℝ)⁻¹ * ((A' ∩ (Z i).set).card : ℝ))
        = ∏ i ∈ rest, locDens (Z i) A' := Finset.prod_congr rfl fun i _ => by
            unfold locDens; rw [div_eq_inv_mul]
      _ ≤ ∏ _i ∈ rest, (α + τ) := Finset.prod_le_prod (fun i _ => locDens_nonneg _ _) fun i _ => by
            linarith [(abs_le.mp (hdens' i)).2]
      _ = (α + τ) ^ (k - 2) := by rw [Finset.prod_const, hrest_card]
  have hinner_eq : (((Z p.1).set.card : ℝ)⁻¹ * ((Z p.2).set.card : ℝ)⁻¹) *
      (∑ x ∈ (Z p.1).set, ∑ y ∈ (Z p.2).set,
        (if x + y ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
        (if x ∈ A' then (1 : ℝ) else 0) * (if y ∈ A' then (1 : ℝ) else 0)) =
      ((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set,
        (if u ∈ X' then (1 : ℝ) else 0) * convInd (A' ∩ (Z p.1).set) A' (Z p.2) u := by
    rw [mul_assoc]; congr 1
    unfold convInd convZ
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y hy => ?_
    let Lset : Finset ℤ := (Z p.1).set.filter (fun x => x + y ∈ (Z p.1).set)
    let Rset : Finset ℤ := (Z p.1).set.filter (fun u => u - y ∈ (Z p.1).set)
    have hL : ∑ x ∈ (Z p.1).set, ((Z p.2).set.card : ℝ)⁻¹ *
        ((if x + y ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
         (if x ∈ A' then (1 : ℝ) else 0) * (if y ∈ A' then (1 : ℝ) else 0)) =
        ∑ x ∈ Lset, ((Z p.2).set.card : ℝ)⁻¹ *
        ((if x + y ∈ X' then (1 : ℝ) else 0) *
         (if x ∈ A' then (1 : ℝ) else 0) * (if y ∈ A' then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_subset (Finset.filter_subset (fun x => x + y ∈ (Z p.1).set) _)]
      · refine Finset.sum_congr rfl fun x hx => ?_
        have hxyZ := (Finset.mem_filter.mp hx).2
        by_cases hX : x + y ∈ X'
        · rw [if_pos (Finset.mem_inter.mpr ⟨hX, hxyZ⟩), if_pos hX]
        · rw [if_neg (fun h => hX (Finset.mem_inter.mp h).1), if_neg hX]
      · intro x hx hnot
        have hxyZ : x + y ∉ (Z p.1).set := fun h => hnot (Finset.mem_filter.mpr ⟨hx, h⟩)
        rw [if_neg (fun h => hxyZ (Finset.mem_inter.mp h).2)]; ring
    have hR : ∑ u ∈ (Z p.1).set, (if u ∈ X' then (1 : ℝ) else 0) *
        ((if u - y ∈ A' ∩ (Z p.1).set then (1 : ℝ) else 0) *
         ((if y ∈ A' then (1 : ℝ) else 0) * unifMeas (Z p.2).set y)) =
        ∑ u ∈ Rset, ((Z p.2).set.card : ℝ)⁻¹ *
        ((if u ∈ X' then (1 : ℝ) else 0) *
         (if u - y ∈ A' then (1 : ℝ) else 0) * (if y ∈ A' then (1 : ℝ) else 0)) := by
      rw [← Finset.sum_subset (Finset.filter_subset (fun u => u - y ∈ (Z p.1).set) _)]
      · refine Finset.sum_congr rfl fun u hu => ?_
        have huyZ := (Finset.mem_filter.mp hu).2
        dsimp only [unifMeas]; rw [if_pos hy]
        by_cases hA : u - y ∈ A'
        · rw [if_pos (Finset.mem_inter.mpr ⟨hA, huyZ⟩), if_pos hA]; ring
        · rw [if_neg (fun h => hA (Finset.mem_inter.mp h).1), if_neg hA]; ring
      · intro u hu hnot
        have huyZ : u - y ∉ (Z p.1).set := fun h => hnot (Finset.mem_filter.mpr ⟨hu, h⟩)
        rw [if_neg (fun h => huyZ (Finset.mem_inter.mp h).2)]; ring
    rw [hL, hR]
    refine Finset.sum_bij (fun x _ => x + y) ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxZ, hxyZ⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hxyZ, by simpa [add_sub_cancel_right] using hxZ⟩
    · intro _ _ _ _ h; omega
    · intro u hu
      obtain ⟨huZ, huyZ⟩ := Finset.mem_filter.mp hu
      exact ⟨u - y, Finset.mem_filter.mpr ⟨huyZ, by simpa [sub_add_cancel] using huZ⟩, sub_add_cancel u y⟩
    · intro x _; simp [add_sub_cancel_right]
  have hinner_le : ((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set,
      (if u ∈ X' then (1 : ℝ) else 0) * convInd (A' ∩ (Z p.1).set) A' (Z p.2) u ≤
      ε * α ^ 2 + Real.sqrt δ := by
    have hdecomp : ((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set,
        (if u ∈ X' then (1 : ℝ) else 0) * convInd (A' ∩ (Z p.1).set) A' (Z p.2) u =
        locDens (Z p.1) X' * α ^ 2 +
        ((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set,
          (if u ∈ X' then (1 : ℝ) else 0) * (convInd (A' ∩ (Z p.1).set) A' (Z p.2) u - α ^ 2) := by
      have h1 : ∀ u ∈ (Z p.1).set,
          (if u ∈ X' then (1 : ℝ) else 0) * convInd (A' ∩ (Z p.1).set) A' (Z p.2) u =
          (if u ∈ X' then (1 : ℝ) else 0) * α ^ 2 +
          (if u ∈ X' then (1 : ℝ) else 0) * (convInd (A' ∩ (Z p.1).set) A' (Z p.2) u - α ^ 2) :=
        fun _ _ => by ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, mul_add]
      congr 1
      rw [← Finset.sum_mul, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.inter_comm, ← mul_assoc, ← div_eq_inv_mul]; rfl
    rw [hdecomp]
    have h1 : locDens (Z p.1) X' * α ^ 2 ≤ ε * α ^ 2 :=
      mul_le_mul_of_nonneg_right (hX' p.1) (sq_nonneg α)
    have h2 : ((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set,
        (if u ∈ X' then (1 : ℝ) else 0) * (convInd (A' ∩ (Z p.1).set) A' (Z p.2) u - α ^ 2) ≤
        Real.sqrt δ := by
      let d : ℤ → ℝ := fun u => |convInd (A' ∩ (Z p.1).set) A' (Z p.2) u - α ^ 2|
      have hle_abs : ((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set,
          (if u ∈ X' then (1 : ℝ) else 0) * (convInd (A' ∩ (Z p.1).set) A' (Z p.2) u - α ^ 2) ≤
          ((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set, d u := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        refine Finset.sum_le_sum fun u _ => ?_
        dsimp only [d]
        split_ifs
        · rw [one_mul]; exact le_abs_self _
        · rw [zero_mul]; exact abs_nonneg _
      have hcs : (((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set, d u) ^ 2 ≤
          ((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set, (d u) ^ 2 := by
        let P0 := FinProb.unifFinset (Z p.1).set (Z p.1).nonempty
        have hsq := P0.1.sq_expect_le (fun i => d (P0.2 i))
        have h1 := FinProb.unifFinset_expect (Z p.1).set (Z p.1).nonempty d
        have h2 := FinProb.unifFinset_expect (Z p.1).set (Z p.1).nonempty (fun x => (d x) ^ 2)
        dsimp only [P0] at hsq
        rw [h1, h2] at hsq
        exact hsq
      have hU2_p := hU2' p.1 p.2 hlt
      have hdsq : ∑ u ∈ (Z p.1).set, (d u) ^ 2 =
          ∑ u ∈ (Z p.1).set, (convInd (A' ∩ (Z p.1).set) A' (Z p.2) u - α ^ 2) ^ 2 :=
        Finset.sum_congr rfl fun u _ => sq_abs _
      rw [hdsq] at hcs
      have hnn : 0 ≤ ((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set, d u :=
        mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      have hsqrt : ((Z p.1).set.card : ℝ)⁻¹ * ∑ u ∈ (Z p.1).set, d u ≤ Real.sqrt δ := by
        rw [← Real.sqrt_sq hnn]; exact Real.sqrt_le_sqrt (hcs.trans hU2_p)
      exact hle_abs.trans hsqrt
    linarith
  have hinner_nn : 0 ≤ (((Z p.1).set.card : ℝ)⁻¹ * ((Z p.2).set.card : ℝ)⁻¹) *
      (∑ x ∈ (Z p.1).set, ∑ y ∈ (Z p.2).set,
        (if x + y ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
        (if x ∈ A' then (1 : ℝ) else 0) * (if y ∈ A' then (1 : ℝ) else 0)) := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ?_)
    split_ifs <;> norm_num
  have hrearr : ((((Z p.1).set.card : ℝ)⁻¹ * ((Z p.2).set.card : ℝ)⁻¹) *
        ∏ i ∈ rest, ((Z i).set.card : ℝ)⁻¹) *
      ((∑ x ∈ (Z p.1).set, ∑ y ∈ (Z p.2).set,
        (if x + y ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
        (if x ∈ A' then (1 : ℝ) else 0) * (if y ∈ A' then (1 : ℝ) else 0)) *
        ∏ i ∈ rest, ((A' ∩ (Z i).set).card : ℝ)) =
      ((∏ i ∈ rest, ((Z i).set.card : ℝ)⁻¹) * ∏ i ∈ rest, ((A' ∩ (Z i).set).card : ℝ)) *
      ((((Z p.1).set.card : ℝ)⁻¹ * ((Z p.2).set.card : ℝ)⁻¹) *
        ∑ x ∈ (Z p.1).set, ∑ y ∈ (Z p.2).set,
          (if x + y ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
          (if x ∈ A' then (1 : ℝ) else 0) * (if y ∈ A' then (1 : ℝ) else 0)) := by ring
  rw [hrearr]
  exact mul_le_mul hrest_le (hinner_eq.le.trans hinner_le) hinner_nn (by positivity)

private lemma lem_c_summing {k : ℕ} {A X : Finset ℤ} {z0 : ℤ} {Z : Fin k → SymNbhd}
    {α τ ε δ : ℝ}
    (hk : 2 ≤ k) (hα0 : 0 < α) (_hα1 : α ≤ 1)
    (hτ : 0 ≤ τ) (hε0 : 0 ≤ ε) (_hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hsum : IsSumming k A X)
    (hclosed : ∀ i : Fin k, ∀ hi : i.val + 1 < k, IsClosedPair τ (Z i) (Z ⟨i.val + 1, hi⟩))
    (hsub : ∀ i j : Fin k, i ≤ j → (Z j).set ⊆ (Z i).set)
    (hdens : ∀ i : Fin k, |cosetDens z0 (Z i) A - α| ≤ τ)
    (hX : ∀ i : Fin k, cosetDens (2 * z0) (Z i) X ≤ ε)
    (hU2 : ∀ i j : Fin k, i < j →
      ((Z i).set.card : ℝ)⁻¹ * ∑ x ∈ coset (2 * z0) (Z i),
        (cosetConvInd z0 (Z i) (Z j) A x - α ^ 2) ^ 2 ≤ δ)
    (hτ_small : 8 * (k : ℝ) * τ ≤ α)
    (hε_small : 16 * (k : ℝ) ^ 2 * ε ≤ 1)
    (hδ_small : 256 * (k : ℝ) ^ 4 * δ ≤ α ^ 4) :
    ((Z ⟨k - 1, by omega⟩).set.card : ℝ) ≤ 2 * (k : ℝ) ^ 2 / α ^ k := by
  classical
  let A' : Finset ℤ := A.image (· - z0)
  let X' : Finset ℤ := X.image (· - 2 * z0)
  have hsum' : IsSumming k A' X' := by
    intro S hSA' hSk
    let S0 : Finset ℤ := S.image (· + z0)
    have hS0A : S0 ⊆ A := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨u, hu, hueq⟩ := Finset.mem_image.mp (hSA' hy)
      have : y + z0 = u := by omega
      rwa [this]
    have hS0k : S0.card = k := by
      rw [Finset.card_image_of_injective _ (add_left_injective z0), hSk]
    obtain ⟨a, ha, b, hb, hne, habX⟩ := hsum S0 hS0A hS0k
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    refine ⟨a', ha', b', hb', fun h => hne (by omega), ?_⟩
    exact Finset.mem_image.mpr ⟨(a' + z0) + (b' + z0), habX, by ring⟩
  have hdens' : ∀ i : Fin k, |locDens (Z i) A' - α| ≤ τ := by
    intro i
    have heq : locDens (Z i) A' = cosetDens z0 (Z i) A := by
      unfold locDens cosetDens
      congr 2
      refine Finset.card_bij (fun x _ => x + z0) ?_ ?_ ?_
      · intro x hx
        obtain ⟨hxA', hxZ⟩ := Finset.mem_inter.mp hx
        obtain ⟨u, hu, hueq⟩ := Finset.mem_image.mp hxA'
        have hxzu : x + z0 = u := by omega
        exact Finset.mem_inter.mpr ⟨by rwa [hxzu], Finset.mem_image.mpr ⟨x, hxZ, rfl⟩⟩
      · intro x1 _ x2 _ h; omega
      · intro u hu
        obtain ⟨huA, huC⟩ := Finset.mem_inter.mp hu
        obtain ⟨y, hyZ, rfl⟩ := Finset.mem_image.mp huC
        exact ⟨y, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨y + z0, huA, by ring⟩, hyZ⟩, rfl⟩
    rw [heq]; exact hdens i
  have hX' : ∀ i : Fin k, locDens (Z i) X' ≤ ε := by
    intro i
    have heq : locDens (Z i) X' = cosetDens (2 * z0) (Z i) X := by
      unfold locDens cosetDens
      congr 2
      refine Finset.card_bij (fun x _ => x + 2 * z0) ?_ ?_ ?_
      · intro x hx
        obtain ⟨hxX', hxZ⟩ := Finset.mem_inter.mp hx
        obtain ⟨u, hu, hueq⟩ := Finset.mem_image.mp hxX'
        have hxzu : x + 2 * z0 = u := by omega
        exact Finset.mem_inter.mpr ⟨by rwa [hxzu], Finset.mem_image.mpr ⟨x, hxZ, rfl⟩⟩
      · intro x1 _ x2 _ h; omega
      · intro u hu
        obtain ⟨huX, huC⟩ := Finset.mem_inter.mp hu
        obtain ⟨y, hyZ, rfl⟩ := Finset.mem_image.mp huC
        exact ⟨y, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨y + 2 * z0, huX, by ring⟩, hyZ⟩, rfl⟩
    rw [heq]; exact hX i
  have hU2' : ∀ i j : Fin k, i < j →
      ((Z i).set.card : ℝ)⁻¹ * ∑ x ∈ (Z i).set,
        (convInd (A' ∩ (Z i).set) A' (Z j) x - α ^ 2) ^ 2 ≤ δ := by
    intro i j hij
    have hsum_eq : ∑ x ∈ (Z i).set, (convInd (A' ∩ (Z i).set) A' (Z j) x - α ^ 2) ^ 2 =
        ∑ u ∈ coset (2 * z0) (Z i), (cosetConvInd z0 (Z i) (Z j) A u - α ^ 2) ^ 2 := by
      unfold coset
      rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [cosetConvInd_shift]
    rw [hsum_eq]; exact hU2 i j hij
  let T : Finset (Fin k → ℤ) := Fintype.piFinset (fun i => (Z i).set)
  let pairs : Finset (Fin k × Fin k) := Finset.univ.filter (fun p => p.1 < p.2)
  have hpairs_le : (pairs.card : ℝ) ≤ (k : ℝ) ^ 2 / 2 := by
    have hnat : 2 * pairs.card ≤ k * k := by
      have hdisj : Disjoint pairs (Finset.univ.filter (fun p : Fin k × Fin k => p.2 < p.1)) := by
        rw [Finset.disjoint_left]; intro p h1 h2
        exact lt_asymm (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
      have hswap : (Finset.univ.filter (fun p : Fin k × Fin k => p.2 < p.1)).card = pairs.card := by
        refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
        · intro p hp; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
        · intro _ _ _ _ h; exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
        · intro q hq; exact ⟨(q.2, q.1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩, rfl⟩
      have hu : (pairs ∪ Finset.univ.filter (fun p : Fin k × Fin k => p.2 < p.1)).card ≤
          (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_le_card (Finset.subset_univ _)
      rw [Finset.card_union_of_disjoint hdisj, hswap, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hu
      omega
    have hR : (2 : ℝ) * (pairs.card : ℝ) ≤ (k : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast hnat
    linarith
  let Wprod : ℝ := (∏ i : Fin k, ((Z i).set.card : ℝ))⁻¹
  have hWprod_pos : 0 < Wprod := inv_pos.mpr (Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Z i).card_pos)
  let I : ℝ := Wprod * ∑ z ∈ T,
    (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) *
    (∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set \ X' then (1 : ℝ) else 0)
  have hI_lb : (1 / 2 : ℝ) * α ^ k ≤ I := by
    have hex_Zm : ∀ i : Fin k, ∃ Zm : SymNbhd,
        Zm.set ⊆ (Z i).set ∧
        (∀ hi : i.val + 1 < k, Zm.set + (Z ⟨i.val + 1, hi⟩).set ⊆ (Z i).set) ∧
        (((Z i).set \ Zm.set).card : ℝ) ≤ τ * ((Z i).set.card : ℝ) := by
      intro i
      by_cases hi : i.val + 1 < k
      · obtain ⟨Zm, Zp, h1, h2, h3⟩ := hclosed i hi
        have hZmZ : Zm.set ⊆ (Z i).set := fun x hx => by
          simpa using h1 (Finset.add_mem_add hx (Z ⟨i.val + 1, hi⟩).zero_mem)
        have hZZp : (Z i).set ⊆ Zp.set := fun x hx => by
          simpa using h2 (Finset.add_mem_add hx (Z ⟨i.val + 1, hi⟩).zero_mem)
        refine ⟨Zm, hZmZ, fun _ => h1, ?_⟩
        have hc : ((Z i).set \ Zm.set).card = (Z i).set.card - Zm.set.card := Finset.card_sdiff_of_subset hZmZ
        rw [hc, Nat.cast_sub (Finset.card_le_card hZmZ)]
        have hle1 : ((Z i).set.card : ℝ) ≤ (Zp.set.card : ℝ) := by exact_mod_cast Finset.card_le_card hZZp
        have hle2 : (Zm.set.card : ℝ) ≤ ((Z i).set.card : ℝ) := by exact_mod_cast Finset.card_le_card hZmZ
        nlinarith
      · refine ⟨Z i, Subset.rfl, fun h => (hi h).elim, ?_⟩
        simp; positivity
    choose Zm hZm_sub hZm_add hZm_sdiff using hex_Zm
    have hpt : ∀ z ∈ T,
        (∏ i : Fin k, if z i ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0) -
        ∑ p ∈ pairs,
          (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
          (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) ≤
        (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) *
        (∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set \ X' then (1 : ℝ) else 0) := by
      intro z hz
      let fA : ℝ := ∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0
      have hfA_nn : 0 ≤ fA := Finset.prod_nonneg fun _ _ => by split_ifs <;> norm_num
      have hbonf := one_sub_sum_le_prod_one_sub pairs
        (fun p => if z p.1 + z p.2 ∈ X' then (1 : ℝ) else 0)
        (fun _ _ => by split_ifs <;> norm_num)
        (fun _ _ => by split_ifs <;> norm_num)
      have hprod_eq : ∏ p ∈ pairs, (if z p.1 + z p.2 ∈ (Z p.1).set \ X' then (1 : ℝ) else 0) =
          (∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set then (1 : ℝ) else 0) *
          (∏ p ∈ pairs, (1 - if z p.1 + z p.2 ∈ X' then (1 : ℝ) else 0)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun p _ => ?_
        by_cases h1 : z p.1 + z p.2 ∈ (Z p.1).set <;> by_cases h2 : z p.1 + z p.2 ∈ X'
        · simp [Finset.mem_sdiff, h1, h2]
        · simp [Finset.mem_sdiff, h1, h2]
        · simp [Finset.mem_sdiff, h1, h2]
        · simp [Finset.mem_sdiff, h1, h2]
      have hZ_ind_ge : (∏ i : Fin k, if z i ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0) ≤
          fA * (∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set then (1 : ℝ) else 0) := by
        by_cases hall : ∀ i : Fin k, z i ∈ A' ∩ (Zm i).set
        · have hL : (∏ i : Fin k, if z i ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0) = 1 :=
            Finset.prod_eq_one fun i _ => if_pos (hall i)
          have hA : fA = 1 := Finset.prod_eq_one fun i _ => if_pos (Finset.mem_inter.mp (hall i)).1
          have hP : (∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set then (1 : ℝ) else 0) = 1 := by
            refine Finset.prod_eq_one fun p hp => if_pos ?_
            have hlt : p.1 < p.2 := (Finset.mem_filter.mp hp).2
            have hi1 : p.1.val + 1 < k := by have := p.2.isLt; omega
            have hle : (⟨p.1.val + 1, hi1⟩ : Fin k) ≤ p.2 := by
              change p.1.val + 1 ≤ p.2.val; exact hlt
            have hz1 : z p.1 ∈ (Zm p.1).set := (Finset.mem_inter.mp (hall p.1)).2
            have hz2 : z p.2 ∈ (Z ⟨p.1.val + 1, hi1⟩).set :=
              hsub _ _ hle (Fintype.mem_piFinset.mp hz p.2)
            exact hZm_add p.1 hi1 (Finset.add_mem_add hz1 hz2)
          rw [hL, hA, hP, mul_one]
        · push Not at hall
          obtain ⟨i0, hi0⟩ := hall
          have hL : (∏ i : Fin k, if z i ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i0) (if_neg hi0)
          rw [hL]
          exact mul_nonneg hfA_nn (Finset.prod_nonneg fun _ _ => by split_ifs <;> norm_num)
      have hterm_le : ∀ p ∈ pairs,
          (∏ q ∈ pairs, if z q.1 + z q.2 ∈ (Z q.1).set then (1 : ℝ) else 0) *
            (if z p.1 + z p.2 ∈ X' then (1 : ℝ) else 0) ≤
          if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0 := by
        intro p hp
        by_cases h1 : z p.1 + z p.2 ∈ (Z p.1).set
        · have hprod1 : (∏ q ∈ pairs, if z q.1 + z q.2 ∈ (Z q.1).set then (1 : ℝ) else 0) ≤ 1 :=
            Finset.prod_le_one (fun _ _ => by split_ifs <;> norm_num) (fun _ _ => by split_ifs <;> norm_num)
          by_cases h2 : z p.1 + z p.2 ∈ X'
          · rw [if_pos h2, mul_one, if_pos (Finset.mem_inter.mpr ⟨h2, h1⟩)]; exact hprod1
          · rw [if_neg h2, mul_zero, if_neg (fun h => h2 (Finset.mem_inter.mp h).1)]
        · have hprod0 : (∏ q ∈ pairs, if z q.1 + z q.2 ∈ (Z q.1).set then (1 : ℝ) else 0) = 0 :=
            Finset.prod_eq_zero hp (if_neg h1)
          rw [hprod0, zero_mul]
          split_ifs <;> norm_num
      have hP_nn : 0 ≤ ∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set then (1 : ℝ) else 0 :=
        Finset.prod_nonneg fun _ _ => by split_ifs <;> norm_num
      rw [hprod_eq]
      calc (∏ i : Fin k, if z i ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0) -
            ∑ p ∈ pairs, (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) * fA
          ≤ fA * (∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set then (1 : ℝ) else 0) -
            fA * ((∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set then (1 : ℝ) else 0) *
              ∑ p ∈ pairs, if z p.1 + z p.2 ∈ X' then (1 : ℝ) else 0) := by
            have hsum_le : fA * ((∏ q ∈ pairs, if z q.1 + z q.2 ∈ (Z q.1).set then (1 : ℝ) else 0) *
                ∑ p ∈ pairs, if z p.1 + z p.2 ∈ X' then (1 : ℝ) else 0) ≤
                ∑ p ∈ pairs, (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) * fA := by
              rw [Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_le_sum fun p hp => ?_
              have h1 := mul_le_mul_of_nonneg_left (hterm_le p hp) hfA_nn
              linarith
            linarith
        _ = fA * ((∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set then (1 : ℝ) else 0) *
              (1 - ∑ p ∈ pairs, if z p.1 + z p.2 ∈ X' then (1 : ℝ) else 0)) := by ring
        _ ≤ fA * ((∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set then (1 : ℝ) else 0) *
              (∏ p ∈ pairs, (1 - if z p.1 + z p.2 ∈ X' then (1 : ℝ) else 0))) := by
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbonf hP_nn) hfA_nn
    have hpi_sum_prod : ∀ (S : Fin k → Finset ℤ) (f : Fin k → ℤ → ℝ),
        ∑ z ∈ Fintype.piFinset S, ∏ i : Fin k, f i (z i) = ∏ i : Fin k, ∑ x ∈ S i, f i x :=
      fun S f => (Finset.prod_univ_sum S f).symm
    have hmain_term : (α - 2 * τ) ^ k ≤
        Wprod * ∑ z ∈ T, ∏ i : Fin k, if z i ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0 := by
      rw [hpi_sum_prod (fun i => (Z i).set) (fun i x => if x ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0)]
      have hfac_eq : Wprod * ∏ i : Fin k, ∑ x ∈ (Z i).set, (if x ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0) =
          ∏ i : Fin k, (((Z i).set.card : ℝ)⁻¹ * ∑ x ∈ (Z i).set, if x ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0) := by
        dsimp only [Wprod]
        rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
      rw [hfac_eq]
      have hα2τ_nn : 0 ≤ α - 2 * τ := by
        have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        nlinarith
      calc (α - 2 * τ) ^ k = ∏ _i : Fin k, (α - 2 * τ) := by simp
        _ ≤ ∏ i : Fin k, (((Z i).set.card : ℝ)⁻¹ * ∑ x ∈ (Z i).set, if x ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0) := by
            refine Finset.prod_le_prod (fun _ _ => hα2τ_nn) fun i _ => ?_
            have hZpos : (0 : ℝ) < ((Z i).set.card : ℝ) := Nat.cast_pos.mpr (Z i).card_pos
            have hsum_eq : ∑ x ∈ (Z i).set, (if x ∈ A' ∩ (Zm i).set then (1 : ℝ) else 0) =
                ((A' ∩ (Zm i).set).card : ℝ) := by
              rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one]
              congr 2
              ext x; simp only [Finset.mem_inter]
              exact ⟨fun ⟨_, hA, hZm⟩ => ⟨hA, hZm⟩, fun ⟨hA, hZm⟩ => ⟨hZm_sub i hZm, hA, hZm⟩⟩
            rw [hsum_eq]
            have hdiff_sub : (A' ∩ (Z i).set) \ (A' ∩ (Zm i).set) ⊆ (Z i).set \ (Zm i).set := by
              intro x hx
              obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
              obtain ⟨hxA, hxZ⟩ := Finset.mem_inter.mp h1
              exact Finset.mem_sdiff.mpr ⟨hxZ, fun hZm => h2 (Finset.mem_inter.mpr ⟨hxA, hZm⟩)⟩
            have hcard_ge : ((A' ∩ (Z i).set).card : ℝ) - (((Z i).set \ (Zm i).set).card : ℝ) ≤
                ((A' ∩ (Zm i).set).card : ℝ) := by
              have hsub_inter : A' ∩ (Zm i).set ⊆ A' ∩ (Z i).set :=
                Finset.inter_subset_inter Subset.rfl (hZm_sub i)
              have h1 := Finset.card_sdiff_add_card_eq_card hsub_inter
              have h2 := Finset.card_le_card hdiff_sub
              have hnat : (A' ∩ (Z i).set).card ≤ (A' ∩ (Zm i).set).card + ((Z i).set \ (Zm i).set).card := by
                omega
              have hR : ((A' ∩ (Z i).set).card : ℝ) ≤ ((A' ∩ (Zm i).set).card : ℝ) + (((Z i).set \ (Zm i).set).card : ℝ) := by
                exact_mod_cast hnat
              linarith
            have hdens_lb : α - τ ≤ locDens (Z i) A' := by linarith [(abs_le.mp (hdens' i)).1]
            have hdens_mul : (α - τ) * ((Z i).set.card : ℝ) ≤ ((A' ∩ (Z i).set).card : ℝ) := by
              unfold locDens at hdens_lb; rwa [le_div_iff₀ hZpos] at hdens_lb
            have hZm_lb : (α - 2 * τ) * ((Z i).set.card : ℝ) ≤ ((A' ∩ (Zm i).set).card : ℝ) := by
              linarith [hZm_sdiff i]
            rw [← div_eq_inv_mul, le_div_iff₀ hZpos]; exact hZm_lb
    have hpair_err : ∀ p ∈ pairs,
        Wprod * ∑ z ∈ T,
          (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
          (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) ≤
        (α + τ) ^ (k - 2) * (ε * α ^ 2 + Real.sqrt δ) :=
      fun p hp => lem_c_pair_err hα0 hτ hε0 hδ hdens' hX' hU2' (Finset.mem_filter.mp hp).2
    have hsum_pt := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib, Finset.sum_comm] at hsum_pt
    have hmul_pt := mul_le_mul_of_nonneg_left hsum_pt hWprod_pos.le
    rw [mul_sub] at hmul_pt
    have hmul_err : Wprod * ∑ p ∈ pairs, ∑ z ∈ T,
        (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
        (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) =
        ∑ p ∈ pairs, Wprod * ∑ z ∈ T,
        (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
        (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) :=
      Finset.mul_sum _ _ _
    rw [hmul_err] at hmul_pt
    have herr_total : ∑ p ∈ pairs, Wprod * ∑ z ∈ T,
        (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
        (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) ≤
        (1 / 4 : ℝ) * α ^ k := by
      calc ∑ p ∈ pairs, Wprod * ∑ z ∈ T,
            (if z p.1 + z p.2 ∈ X' ∩ (Z p.1).set then (1 : ℝ) else 0) *
            (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0)
          ≤ ∑ _p ∈ pairs, ((α + τ) ^ (k - 2) * (ε * α ^ 2 + Real.sqrt δ)) := Finset.sum_le_sum hpair_err
        _ = (pairs.card : ℝ) * ((α + τ) ^ (k - 2) * (ε * α ^ 2 + Real.sqrt δ)) := by simp
        _ ≤ ((k : ℝ) ^ 2 / 2) * ((2 * α ^ (k - 2)) * (ε * α ^ 2 + Real.sqrt δ)) := by
            have hpow2 := pow_add_le_two hα0 hτ hτ_small
            have h1 := mul_le_mul_of_nonneg_right hpow2 (by positivity : 0 ≤ ε * α ^ 2 + Real.sqrt δ)
            exact mul_le_mul hpairs_le h1 (by positivity) (by positivity)
        _ = (k : ℝ) ^ 2 * ε * (α ^ (k - 2) * α ^ 2) + (k : ℝ) ^ 2 * Real.sqrt δ * α ^ (k - 2) := by ring
        _ ≤ (1 / 16 : ℝ) * α ^ k + (1 / 16 : ℝ) * α ^ k := by
            have hα_split : α ^ (k - 2) * α ^ 2 = α ^ k := by
              rw [← pow_add, Nat.sub_add_cancel hk]
            rw [hα_split]
            have ht1 : (k : ℝ) ^ 2 * ε * α ^ k ≤ (1 / 16 : ℝ) * α ^ k := by
              have : (k : ℝ) ^ 2 * ε ≤ 1 / 16 := by linarith
              exact mul_le_mul_of_nonneg_right this (pow_nonneg hα0.le k)
            have ht2 : (k : ℝ) ^ 2 * Real.sqrt δ * α ^ (k - 2) ≤ (1 / 16 : ℝ) * α ^ k := by
              have hsqrt_le : 16 * (k : ℝ) ^ 2 * Real.sqrt δ ≤ α ^ 2 := by
                have hsq : (16 * (k : ℝ) ^ 2 * Real.sqrt δ) ^ 2 ≤ (α ^ 2) ^ 2 := by
                  rw [mul_pow, mul_pow, Real.sq_sqrt hδ]; nlinarith
                nlinarith [Real.sqrt_nonneg δ, sq_nonneg α]
              have : (k : ℝ) ^ 2 * Real.sqrt δ ≤ (1 / 16 : ℝ) * α ^ 2 := by linarith
              calc (k : ℝ) ^ 2 * Real.sqrt δ * α ^ (k - 2)
                  ≤ ((1 / 16 : ℝ) * α ^ 2) * α ^ (k - 2) :=
                    mul_le_mul_of_nonneg_right this (pow_nonneg hα0.le _)
                _ = (1 / 16 : ℝ) * (α ^ (k - 2) * α ^ 2) := by ring
                _ = (1 / 16 : ℝ) * α ^ k := by rw [hα_split]
            linarith
        _ = (1 / 4 : ℝ) * α ^ k - (1 / 8 : ℝ) * α ^ k := by ring
        _ ≤ (1 / 4 : ℝ) * α ^ k := by linarith [pow_nonneg hα0.le k]
    have hmain_ge := pow_sub_ge_three_quarters hα0 hτ hτ_small
    dsimp only [I]
    linarith
  have hI_ub : I ≤ (pairs.card : ℝ) / ((Z ⟨k - 1, by omega⟩).set.card : ℝ) := by
    let goodT : Finset (Fin k → ℤ) := T.filter (fun z =>
      (∀ i : Fin k, z i ∈ A') ∧ (∀ p ∈ pairs, z p.1 + z p.2 ∈ (Z p.1).set \ X'))
    have hI_eq : I = Wprod * (goodT.card : ℝ) := by
      dsimp only [I]; congr 1
      have hterm : ∀ z ∈ T,
          (∏ i : Fin k, if z i ∈ A' then (1 : ℝ) else 0) *
          (∏ p ∈ pairs, if z p.1 + z p.2 ∈ (Z p.1).set \ X' then (1 : ℝ) else 0) =
          if z ∈ goodT then (1 : ℝ) else 0 := by
        intro z hz
        by_cases hg : z ∈ goodT
        · obtain ⟨_, hA, hP⟩ := Finset.mem_filter.mp hg
          rw [if_pos hg, Finset.prod_eq_one (fun i _ => if_pos (hA i)),
            Finset.prod_eq_one (fun p hp => if_pos (hP p hp)), mul_one]
        · rw [if_neg hg]
          by_cases hA : ∀ i : Fin k, z i ∈ A'
          · have hnotP : ¬ (∀ p ∈ pairs, z p.1 + z p.2 ∈ (Z p.1).set \ X') := fun hP =>
              hg (Finset.mem_filter.mpr ⟨hz, hA, hP⟩)
            push Not at hnotP
            obtain ⟨p, hp, hnp⟩ := hnotP
            rw [Finset.prod_eq_zero hp (if_neg hnp), mul_zero]
          · push Not at hA
            obtain ⟨i, hi⟩ := hA
            rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), zero_mul]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.filter_subset _ _),
        Finset.sum_const, nsmul_eq_mul, mul_one]
    have hgood_sub : goodT ⊆ pairs.biUnion (fun p => T.filter (fun z => z p.1 = z p.2)) := by
      intro z hz
      obtain ⟨hzT, hA, hP⟩ := Finset.mem_filter.mp hz
      by_contra hno
      have hinj : Function.Injective z := by
        intro i j hij
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hno (Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩,
            Finset.mem_filter.mpr ⟨hzT, hij⟩⟩)
        · exact hno (Finset.mem_biUnion.mpr ⟨(j, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩,
            Finset.mem_filter.mpr ⟨hzT, hij.symm⟩⟩)
      have himg_sub : (Finset.univ : Finset (Fin k)).image z ⊆ A' := by
        intro x hx; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact hA i
      have himg_card : ((Finset.univ : Finset (Fin k)).image z).card = k := by
        rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      obtain ⟨a, ha, b, hb, hne, habX⟩ := hsum' _ himg_sub himg_card
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
      have hij : i ≠ j := fun h => hne (congrArg z h)
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact (Finset.mem_sdiff.mp (hP (i, j) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩))).2 habX
      · rw [add_comm] at habX
        exact (Finset.mem_sdiff.mp (hP (j, i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩))).2 habX
    have hpair_card : ∀ p ∈ pairs,
        ((T.filter (fun z => z p.1 = z p.2)).card : ℝ) * ((Z p.1).set.card : ℝ) ≤
        ∏ i : Fin k, ((Z i).set.card : ℝ) := by
      intro p hp
      have hne : p.1 ≠ p.2 := ne_of_lt (Finset.mem_filter.mp hp).2
      let U : Finset ({i : Fin k // i ≠ p.1} → ℤ) := Fintype.piFinset (fun i => (Z i.1).set)
      have hcard_le : (T.filter (fun z => z p.1 = z p.2)).card ≤ U.card := by
        refine Finset.card_le_card_of_injOn (fun z i => z i.1) ?_ ?_
        · intro z hz
          rw [Finset.mem_coe] at hz ⊢
          exact Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp (Finset.mem_filter.mp hz).1 i.1
        · intro z1 hz1 z2 hz2 h
          funext i
          by_cases hi : i = p.1
          · subst hi
            have e1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hz1)).2
            have e2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hz2)).2
            exact e1.trans ((congrFun h ⟨p.2, hne.symm⟩).trans e2.symm)
          · exact congrFun h ⟨i, hi⟩
      have hU_card : (U.card : ℝ) * ((Z p.1).set.card : ℝ) = ∏ i : Fin k, ((Z i).set.card : ℝ) := by
        have hnat : U.card * (Z p.1).set.card = ∏ i : Fin k, (Z i).set.card := by
          dsimp only [U]; rw [Fintype.card_piFinset]
          have hprod := Finset.mul_prod_erase (Finset.univ : Finset (Fin k)) (fun i => (Z i).set.card) (Finset.mem_univ p.1)
          rw [mul_comm, ← hprod]
          congr 1
          refine Finset.prod_bij (fun i _ => i.1) ?_ ?_ ?_ ?_
          · intro i _; exact Finset.mem_erase.mpr ⟨i.2, Finset.mem_univ _⟩
          · intro _ _ _ _ h; exact Subtype.ext h
          · intro j hj; exact ⟨⟨j, (Finset.mem_erase.mp hj).1⟩, Finset.mem_univ _, rfl⟩
          · intro _ _; rfl
        exact_mod_cast hnat
      rw [← hU_card]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) (Nat.cast_nonneg _)
    have hgood_le : (goodT.card : ℝ) ≤
        ∑ p ∈ pairs, ((T.filter (fun z => z p.1 = z p.2)).card : ℝ) := by
      have hnat : goodT.card ≤ ∑ p ∈ pairs, (T.filter (fun z => z p.1 = z p.2)).card :=
        (Finset.card_le_card hgood_sub).trans Finset.card_biUnion_le
      exact_mod_cast hnat
    rw [hI_eq]
    calc Wprod * (goodT.card : ℝ)
        ≤ Wprod * ∑ p ∈ pairs, ((T.filter (fun z => z p.1 = z p.2)).card : ℝ) :=
          mul_le_mul_of_nonneg_left hgood_le hWprod_pos.le
      _ = ∑ p ∈ pairs, Wprod * ((T.filter (fun z => z p.1 = z p.2)).card : ℝ) := Finset.mul_sum _ _ _
      _ ≤ ∑ _p ∈ pairs, (((Z ⟨k - 1, by omega⟩).set.card : ℝ))⁻¹ := by
          refine Finset.sum_le_sum fun p hp => ?_
          have h1 : Wprod * ((T.filter (fun z => z p.1 = z p.2)).card : ℝ) ≤ ((Z p.1).set.card : ℝ)⁻¹ := by
            dsimp only [Wprod]
            have hPpos : (0 : ℝ) < ∏ i : Fin k, ((Z i).set.card : ℝ) :=
              Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Z i).card_pos
            have hZppos : (0 : ℝ) < ((Z p.1).set.card : ℝ) := Nat.cast_pos.mpr (Z p.1).card_pos
            rw [inv_mul_le_iff₀ hPpos, le_mul_inv_iff₀ hZppos]
            exact hpair_card p hp
          have hle_last : ((Z ⟨k - 1, by omega⟩).set.card : ℝ) ≤ ((Z p.1).set.card : ℝ) := by
            have hple : p.1 ≤ ⟨k - 1, by omega⟩ := by change p.1.val ≤ k - 1; have := p.1.isLt; omega
            exact_mod_cast Finset.card_le_card (hsub _ _ hple)
          exact h1.trans (inv_anti₀ (Nat.cast_pos.mpr (Z ⟨k - 1, by omega⟩).card_pos) hle_last)
      _ = (pairs.card : ℝ) / ((Z ⟨k - 1, by omega⟩).set.card : ℝ) := by
          simp [div_eq_mul_inv]
  have hcomb : (1 / 2 : ℝ) * α ^ k ≤ ((k : ℝ) ^ 2 / 2) / ((Z ⟨k - 1, by omega⟩).set.card : ℝ) := by
    calc (1 / 2 : ℝ) * α ^ k ≤ I := hI_lb
      _ ≤ (pairs.card : ℝ) / ((Z ⟨k - 1, by omega⟩).set.card : ℝ) := hI_ub
      _ ≤ ((k : ℝ) ^ 2 / 2) / ((Z ⟨k - 1, by omega⟩).set.card : ℝ) :=
          div_le_div_of_nonneg_right hpairs_le (Nat.cast_nonneg _)
  have hZk_pos : (0 : ℝ) < ((Z ⟨k - 1, by omega⟩).set.card : ℝ) :=
    Nat.cast_pos.mpr (Z ⟨k - 1, by omega⟩).card_pos
  have hαk_pos : (0 : ℝ) < α ^ k := pow_pos hα0 k
  rw [le_div_iff₀ hαk_pos]
  rw [le_div_iff₀ hZk_pos] at hcomb
  linarith

/- ### Module 5B: Inductive step (`lem_inductivestep`) and regularity iteration (`cor_iju`) -/

private lemma scale2_subset_iterAddNbhd (W : SymNbhd) :
    ∀ t : ℕ, (W.scale2 t).set ⊆ (iterAddNbhd (2 ^ t) W).set := by
  intro t
  induction t with
  | zero =>
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    change (2 : ℤ) ^ 0 * y ∈ ({0} : Finset ℤ) + W.set
    rw [finset_singleton_zero_add]; simpa using hy
  | succ t ih =>
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hpow : 2 ^ (t + 1) = 2 ^ t + 2 ^ t := by ring
    rw [hpow, iterAddNbhd_add_set]
    have hy' : (2 : ℤ) ^ t * y ∈ (iterAddNbhd (2 ^ t) W).set :=
      ih (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    have h2 : (2 : ℤ) ^ (t + 1) * y = (2 : ℤ) ^ t * y + (2 : ℤ) ^ t * y := by rw [pow_succ]; ring
    rw [h2]
    exact Finset.add_mem_add hy' hy'

private lemma scale2_subset_sys_level (T : Sys) (hT : T.IsFinite) {W : SymNbhd} {m0 s r : ℕ}
    (hsr : s ≤ r) (hW : W.set ⊆ (T.toSymNbhd hT (m0 + r)).set) :
    (W.scale2 s).set ⊆ (T.toSymNbhd hT m0).set := by
  have h1 : (W.scale2 s).set ⊆ (iterAddNbhd (2 ^ s) W).set := scale2_subset_iterAddNbhd W s
  have hW' : W.set ⊆ (T.toSymNbhd hT (m0 + s)).set := fun x hx => by
    have hmem : x ∈ T.set (m0 + r) := (Set.Finite.mem_toFinset _).mp (hW hx)
    exact (Set.Finite.mem_toFinset _).mpr (T.antitone (by omega) hmem)
  have hiter_mono : ∀ n : ℕ, (iterAddNbhd n W).set ⊆ (iterAddNbhd n (T.toSymNbhd hT (m0 + s))).set := by
    intro n
    induction n with
    | zero => exact Subset.rfl
    | succ n ih => exact Finset.add_subset_add ih hW'
  exact (h1.trans (hiter_mono (2 ^ s))).trans (iterAddNbhd_pow_subset T hT s m0)

private lemma symNbhd_scale2_scale2 (W : SymNbhd) (a b : ℕ) :
    (W.scale2 b).scale2 a = W.scale2 (a + b) := by
  cases W with
  | mk S h0 hneg =>
    dsimp only [SymNbhd.scale2]
    congr 1
    ext x
    simp only [scale2Fin, Finset.mem_image]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by rw [← mul_assoc, ← pow_add]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨(2 : ℤ) ^ b * y, ⟨y, hy, rfl⟩, by rw [← mul_assoc, ← pow_add]⟩

private lemma symNbhd_scale2_mono {W1 W2 : SymNbhd} (m : ℕ) (h : W1.set ⊆ W2.set) :
    (W1.scale2 m).set ⊆ (W2.scale2 m).set :=
  Finset.image_subset_image h

private lemma build_nested_chain (T : Sys) (hT : T.IsFinite) {d k r : ℕ}
    (hd : T.HasDim d) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) :
    let step_m : ℕ := Nat.clog 2 (Nat.ceil (2 * (d : ℝ) / η)) + 2
    let mSeq : ℕ → ℕ := fun i => r + i * step_m
    ∃ Z' : Fin k → SymNbhd,
      (∀ i : Fin k, (T.toSymNbhd hT (mSeq i.val + 1)).set ⊆ (Z' i).set) ∧
      (∀ i : Fin k, (Z' i).set ⊆ (T.toSymNbhd hT (mSeq i.val)).set) ∧
      (∀ i : Fin k, IsClosedPair η (Z' i) (T.toSymNbhd hT (mSeq (i.val + 1)))) := by
  classical
  intro step_m mSeq
  have hstep2 : 2 ≤ step_m := by dsimp [step_m]; omega
  have hdm : (2 : ℝ) * (d : ℝ) ≤ (2 ^ (step_m - 2) : ℝ) * η := by
    have h1 : 2 * (d : ℝ) / η ≤ (Nat.ceil (2 * (d : ℝ) / η) : ℝ) := Nat.le_ceil _
    have h2 : Nat.ceil (2 * (d : ℝ) / η) ≤ 2 ^ (step_m - 2) := by
      have : step_m - 2 = Nat.clog 2 (Nat.ceil (2 * (d : ℝ) / η)) := by dsimp [step_m]; omega
      rw [this]; exact Nat.le_pow_clog (by norm_num) _
    exact (div_le_iff₀ hη0).mp (h1.trans (by exact_mod_cast h2))
  have hex : ∀ i : Fin k, ∃ Zi : SymNbhd,
      (T.toSymNbhd hT (mSeq i.val + 1)).set ⊆ Zi.set ∧
      Zi.set ⊆ (T.toSymNbhd hT (mSeq i.val)).set ∧
      IsClosedPair η Zi (T.toSymNbhd hT (mSeq (i.val + 1))) := by
    intro i
    let Ti : Sys := T.dilate (mSeq i.val)
    have hTifin : Ti.IsFinite := T.dilate_isFinite (mSeq i.val) hT
    have hTidim : Ti.HasDim d := T.dilate_hasDim (mSeq i.val) hd
    obtain ⟨Zi, hlo, hhi, hcl⟩ := lem_cc Ti hTifin hTidim hη0 hη1 hstep2 hdm
    have heq1 : (Ti.toSymNbhd hTifin 1).set = (T.toSymNbhd hT (mSeq i.val + 1)).set := by
      ext x; simp [Ti, Sys.toSymNbhd, Sys.dilate, add_comm]
    have heq0 : (Ti.toSymNbhd hTifin 0).set = (T.toSymNbhd hT (mSeq i.val)).set := by
      ext x; simp [Ti, Sys.toSymNbhd, Sys.dilate]
    have heqm : (Ti.toSymNbhd hTifin step_m).set = (T.toSymNbhd hT (mSeq (i.val + 1))).set := by
      ext x
      have hidx : step_m + mSeq i.val = mSeq (i.val + 1) := by
        dsimp only [mSeq]; rw [Nat.add_mul, one_mul]; omega
      simp [Ti, Sys.toSymNbhd, Sys.dilate, hidx]
    refine ⟨Zi, by rwa [← heq1], by rwa [← heq0], ?_⟩
    obtain ⟨Zm, Zp, h1, h2, h3⟩ := hcl
    exact ⟨Zm, Zp, by rwa [← heqm], by rwa [← heqm], h3⟩
  choose Z' hlo hhi hcl using hex
  exact ⟨Z', hlo, hhi, hcl⟩

private lemma lem_inductivestep_case2_pointwise {A : Finset ℤ}
    {Z0 Z1 W'' : SymNbhd} {a : ℤ} {α β η δ₃ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hinc : (Z0.set.card : ℝ)⁻¹ * ∑ x ∈ Z0.set, (convInd (A.image (· - a)) W''.set W'' x - α) ^ 2 ≥
      (Z0.set.card : ℝ)⁻¹ * ∑ x ∈ Z0.set, (convInd (A.image (· - a) ∩ Z0.set) (A.image (· - a)) Z1 x - α ^ 2) ^ 2 -
        (δ₃ ^ 2 + 8 * η / δ₃ ^ 2 + 2 * δ₃ + 3 * η + 2 * |locDens Z1 (A.image (· - a)) - α|)) :
    (Z0.set.card : ℝ)⁻¹ * ∑ u ∈ coset a Z0, (convInd A W''.set W'' u - β) ^ 2 ≥
      (Z0.set.card : ℝ)⁻¹ * ∑ u ∈ coset (2 * a) Z0, (cosetConvInd a Z0 Z1 A u - α ^ 2) ^ 2 -
        (δ₃ ^ 2 + 8 * η / δ₃ ^ 2 + 2 * δ₃ + 3 * η + 2 * |cosetDens a Z1 A - α| + 2 * |β - α|) := by
  have hL_eq : ∑ u ∈ coset a Z0, (convInd A W''.set W'' u - α) ^ 2 =
      ∑ x ∈ Z0.set, (convInd (A.image (· - a)) W''.set W'' x - α) ^ 2 := by
    unfold coset
    rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 2
    unfold convInd convZ
    refine Finset.sum_congr rfl fun y _ => ?_
    have hiff : x + a - y ∈ A ↔ x - y ∈ A.image (· - a) := by
      simp only [Finset.mem_image]
      constructor
      · intro h; exact ⟨x + a - y, h, by ring⟩
      · rintro ⟨u, hu, heq⟩
        have hxa : x + a - y = u := by omega
        rwa [hxa]
    dsimp only
    by_cases hc : x - y ∈ A.image (· - a)
    · rw [if_pos (hiff.mpr hc), if_pos hc]
    · rw [if_neg (mt hiff.mp hc), if_neg hc]
  have hR_eq : ∑ u ∈ coset (2 * a) Z0, (cosetConvInd a Z0 Z1 A u - α ^ 2) ^ 2 =
      ∑ x ∈ Z0.set, (convInd (A.image (· - a) ∩ Z0.set) (A.image (· - a)) Z1 x - α ^ 2) ^ 2 := by
    unfold coset
    rw [Finset.sum_image (fun _ _ _ _ h => add_right_cancel h)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [cosetConvInd_shift]
  have hdens_eq : locDens Z1 (A.image (· - a)) = cosetDens a Z1 A := by
    unfold locDens cosetDens
    congr 2
    refine Finset.card_bij (fun x _ => x + a) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxA, hxZ⟩ := Finset.mem_inter.mp hx
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hxA
      have hxa : x + a = u := by omega
      exact Finset.mem_inter.mpr ⟨by rwa [hxa], Finset.mem_image.mpr ⟨x, hxZ, rfl⟩⟩
    · intro _ _ _ _ h; omega
    · intro u hu
      obtain ⟨huA, huC⟩ := Finset.mem_inter.mp hu
      obtain ⟨y, hyZ, rfl⟩ := Finset.mem_image.mp huC
      exact ⟨y, Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨y + a, huA, by ring⟩, hyZ⟩, rfl⟩
  have hshift_beta : (Z0.set.card : ℝ)⁻¹ * ∑ u ∈ coset a Z0, (convInd A W''.set W'' u - α) ^ 2 - 2 * |β - α| ≤
      (Z0.set.card : ℝ)⁻¹ * ∑ u ∈ coset a Z0, (convInd A W''.set W'' u - β) ^ 2 := by
    have hpt : ∀ u ∈ coset a Z0, (convInd A W''.set W'' u - α) ^ 2 - 2 * |β - α| ≤
        (convInd A W''.set W'' u - β) ^ 2 := by
      intro u _
      set v := convInd A W''.set W'' u
      have hv0 : 0 ≤ v := convInd_nonneg _ _ _ _
      have hv1 : v ≤ 1 := convInd_le_one _ _ _ _
      have heq : (v - α) ^ 2 - (v - β) ^ 2 = (2 * v - α - β) * (β - α) := by ring
      have habs : |2 * v - α - β| ≤ 2 := by rw [abs_le]; constructor <;> linarith
      have h1 : (2 * v - α - β) * (β - α) ≤ |2 * v - α - β| * |β - α| := by
        rw [← abs_mul]; exact le_abs_self _
      nlinarith [abs_nonneg (β - α)]
    have hsum := Finset.sum_le_sum hpt
    rw [Finset.sum_sub_distrib, Finset.sum_const, coset_card, nsmul_eq_mul] at hsum
    have hmul := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (Nat.cast_nonneg Z0.set.card))
    have hZ0pos : ((Z0.set.card : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr Z0.card_pos.ne'
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hZ0pos, one_mul] at hmul
    exact hmul
  rw [← hL_eq, ← hR_eq, hdens_eq] at hinc
  linarith

private lemma lem_inductivestep {k r d D : ℕ} {A S : Finset ℤ}
    {P : FinProb} {z : Fin P.N → ℤ} {Z : Fin P.N → SymNbhd}
    {T : Fin P.N → Sys} (hT : ∀ ω, (T ω).IsFinite)
    {τ δ ν : ℝ}
    (hk : 2 ≤ k) (hr : 1 ≤ r)
    (hτ0 : 0 < τ) (hτ1 : τ ≤ 1 / 2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hν0 : 0 < ν) (hν1 : ν ≤ 1 / 2)
    (hτ_small : 32768 * ((r + 1 : ℕ) : ℝ) * τ ≤ δ ^ 2)
    (hZT : ∀ ω, IsClosedPair τ (Z ω) ((T ω).toSymNbhd (hT ω) 0))
    (hTdim : ∀ ω, (T ω).HasDim d)
    (hTcov : ∀ ω, covFlat (S : Set ℤ) ((T ω).set 0) ≤ ((2 ^ D : ℕ) : ℕ∞)) :
    let δ₃ : ℝ := δ / 16
    let η : ℝ := min (δ ^ 3 / (65536 * ((r + 1 : ℕ) : ℝ))) ν
    let dB : ℕ := 3 * Nat.floor (2 / δ₃ ^ 2)
    let DB : ℕ := 3 * (Nat.clog 2 (Nat.ceil (8 / δ₃)) + 2) * Nat.floor (2 / δ₃ ^ 2)
    let step_m : ℕ := Nat.clog 2 (Nat.ceil (2 * (d : ℝ) / η)) + 2
    let m' : ℕ := Nat.clog 2 (Nat.ceil (2 * ((d + dB : ℕ) : ℝ) / η)) + 2
    let Dnew : ℕ := D + (3 * r + k * step_m + 2) * d + DB + (4 * r + m' + 2) * (d + dB)
    (∃ (P'' : FinProb) (z'' : Fin P''.N → ℤ) (Z'' : Fin P''.N → SymNbhd)
      (T'' : Fin P''.N → Sys) (hT'' : ∀ ω'', (T'' ω'').IsFinite),
      tvLe (fun x => P''.expect (fun ω'' => unifMeas (coset (z'' ω'') (Z'' ω'')) x))
        (fun x => P.expect (fun ω => unifMeas (coset (z ω) (Z ω)) x)) (2 * τ + 2 * ν) ∧
      ∑ s ∈ Finset.range (r + 1), P''.expect (fun ω'' =>
          (cosetDens ((2 : ℤ) ^ s * z'' ω'') ((Z'' ω'').scale2 s) A) ^ 2) ≥
        ∑ s ∈ Finset.range (r + 1), P.expect (fun ω =>
          (cosetDens ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s) A) ^ 2) + δ ^ 2 / 8192 ∧
      (∀ ω'', IsClosedPair ν (Z'' ω'') ((T'' ω'').toSymNbhd (hT'' ω'') 0)) ∧
      (∀ ω'', (T'' ω'').HasDim (d + dB)) ∧
      (∀ ω'', covFlat (S : Set ℤ) ((T'' ω'').set 0) ≤ ((2 ^ Dnew : ℕ) : ℕ∞)))
    ∨
    (∃ (P' : FinProb) (proj : Fin P'.N → Fin P.N) (z' : Fin P'.N → ℤ)
      (Ztup : Fin P'.N → Fin k → SymNbhd),
      (∀ f : Fin P.N → ℝ, P'.expect (fun ω' => f (proj ω')) = P.expect f) ∧
      (∀ (i : Fin k) (s : ℕ), s ≤ r →
        tvLe (fun x => P'.expect (fun ω' => unifMeas (coset ((2 : ℤ) ^ s * z' ω') (Ztup ω' i)) x))
          (fun x => P.expect (fun ω => unifMeas (coset ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s)) x)) (2 * τ)) ∧
      (∀ (i : Fin k) (s : ℕ), s ≤ r →
        P'.expect (fun ω' => (cosetDens ((2 : ℤ) ^ s * z' ω') (Ztup ω' i) A -
          cosetDens ((2 : ℤ) ^ s * z (proj ω')) ((Z (proj ω')).scale2 s) A) ^ 2) ≤ δ) ∧
      (∀ (i j : Fin k), i < j → ∀ s : ℕ, s ≤ r →
        P'.expect (fun ω' => ((Ztup ω' i).set.card : ℝ)⁻¹ *
          ∑ u ∈ coset ((2 : ℤ) ^ (s + 1) * z' ω') (Ztup ω' i),
            (cosetConvInd ((2 : ℤ) ^ s * z' ω') (Ztup ω' i) (Ztup ω' j) A u -
              (cosetDens ((2 : ℤ) ^ s * z (proj ω')) ((Z (proj ω')).scale2 s) A) ^ 2) ^ 2) ≤ δ) ∧
      (∀ ω' (i : Fin k) (hi : i.val + 1 < k), IsClosedPair δ (Ztup ω' i) (Ztup ω' ⟨i.val + 1, hi⟩)) ∧
      (∀ ω' (i j : Fin k), i ≤ j → (Ztup ω' j).set ⊆ (Ztup ω' i).set) ∧
      (∀ ω', covFlat (S : Set ℤ) ((Ztup ω' ⟨k - 1, by omega⟩).set : Set ℤ) ≤ ((2 ^ Dnew : ℕ) : ℕ∞))) := by
  classical
  intro δ₃ η dB DB step_m m' Dnew
  have hδ₃_pos : 0 < δ₃ := by dsimp only [δ₃]; positivity
  have hη_pos : 0 < η := lt_min (by positivity) hν0
  have hη_le_ν : η ≤ ν := min_le_right _ _
  have hη_le_1 : η ≤ 1 := hη_le_ν.trans (by linarith)
  have hη_le_δ : η ≤ δ := by
    have h1 : η ≤ δ ^ 3 / (65536 * ((r + 1 : ℕ) : ℝ)) := min_le_left _ _
    have h2 : δ ^ 3 ≤ δ := by nlinarith
    have h3 : (1 : ℝ) ≤ 65536 * ((r + 1 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
      linarith
    have h4 : δ ^ 3 / (65536 * ((r + 1 : ℕ) : ℝ)) ≤ δ ^ 3 := div_le_self (by positivity) h3
    linarith
  let δ₁ : ℝ := δ ^ 2 / 4096
  let mSeq : ℕ → ℕ := fun i => r + i * step_m
  have hstep2 : 2 ≤ step_m := by dsimp [step_m]; omega
  have hchain : ∀ ω : Fin P.N, ∃ Z' : Fin k → SymNbhd,
      (∀ i : Fin k, ((T ω).toSymNbhd (hT ω) (mSeq i.val + 1)).set ⊆ (Z' i).set) ∧
      (∀ i : Fin k, (Z' i).set ⊆ ((T ω).toSymNbhd (hT ω) (mSeq i.val)).set) ∧
      (∀ i : Fin k, IsClosedPair η (Z' i) ((T ω).toSymNbhd (hT ω) (mSeq (i.val + 1)))) :=
    fun ω => build_nested_chain (T ω) (hT ω) (hTdim ω) hη_pos hη_le_1
  choose Z' hZ'lo hZ'hi hZ'cl using hchain
  have hZ'_mono : ∀ ω (i j : Fin k), i ≤ j → (Z' ω j).set ⊆ (Z' ω i).set := by
    intro ω i j hij
    by_cases heq : i = j
    · subst heq; exact Subset.rfl
    · have hlt : i.val < j.val := lt_of_le_of_ne hij (fun h => heq (Fin.ext h))
      have hidx : mSeq i.val + 1 ≤ mSeq j.val := by
        dsimp only [mSeq]
        have : (i.val + 1) * step_m ≤ j.val * step_m := Nat.mul_le_mul_right step_m (by omega)
        rw [Nat.add_mul, one_mul] at this; omega
      refine (hZ'hi ω j).trans (Subset.trans ?_ (hZ'lo ω i))
      intro x hx
      exact (Set.Finite.mem_toFinset _).mpr ((T ω).antitone hidx ((Set.Finite.mem_toFinset _).mp hx))
  have hZ'_cl_pair : ∀ ω (i j : Fin k), i < j → IsClosedPair η (Z' ω i) (Z' ω j) := by
    intro ω i j hij
    have hidx : mSeq (i.val + 1) ≤ mSeq j.val := by
      dsimp only [mSeq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right step_m hij) r
    have hsub : (Z' ω j).set ⊆ ((T ω).toSymNbhd (hT ω) (mSeq (i.val + 1))).set :=
      (hZ'hi ω j).trans fun x hx =>
        (Set.Finite.mem_toFinset _).mpr ((T ω).antitone hidx ((Set.Finite.mem_toFinset _).mp hx))
    exact isClosedPair_mono_right (hZ'cl ω i) hsub
  have hZ_scale_T0 : ∀ ω (i : Fin k) (s : ℕ), s ≤ r →
      ((Z' ω i).scale2 s).set ⊆ ((T ω).toSymNbhd (hT ω) 0).set := by
    intro ω i s hsr
    have hsub : (Z' ω i).set ⊆ ((T ω).toSymNbhd (hT ω) (0 + r)).set := by
      refine (hZ'hi ω i).trans fun x hx => ?_
      have hidx : 0 + r ≤ mSeq i.val := by dsimp only [mSeq]; omega
      exact (Set.Finite.mem_toFinset _).mpr ((T ω).antitone hidx ((Set.Finite.mem_toFinset _).mp hx))
    exact scale2_subset_sys_level (T ω) (hT ω) hsr hsub
  let ext := P.extend Z
  let P' : FinProb := ext.1
  let proj : Fin P'.N → Fin P.N := ext.2.1
  let z' : Fin P'.N → ℤ := fun ω' => z (proj ω') + ext.2.2 ω'
  let Ztup : Fin P'.N → Fin k → SymNbhd := fun ω' i => (Z' (proj ω') i).scale2 r
  by_cases hU1 : ∃ (i0 : Fin k) (s0 : ℕ), s0 ≤ r ∧
      δ₁ < P'.expect (fun ω' => (cosetDens ((2 : ℤ) ^ s0 * z' ω') (Ztup ω' i0) A -
        cosetDens ((2 : ℤ) ^ s0 * z (proj ω')) ((Z (proj ω')).scale2 s0) A) ^ 2)
  · left
    obtain ⟨i0, s0, hs0, hfail⟩ := hU1
    let Z'' : Fin P'.N → SymNbhd := fun ω' => (Z' (proj ω') i0).scale2 (r - s0)
    let T'' : Fin P'.N → Sys := fun ω' => ((T (proj ω')).dilate (mSeq (i0.val + 1))).scale2 (r - s0)
    have hT''fin : ∀ ω', (T'' ω').IsFinite := fun ω' =>
      Sys.scale2_isFinite (r - s0) ((T (proj ω')).dilate_isFinite _ (hT (proj ω')))
    have hZW_cl : ∀ ω, IsClosedPair τ (Z ω) ((Z' ω i0).scale2 (r - s0)) := fun ω =>
      isClosedPair_mono_right (hZT ω) (hZ_scale_T0 ω i0 (r - s0) (Nat.sub_le r s0))
    have htv1 := lem_newprob_ifr P z Z (fun ω => (Z' ω i0).scale2 (r - s0)) hτ0.le hZW_cl
    have htv : tvLe (fun x => P'.expect (fun ω' => unifMeas (coset (z' ω') (Z'' ω')) x))
        (fun x => P.expect (fun ω => unifMeas (coset (z ω) (Z ω)) x)) (2 * τ + 2 * ν) :=
      tvLe_mono htv1 (by linarith)
    have hirf := lem_newprob_irf P z Z (fun ω => Z' ω i0) A hs0 hτ0.le hZW_cl
    have hinc : ∑ s ∈ Finset.range (r + 1), P'.expect (fun ω' =>
          (cosetDens ((2 : ℤ) ^ s * z' ω') ((Z'' ω').scale2 s) A) ^ 2) ≥
        ∑ s ∈ Finset.range (r + 1), P.expect (fun ω =>
          (cosetDens ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s) A) ^ 2) + δ ^ 2 / 8192 := by
      have h4τ : 4 * τ * ((r + 1 : ℕ) : ℝ) ≤ δ₁ / 2 := by
        dsimp only [δ₁]; linarith
      have hhalf : δ₁ / 2 = δ ^ 2 / 8192 := by dsimp only [δ₁]; ring
      linarith
    refine ⟨P', z', Z'', T'', hT''fin, htv, hinc, ?_, ?_, ?_⟩
    · intro ω'
      have hcl := isClosedPair_scale2 (r - s0) (hZ'cl (proj ω') i0)
      have h0eq : ((T'' ω').toSymNbhd (hT''fin ω') 0).set =
          (((T (proj ω')).toSymNbhd (hT (proj ω')) (mSeq (i0.val + 1))).scale2 (r - s0)).set := by
        ext x
        simp only [T'', Sys.toSymNbhd, Sys.scale2, Sys.dilate, SymNbhd.scale2, scale2Fin,
          Set.Finite.mem_toFinset, scale2Set, Set.mem_image, Finset.mem_image, zero_add]
      obtain ⟨Zm, Zp, h1, h2, h3⟩ := isClosedPair_mono_tau hcl hη_le_ν
      exact ⟨Zm, Zp, by rwa [h0eq], by rwa [h0eq], h3⟩
    · intro ω'
      exact (Sys.scale2_hasDim (r - s0) ((T (proj ω')).dilate_hasDim _ (hTdim (proj ω')))).mono (Nat.le_add_right d dB)
    · intro ω'
      let Tdil := (T (proj ω')).dilate (mSeq (i0.val + 1))
      have hTd_dim : Tdil.HasDim d := (T (proj ω')).dilate_hasDim _ (hTdim (proj ω'))
      have hTd_fin : Tdil.IsFinite := (T (proj ω')).dilate_isFinite _ (hT (proj ω'))
      have hm_le : mSeq (i0.val + 1) ≤ r + k * step_m := by
        dsimp only [mSeq]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right step_m i0.isLt) r
      have hexp_le : D + (mSeq (i0.val + 1) + 1) * d + (2 * (r - s0) + 1) * d ≤ Dnew := by
        dsimp only [Dnew]
        have h1 : (mSeq (i0.val + 1) + 1) * d + (2 * (r - s0) + 1) * d ≤ (3 * r + k * step_m + 2) * d := by
          rw [← Nat.add_mul]
          exact Nat.mul_le_mul_right d (by omega)
        omega
      calc covFlat (S : Set ℤ) ((T'' ω').set 0)
          ≤ covFlat (S : Set ℤ) (Tdil.set 0) * ((2 ^ ((2 * (r - s0) + 1) * d) : ℕ) : ℕ∞) :=
            Tdil.scale2_covFlat hTd_dim hTd_fin (r - s0) (S : Set ℤ)
        _ ≤ (covFlat (S : Set ℤ) ((T (proj ω')).set 0) * ((2 ^ ((mSeq (i0.val + 1) + 1) * d) : ℕ) : ℕ∞)) *
              ((2 ^ ((2 * (r - s0) + 1) * d) : ℕ) : ℕ∞) :=
            mul_le_mul' ((T (proj ω')).dilate_covFlat (hTdim (proj ω')) _ (S : Set ℤ)) le_rfl
        _ ≤ (((2 ^ D : ℕ) : ℕ∞) * ((2 ^ ((mSeq (i0.val + 1) + 1) * d) : ℕ) : ℕ∞)) *
              ((2 ^ ((2 * (r - s0) + 1) * d) : ℕ) : ℕ∞) :=
            mul_le_mul' (mul_le_mul' (hTcov (proj ω')) le_rfl) le_rfl
        _ = ((2 ^ (D + (mSeq (i0.val + 1) + 1) * d + (2 * (r - s0) + 1) * d) : ℕ) : ℕ∞) := by
            rw [← Nat.cast_mul, ← Nat.cast_mul, ← pow_add, ← pow_add]
        _ ≤ ((2 ^ Dnew : ℕ) : ℕ∞) := ENat.natCast_le_natCast.mpr (Nat.pow_le_pow_right (by norm_num) hexp_le)
  · -- U_1 holds for all (i, s) with bound δ₁!
    push Not at hU1
    by_cases hU2 : ∃ (i1 j1 : Fin k), i1 < j1 ∧ ∃ s1 : ℕ, s1 ≤ r ∧
        δ < P'.expect (fun ω' => ((Ztup ω' i1).set.card : ℝ)⁻¹ *
          ∑ u ∈ coset ((2 : ℤ) ^ (s1 + 1) * z' ω') (Ztup ω' i1),
            (cosetConvInd ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' i1) (Ztup ω' j1) A u -
              (cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A) ^ 2) ^ 2)
    · -- Case 2: U_2 fails at (i1, j1, s1)! Apply `lem_increment` + `lem_cc` + `lem_newprob`!
      left
      obtain ⟨i1, j1, hij1, s1, hs1, hU2_fail⟩ := hU2
      let T' : Fin P.N → Sys := fun ω => ((T ω).dilate (mSeq k)).scale2 r
      have hT'fin : ∀ ω, (T' ω).IsFinite := fun ω =>
        Sys.scale2_isFinite r ((T ω).dilate_isFinite _ (hT ω))
      have hT'dim : ∀ ω, (T' ω).HasDim d := fun ω =>
        Sys.scale2_hasDim r ((T ω).dilate_hasDim _ (hTdim ω))
      have hT'0_eq : ∀ ω, ((T' ω).toSymNbhd (hT'fin ω) 0).set =
          (((T ω).toSymNbhd (hT ω) (mSeq k)).scale2 r).set := fun ω => by
        ext x
        simp only [T', Sys.toSymNbhd, Sys.scale2, Sys.dilate, SymNbhd.scale2, scale2Fin,
          Set.Finite.mem_toFinset, scale2Set, Set.mem_image, Finset.mem_image, zero_add]
      have hT'0_sub_Zj1 : ∀ ω', ((T' (proj ω')).toSymNbhd (hT'fin (proj ω')) 0).set ⊆ (Ztup ω' j1).set := by
        intro ω'
        rw [hT'0_eq]
        refine symNbhd_scale2_mono r ?_
        have hidx : mSeq j1.val + 1 ≤ mSeq k := by
          dsimp only [mSeq]
          have : (j1.val + 1) * step_m ≤ k * step_m := Nat.mul_le_mul_right step_m j1.isLt
          rw [Nat.add_mul, one_mul] at this; omega
        have hsub0 : ((T (proj ω')).toSymNbhd (hT (proj ω')) (mSeq k)).set ⊆
            ((T (proj ω')).toSymNbhd (hT (proj ω')) (mSeq j1.val + 1)).set := fun x hx =>
          (Set.Finite.mem_toFinset _).mpr ((T (proj ω')).antitone hidx ((Set.Finite.mem_toFinset _).mp hx))
        exact hsub0.trans (hZ'lo (proj ω') j1)
      have hZj1_T'0 : ∀ ω', IsClosedPair η (Ztup ω' j1) ((T' (proj ω')).toSymNbhd (hT'fin (proj ω')) 0) := by
        intro ω'
        have hidx : mSeq (j1.val + 1) ≤ mSeq k := by
          dsimp only [mSeq]
          exact Nat.add_le_add_left (Nat.mul_le_mul_right step_m j1.isLt) r
        have hsub : ((T (proj ω')).toSymNbhd (hT (proj ω')) (mSeq k)).set ⊆
            ((T (proj ω')).toSymNbhd (hT (proj ω')) (mSeq (j1.val + 1))).set := fun x hx =>
          (Set.Finite.mem_toFinset _).mpr ((T (proj ω')).antitone hidx ((Set.Finite.mem_toFinset _).mp hx))
        have hcl := isClosedPair_scale2 r (isClosedPair_mono_right (hZ'cl (proj ω') j1) hsub)
        obtain ⟨Zm, Zp, h1, h2, h3⟩ := hcl
        exact ⟨Zm, Zp, by rwa [hT'0_eq], by rwa [hT'0_eq], h3⟩
      have hinc_all : ∀ ω' : Fin P'.N, ∃ B'' : Sys,
          B''.HasDim dB ∧
          covFlat (Set.univ : Set ℤ) (B''.set 0) ≤ ((2 ^ DB : ℕ) : ℕ∞) ∧
          ∀ W'' : SymNbhd,
            W''.set ⊆ ((T' (proj ω')).toSymNbhd (hT'fin (proj ω')) 0).set →
            (W''.set : Set ℤ) ⊆ B''.set 0 →
            ((Ztup ω' i1).set.card : ℝ)⁻¹ * ∑ x ∈ (Ztup ω' i1).set,
              (convInd (A.image (· - (2 : ℤ) ^ s1 * z' ω')) W''.set W'' x -
                cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A) ^ 2 ≥
            ((Ztup ω' i1).set.card : ℝ)⁻¹ * ∑ x ∈ (Ztup ω' i1).set,
              (convInd (A.image (· - (2 : ℤ) ^ s1 * z' ω') ∩ (Ztup ω' i1).set)
                (A.image (· - (2 : ℤ) ^ s1 * z' ω')) (Ztup ω' j1) x -
                (cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A) ^ 2) ^ 2 -
              (δ₃ ^ 2 + 8 * η / δ₃ ^ 2 + 2 * δ₃ + 3 * η +
                2 * |locDens (Ztup ω' j1) (A.image (· - (2 : ℤ) ^ s1 * z' ω')) -
                  cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A|) := by
        intro ω'
        exact lem_increment hη_pos.le (cosetDens_nonneg _ _ _) (cosetDens_le_one _ _ _)
          hδ₃_pos hδ₃_pos (hT'0_sub_Zj1 ω')
          (isClosedPair_scale2 r (hZ'_cl_pair (proj ω') i1 j1 hij1)) (hZj1_T'0 ω')
      choose B'' hB''dim hB''cov hB''inc using hinc_all
      let TB : Fin P'.N → Sys := fun ω' => (T' (proj ω')).inter (B'' ω')
      have hTBfin : ∀ ω', (TB ω').IsFinite := fun ω' =>
        (hT'fin (proj ω')).subset Set.inter_subset_left
      have hTBdim : ∀ ω', (TB ω').HasDim (d + dB) := fun ω' =>
        Sys.inter_hasDim (hT'dim (proj ω')) (hB''dim ω')
      have hm'2 : 2 ≤ m' := by dsimp [m']; omega
      have hdm' : (2 : ℝ) * ((d + dB : ℕ) : ℝ) ≤ (2 ^ (m' - 2) : ℝ) * η := by
        have h1 : 2 * ((d + dB : ℕ) : ℝ) / η ≤ (Nat.ceil (2 * ((d + dB : ℕ) : ℝ) / η) : ℝ) := Nat.le_ceil _
        have h2 : Nat.ceil (2 * ((d + dB : ℕ) : ℝ) / η) ≤ 2 ^ (m' - 2) := by
          have : m' - 2 = Nat.clog 2 (Nat.ceil (2 * ((d + dB : ℕ) : ℝ) / η)) := by dsimp [m']; omega
          rw [this]; exact Nat.le_pow_clog (by norm_num) _
        exact (div_le_iff₀ hη_pos).mp (h1.trans (by exact_mod_cast h2))
      have hcc_all : ∀ ω' : Fin P'.N, ∃ Z'' : SymNbhd,
          Z''.set ⊆ ((TB ω').toSymNbhd (hTBfin ω') (2 * r)).set ∧
          IsClosedPair η Z'' ((TB ω').toSymNbhd (hTBfin ω') (2 * r + m')) := by
        intro ω'
        let TB2r := (TB ω').dilate (2 * r)
        have hTB2rfin : TB2r.IsFinite := (TB ω').dilate_isFinite (2 * r) (hTBfin ω')
        obtain ⟨Z'', _, hhi, hcl⟩ := lem_cc TB2r hTB2rfin ((TB ω').dilate_hasDim (2 * r) (hTBdim ω'))
          hη_pos hη_le_1 hm'2 hdm'
        have heq0 : (TB2r.toSymNbhd hTB2rfin 0).set = ((TB ω').toSymNbhd (hTBfin ω') (2 * r)).set := by
          ext x; simp [TB2r, Sys.toSymNbhd, Sys.dilate]
        have heqm : (TB2r.toSymNbhd hTB2rfin m').set = ((TB ω').toSymNbhd (hTBfin ω') (2 * r + m')).set := by
          ext x; simp [TB2r, Sys.toSymNbhd, Sys.dilate, add_comm]
        refine ⟨Z'', by rwa [← heq0], ?_⟩
        obtain ⟨Zm, Zp, h1, h2, h3⟩ := hcl
        exact ⟨Zm, Zp, by rwa [← heqm], by rwa [← heqm], h3⟩
      choose Z'' hZ''sub hZ''cl using hcc_all
      have hW''_sub : ∀ ω', ((Z'' ω').scale2 r).set ⊆ ((TB ω').toSymNbhd (hTBfin ω') 0).set := by
        intro ω'
        have hsub_r : (Z'' ω').set ⊆ ((TB ω').toSymNbhd (hTBfin ω') (0 + r)).set := by
          refine (hZ''sub ω').trans fun x hx => ?_
          exact (Set.Finite.mem_toFinset _).mpr ((TB ω').antitone (by omega) ((Set.Finite.mem_toFinset _).mp hx))
        exact scale2_subset_sys_level (TB ω') (hTBfin ω') le_rfl hsub_r
      have hW''_T'0 : ∀ ω', ((Z'' ω').scale2 r).set ⊆ ((T' (proj ω')).toSymNbhd (hT'fin (proj ω')) 0).set := by
        intro ω' x hx
        have h1 : x ∈ (TB ω').set 0 := (Set.Finite.mem_toFinset _).mp (hW''_sub ω' hx)
        exact (Set.Finite.mem_toFinset _).mpr h1.1
      have hW''_B''0 : ∀ ω', (((Z'' ω').scale2 r).set : Set ℤ) ⊆ (B'' ω').set 0 := by
        intro ω' x hx
        have h1 : x ∈ (TB ω').set 0 := (Set.Finite.mem_toFinset _).mp (hW''_sub ω' (Finset.mem_coe.mp hx))
        exact h1.2
      have hZ''_sub_Tk : ∀ ω', (Z'' ω').set ⊆ ((T (proj ω')).toSymNbhd (hT (proj ω')) (mSeq k)).set := by
        intro ω' x hx
        have hmem_T' : x ∈ (T' (proj ω')).set (2 * r) := ((Set.Finite.mem_toFinset _).mp (hZ''sub ω' hx)).1
        obtain ⟨y, hy, rfl⟩ := hmem_T'
        have hy_fin : y ∈ ((T (proj ω')).toSymNbhd (hT (proj ω')) (mSeq k + 2 * r)).set := by
          have : y ∈ (T (proj ω')).set (2 * r + mSeq k) := hy
          rw [add_comm] at this
          exact (Set.Finite.mem_toFinset _).mpr this
        have hscale := scale2_subset_sys_level (T (proj ω')) (hT (proj ω')) (m0 := mSeq k) (s := r) (r := 2 * r)
          (by omega) Subset.rfl
        exact hscale (Finset.mem_image.mpr ⟨y, hy_fin, rfl⟩)
      have hZmid_Z''_cl : ∀ ω', IsClosedPair η ((Z' (proj ω') i1).scale2 (r - s1)) ((Z'' ω').scale2 (r - s1)) := by
        intro ω'
        have hidx : mSeq (i1.val + 1) ≤ mSeq k := by
          dsimp only [mSeq]
          exact Nat.add_le_add_left (Nat.mul_le_mul_right step_m i1.isLt) r
        have hsub : (Z'' ω').set ⊆ ((T (proj ω')).toSymNbhd (hT (proj ω')) (mSeq (i1.val + 1))).set :=
          (hZ''_sub_Tk ω').trans fun x hx =>
            (Set.Finite.mem_toFinset _).mpr ((T (proj ω')).antitone hidx ((Set.Finite.mem_toFinset _).mp hx))
        exact isClosedPair_scale2 (r - s1) (isClosedPair_mono_right (hZ'cl (proj ω') i1) hsub)
      have hL2_lb : P'.expect (fun ω' => ((Ztup ω' i1).set.card : ℝ)⁻¹ *
          ∑ u ∈ coset ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' i1),
            (convInd A ((Z'' ω').scale2 r).set ((Z'' ω').scale2 r) u -
              cosetDens ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' i1) A) ^ 2) ≥ δ / 2 := by
        have hpt : ∀ ω' : Fin P'.N,
            ((Ztup ω' i1).set.card : ℝ)⁻¹ *
              ∑ u ∈ coset ((2 : ℤ) ^ (s1 + 1) * z' ω') (Ztup ω' i1),
                (cosetConvInd ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' i1) (Ztup ω' j1) A u -
                  (cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A) ^ 2) ^ 2 -
              (δ₃ ^ 2 + 8 * η / δ₃ ^ 2 + 2 * δ₃ + 3 * η +
                2 * |cosetDens ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' j1) A -
                  cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A| +
                2 * |cosetDens ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' i1) A -
                  cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A|) ≤
            ((Ztup ω' i1).set.card : ℝ)⁻¹ *
              ∑ u ∈ coset ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' i1),
                (convInd A ((Z'' ω').scale2 r).set ((Z'' ω').scale2 r) u -
                  cosetDens ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' i1) A) ^ 2 := by
          intro ω'
          have h2eq : 2 * ((2 : ℤ) ^ s1 * z' ω') = (2 : ℤ) ^ (s1 + 1) * z' ω' := by rw [pow_succ]; ring
          have h1 := lem_inductivestep_case2_pointwise
            (β := cosetDens ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' i1) A)
            (cosetDens_nonneg _ _ _) (cosetDens_le_one _ _ _)
            (cosetDens_nonneg _ _ _) (cosetDens_le_one _ _ _)
            (hB''inc ω' ((Z'' ω').scale2 r) (hW''_T'0 ω') (hW''_B''0 ω'))
          rwa [h2eq] at h1
        have hexp := P'.expect_mono hpt
        rw [P'.expect_sub, P'.expect_add, P'.expect_add, P'.expect_const,
          P'.expect_mul_const, P'.expect_mul_const] at hexp
        have hj1_err : P'.expect (fun ω' => |cosetDens ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' j1) A -
            cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A|) ≤ δ / 64 := by
          have h1 := P'.expect_abs_le_sqrt (fun ω' => cosetDens ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' j1) A -
            cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A)
          have h2 := hU1 j1 s1 hs1
          have hsq : Real.sqrt δ₁ = δ / 64 := by
            have : δ₁ = (δ / 64) ^ 2 := by dsimp only [δ₁]; ring
            rw [this, Real.sqrt_sq (by positivity)]
          exact h1.trans ((Real.sqrt_le_sqrt h2).trans_eq hsq)
        have hi1_err : P'.expect (fun ω' => |cosetDens ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' i1) A -
            cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A|) ≤ δ / 64 := by
          have h1 := P'.expect_abs_le_sqrt (fun ω' => cosetDens ((2 : ℤ) ^ s1 * z' ω') (Ztup ω' i1) A -
            cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A)
          have h2 := hU1 i1 s1 hs1
          have hsq : Real.sqrt δ₁ = δ / 64 := by
            have : δ₁ = (δ / 64) ^ 2 := by dsimp only [δ₁]; ring
            rw [this, Real.sqrt_sq (by positivity)]
          exact h1.trans ((Real.sqrt_le_sqrt h2).trans_eq hsq)
        have hη_bound : η ≤ δ ^ 3 / (65536 * ((r + 1 : ℕ) : ℝ)) := min_le_left _ _
        have h8η : 8 * η / δ₃ ^ 2 ≤ δ / 32 := by
          have hr1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
          have h1 : η ≤ δ ^ 3 / 65536 := hη_bound.trans (by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            nlinarith)
          have heq : 8 * (δ ^ 3 / 65536) / δ₃ ^ 2 = δ / 32 := by dsimp only [δ₃]; field_simp; ring
          have h2 : 8 * η / δ₃ ^ 2 ≤ 8 * (δ ^ 3 / 65536) / δ₃ ^ 2 :=
            div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
          linarith
        have h3η : 3 * η ≤ δ / 64 := by
          have h1 : η ≤ δ ^ 3 / 65536 := hη_bound.trans (by
            have hr1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
            apply div_le_div_of_nonneg_left (by positivity) (by positivity); nlinarith)
          nlinarith
        have hδ3sq : δ₃ ^ 2 + 2 * δ₃ ≤ δ / 4 := by dsimp only [δ₃]; nlinarith
        linarith
      let Zmid : Fin P'.N → SymNbhd := fun ω' => (Z' (proj ω') i1).scale2 (r - s1)
      let ext2 := P'.extend Zmid
      let P'' : FinProb := ext2.1
      let proj2 : Fin P''.N → Fin P'.N := ext2.2.1
      let z'' : Fin P''.N → ℤ := fun ω'' => z' (proj2 ω'') + ext2.2.2 ω''
      let Z''_out : Fin P''.N → SymNbhd := fun ω'' => (Z'' (proj2 ω'')).scale2 (r - s1)
      let T''_out : Fin P''.N → Sys := fun ω'' => ((TB (proj2 ω'')).dilate (2 * r + m')).scale2 (r - s1)
      have hT''fin : ∀ ω'', (T''_out ω'').IsFinite := fun ω'' =>
        Sys.scale2_isFinite (r - s1) ((TB (proj2 ω'')).dilate_isFinite _ (hTBfin (proj2 ω'')))
      have hZW1 : ∀ ω, IsClosedPair τ (Z ω) ((Z' ω i1).scale2 (r - s1)) := fun ω =>
        isClosedPair_mono_right (hZT ω) (hZ_scale_T0 ω i1 (r - s1) (Nat.sub_le r s1))
      have htv1 := lem_newprob_ifr P z Z (fun ω => (Z' ω i1).scale2 (r - s1)) hτ0.le hZW1
      have htv2 := lem_newprob_ifr P' z' Zmid (fun ω' => (Z'' ω').scale2 (r - s1)) hη_pos.le hZmid_Z''_cl
      have htv : tvLe (fun x => P''.expect (fun ω'' => unifMeas (coset (z'' ω'') (Z''_out ω'')) x))
          (fun x => P.expect (fun ω => unifMeas (coset (z ω) (Z ω)) x)) (2 * τ + 2 * ν) :=
        tvLe_mono (tvLe_trans htv2 htv1) (by linarith)
      have hkkj := lem_newprob_kkj P' z' Zmid Z'' A s1 r
      have hZmid_s1 : ∀ ω', (Zmid ω').scale2 s1 = Ztup ω' i1 := fun ω' => by
        dsimp only [Zmid, Ztup]
        rw [symNbhd_scale2_scale2, Nat.add_sub_cancel' hs1]
      have hZmid_card : ∀ ω', (Zmid ω').set.card = (Ztup ω' i1).set.card := fun ω' => by
        dsimp only [Zmid, Ztup, SymNbhd.scale2]; rw [scale2Fin_card, scale2Fin_card]
      have hkkj_eq : P''.expect (fun ω'' =>
          (cosetDens ((2 : ℤ) ^ s1 * z'' ω'') ((Z'' (proj2 ω'')).scale2 r) A -
            cosetDens ((2 : ℤ) ^ s1 * z' (proj2 ω'')) ((Zmid (proj2 ω'')).scale2 s1) A) ^ 2) ≥ δ / 2 := by
        rw [← hkkj]
        refine le_trans hL2_lb (le_of_eq ?_)
        unfold FinProb.expect
        refine Finset.sum_congr rfl fun ω' _ => ?_
        dsimp only
        rw [hZmid_s1 ω', hZmid_card ω']
      have hirf2 := lem_newprob_irf P' z' Zmid Z'' A hs1 hη_pos.le hZmid_Z''_cl
      have hirf1 := lem_newprob_irf P z Z (fun ω => Z' ω i1) A hs1 hτ0.le hZW1
      have hvar1_nn : 0 ≤ P'.expect (fun ω' =>
          (cosetDens ((2 : ℤ) ^ s1 * z' ω') ((Z' (proj ω') i1).scale2 r) A -
            cosetDens ((2 : ℤ) ^ s1 * z (proj ω')) ((Z (proj ω')).scale2 s1) A) ^ 2) :=
        P'.expect_nonneg fun _ => sq_nonneg _
      have hinc : ∑ s ∈ Finset.range (r + 1), P''.expect (fun ω'' =>
            (cosetDens ((2 : ℤ) ^ s * z'' ω'') ((Z''_out ω'').scale2 s) A) ^ 2) ≥
          ∑ s ∈ Finset.range (r + 1), P.expect (fun ω =>
            (cosetDens ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s) A) ^ 2) + δ ^ 2 / 8192 := by
        have h4η : 4 * η * ((r + 1 : ℕ) : ℝ) ≤ δ / 8 := by
          have h1 : η ≤ δ ^ 3 / (65536 * ((r + 1 : ℕ) : ℝ)) := min_le_left _ _
          have hrpos : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
          have h2 : η * ((r + 1 : ℕ) : ℝ) ≤ δ ^ 3 / 65536 := by
            have := (le_div_iff₀ (by positivity : (0 : ℝ) < 65536 * ((r + 1 : ℕ) : ℝ))).mp h1
            linarith
          nlinarith
        have h4τ : 4 * τ * ((r + 1 : ℕ) : ℝ) ≤ δ / 8 := by
          have : δ ^ 2 ≤ δ := by nlinarith
          linarith
        have hδ_big : δ ^ 2 / 8192 ≤ δ / 4 := by nlinarith
        linarith
      refine ⟨P'', z'', Z''_out, T''_out, hT''fin, htv, hinc, ?_, ?_, ?_⟩
      · intro ω''
        have hcl := isClosedPair_scale2 (r - s1) (hZ''cl (proj2 ω''))
        have h0eq : ((T''_out ω'').toSymNbhd (hT''fin ω'') 0).set =
            (((TB (proj2 ω'')).toSymNbhd (hTBfin (proj2 ω'')) (2 * r + m')).scale2 (r - s1)).set := by
          ext x
          simp only [T''_out, Sys.toSymNbhd, Sys.scale2, Sys.dilate, SymNbhd.scale2, scale2Fin,
            Set.Finite.mem_toFinset, scale2Set, Set.mem_image, Finset.mem_image, zero_add]
        obtain ⟨Zm, Zp, h1, h2, h3⟩ := isClosedPair_mono_tau hcl hη_le_ν
        exact ⟨Zm, Zp, by rwa [h0eq], by rwa [h0eq], h3⟩
      · intro ω''
        exact Sys.scale2_hasDim (r - s1) ((TB (proj2 ω'')).dilate_hasDim _ (hTBdim (proj2 ω'')))
      · intro ω''
        let ω' := proj2 ω''
        let ω := proj ω'
        have hcov_T' : covFlat (S : Set ℤ) ((T' ω).set 0) ≤ ((2 ^ (D + (3 * r + k * step_m + 2) * d) : ℕ) : ℕ∞) := by
          let Tdil := (T ω).dilate (mSeq k)
          have hTd_dim : Tdil.HasDim d := (T ω).dilate_hasDim _ (hTdim ω)
          have hTd_fin : Tdil.IsFinite := (T ω).dilate_isFinite _ (hT ω)
          have hexp : D + (mSeq k + 1) * d + (2 * r + 1) * d = D + (3 * r + k * step_m + 2) * d := by
            dsimp only [mSeq]; ring
          calc covFlat (S : Set ℤ) ((T' ω).set 0)
              ≤ covFlat (S : Set ℤ) (Tdil.set 0) * ((2 ^ ((2 * r + 1) * d) : ℕ) : ℕ∞) :=
                Tdil.scale2_covFlat hTd_dim hTd_fin r (S : Set ℤ)
            _ ≤ (covFlat (S : Set ℤ) ((T ω).set 0) * ((2 ^ ((mSeq k + 1) * d) : ℕ) : ℕ∞)) *
                  ((2 ^ ((2 * r + 1) * d) : ℕ) : ℕ∞) :=
                mul_le_mul' ((T ω).dilate_covFlat (hTdim ω) _ (S : Set ℤ)) le_rfl
            _ ≤ (((2 ^ D : ℕ) : ℕ∞) * ((2 ^ ((mSeq k + 1) * d) : ℕ) : ℕ∞)) * ((2 ^ ((2 * r + 1) * d) : ℕ) : ℕ∞) :=
                mul_le_mul' (mul_le_mul' (hTcov ω) le_rfl) le_rfl
            _ = ((2 ^ (D + (mSeq k + 1) * d + (2 * r + 1) * d) : ℕ) : ℕ∞) := by
                rw [← Nat.cast_mul, ← Nat.cast_mul, ← pow_add, ← pow_add]
            _ = ((2 ^ (D + (3 * r + k * step_m + 2) * d) : ℕ) : ℕ∞) := by rw [hexp]
        have hcov_B'' : covFlat (S : Set ℤ) ((B'' ω').set 0) ≤ ((2 ^ DB : ℕ) : ℕ∞) :=
          (covFlat_mono (Set.subset_univ _) Set.Subset.rfl).trans (hB''cov ω')
        have hcov_TB : covFlat (S : Set ℤ) ((TB ω').set 0) ≤
            ((2 ^ (D + (3 * r + k * step_m + 2) * d + DB) : ℕ) : ℕ∞) := by
          calc covFlat (S : Set ℤ) ((TB ω').set 0)
              ≤ covFlat (S : Set ℤ) ((T' ω).set 0) * covFlat (S : Set ℤ) ((B'' ω').set 0) :=
                (T' ω).inter_covFlat (B'' ω') (S : Set ℤ)
            _ ≤ ((2 ^ (D + (3 * r + k * step_m + 2) * d) : ℕ) : ℕ∞) * ((2 ^ DB : ℕ) : ℕ∞) :=
                mul_le_mul' hcov_T' hcov_B''
            _ = ((2 ^ (D + (3 * r + k * step_m + 2) * d + DB) : ℕ) : ℕ∞) := by
                rw [← Nat.cast_mul, ← pow_add]
        let TBdil := (TB ω').dilate (2 * r + m')
        have hTBdil_dim : TBdil.HasDim (d + dB) := (TB ω').dilate_hasDim _ (hTBdim ω')
        have hTBdil_fin : TBdil.IsFinite := (TB ω').dilate_isFinite _ (hTBfin ω')
        have hexp_le : D + (3 * r + k * step_m + 2) * d + DB + (2 * r + m' + 1) * (d + dB) +
            (2 * (r - s1) + 1) * (d + dB) ≤ Dnew := by
          dsimp only [Dnew]
          have h1 : (2 * r + m' + 1) * (d + dB) + (2 * (r - s1) + 1) * (d + dB) ≤ (4 * r + m' + 2) * (d + dB) := by
            rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
          omega
        calc covFlat (S : Set ℤ) ((T''_out ω'').set 0)
            ≤ covFlat (S : Set ℤ) (TBdil.set 0) * ((2 ^ ((2 * (r - s1) + 1) * (d + dB)) : ℕ) : ℕ∞) :=
              TBdil.scale2_covFlat hTBdil_dim hTBdil_fin (r - s1) (S : Set ℤ)
          _ ≤ (covFlat (S : Set ℤ) ((TB ω').set 0) * ((2 ^ ((2 * r + m' + 1) * (d + dB)) : ℕ) : ℕ∞)) *
                ((2 ^ ((2 * (r - s1) + 1) * (d + dB)) : ℕ) : ℕ∞) :=
              mul_le_mul' ((TB ω').dilate_covFlat (hTBdim ω') _ (S : Set ℤ)) le_rfl
          _ ≤ (((2 ^ (D + (3 * r + k * step_m + 2) * d + DB) : ℕ) : ℕ∞) *
                ((2 ^ ((2 * r + m' + 1) * (d + dB)) : ℕ) : ℕ∞)) *
                ((2 ^ ((2 * (r - s1) + 1) * (d + dB)) : ℕ) : ℕ∞) :=
              mul_le_mul' (mul_le_mul' hcov_TB le_rfl) le_rfl
          _ = ((2 ^ (D + (3 * r + k * step_m + 2) * d + DB + (2 * r + m' + 1) * (d + dB) +
                (2 * (r - s1) + 1) * (d + dB)) : ℕ) : ℕ∞) := by
              rw [← Nat.cast_mul, ← Nat.cast_mul, ← pow_add, ← pow_add]
          _ ≤ ((2 ^ Dnew : ℕ) : ℕ∞) := ENat.natCast_le_natCast.mpr (Nat.pow_le_pow_right (by norm_num) hexp_le)
    · -- Case 3: Both U_1 and U_2 hold! Return `(P', proj, z', Ztup)`!
      right
      push Not at hU2
      refine ⟨P', proj, z', Ztup, fun f => P.extend_pullback Z f, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro i s hsr
        have hZW : ∀ ω, IsClosedPair τ (Z ω) ((Z' ω i).scale2 (r - s)) := fun ω =>
          isClosedPair_mono_right (hZT ω) (hZ_scale_T0 ω i (r - s) (Nat.sub_le r s))
        have htv := tvLe_pushScale2 s (lem_newprob_ifr P z Z (fun ω => (Z' ω i).scale2 (r - s)) hτ0.le hZW)
        have hscale_eq : ∀ ω, ((Z' ω i).scale2 (r - s)).scale2 s = (Z' ω i).scale2 r := fun ω => by
          rw [symNbhd_scale2_scale2, Nat.add_sub_cancel' hsr]
        have hL : ∀ x, pushScale2 s (fun u => P'.expect (fun ω' => unifMeas (coset (z' ω') ((Z' (proj ω') i).scale2 (r - s))) u)) x =
            P'.expect (fun ω' => unifMeas (coset ((2 : ℤ) ^ s * z' ω') (Ztup ω' i)) x) := by
          intro x
          have hlin : pushScale2 s (fun u => ∑ ω' : Fin P'.N, P'.w ω' * unifMeas (coset (z' ω') ((Z' (proj ω') i).scale2 (r - s))) u) x =
              ∑ ω' : Fin P'.N, P'.w ω' * pushScale2 s (unifMeas (coset (z' ω') ((Z' (proj ω') i).scale2 (r - s)))) x := by
            unfold pushScale2; split_ifs
            · rfl
            · simp
          unfold FinProb.expect
          rw [hlin]
          refine Finset.sum_congr rfl fun ω' _ => ?_
          rw [← unifMeas_scale2Fin, scale2Fin_coset, hscale_eq]
        have hR : ∀ x, pushScale2 s (fun u => P.expect (fun ω => unifMeas (coset (z ω) (Z ω)) u)) x =
            P.expect (fun ω => unifMeas (coset ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s)) x) := by
          intro x
          have hlin : pushScale2 s (fun u => ∑ ω : Fin P.N, P.w ω * unifMeas (coset (z ω) (Z ω)) u) x =
              ∑ ω : Fin P.N, P.w ω * pushScale2 s (unifMeas (coset (z ω) (Z ω))) x := by
            unfold pushScale2; split_ifs
            · rfl
            · simp
          unfold FinProb.expect
          rw [hlin]
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [← unifMeas_scale2Fin, scale2Fin_coset]
        dsimp only [P', proj, z', ext] at hL
        intro U
        simpa only [hL, hR] using htv U
      · intro i s hsr
        have hle := hU1 i s hsr
        have hδ1_le : δ₁ ≤ δ := by dsimp only [δ₁]; nlinarith
        exact hle.trans hδ1_le
      · intro i j hij s hsr
        exact hU2 i j hij s hsr
      · intro ω' i hi
        have hlt : i < ⟨i.val + 1, hi⟩ := Nat.lt_succ_self i.val
        exact isClosedPair_mono_tau (isClosedPair_scale2 r (hZ'_cl_pair (proj ω') i ⟨i.val + 1, hi⟩ hlt)) hη_le_δ
      · intro ω' i j hij
        exact symNbhd_scale2_mono r (hZ'_mono (proj ω') i j hij)
      · intro ω'
        let ω := proj ω'
        let Tdil := (T ω).dilate (mSeq k)
        let T' := Tdil.scale2 r
        have hsub : T'.set 0 ⊆ ((Ztup ω' ⟨k - 1, by omega⟩).set : Set ℤ) := by
          intro x hx
          obtain ⟨y, hy, rfl⟩ := hx
          have hy' : y ∈ (T ω).set (mSeq (k - 1) + 1) := by
            have hidx : mSeq (k - 1) + 1 ≤ 0 + mSeq k := by
              dsimp only [mSeq]
              have h1 : (k - 1) * step_m + 1 ≤ k * step_m := by
                have hk1 : k = (k - 1) + 1 := by omega
                calc (k - 1) * step_m + 1 ≤ (k - 1) * step_m + step_m := by omega
                  _ = ((k - 1) + 1) * step_m := by ring
                  _ = k * step_m := by rw [← hk1]
              omega
            exact (T ω).antitone hidx hy
          have hyZ : y ∈ (Z' ω ⟨k - 1, by omega⟩).set :=
            hZ'lo ω ⟨k - 1, by omega⟩ ((Set.Finite.mem_toFinset _).mpr hy')
          exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨y, hyZ, rfl⟩)
        have hTd_dim : Tdil.HasDim d := (T ω).dilate_hasDim _ (hTdim ω)
        have hTd_fin : Tdil.IsFinite := (T ω).dilate_isFinite _ (hT ω)
        have hexp : D + (mSeq k + 1) * d + (2 * r + 1) * d ≤ Dnew := by
          dsimp only [Dnew, mSeq]
          have : (r + k * step_m + 1) * d + (2 * r + 1) * d = (3 * r + k * step_m + 2) * d := by ring
          omega
        calc covFlat (S : Set ℤ) ((Ztup ω' ⟨k - 1, by omega⟩).set : Set ℤ)
            ≤ covFlat (S : Set ℤ) (T'.set 0) := covFlat_mono Set.Subset.rfl hsub
          _ ≤ covFlat (S : Set ℤ) (Tdil.set 0) * ((2 ^ ((2 * r + 1) * d) : ℕ) : ℕ∞) :=
              Tdil.scale2_covFlat hTd_dim hTd_fin r (S : Set ℤ)
          _ ≤ (covFlat (S : Set ℤ) ((T ω).set 0) * ((2 ^ ((mSeq k + 1) * d) : ℕ) : ℕ∞)) * ((2 ^ ((2 * r + 1) * d) : ℕ) : ℕ∞) :=
              mul_le_mul' ((T ω).dilate_covFlat (hTdim ω) _ (S : Set ℤ)) le_rfl
          _ ≤ (((2 ^ D : ℕ) : ℕ∞) * ((2 ^ ((mSeq k + 1) * d) : ℕ) : ℕ∞)) * ((2 ^ ((2 * r + 1) * d) : ℕ) : ℕ∞) :=
              mul_le_mul' (mul_le_mul' (hTcov ω) le_rfl) le_rfl
          _ = ((2 ^ (D + (mSeq k + 1) * d + (2 * r + 1) * d) : ℕ) : ℕ∞) := by
              rw [← Nat.cast_mul, ← Nat.cast_mul, ← pow_add, ← pow_add]
          _ ≤ ((2 ^ Dnew : ℕ) : ℕ∞) := ENat.natCast_le_natCast.mpr (Nat.pow_le_pow_right (by norm_num) hexp)

private lemma cor_iju {k r d0 D0 : ℕ} {A S : Finset ℤ}
    {P0 : FinProb} {z0 : Fin P0.N → ℤ} {Z0 : Fin P0.N → SymNbhd}
    {T0 : Fin P0.N → Sys} (hT0 : ∀ ω, (T0 ω).IsFinite)
    {τ δ : ℝ}
    (hk : 2 ≤ k) (hr : 1 ≤ r)
    (hτ0 : 0 < τ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hτ_small : 32768 * ((r + 1 : ℕ) : ℝ) * τ ≤ δ ^ 2)
    (hZT0 : ∀ ω, IsClosedPair τ (Z0 ω) ((T0 ω).toSymNbhd (hT0 ω) 0))
    (hT0dim : ∀ ω, (T0 ω).HasDim d0)
    (hT0cov : ∀ ω, covFlat (S : Set ℤ) ((T0 ω).set 0) ≤ ((2 ^ D0 : ℕ) : ℕ∞)) :
    let Mmax : ℕ := Nat.ceil (((r + 1 : ℕ) : ℝ) * 8192 / δ ^ 2) + 1
    let δ₃ : ℝ := δ / 16
    let dB : ℕ := 3 * Nat.floor (2 / δ₃ ^ 2)
    let DB : ℕ := 3 * (Nat.clog 2 (Nat.ceil (8 / δ₃)) + 2) * Nat.floor (2 / δ₃ ^ 2)
    let ν0 : ℝ := min (δ ^ 2 / (32768 * ((r + 1 : ℕ) : ℝ))) (δ / (16 * (Mmax : ℝ)))
    let η0 : ℝ := min (δ ^ 3 / (65536 * ((r + 1 : ℕ) : ℝ))) ν0
    let dmax : ℕ := d0 + Mmax * dB
    let step_max : ℕ := Nat.clog 2 (Nat.ceil (2 * ((dmax + dB : ℕ) : ℝ) / η0)) + 2
    let Dstep : ℕ := (3 * r + k * step_max + 2) * dmax + DB + (4 * r + step_max + 2) * (dmax + dB)
    ∃ (P' : FinProb) (z' : Fin P'.N → ℤ) (Z' : Fin P'.N → SymNbhd)
      (P'' : FinProb) (proj : Fin P''.N → Fin P'.N) (z'' : Fin P''.N → ℤ)
      (Ztup : Fin P''.N → Fin k → SymNbhd),
      (∀ f : Fin P'.N → ℝ, P''.expect (fun ω'' => f (proj ω'')) = P'.expect f) ∧
      tvLe (fun x => P'.expect (fun ω' => unifMeas (coset (z' ω') (Z' ω')) x))
        (fun x => P0.expect (fun ω => unifMeas (coset (z0 ω) (Z0 ω)) x)) δ ∧
      (∀ (i : Fin k) (s : ℕ), s ≤ r →
        tvLe (fun x => P''.expect (fun ω'' => unifMeas (coset ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i)) x))
          (fun x => P'.expect (fun ω' => unifMeas (coset ((2 : ℤ) ^ s * z' ω') ((Z' ω').scale2 s)) x)) δ) ∧
      (∀ (i : Fin k) (s : ℕ), s ≤ r →
        P''.expect (fun ω'' => (cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A -
          cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A) ^ 2) ≤ δ) ∧
      (∀ (i j : Fin k), i < j → ∀ s : ℕ, s ≤ r →
        P''.expect (fun ω'' => ((Ztup ω'' i).set.card : ℝ)⁻¹ *
          ∑ u ∈ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i),
            (cosetConvInd ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (Ztup ω'' j) A u -
              (cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A) ^ 2) ^ 2) ≤ δ) ∧
      (∀ ω'' (i : Fin k) (hi : i.val + 1 < k), IsClosedPair δ (Ztup ω'' i) (Ztup ω'' ⟨i.val + 1, hi⟩)) ∧
      (∀ ω'' (i j : Fin k), i ≤ j → (Ztup ω'' j).set ⊆ (Ztup ω'' i).set) ∧
      (∀ ω'', covFlat (S : Set ℤ) ((Ztup ω'' ⟨k - 1, by omega⟩).set : Set ℤ) ≤
        ((2 ^ (D0 + (Mmax + 1) * Dstep) : ℕ) : ℕ∞)) := by
  classical
  intro Mmax δ₃ dB DB ν0 η0 dmax step_max Dstep
  have hMmax_pos : (0 : ℝ) < (Mmax : ℝ) := by positivity
  have hMmax_gt : ((r + 1 : ℕ) : ℝ) < (Mmax : ℝ) * (δ ^ 2 / 8192) := by
    have h1 : ((r + 1 : ℕ) : ℝ) * 8192 / δ ^ 2 ≤ (Nat.ceil (((r + 1 : ℕ) : ℝ) * 8192 / δ ^ 2) : ℝ) :=
      Nat.le_ceil _
    have h2 : (Nat.ceil (((r + 1 : ℕ) : ℝ) * 8192 / δ ^ 2) : ℝ) + 1 = (Mmax : ℝ) := by
      dsimp only [Mmax]; push_cast; ring
    have h3 : ((r + 1 : ℕ) : ℝ) * 8192 / δ ^ 2 < (Mmax : ℝ) := by linarith
    have h4 := (div_lt_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)).mp h3
    linarith
  have hν0_pos : 0 < ν0 := lt_min (by positivity) (by positivity)
  have hν0_small : 32768 * ((r + 1 : ℕ) : ℝ) * ν0 ≤ δ ^ 2 := by
    have h1 : ν0 ≤ δ ^ 2 / (32768 * ((r + 1 : ℕ) : ℝ)) := min_le_left _ _
    exact (le_div_iff₀' (by positivity)).mp h1
  have hν0_le_half : ν0 ≤ 1 / 2 := by
    have hr1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
    nlinarith
  have hτ_le_half : τ ≤ 1 / 2 := by
    have hr1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
    nlinarith
  have h2τ_le : 2 * τ ≤ δ / 4 := by
    have hr1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
    nlinarith
  have h2ν_le : 2 * ν0 ≤ δ / 4 := by
    have hr1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
    nlinarith
  have h4Mν_le : (Mmax : ℝ) * (4 * ν0) ≤ δ / 4 := by
    have h1 : ν0 ≤ δ / (16 * (Mmax : ℝ)) := min_le_right _ _
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (Mmax : ℝ))).mp h1
    linarith
  have hη0_pos : 0 < η0 := lt_min (by positivity) hν0_pos
  suffices hrec : ∀ (rem : ℕ), rem ≤ Mmax →
      let idx := Mmax - rem
      let τcur : ℝ := if idx = 0 then τ else ν0
      ∀ (P : FinProb) (z : Fin P.N → ℤ) (Z : Fin P.N → SymNbhd)
        (T : Fin P.N → Sys) (hT : ∀ ω, (T ω).IsFinite),
        tvLe (fun x => P.expect (fun ω => unifMeas (coset (z ω) (Z ω)) x))
          (fun x => P0.expect (fun ω => unifMeas (coset (z0 ω) (Z0 ω)) x))
          (if idx = 0 then 0 else 2 * τ + (idx : ℝ) * (4 * ν0)) →
        ∑ s ∈ Finset.range (r + 1), P.expect (fun ω =>
          (cosetDens ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s) A) ^ 2) ≥ (idx : ℝ) * (δ ^ 2 / 8192) →
        (∀ ω, IsClosedPair τcur (Z ω) ((T ω).toSymNbhd (hT ω) 0)) →
        (∀ ω, (T ω).HasDim (d0 + idx * dB)) →
        (∀ ω, covFlat (S : Set ℤ) ((T ω).set 0) ≤ ((2 ^ (D0 + idx * Dstep) : ℕ) : ℕ∞)) →
        ∃ (P' : FinProb) (z' : Fin P'.N → ℤ) (Z' : Fin P'.N → SymNbhd)
          (P'' : FinProb) (proj : Fin P''.N → Fin P'.N) (z'' : Fin P''.N → ℤ)
          (Ztup : Fin P''.N → Fin k → SymNbhd),
          (∀ f : Fin P'.N → ℝ, P''.expect (fun ω'' => f (proj ω'')) = P'.expect f) ∧
          tvLe (fun x => P'.expect (fun ω' => unifMeas (coset (z' ω') (Z' ω')) x))
            (fun x => P0.expect (fun ω => unifMeas (coset (z0 ω) (Z0 ω)) x)) δ ∧
          (∀ (i : Fin k) (s : ℕ), s ≤ r →
            tvLe (fun x => P''.expect (fun ω'' => unifMeas (coset ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i)) x))
              (fun x => P'.expect (fun ω' => unifMeas (coset ((2 : ℤ) ^ s * z' ω') ((Z' ω').scale2 s)) x)) δ) ∧
          (∀ (i : Fin k) (s : ℕ), s ≤ r →
            P''.expect (fun ω'' => (cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A -
              cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A) ^ 2) ≤ δ) ∧
          (∀ (i j : Fin k), i < j → ∀ s : ℕ, s ≤ r →
            P''.expect (fun ω'' => ((Ztup ω'' i).set.card : ℝ)⁻¹ *
              ∑ u ∈ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i),
                (cosetConvInd ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (Ztup ω'' j) A u -
                  (cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A) ^ 2) ^ 2) ≤ δ) ∧
          (∀ ω'' (i : Fin k) (hi : i.val + 1 < k), IsClosedPair δ (Ztup ω'' i) (Ztup ω'' ⟨i.val + 1, hi⟩)) ∧
          (∀ ω'' (i j : Fin k), i ≤ j → (Ztup ω'' j).set ⊆ (Ztup ω'' i).set) ∧
          (∀ ω'', covFlat (S : Set ℤ) ((Ztup ω'' ⟨k - 1, by omega⟩).set : Set ℤ) ≤
            ((2 ^ (D0 + (Mmax + 1) * Dstep) : ℕ) : ℕ∞)) by
    have h0 := hrec Mmax le_rfl
    dsimp only at h0
    have hsub0 : Mmax - Mmax = 0 := Nat.sub_self Mmax
    rw [hsub0] at h0
    refine h0 P0 z0 Z0 T0 hT0
      (by simp [tvLe_refl]) ?_ (by simpa using hZT0) (by simpa using hT0dim) (by simpa using hT0cov)
    simp only [Nat.cast_zero, zero_mul]
    exact Finset.sum_nonneg fun _ _ => P0.expect_nonneg fun _ => sq_nonneg _
  intro rem
  induction rem with
  | zero =>
    intro _ idx _ P z Z _ _ _ henergy _ _ _
    exfalso
    have hsub : idx = Mmax := Nat.sub_zero Mmax
    rw [hsub] at henergy
    have hub : ∑ s ∈ Finset.range (r + 1), P.expect (fun ω =>
        (cosetDens ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s) A) ^ 2) ≤ ((r + 1 : ℕ) : ℝ) := by
      calc ∑ s ∈ Finset.range (r + 1), P.expect (fun ω =>
            (cosetDens ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s) A) ^ 2)
          ≤ ∑ _s ∈ Finset.range (r + 1), (1 : ℝ) := by
            refine Finset.sum_le_sum fun s _ => ?_
            calc P.expect (fun ω => (cosetDens ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s) A) ^ 2)
                ≤ P.expect (fun _ => 1) := P.expect_mono fun ω => by
                  have h0 := cosetDens_nonneg ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s) A
                  have h1 := cosetDens_le_one ((2 : ℤ) ^ s * z ω) ((Z ω).scale2 s) A
                  nlinarith
              _ = 1 := P.expect_const 1
        _ = ((r + 1 : ℕ) : ℝ) := by simp
    linarith
  | succ rem' ih =>
    intro hrem idx τcur P z Z T hT htv_cur henergy hZT hTdim hTcov
    have hτc0 : 0 < τcur := by dsimp only [τcur]; split_ifs <;> assumption
    have hτc1 : τcur ≤ 1 / 2 := by dsimp only [τcur]; split_ifs <;> assumption
    have hτc_small : 32768 * ((r + 1 : ℕ) : ℝ) * τcur ≤ δ ^ 2 := by dsimp only [τcur]; split_ifs <;> assumption
    have h2τc : 2 * τcur ≤ δ := by dsimp only [τcur]; split_ifs <;> linarith
    have hidx_le : idx ≤ Mmax := Nat.sub_le _ _
    have hidx_succ : Mmax - rem' = idx + 1 := by dsimp only [idx]; omega
    have hcur_d_le : d0 + idx * dB ≤ dmax := by
      dsimp only [dmax]; exact Nat.add_le_add_left (Nat.mul_le_mul_right dB hidx_le) d0
    have hDnew_le : D0 + idx * Dstep +
        (3 * r + k * (Nat.clog 2 (Nat.ceil (2 * ((d0 + idx * dB : ℕ) : ℝ) / η0)) + 2) + 2) * (d0 + idx * dB) +
        DB + (4 * r + (Nat.clog 2 (Nat.ceil (2 * ((d0 + idx * dB + dB : ℕ) : ℝ) / η0)) + 2) + 2) * (d0 + idx * dB + dB) ≤
        D0 + (idx + 1) * Dstep := by
      have hclog1 : Nat.clog 2 (Nat.ceil (2 * ((d0 + idx * dB : ℕ) : ℝ) / η0)) + 2 ≤ step_max := by
        dsimp only [step_max]
        have hle : (d0 + idx * dB : ℕ) ≤ dmax + dB := hcur_d_le.trans (Nat.le_add_right _ _)
        have hR : 2 * ((d0 + idx * dB : ℕ) : ℝ) / η0 ≤ 2 * ((dmax + dB : ℕ) : ℝ) / η0 :=
          div_le_div_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_left 2 hle) hη0_pos.le
        exact Nat.add_le_add_right (Nat.clog_mono_right 2 (Nat.ceil_mono hR)) 2
      have hclog2 : Nat.clog 2 (Nat.ceil (2 * ((d0 + idx * dB + dB : ℕ) : ℝ) / η0)) + 2 ≤ step_max := by
        dsimp only [step_max]
        have hle : d0 + idx * dB + dB ≤ dmax + dB := Nat.add_le_add_right hcur_d_le dB
        have hR : 2 * ((d0 + idx * dB + dB : ℕ) : ℝ) / η0 ≤ 2 * ((dmax + dB : ℕ) : ℝ) / η0 :=
          div_le_div_of_nonneg_right (by exact_mod_cast Nat.mul_le_mul_left 2 hle) hη0_pos.le
        exact Nat.add_le_add_right (Nat.clog_mono_right 2 (Nat.ceil_mono hR)) 2
      have ht1 : (3 * r + k * (Nat.clog 2 (Nat.ceil (2 * ((d0 + idx * dB : ℕ) : ℝ) / η0)) + 2) + 2) * (d0 + idx * dB) ≤
          (3 * r + k * step_max + 2) * dmax :=
        Nat.mul_le_mul (Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left k hclog1) (3 * r)) 2) hcur_d_le
      have ht2 : (4 * r + (Nat.clog 2 (Nat.ceil (2 * ((d0 + idx * dB + dB : ℕ) : ℝ) / η0)) + 2) + 2) * (d0 + idx * dB + dB) ≤
          (4 * r + step_max + 2) * (dmax + dB) :=
        Nat.mul_le_mul (by omega) (Nat.add_le_add_right hcur_d_le dB)
      have hrhs : D0 + (idx + 1) * Dstep = D0 + idx * Dstep + Dstep := by ring
      rw [hrhs]
      dsimp only [Dstep]; omega
    rcases lem_inductivestep hT hk hr hτc0 hτc1 hδ0 hδ1 hν0_pos hν0_le_half hτc_small hZT hTdim hTcov with
      ⟨P'', z'', Z'', T'', hT'', htv_step, hinc_step, hcl'', hdim'', hcov''⟩ |
      ⟨P', proj, z', Ztup, hpull', htv', hU1', hU2', hcl', hsub', hcov'⟩
    · have htv_next : tvLe (fun x => P''.expect (fun ω'' => unifMeas (coset (z'' ω'') (Z'' ω'')) x))
          (fun x => P0.expect (fun ω => unifMeas (coset (z0 ω) (Z0 ω)) x))
          (if idx + 1 = 0 then 0 else 2 * τ + ((idx + 1 : ℕ) : ℝ) * (4 * ν0)) := by
        rw [if_neg (Nat.succ_ne_zero idx)]
        have htr := tvLe_trans htv_step htv_cur
        refine tvLe_mono htr ?_
        dsimp only [τcur]
        by_cases h0 : idx = 0
        · rw [if_pos h0, if_pos h0, h0]; push_cast; linarith
        · rw [if_neg h0, if_neg h0]; push_cast; linarith
      have hnext := ih (by omega) P'' z'' Z'' T'' hT''
      rw [hidx_succ] at hnext
      exact hnext htv_next (by push_cast; linarith)
        (by rw [if_neg (Nat.succ_ne_zero idx)]; exact hcl'')
        (fun ω'' => by rw [Nat.add_mul, one_mul, ← add_assoc]; exact hdim'' ω'')
        (fun ω'' => (hcov'' ω'').trans (ENat.natCast_le_natCast.mpr (Nat.pow_le_pow_right (by norm_num) hDnew_le)))
    · -- Case 2: uniform tuple found! Return `(P, z, Z)` and `(P', proj, z', Ztup)`!
      have htv_P : tvLe (fun x => P.expect (fun ω => unifMeas (coset (z ω) (Z ω)) x))
          (fun x => P0.expect (fun ω => unifMeas (coset (z0 ω) (Z0 ω)) x)) δ := by
        refine tvLe_mono htv_cur ?_
        split_ifs
        · exact hδ0.le
        · have hidxR : (idx : ℝ) ≤ (Mmax : ℝ) := by exact_mod_cast hidx_le
          have hmul : (idx : ℝ) * (4 * ν0) ≤ (Mmax : ℝ) * (4 * ν0) :=
            mul_le_mul_of_nonneg_right hidxR (by positivity)
          linarith
      refine ⟨P, z, Z, P', proj, z', Ztup, hpull', htv_P, ?_, hU1', hU2', hcl', hsub', ?_⟩
      · intro i s hsr
        exact tvLe_mono (htv' i s hsr) h2τc
      · intro ω'
        have hexp_le : D0 + (idx + 1) * Dstep ≤ D0 + (Mmax + 1) * Dstep :=
          Nat.add_le_add_left (Nat.mul_le_mul_right Dstep (by omega)) D0
        exact (hcov' ω').trans (ENat.natCast_le_natCast.mpr
          (Nat.pow_le_pow_right (by norm_num) (hDnew_le.trans hexp_le)))

/- ### Module 6B: Proof of Proposition 2.8 (`propG : PropGSpec`) and Final Solution -/

private lemma expect_pushScale2_coset (P : FinProb) (z : Fin P.N → ℤ) (Z : Fin P.N → SymNbhd)
    (j : ℕ) (x : ℤ) :
    pushScale2 j (fun u => P.expect (fun ω => unifMeas (coset (z ω) (Z ω)) u)) x =
    P.expect (fun ω => unifMeas (coset ((2 : ℤ) ^ j * z ω) ((Z ω).scale2 j)) x) := by
  have hlin : pushScale2 j (fun u => ∑ ω : Fin P.N, P.w ω * unifMeas (coset (z ω) (Z ω)) u) x =
      ∑ ω : Fin P.N, P.w ω * pushScale2 j (unifMeas (coset (z ω) (Z ω))) x := by
    unfold pushScale2; split_ifs
    · rfl
    · simp
  unfold FinProb.expect
  rw [hlin]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [← unifMeas_scale2Fin, scale2Fin_coset]

private lemma sum_pushScale2_unifMeas (j : ℕ) (S A : Finset ℤ) :
    ∑ x ∈ A, pushScale2 j (unifMeas S) x = ((scale2Finset j S ∩ A).card : ℝ) / (S.card : ℝ) := by
  have hscale_eq : scale2Fin j S = scale2Finset j S := rfl
  simp_rw [← unifMeas_scale2Fin, hscale_eq]
  unfold unifMeas
  have hcard : (scale2Finset j S).card = S.card := scale2Fin_card j S
  rw [hcard, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Finset.sum_const_zero, add_zero, div_eq_mul_inv]
  have hfilt : A.filter (· ∈ scale2Finset j S) = scale2Finset j S ∩ A := by
    ext x; simp only [Finset.mem_filter, Finset.mem_inter]; tauto
  rw [hfilt]

private lemma propG_Dfinal_bound {k r d0 D0 : ℕ}
    (hk : 2 ≤ k) (hr : 1 ≤ r)
    (hd0 : d0 ≤ k ^ 2228)
    (hD0 : D0 ≤ k ^ 2242 * (Nat.clog 2 (Nat.ceil (1 / (1 / ((k * r : ℕ) : ℝ) ^ 5620))) + 10)) :
    let kr : ℕ := k * r
    let δ₀ : ℝ := 1 / (kr : ℝ) ^ 2800
    let Mmax : ℕ := Nat.ceil (((r + 1 : ℕ) : ℝ) * 8192 / δ₀ ^ 2) + 1
    let δ₃ : ℝ := δ₀ / 16
    let dB : ℕ := 3 * Nat.floor (2 / δ₃ ^ 2)
    let DB : ℕ := 3 * (Nat.clog 2 (Nat.ceil (8 / δ₃)) + 2) * Nat.floor (2 / δ₃ ^ 2)
    let ν0 : ℝ := min (δ₀ ^ 2 / (32768 * ((r + 1 : ℕ) : ℝ))) (δ₀ / (16 * (Mmax : ℝ)))
    let η0 : ℝ := min (δ₀ ^ 3 / (65536 * ((r + 1 : ℕ) : ℝ))) ν0
    let dmax : ℕ := d0 + Mmax * dB
    let step_max : ℕ := Nat.clog 2 (Nat.ceil (2 * ((dmax + dB : ℕ) : ℝ) / η0)) + 2
    let Dstep : ℕ := (3 * r + k * step_max + 2) * dmax + DB + (4 * r + step_max + 2) * (dmax + dB)
    D0 + (Mmax + 1) * Dstep ≤ kr ^ 16900 := by
  intro kr δ₀ Mmax δ₃ dB DB ν0 η0 dmax step_max Dstep
  have hkr2 : 2 ≤ kr := by dsimp only [kr]; nlinarith
  have hkr_pos : (0 : ℝ) < (kr : ℝ) := by positivity
  have hkr2R : (2 : ℝ) ≤ (kr : ℝ) := by exact_mod_cast hkr2
  have hk_le_kr : k ≤ kr := by dsimp only [kr]; exact Nat.le_mul_of_pos_right k hr
  have hr_le_kr : r ≤ kr := by dsimp only [kr]; exact Nat.le_mul_of_pos_left r (by omega)
  have hr1_le_kr : r + 1 ≤ kr := by dsimp only [kr]; nlinarith
  have h2pow : ∀ n : ℕ, 2 ^ n ≤ kr ^ n := fun n => Nat.pow_le_pow_left hkr2 n
  have h2powR : ∀ n : ℕ, (2 : ℝ) ^ n ≤ (kr : ℝ) ^ n := fun n => pow_le_pow_left₀ (by norm_num) hkr2R n
  have hkr_le_2kr : kr ≤ 2 ^ kr := (Nat.lt_two_pow_self (n := kr)).le
  have hclog_pow : ∀ n : ℕ, Nat.clog 2 (kr ^ n) ≤ n * kr := fun n => by
    apply Nat.clog_le_of_le_pow
    calc kr ^ n ≤ (2 ^ kr) ^ n := Nat.pow_le_pow_left hkr_le_2kr n
      _ = 2 ^ (n * kr) := by rw [← pow_mul, mul_comm]
  have hd0_kr : d0 ≤ kr ^ 2228 := hd0.trans (Nat.pow_le_pow_left hk_le_kr 2228)
  have hD0_kr : D0 ≤ kr ^ 2260 := by
    have hinv : (1 : ℝ) / (1 / (kr : ℝ) ^ 5620) = ((kr ^ 5620 : ℕ) : ℝ) := by push_cast; field_simp
    have hceil : Nat.ceil (1 / (1 / ((k * r : ℕ) : ℝ) ^ 5620)) = kr ^ 5620 := by
      dsimp only [kr]; rw [hinv, Nat.ceil_natCast]
    have hclog : Nat.clog 2 (Nat.ceil (1 / (1 / ((k * r : ℕ) : ℝ) ^ 5620))) ≤ 5620 * kr := by
      rw [hceil]; exact hclog_pow 5620
    have h5630 : 5620 * kr + 10 ≤ kr ^ 14 := by
      have h1 : 5620 * kr + 10 ≤ 5630 * kr := by omega
      have h2 : 5630 ≤ 2 ^ 13 := by norm_num
      calc 5620 * kr + 10 ≤ 5630 * kr := h1
        _ ≤ kr ^ 13 * kr := Nat.mul_le_mul_right kr (h2.trans (h2pow 13))
        _ = kr ^ 14 := by rw [← pow_succ]
    calc D0 ≤ k ^ 2242 * (5620 * kr + 10) := hD0.trans (Nat.mul_le_mul_left _ (by omega))
      _ ≤ kr ^ 2242 * kr ^ 14 := Nat.mul_le_mul (Nat.pow_le_pow_left hk_le_kr 2242) h5630
      _ = kr ^ 2256 := by rw [← pow_add]
      _ ≤ kr ^ 2260 := Nat.pow_le_pow_right (by omega) (by omega)
  have hMmax_le : Mmax ≤ kr ^ 5620 := by
    have hceil : Nat.ceil (((r + 1 : ℕ) : ℝ) * 8192 / δ₀ ^ 2) ≤ kr ^ 5616 := by
      apply Nat.ceil_le.mpr
      have hr1R : ((r + 1 : ℕ) : ℝ) ≤ (kr : ℝ) := by exact_mod_cast hr1_le_kr
      have h8192 : (8192 : ℝ) ≤ (kr : ℝ) ^ 13 := (by norm_num : (8192 : ℝ) = (2 : ℝ) ^ 13).le.trans (h2powR 13)
      have heq : ((r + 1 : ℕ) : ℝ) * 8192 / δ₀ ^ 2 = ((r + 1 : ℕ) : ℝ) * 8192 * (kr : ℝ) ^ 5600 := by
        dsimp only [δ₀]; rw [one_div_pow, one_div, div_inv_eq_mul]; ring
      rw [heq, Nat.cast_pow]
      calc ((r + 1 : ℕ) : ℝ) * 8192 * (kr : ℝ) ^ 5600
          ≤ (kr : ℝ) * (kr : ℝ) ^ 13 * (kr : ℝ) ^ 5600 := by gcongr
        _ = (kr : ℝ) ^ 5614 := by ring
        _ ≤ (kr : ℝ) ^ 5616 := pow_le_pow_right₀ (by linarith) (by omega)
    have h1 : 1 ≤ kr ^ 5616 := Nat.one_le_pow _ _ (by omega)
    have h2 : 2 * kr ^ 5616 ≤ kr ^ 5620 := by
      calc 2 * kr ^ 5616 ≤ kr * kr ^ 5616 := Nat.mul_le_mul_right _ hkr2
        _ = kr ^ 5617 := by rw [← pow_succ']
        _ ≤ kr ^ 5620 := Nat.pow_le_pow_right (by omega) (by omega)
    dsimp only [Mmax]; omega
  have hfl_le : Nat.floor (2 / δ₃ ^ 2) ≤ 512 * kr ^ 5600 := by
    apply Nat.floor_le_of_le
    have heq : 2 / δ₃ ^ 2 = 512 * (kr : ℝ) ^ 5600 := by dsimp only [δ₃, δ₀]; field_simp; ring
    rw [heq]; push_cast; rfl
  have hdB_le : dB ≤ kr ^ 5620 := by
    have h1536 : 3 * 512 ≤ kr ^ 11 := (by norm_num : 3 * 512 ≤ 2 ^ 11).trans (h2pow 11)
    calc dB ≤ 3 * (512 * kr ^ 5600) := Nat.mul_le_mul_left 3 hfl_le
      _ = (3 * 512) * kr ^ 5600 := by ring
      _ ≤ kr ^ 11 * kr ^ 5600 := Nat.mul_le_mul_right _ h1536
      _ = kr ^ 5611 := by rw [← pow_add]
      _ ≤ kr ^ 5620 := Nat.pow_le_pow_right (by omega) (by omega)
  have hDB_le : DB ≤ kr ^ 5630 := by
    have hclog_le : Nat.clog 2 (Nat.ceil (8 / δ₃)) + 2 ≤ 2810 * kr := by
      have h8 : 8 / δ₃ = ((128 * kr ^ 2800 : ℕ) : ℝ) := by dsimp only [δ₃, δ₀]; push_cast; field_simp; ring
      rw [h8, Nat.ceil_natCast]
      have h128 : 128 * kr ^ 2800 ≤ 2 ^ (7 + 2800 * kr) := by
        rw [pow_add]
        have h1 : 128 = 2 ^ 7 := by norm_num
        have h2 : kr ^ 2800 ≤ 2 ^ (2800 * kr) := by
          calc kr ^ 2800 ≤ (2 ^ kr) ^ 2800 := Nat.pow_le_pow_left hkr_le_2kr 2800
            _ = 2 ^ (2800 * kr) := by rw [← pow_mul, mul_comm]
        rw [h1]; exact Nat.mul_le_mul_left _ h2
      have hc := Nat.clog_le_of_le_pow h128
      omega
    have hconst : 3 * 2810 * 512 ≤ kr ^ 23 := (by norm_num : 3 * 2810 * 512 ≤ 2 ^ 23).trans (h2pow 23)
    calc DB ≤ 3 * (2810 * kr) * (512 * kr ^ 5600) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 3 hclog_le) hfl_le
      _ = (3 * 2810 * 512) * (kr * kr ^ 5600) := by ring
      _ = (3 * 2810 * 512) * kr ^ 5601 := by rw [← pow_succ']
      _ ≤ kr ^ 23 * kr ^ 5601 := Nat.mul_le_mul_right _ hconst
      _ = kr ^ 5624 := by rw [← pow_add]
      _ ≤ kr ^ 5630 := Nat.pow_le_pow_right (by omega) (by omega)
  have hdmax_le : dmax ≤ kr ^ 11242 := by
    have h1 : d0 ≤ kr ^ 11240 := hd0_kr.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : Mmax * dB ≤ kr ^ 11240 := by
      calc Mmax * dB ≤ kr ^ 5620 * kr ^ 5620 := Nat.mul_le_mul hMmax_le hdB_le
        _ = kr ^ 11240 := by rw [← pow_add]
    calc dmax = d0 + Mmax * dB := rfl
      _ ≤ kr ^ 11240 + kr ^ 11240 := Nat.add_le_add h1 h2
      _ = 2 * kr ^ 11240 := by ring
      _ ≤ kr * kr ^ 11240 := Nat.mul_le_mul_right _ hkr2
      _ = kr ^ 11241 := by rw [← pow_succ']
      _ ≤ kr ^ 11242 := Nat.pow_le_pow_right (by omega) (by omega)
  have hη0_lb : 1 / (kr : ℝ) ^ 8440 ≤ η0 := by
    dsimp only [η0, ν0]
    refine le_min ?_ (le_min ?_ ?_)
    · dsimp only [δ₀]
      rw [one_div_pow, div_div, one_div_le_one_div (by positivity) (by positivity)]
      have h65536 : (65536 : ℝ) ≤ (kr : ℝ) ^ 16 := (by norm_num : (65536 : ℝ) = (2 : ℝ) ^ 16).le.trans (h2powR 16)
      have hr1R : ((r + 1 : ℕ) : ℝ) ≤ (kr : ℝ) := by exact_mod_cast hr1_le_kr
      have heq : ((kr : ℝ) ^ 2800) ^ 3 = (kr : ℝ) ^ 8400 := by ring
      calc ((kr : ℝ) ^ 2800) ^ 3 * (65536 * ((r + 1 : ℕ) : ℝ))
          ≤ (kr : ℝ) ^ 8400 * ((kr : ℝ) ^ 16 * (kr : ℝ)) := by rw [heq]; gcongr
        _ = (kr : ℝ) ^ 8417 := by ring
        _ ≤ (kr : ℝ) ^ 8440 := pow_le_pow_right₀ (by linarith) (by omega)
    · dsimp only [δ₀]
      rw [one_div_pow, div_div, one_div_le_one_div (by positivity) (by positivity)]
      have h32768 : (32768 : ℝ) ≤ (kr : ℝ) ^ 15 := (by norm_num : (32768 : ℝ) = (2 : ℝ) ^ 15).le.trans (h2powR 15)
      have hr1R : ((r + 1 : ℕ) : ℝ) ≤ (kr : ℝ) := by exact_mod_cast hr1_le_kr
      have heq : ((kr : ℝ) ^ 2800) ^ 2 = (kr : ℝ) ^ 5600 := by ring
      calc ((kr : ℝ) ^ 2800) ^ 2 * (32768 * ((r + 1 : ℕ) : ℝ))
          ≤ (kr : ℝ) ^ 5600 * ((kr : ℝ) ^ 15 * (kr : ℝ)) := by rw [heq]; gcongr
        _ = (kr : ℝ) ^ 5616 := by ring
        _ ≤ (kr : ℝ) ^ 8440 := pow_le_pow_right₀ (by linarith) (by omega)
    · dsimp only [δ₀]
      rw [div_div, one_div_le_one_div (by positivity) (by positivity)]
      have h16 : (16 : ℝ) ≤ (kr : ℝ) ^ 4 := (by norm_num : (16 : ℝ) = (2 : ℝ) ^ 4).le.trans (h2powR 4)
      have hM : (Mmax : ℝ) ≤ (kr : ℝ) ^ 5620 := by exact_mod_cast hMmax_le
      calc (kr : ℝ) ^ 2800 * (16 * (Mmax : ℝ))
          ≤ (kr : ℝ) ^ 2800 * ((kr : ℝ) ^ 4 * (kr : ℝ) ^ 5620) := by gcongr
        _ = (kr : ℝ) ^ 8424 := by ring
        _ ≤ (kr : ℝ) ^ 8440 := pow_le_pow_right₀ (by linarith) (by omega)
  have hstep_le : step_max ≤ kr ^ 16 := by
    have hη0_pos : 0 < η0 := lt_of_lt_of_le (by positivity) hη0_lb
    have hceil : Nat.ceil (2 * ((dmax + dB : ℕ) : ℝ) / η0) ≤ kr ^ 19690 := by
      apply Nat.ceil_le.mpr
      have hdd : dmax + dB ≤ 2 * kr ^ 11242 := by
        have : dB ≤ kr ^ 11242 := hdB_le.trans (Nat.pow_le_pow_right (by omega) (by omega))
        omega
      have hddR : ((dmax + dB : ℕ) : ℝ) ≤ 2 * (kr : ℝ) ^ 11242 := by exact_mod_cast hdd
      have h4 : (4 : ℝ) ≤ (kr : ℝ) ^ 2 := (by norm_num : (4 : ℝ) = (2 : ℝ) ^ 2).le.trans (h2powR 2)
      have hdiv : 2 * ((dmax + dB : ℕ) : ℝ) / η0 ≤ 2 * ((dmax + dB : ℕ) : ℝ) / (1 / (kr : ℝ) ^ 8440) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hη0_lb
      rw [one_div, div_inv_eq_mul] at hdiv
      rw [Nat.cast_pow]
      calc 2 * ((dmax + dB : ℕ) : ℝ) / η0
          ≤ 2 * (2 * (kr : ℝ) ^ 11242) * (kr : ℝ) ^ 8440 := by
            exact hdiv.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
        _ = 4 * (kr : ℝ) ^ 19682 := by ring
        _ ≤ (kr : ℝ) ^ 2 * (kr : ℝ) ^ 19682 := mul_le_mul_of_nonneg_right h4 (by positivity)
        _ = (kr : ℝ) ^ 19684 := by ring
        _ ≤ (kr : ℝ) ^ 19690 := pow_le_pow_right₀ (by linarith) (by omega)
    have hclog : Nat.clog 2 (Nat.ceil (2 * ((dmax + dB : ℕ) : ℝ) / η0)) ≤ 19690 * kr :=
      (Nat.clog_mono_right 2 hceil).trans (hclog_pow 19690)
    have h19692 : 19692 ≤ 2 ^ 15 := by norm_num
    calc step_max ≤ 19690 * kr + 2 := by dsimp only [step_max]; omega
      _ ≤ 19692 * kr := by omega
      _ ≤ kr ^ 15 * kr := Nat.mul_le_mul_right kr (h19692.trans (h2pow 15))
      _ = kr ^ 16 := by rw [← pow_succ]
  have hDstep_le : Dstep ≤ kr ^ 11270 := by
    have h1 : 3 * r + k * step_max + 2 ≤ kr ^ 20 := by
      have ha : 3 * r + 2 ≤ 5 * kr := by omega
      have hb : k * step_max ≤ kr * kr ^ 16 := Nat.mul_le_mul hk_le_kr hstep_le
      have hc : kr * kr ^ 16 = kr ^ 17 := by rw [← pow_succ']
      have hd : 5 * kr ≤ 5 * kr ^ 17 := Nat.mul_le_mul_left 5 (by simpa using Nat.pow_le_pow_right (n := kr) (by omega) (show 1 ≤ 17 by omega))
      have h6 : 6 ≤ kr ^ 3 := (by norm_num : 6 ≤ 2 ^ 3).trans (h2pow 3)
      calc 3 * r + k * step_max + 2 ≤ 5 * kr ^ 17 + kr ^ 17 := by omega
        _ = 6 * kr ^ 17 := by ring
        _ ≤ kr ^ 3 * kr ^ 17 := Nat.mul_le_mul_right _ h6
        _ = kr ^ 20 := by rw [← pow_add]
    have h2 : 4 * r + step_max + 2 ≤ kr ^ 20 := by
      have hle : 4 * r + step_max + 2 ≤ 3 * r + k * step_max + 2 + r := by
        have : step_max ≤ k * step_max := Nat.le_mul_of_pos_left _ (by omega)
        omega
      have ha : 4 * r + 2 ≤ 6 * kr := by omega
      have hb : step_max ≤ kr ^ 17 := hstep_le.trans (Nat.pow_le_pow_right (by omega) (by omega))
      have hd : 6 * kr ≤ 6 * kr ^ 17 := Nat.mul_le_mul_left 6 (by simpa using Nat.pow_le_pow_right (n := kr) (by omega) (show 1 ≤ 17 by omega))
      have h7 : 7 ≤ kr ^ 3 := (by norm_num : 7 ≤ 2 ^ 3).trans (h2pow 3)
      calc 4 * r + step_max + 2 ≤ 6 * kr ^ 17 + kr ^ 17 := by omega
        _ = 7 * kr ^ 17 := by ring
        _ ≤ kr ^ 3 * kr ^ 17 := Nat.mul_le_mul_right _ h7
        _ = kr ^ 20 := by rw [← pow_add]
    have ht1 : (3 * r + k * step_max + 2) * dmax ≤ kr ^ 11262 := by
      calc (3 * r + k * step_max + 2) * dmax ≤ kr ^ 20 * kr ^ 11242 := Nat.mul_le_mul h1 hdmax_le
        _ = kr ^ 11262 := by rw [← pow_add]
    have ht2 : DB ≤ kr ^ 11262 := hDB_le.trans (Nat.pow_le_pow_right (by omega) (by omega))
    have ht3 : (4 * r + step_max + 2) * (dmax + dB) ≤ 2 * kr ^ 11262 := by
      have hdd : dmax + dB ≤ 2 * kr ^ 11242 := by
        have : dB ≤ kr ^ 11242 := hdB_le.trans (Nat.pow_le_pow_right (by omega) (by omega))
        omega
      calc (4 * r + step_max + 2) * (dmax + dB) ≤ kr ^ 20 * (2 * kr ^ 11242) := Nat.mul_le_mul h2 hdd
        _ = 2 * (kr ^ 20 * kr ^ 11242) := by ring
        _ = 2 * kr ^ 11262 := by rw [← pow_add]
    have h4 : 4 ≤ kr ^ 2 := (by norm_num : 4 ≤ 2 ^ 2).trans (h2pow 2)
    calc Dstep ≤ kr ^ 11262 + kr ^ 11262 + 2 * kr ^ 11262 := by dsimp only [Dstep]; omega
      _ = 4 * kr ^ 11262 := by ring
      _ ≤ kr ^ 2 * kr ^ 11262 := Nat.mul_le_mul_right _ h4
      _ = kr ^ 11264 := by rw [← pow_add]
      _ ≤ kr ^ 11270 := Nat.pow_le_pow_right (by omega) (by omega)
  have hM1 : Mmax + 1 ≤ 2 * kr ^ 5620 := by
    have : 1 ≤ kr ^ 5620 := Nat.one_le_pow _ _ (by omega)
    omega
  have hprod : (Mmax + 1) * Dstep ≤ 2 * kr ^ 16890 := by
    calc (Mmax + 1) * Dstep ≤ (2 * kr ^ 5620) * kr ^ 11270 := Nat.mul_le_mul hM1 hDstep_le
      _ = 2 * (kr ^ 5620 * kr ^ 11270) := by ring
      _ = 2 * kr ^ 16890 := by rw [← pow_add]
  have hD0_big : D0 ≤ kr ^ 16890 := hD0_kr.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h3 : 3 ≤ kr ^ 2 := (by norm_num : 3 ≤ 2 ^ 2).trans (h2pow 2)
  calc D0 + (Mmax + 1) * Dstep ≤ kr ^ 16890 + 2 * kr ^ 16890 := Nat.add_le_add hD0_big hprod
    _ = 3 * kr ^ 16890 := by ring
    _ ≤ kr ^ 2 * kr ^ 16890 := Nat.mul_le_mul_right _ h3
    _ = kr ^ 16892 := by rw [← pow_add]
    _ ≤ kr ^ 16900 := Nat.pow_le_pow_right (by omega) (by omega)

private def propG_goodR {k : ℕ} (r : ℕ) (A X : Finset ℤ)
    {P' P'' : FinProb} (proj : Fin P''.N → Fin P'.N)
    (z' : Fin P'.N → ℤ) (Z' : Fin P'.N → SymNbhd)
    (z'' : Fin P''.N → ℤ) (Ztup : Fin P''.N → Fin k → SymNbhd) (ω'' : Fin P''.N) : Prop :=
  let ν₀ : ℝ := 1 / (k : ℝ) ^ 552
  let ε₀ : ℝ := 1 / (16 * (k : ℝ) ^ 2)
  let α₀ : ℝ := ν₀ / 2
  let τ₁ : ℝ := α₀ / (8 * (k : ℝ))
  let δ₁ : ℝ := α₀ ^ 4 / (256 * (k : ℝ) ^ 4)
  let mZ' : ℕ → ℝ := fun s =>
    cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A
  (ν₀ / 2 ≤ mZ' 0) ∧
  (∀ s ∈ Finset.Icc 1 r, ∀ i : Fin k,
    cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (X \ A) ≤ ε₀ / 4) ∧
  (∀ s ∈ Finset.range (r + 1), ∀ i : Fin k,
    |cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A - mZ' s| ≤ τ₁) ∧
  (∀ s ∈ Finset.range r, ∀ i j : Fin k, i < j →
    ((Ztup ω'' i).set.card : ℝ)⁻¹ *
      ∑ u ∈ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i),
        (cosetConvInd ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (Ztup ω'' j) A u - (mZ' s) ^ 2) ^ 2 ≤ δ₁)

open Classical in
private lemma propG_goodR_expect {k r : ℕ} {A X S : Finset ℤ} {η : ℝ}
    {P' P'' : FinProb} {proj : Fin P''.N → Fin P'.N}
    {z' : Fin P'.N → ℤ} {Z' : Fin P'.N → SymNbhd}
    {z'' : Fin P''.N → ℤ} {Ztup : Fin P''.N → Fin k → SymNbhd}
    (hk : 2 ≤ k) (hr : 1 ≤ r) (hη0 : 0 < η) (hη_big : ((k * r : ℕ) : ℝ) ^ 580 < 1 / η)
    (hSne : S.Nonempty)
    (hAS : (A.card : ℝ) ≤ (k : ℝ) ^ 10 * (S.card : ℝ))
    (hXA : ((X \ A).card : ℝ) ≤ η * (A.card : ℝ))
    (hAS_inter : (S.card : ℝ) ≤ (k : ℝ) ^ 552 * ((A ∩ S).card : ℝ))
    (hpull : ∀ f : Fin P'.N → ℝ, P''.expect (fun ω'' => f (proj ω'')) = P'.expect f)
    (htv_P'_S : tvLe (fun x => P'.expect (fun ω' => unifMeas (coset (z' ω') (Z' ω')) x))
      (unifMeas S) (1 / ((k * r : ℕ) : ℝ) ^ 2800 + 1 / ((k * r : ℕ) : ℝ) ^ 5620))
    (htv_P''_P' : ∀ (i : Fin k) (s : ℕ), s ≤ r →
      tvLe (fun x => P''.expect (fun ω'' => unifMeas (coset ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i)) x))
        (fun x => P'.expect (fun ω' => unifMeas (coset ((2 : ℤ) ^ s * z' ω') ((Z' ω').scale2 s)) x))
        (1 / ((k * r : ℕ) : ℝ) ^ 2800))
    (hU1 : ∀ (i : Fin k) (s : ℕ), s ≤ r →
      P''.expect (fun ω'' => (cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A -
        cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A) ^ 2) ≤
        1 / ((k * r : ℕ) : ℝ) ^ 2800)
    (hU2 : ∀ (i j : Fin k), i < j → ∀ s : ℕ, s ≤ r →
      P''.expect (fun ω'' => ((Ztup ω'' i).set.card : ℝ)⁻¹ *
        ∑ u ∈ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i),
          (cosetConvInd ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (Ztup ω'' j) A u -
            (cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A) ^ 2) ^ 2) ≤
        1 / ((k * r : ℕ) : ℝ) ^ 2800) :
    1 / (k : ℝ) ^ 552 / 4 ≤
      P''.expect (fun ω'' => if propG_goodR r A X proj z' Z' z'' Ztup ω'' then
        cosetDens ((2 : ℤ) ^ 0 * z' (proj ω'')) ((Z' (proj ω'')).scale2 0) A else 0) := by
  classical
  let kr : ℕ := k * r
  have hkr2 : 2 ≤ kr := by dsimp only [kr]; nlinarith
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hr_pos : (0 : ℝ) < (r : ℝ) := by positivity
  have hkr2R : (2 : ℝ) ≤ (kr : ℝ) := by exact_mod_cast hkr2
  have hkr_pos : (0 : ℝ) < (kr : ℝ) := by positivity
  have hk_le_krR : (k : ℝ) ≤ (kr : ℝ) := by exact_mod_cast (show k ≤ kr by dsimp [kr]; exact Nat.le_mul_of_pos_right k hr)
  have hr_le_krR : (r : ℝ) ≤ (kr : ℝ) := by exact_mod_cast (show r ≤ kr by dsimp [kr]; exact Nat.le_mul_of_pos_left r (by omega))
  have hr1_le_krR : ((r + 1 : ℕ) : ℝ) ≤ (kr : ℝ) := by exact_mod_cast (show r + 1 ≤ kr by dsimp [kr]; nlinarith)
  have h2powKR : ∀ n : ℕ, (2 : ℝ) ^ n ≤ (kr : ℝ) ^ n := fun n => pow_le_pow_left₀ (by norm_num) hkr2R n
  let ν₀ : ℝ := 1 / (k : ℝ) ^ 552
  let ε₀ : ℝ := 1 / (16 * (k : ℝ) ^ 2)
  let α₀ : ℝ := ν₀ / 2
  let τ₁ : ℝ := α₀ / (8 * (k : ℝ))
  let δ₁ : ℝ := α₀ ^ 4 / (256 * (k : ℝ) ^ 4)
  let δ₀ : ℝ := 1 / (kr : ℝ) ^ 2800
  let τ₀ : ℝ := 1 / (kr : ℝ) ^ 5620
  have hν₀_pos : 0 < ν₀ := by dsimp only [ν₀]; positivity
  have hε₀_pos : 0 < ε₀ := by dsimp only [ε₀]; positivity
  have hα₀_pos : 0 < α₀ := by dsimp only [α₀]; positivity
  have hτ₁_pos : 0 < τ₁ := by dsimp only [τ₁]; positivity
  have hδ₁_pos : 0 < δ₁ := by dsimp only [δ₁]; positivity
  have hτ₀_le_δ₀ : τ₀ ≤ δ₀ := by
    dsimp only [τ₀, δ₀]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
  let mZ' : ℕ → Fin P''.N → ℝ := fun s ω'' =>
    cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A
  let goodB : Fin P''.N → Prop := fun ω'' => ν₀ / 2 ≤ mZ' 0 ω''
  let goodL : ℕ → Fin k → Fin P''.N → Prop := fun s i ω'' =>
    cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (X \ A) ≤ ε₀ / 4
  let goodF : ℕ → Fin k → Fin P''.N → Prop := fun s i ω'' =>
    |cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A - mZ' s ω''| ≤ τ₁
  let goodE : ℕ → Fin k → Fin k → Fin P''.N → Prop := fun s i j ω'' =>
    ((Ztup ω'' i).set.card : ℝ)⁻¹ *
      ∑ u ∈ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i),
        (cosetConvInd ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (Ztup ω'' j) A u - (mZ' s ω'') ^ 2) ^ 2 ≤ δ₁
  let goodR : Fin P''.N → Prop := fun ω'' =>
    goodB ω'' ∧
    (∀ s ∈ Finset.Icc 1 r, ∀ i : Fin k, goodL s i ω'') ∧
    (∀ s ∈ Finset.range (r + 1), ∀ i : Fin k, goodF s i ω'') ∧
    (∀ s ∈ Finset.range r, ∀ i j : Fin k, i < j → goodE s i j ω'')
  have hE0_lb : ν₀ - (δ₀ + τ₀) ≤ P''.expect (fun ω'' => mZ' 0 ω'') := by
    have hpull0 : P''.expect (fun ω'' => mZ' 0 ω'') =
        P'.expect (fun ω' => cosetDens (z' ω') (Z' ω') A) := by
      have h1 := hpull (fun ω' => cosetDens ((2 : ℤ) ^ 0 * z' ω') ((Z' ω').scale2 0) A)
      rw [h1]
      unfold FinProb.expect
      refine Finset.sum_congr rfl fun ω' _ => ?_
      dsimp only
      have hsc0 : (Z' ω').scale2 0 = Z' ω' := by
        cases Z' ω' with | mk S0 h0 hneg =>
          dsimp only [SymNbhd.scale2]; congr 1; ext x; simp [scale2Fin]
      rw [pow_zero, one_mul, hsc0]
    rw [hpull0]
    have hev := tvLe_eval htv_P'_S A
    have hL : ∑ x ∈ A, P'.expect (fun ω' => unifMeas (coset (z' ω') (Z' ω')) x) =
        P'.expect (fun ω' => cosetDens (z' ω') (Z' ω') A) := by
      unfold FinProb.expect
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω' _ => ?_
      rw [← Finset.mul_sum, ← cosetDens_eq_sum]
    have hR : ∑ x ∈ A, unifMeas S x = ((A ∩ S).card : ℝ) / (S.card : ℝ) := by
      unfold unifMeas
      rw [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Finset.sum_const_zero, add_zero, div_eq_mul_inv]
      have hfilt : A.filter (· ∈ S) = A ∩ S := by ext x; simp [Finset.mem_filter, Finset.mem_inter]
      rw [hfilt]
    rw [hL, hR] at hev
    have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hSne.card_pos
    have hmSA : ν₀ ≤ ((A ∩ S).card : ℝ) / (S.card : ℝ) := by
      dsimp only [ν₀]; rw [div_le_div_iff₀ (by positivity) hSpos]; linarith
    have habs := (abs_le.mp hev).1
    linarith
  have hprob_L : ∀ s ∈ Finset.Icc 1 r, ∀ i : Fin k,
      P''.expect (fun ω'' => if goodL s i ω'' then (0 : ℝ) else 1) ≤
      (4 / ε₀) * (2 * δ₀ + τ₀ + (k : ℝ) ^ 10 * η) := by
    intro s hs i
    have hsr : s ≤ r := (Finset.mem_Icc.mp hs).2
    have hmarkov : P''.expect (fun ω'' => if goodL s i ω'' then (0 : ℝ) else 1) ≤
        (4 / ε₀) * P''.expect (fun ω'' => cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (X \ A)) := by
      rw [← P''.expect_mul_const]
      refine P''.expect_mono fun ω'' => ?_
      by_cases hg : goodL s i ω''
      · rw [if_pos hg]; exact mul_nonneg (by positivity) (cosetDens_nonneg _ _ _)
      · rw [if_neg hg]
        have hgt : ε₀ / 4 < cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (X \ A) := not_le.mp hg
        have h1 : (4 / ε₀) * (ε₀ / 4) = 1 := by field_simp
        rw [← h1]
        exact mul_le_mul_of_nonneg_left hgt.le (by positivity)
    have htv_s : tvLe
        (fun x => P''.expect (fun ω'' => unifMeas (coset ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i)) x))
        (pushScale2 s (unifMeas S)) (2 * δ₀ + τ₀) := by
      have h1 := htv_P''_P' i s hsr
      have h2 := tvLe_pushScale2 s htv_P'_S
      have h2' : tvLe (fun x => P'.expect (fun ω' => unifMeas (coset ((2 : ℤ) ^ s * z' ω') ((Z' ω').scale2 s)) x))
          (pushScale2 s (unifMeas S)) (δ₀ + τ₀) := fun U => by
        simpa only [expect_pushScale2_coset] using h2 U
      exact tvLe_mono (tvLe_trans h1 h2') (by linarith)
    have hev := tvLe_eval htv_s (X \ A)
    have hL : ∑ x ∈ X \ A, P''.expect (fun ω'' => unifMeas (coset ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i)) x) =
        P''.expect (fun ω'' => cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (X \ A)) := by
      unfold FinProb.expect; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω'' _ => by rw [← Finset.mul_sum, ← cosetDens_eq_sum]
    have hR : ∑ x ∈ X \ A, pushScale2 s (unifMeas S) x ≤ (k : ℝ) ^ 10 * η := by
      rw [sum_pushScale2_unifMeas]
      have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hSne.card_pos
      rw [div_le_iff₀ hSpos]
      calc ((scale2Finset s S ∩ (X \ A)).card : ℝ)
          ≤ ((X \ A).card : ℝ) := by exact_mod_cast Finset.card_le_card Finset.inter_subset_right
        _ ≤ η * (A.card : ℝ) := hXA
        _ ≤ η * ((k : ℝ) ^ 10 * (S.card : ℝ)) := mul_le_mul_of_nonneg_left hAS hη0.le
        _ = (k : ℝ) ^ 10 * η * (S.card : ℝ) := by ring
    rw [hL] at hev
    have hE_ub : P''.expect (fun ω'' => cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (X \ A)) ≤
        2 * δ₀ + τ₀ + (k : ℝ) ^ 10 * η := by
      linarith [(abs_le.mp hev).2]
    exact hmarkov.trans (mul_le_mul_of_nonneg_left hE_ub (by positivity))
  have hprob_F : ∀ s ∈ Finset.range (r + 1), ∀ i : Fin k,
      P''.expect (fun ω'' => if goodF s i ω'' then (0 : ℝ) else 1) ≤ δ₀ / τ₁ ^ 2 := by
    intro s hs i
    have hsr : s ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
    have hmarkov : P''.expect (fun ω'' => if goodF s i ω'' then (0 : ℝ) else 1) ≤
        (1 / τ₁ ^ 2) * P''.expect (fun ω'' =>
          (cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A - mZ' s ω'') ^ 2) := by
      rw [← P''.expect_mul_const]
      refine P''.expect_mono fun ω'' => ?_
      by_cases hg : goodF s i ω''
      · rw [if_pos hg]; exact mul_nonneg (by positivity) (sq_nonneg _)
      · rw [if_neg hg]
        have hgt : τ₁ < |cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A - mZ' s ω''| := not_le.mp hg
        have hsq : τ₁ ^ 2 ≤ (cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A - mZ' s ω'') ^ 2 := by
          calc τ₁ ^ 2 ≤ |cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A - mZ' s ω''| ^ 2 :=
                pow_le_pow_left₀ hτ₁_pos.le hgt.le 2
            _ = (cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A - mZ' s ω'') ^ 2 := sq_abs _
        calc (1 : ℝ) = (1 / τ₁ ^ 2) * τ₁ ^ 2 := by field_simp
          _ ≤ (1 / τ₁ ^ 2) * (cosetDens ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) A - mZ' s ω'') ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
    exact hmarkov.trans (by
      have h1 := mul_le_mul_of_nonneg_left (hU1 i s hsr) (by positivity : (0 : ℝ) ≤ 1 / τ₁ ^ 2)
      linarith [show (1 / τ₁ ^ 2) * δ₀ = δ₀ / τ₁ ^ 2 by ring])
  have hprob_E : ∀ s ∈ Finset.range r, ∀ i j : Fin k, i < j →
      P''.expect (fun ω'' => if goodE s i j ω'' then (0 : ℝ) else 1) ≤ δ₀ / δ₁ := by
    intro s hs i j hij
    have hsr : s ≤ r := (Finset.mem_range.mp hs).le
    have hmarkov : P''.expect (fun ω'' => if goodE s i j ω'' then (0 : ℝ) else 1) ≤
        (1 / δ₁) * P''.expect (fun ω'' => ((Ztup ω'' i).set.card : ℝ)⁻¹ *
          ∑ u ∈ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i),
            (cosetConvInd ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (Ztup ω'' j) A u - (mZ' s ω'') ^ 2) ^ 2) := by
      rw [← P''.expect_mul_const]
      refine P''.expect_mono fun ω'' => ?_
      by_cases hg : goodE s i j ω''
      · rw [if_pos hg]
        exact mul_nonneg (by positivity)
          (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      · rw [if_neg hg]
        have hgt : δ₁ < ((Ztup ω'' i).set.card : ℝ)⁻¹ *
            ∑ u ∈ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i),
              (cosetConvInd ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (Ztup ω'' j) A u - (mZ' s ω'') ^ 2) ^ 2 :=
          not_le.mp hg
        calc (1 : ℝ) = (1 / δ₁) * δ₁ := by field_simp
          _ ≤ (1 / δ₁) * (((Ztup ω'' i).set.card : ℝ)⁻¹ *
              ∑ u ∈ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i),
                (cosetConvInd ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (Ztup ω'' j) A u - (mZ' s ω'') ^ 2) ^ 2) :=
            mul_le_mul_of_nonneg_left hgt.le (by positivity)
    exact hmarkov.trans (by
      have h1 := mul_le_mul_of_nonneg_left (hU2 i j hij s hsr) (by positivity : (0 : ℝ) ≤ 1 / δ₁)
      linarith [show (1 / δ₁) * δ₀ = δ₀ / δ₁ by ring])
  let pairs : Finset (Fin k × Fin k) := Finset.univ.filter (fun p => p.1 < p.2)
  have hpt : ∀ ω'' : Fin P''.N,
      mZ' 0 ω'' - ν₀ / 2 -
      (∑ s ∈ Finset.Icc 1 r, ∑ i : Fin k, if goodL s i ω'' then (0 : ℝ) else 1) -
      (∑ s ∈ Finset.range (r + 1), ∑ i : Fin k, if goodF s i ω'' then (0 : ℝ) else 1) -
      (∑ s ∈ Finset.range r, ∑ p ∈ pairs, if goodE s p.1 p.2 ω'' then (0 : ℝ) else 1) ≤
      if goodR ω'' then mZ' 0 ω'' else 0 := by
    intro ω''
    have hnnL : 0 ≤ ∑ s ∈ Finset.Icc 1 r, ∑ i : Fin k, if goodL s i ω'' then (0 : ℝ) else 1 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have hnnF : 0 ≤ ∑ s ∈ Finset.range (r + 1), ∑ i : Fin k, if goodF s i ω'' then (0 : ℝ) else 1 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    have hnnE : 0 ≤ ∑ s ∈ Finset.range r, ∑ p ∈ pairs, if goodE s p.1 p.2 ω'' then (0 : ℝ) else 1 :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
    by_cases hgR : goodR ω''
    · rw [if_pos hgR]; linarith
    · rw [if_neg hgR]
      have hm1 : mZ' 0 ω'' ≤ 1 := cosetDens_le_one _ _ _
      by_cases hB : goodB ω''
      · by_cases hL : ∀ s ∈ Finset.Icc 1 r, ∀ i : Fin k, goodL s i ω''
        · by_cases hF : ∀ s ∈ Finset.range (r + 1), ∀ i : Fin k, goodF s i ω''
          · have hnotE : ¬ (∀ s ∈ Finset.range r, ∀ i j : Fin k, i < j → goodE s i j ω'') :=
              fun hE => hgR ⟨hB, hL, hF, hE⟩
            push Not at hnotE
            obtain ⟨s, hs, i, j, hij, hbad⟩ := hnotE
            have hge1 : (1 : ℝ) ≤ ∑ s ∈ Finset.range r, ∑ p ∈ pairs, if goodE s p.1 p.2 ω'' then (0 : ℝ) else 1 := by
              have hp : (i, j) ∈ pairs := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
              have h1 : (1 : ℝ) ≤ ∑ p ∈ pairs, if goodE s p.1 p.2 ω'' then (0 : ℝ) else 1 := by
                have hsing := Finset.single_le_sum (f := fun p : Fin k × Fin k => if goodE s p.1 p.2 ω'' then (0 : ℝ) else 1)
                  (fun _ _ => by split_ifs <;> norm_num) hp
                rwa [if_neg hbad] at hsing
              exact h1.trans (Finset.single_le_sum (f := fun s => ∑ p ∈ pairs, if goodE s p.1 p.2 ω'' then (0 : ℝ) else 1)
                (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num) hs)
            linarith
          · push Not at hF
            obtain ⟨s, hs, i, hbad⟩ := hF
            have hge1 : (1 : ℝ) ≤ ∑ s ∈ Finset.range (r + 1), ∑ i : Fin k, if goodF s i ω'' then (0 : ℝ) else 1 := by
              have h1 : (1 : ℝ) ≤ ∑ i : Fin k, if goodF s i ω'' then (0 : ℝ) else 1 := by
                have hsing := Finset.single_le_sum (f := fun i : Fin k => if goodF s i ω'' then (0 : ℝ) else 1)
                  (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
                rwa [if_neg hbad] at hsing
              exact h1.trans (Finset.single_le_sum (f := fun s => ∑ i : Fin k, if goodF s i ω'' then (0 : ℝ) else 1)
                (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num) hs)
            linarith
        · push Not at hL
          obtain ⟨s, hs, i, hbad⟩ := hL
          have hge1 : (1 : ℝ) ≤ ∑ s ∈ Finset.Icc 1 r, ∑ i : Fin k, if goodL s i ω'' then (0 : ℝ) else 1 := by
            have h1 : (1 : ℝ) ≤ ∑ i : Fin k, if goodL s i ω'' then (0 : ℝ) else 1 := by
              have hsing := Finset.single_le_sum (f := fun i : Fin k => if goodL s i ω'' then (0 : ℝ) else 1)
                (fun _ _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
              rwa [if_neg hbad] at hsing
            exact h1.trans (Finset.single_le_sum (f := fun s => ∑ i : Fin k, if goodL s i ω'' then (0 : ℝ) else 1)
              (fun _ _ => Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num) hs)
          linarith
      · have hlt : mZ' 0 ω'' < ν₀ / 2 := not_le.mp hB
        linarith
  have hexp := P''.expect_mono hpt
  rw [P''.expect_sub, P''.expect_sub, P''.expect_sub, P''.expect_sub, P''.expect_const] at hexp
  have hsum_expect : ∀ {ι : Type} (U : Finset ι) (f : ι → Fin P''.N → ℝ),
      P''.expect (fun ω'' => ∑ u ∈ U, f u ω'') = ∑ u ∈ U, P''.expect (f u) := fun U f => by
    unfold FinProb.expect; simp_rw [Finset.mul_sum]; exact Finset.sum_comm
  have hL_tot : P''.expect (fun ω'' => ∑ s ∈ Finset.Icc 1 r, ∑ i : Fin k, if goodL s i ω'' then (0 : ℝ) else 1) ≤
      ν₀ / 16 := by
    rw [hsum_expect (Finset.Icc (1 : ℕ) r) (fun (s : ℕ) ω'' => ∑ i : Fin k, if goodL s i ω'' then (0 : ℝ) else 1)]
    calc ∑ s ∈ Finset.Icc 1 r, P''.expect (fun ω'' => ∑ i : Fin k, if goodL s i ω'' then (0 : ℝ) else 1)
        = ∑ s ∈ Finset.Icc 1 r, ∑ i : Fin k, P''.expect (fun ω'' => if goodL s i ω'' then (0 : ℝ) else 1) :=
          Finset.sum_congr rfl fun s _ => hsum_expect _ _
      _ ≤ ∑ _s ∈ Finset.Icc 1 r, ∑ _i : Fin k, ((4 / ε₀) * (2 * δ₀ + τ₀ + (k : ℝ) ^ 10 * η)) :=
          Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun i _ => hprob_L s hs i
      _ = (r : ℝ) * (k : ℝ) * ((4 / ε₀) * (2 * δ₀ + τ₀ + (k : ℝ) ^ 10 * η)) := by
          simp [Nat.card_Icc]; ring
      _ ≤ ν₀ / 16 := by
          have h4ε : 4 / ε₀ = 64 * (k : ℝ) ^ 2 := by dsimp only [ε₀]; field_simp; ring
          rw [h4ε]
          have h1 : (r : ℝ) * (k : ℝ) * (64 * (k : ℝ) ^ 2 * (3 * δ₀)) ≤ ν₀ / 32 := by
            dsimp only [δ₀, ν₀]
            have h6144 : (6144 : ℝ) ≤ (kr : ℝ) ^ 13 := (by norm_num : (6144 : ℝ) ≤ (2 : ℝ) ^ 13).trans (h2powKR 13)
            have hlhs : (r : ℝ) * (k : ℝ) * (64 * (k : ℝ) ^ 2 * (3 * (1 / (kr : ℝ) ^ 2800))) =
                (192 * (r : ℝ) * (k : ℝ) ^ 3) / (kr : ℝ) ^ 2800 := by ring
            have hrhs : 1 / (k : ℝ) ^ 552 / 32 = 1 / (32 * (k : ℝ) ^ 552) := by ring
            rw [hlhs, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
            calc 192 * (r : ℝ) * (k : ℝ) ^ 3 * (32 * (k : ℝ) ^ 552)
                = 6144 * (r : ℝ) * (k : ℝ) ^ 555 := by ring
              _ ≤ (kr : ℝ) ^ 13 * (kr : ℝ) * (kr : ℝ) ^ 555 := by gcongr
              _ = (kr : ℝ) ^ 569 := by ring
              _ ≤ 1 * (kr : ℝ) ^ 2800 := by rw [one_mul]; exact pow_le_pow_right₀ (by linarith) (by omega)
          have hη_ub : η ≤ 1 / (kr : ℝ) ^ 580 := by
            rw [le_div_iff₀ (by positivity)]
            have := (lt_div_iff₀ hη0).mp hη_big
            have hkr_cast : ((k * r : ℕ) : ℝ) = (kr : ℝ) := rfl
            rw [hkr_cast] at this; linarith
          have h2 : (r : ℝ) * (k : ℝ) * (64 * (k : ℝ) ^ 2 * ((k : ℝ) ^ 10 * η)) ≤ ν₀ / 32 := by
            dsimp only [ν₀]
            have h2048 : (2048 : ℝ) ≤ (kr : ℝ) ^ 11 := (by norm_num : (2048 : ℝ) = (2 : ℝ) ^ 11).le.trans (h2powKR 11)
            have hstep : (r : ℝ) * (k : ℝ) * (64 * (k : ℝ) ^ 2 * ((k : ℝ) ^ 10 * η)) ≤
                (64 * (r : ℝ) * (k : ℝ) ^ 13) / (kr : ℝ) ^ 580 := by
              calc (r : ℝ) * (k : ℝ) * (64 * (k : ℝ) ^ 2 * ((k : ℝ) ^ 10 * η))
                  = (64 * (r : ℝ) * (k : ℝ) ^ 13) * η := by ring
                _ ≤ (64 * (r : ℝ) * (k : ℝ) ^ 13) * (1 / (kr : ℝ) ^ 580) := by gcongr
                _ = (64 * (r : ℝ) * (k : ℝ) ^ 13) / (kr : ℝ) ^ 580 := by ring
            refine hstep.trans ?_
            have hrhs : 1 / (k : ℝ) ^ 552 / 32 = 1 / (32 * (k : ℝ) ^ 552) := by ring
            rw [hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
            calc 64 * (r : ℝ) * (k : ℝ) ^ 13 * (32 * (k : ℝ) ^ 552)
                = 2048 * (r : ℝ) * (k : ℝ) ^ 565 := by ring
              _ ≤ (kr : ℝ) ^ 11 * (kr : ℝ) * (kr : ℝ) ^ 565 := by gcongr
              _ = (kr : ℝ) ^ 577 := by ring
              _ ≤ 1 * (kr : ℝ) ^ 580 := by rw [one_mul]; exact pow_le_pow_right₀ (by linarith) (by omega)
          have h3 : (r : ℝ) * (k : ℝ) * (64 * (k : ℝ) ^ 2 * (2 * δ₀ + τ₀ + (k : ℝ) ^ 10 * η)) ≤
              (r : ℝ) * (k : ℝ) * (64 * (k : ℝ) ^ 2 * (3 * δ₀)) +
              (r : ℝ) * (k : ℝ) * (64 * (k : ℝ) ^ 2 * ((k : ℝ) ^ 10 * η)) := by
            have hle : 2 * δ₀ + τ₀ + (k : ℝ) ^ 10 * η ≤ 3 * δ₀ + (k : ℝ) ^ 10 * η := by linarith
            calc (r : ℝ) * (k : ℝ) * (64 * (k : ℝ) ^ 2 * (2 * δ₀ + τ₀ + (k : ℝ) ^ 10 * η))
                ≤ (r : ℝ) * (k : ℝ) * (64 * (k : ℝ) ^ 2 * (3 * δ₀ + (k : ℝ) ^ 10 * η)) := by gcongr
              _ = _ := by ring
          linarith
  have hF_tot : P''.expect (fun ω'' => ∑ s ∈ Finset.range (r + 1), ∑ i : Fin k, if goodF s i ω'' then (0 : ℝ) else 1) ≤
      ν₀ / 16 := by
    rw [hsum_expect (Finset.range (r + 1)) (fun s ω'' => ∑ i : Fin k, if goodF s i ω'' then (0 : ℝ) else 1)]
    calc ∑ s ∈ Finset.range (r + 1), P''.expect (fun ω'' => ∑ i : Fin k, if goodF s i ω'' then (0 : ℝ) else 1)
        = ∑ s ∈ Finset.range (r + 1), ∑ i : Fin k, P''.expect (fun ω'' => if goodF s i ω'' then (0 : ℝ) else 1) :=
          Finset.sum_congr rfl fun s _ => hsum_expect _ _
      _ ≤ ∑ _s ∈ Finset.range (r + 1), ∑ _i : Fin k, (δ₀ / τ₁ ^ 2) :=
          Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun i _ => hprob_F s hs i
      _ = ((r + 1 : ℕ) : ℝ) * (k : ℝ) * (δ₀ / τ₁ ^ 2) := by simp; ring
      _ ≤ ν₀ / 16 := by
          have hτ1sq : δ₀ / τ₁ ^ 2 = (256 * (k : ℝ) ^ 1106) / (kr : ℝ) ^ 2800 := by
            dsimp only [δ₀, τ₁, α₀, ν₀]; field_simp; ring
          rw [hτ1sq]
          have hrhs : ν₀ / 16 = 1 / (16 * (k : ℝ) ^ 552) := by dsimp only [ν₀]; ring
          rw [hrhs, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          have h4096 : (4096 : ℝ) ≤ (kr : ℝ) ^ 12 := (by norm_num : (4096 : ℝ) = (2 : ℝ) ^ 12).le.trans (h2powKR 12)
          calc ((r + 1 : ℕ) : ℝ) * (k : ℝ) * (256 * (k : ℝ) ^ 1106) * (16 * (k : ℝ) ^ 552)
              = 4096 * ((r + 1 : ℕ) : ℝ) * (k : ℝ) ^ 1659 := by ring
            _ ≤ (kr : ℝ) ^ 12 * (kr : ℝ) * (kr : ℝ) ^ 1659 := by gcongr
            _ = (kr : ℝ) ^ 1672 := by ring
            _ ≤ 1 * (kr : ℝ) ^ 2800 := by rw [one_mul]; exact pow_le_pow_right₀ (by linarith) (by omega)
  have hE_tot : P''.expect (fun ω'' => ∑ s ∈ Finset.range r, ∑ p ∈ pairs, if goodE s p.1 p.2 ω'' then (0 : ℝ) else 1) ≤
      ν₀ / 16 := by
    rw [hsum_expect (Finset.range r) (fun s ω'' => ∑ p ∈ pairs, if goodE s p.1 p.2 ω'' then (0 : ℝ) else 1)]
    calc ∑ s ∈ Finset.range r, P''.expect (fun ω'' => ∑ p ∈ pairs, if goodE s p.1 p.2 ω'' then (0 : ℝ) else 1)
        = ∑ s ∈ Finset.range r, ∑ p ∈ pairs, P''.expect (fun ω'' => if goodE s p.1 p.2 ω'' then (0 : ℝ) else 1) :=
          Finset.sum_congr rfl fun s _ => hsum_expect _ _
      _ ≤ ∑ _s ∈ Finset.range r, ∑ _p ∈ pairs, (δ₀ / δ₁) :=
          Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun p hp => hprob_E s hs p.1 p.2 (Finset.mem_filter.mp hp).2
      _ = (r : ℝ) * (pairs.card : ℝ) * (δ₀ / δ₁) := by simp; ring
      _ ≤ (r : ℝ) * (k : ℝ) ^ 2 * (δ₀ / δ₁) := by
          have hpcard : (pairs.card : ℝ) ≤ (k : ℝ) ^ 2 := by
            have h1 : pairs.card ≤ (Finset.univ : Finset (Fin k × Fin k)).card := Finset.card_filter_le _ _
            simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
            rw [sq]; exact_mod_cast h1
          gcongr
      _ ≤ ν₀ / 16 := by
          have hδ1eq : δ₀ / δ₁ = (4096 * (k : ℝ) ^ 2212) / (kr : ℝ) ^ 2800 := by
            dsimp only [δ₀, δ₁, α₀, ν₀]; field_simp; ring
          rw [hδ1eq]
          have hrhs : ν₀ / 16 = 1 / (16 * (k : ℝ) ^ 552) := by dsimp only [ν₀]; ring
          rw [hrhs, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          have h65536 : (65536 : ℝ) ≤ (kr : ℝ) ^ 16 := (by norm_num : (65536 : ℝ) = (2 : ℝ) ^ 16).le.trans (h2powKR 16)
          calc (r : ℝ) * (k : ℝ) ^ 2 * (4096 * (k : ℝ) ^ 2212) * (16 * (k : ℝ) ^ 552)
              = 65536 * (r : ℝ) * (k : ℝ) ^ 2766 := by ring
            _ ≤ (kr : ℝ) ^ 16 * (kr : ℝ) * (kr : ℝ) ^ 2766 := by gcongr
            _ = (kr : ℝ) ^ 2783 := by ring
            _ ≤ 1 * (kr : ℝ) ^ 2800 := by rw [one_mul]; exact pow_le_pow_right₀ (by linarith) (by omega)
  have hδτ_small : δ₀ + τ₀ ≤ ν₀ / 16 := by
    have h2δ : δ₀ + τ₀ ≤ 2 * δ₀ := by linarith
    refine h2δ.trans ?_
    dsimp only [δ₀, ν₀]
    have h32 : (32 : ℝ) ≤ (kr : ℝ) ^ 5 := (by norm_num : (32 : ℝ) = (2 : ℝ) ^ 5).le.trans (h2powKR 5)
    have hlhs : 2 * (1 / (kr : ℝ) ^ 2800) = 2 / (kr : ℝ) ^ 2800 := by ring
    have hrhs : 1 / (k : ℝ) ^ 552 / 16 = 1 / (16 * (k : ℝ) ^ 552) := by ring
    rw [hlhs, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 2 * (16 * (k : ℝ) ^ 552) = 32 * (k : ℝ) ^ 552 := by ring
      _ ≤ (kr : ℝ) ^ 5 * (kr : ℝ) ^ 552 := by gcongr
      _ = (kr : ℝ) ^ 557 := by ring
      _ ≤ 1 * (kr : ℝ) ^ 2800 := by rw [one_mul]; exact pow_le_pow_right₀ (by linarith) (by omega)
  have hcongr : P''.expect (fun ω'' => if goodR ω'' then mZ' 0 ω'' else 0) =
      P''.expect (fun ω'' => if propG_goodR r A X proj z' Z' z'' Ztup ω'' then mZ' 0 ω'' else 0) := by
    unfold FinProb.expect
    refine Finset.sum_congr rfl fun ω'' _ => ?_
    dsimp only
    by_cases h : goodR ω''
    · rw [if_pos h, if_pos (show propG_goodR r A X proj z' Z' z'' Ztup ω'' from h)]
    · rw [if_neg h, if_neg (show ¬ propG_goodR r A X proj z' Z' z'' Ztup ω'' from h)]
  change ν₀ / 4 ≤ P''.expect (fun ω'' => if propG_goodR r A X proj z' Z' z'' Ztup ω'' then mZ' 0 ω'' else 0)
  rw [← hcongr]
  linarith

private lemma propG_induct_dens {k r : ℕ} {A X S : Finset ℤ}
    {P' P'' : FinProb} {proj : Fin P''.N → Fin P'.N}
    {z' : Fin P'.N → ℤ} {Z' : Fin P'.N → SymNbhd}
    {z'' : Fin P''.N → ℤ} {Ztup : Fin P''.N → Fin k → SymNbhd}
    (hk : 2 ≤ k) (hr : 1 ≤ r)
    (hA_small : Real.exp (((k * r : ℕ) : ℝ) ^ 16905) < (A.card : ℝ))
    (hsum : IsSumming k A X)
    (hAS : (A.card : ℝ) ≤ (k : ℝ) ^ 10 * (S.card : ℝ))
    (hZcl : ∀ ω'' (i : Fin k) (hi : i.val + 1 < k),
      IsClosedPair (1 / ((k * r : ℕ) : ℝ) ^ 2800) (Ztup ω'' i) (Ztup ω'' ⟨i.val + 1, hi⟩))
    (hZsub : ∀ ω'' (i j : Fin k), i ≤ j → (Ztup ω'' j).set ⊆ (Ztup ω'' i).set)
    (hDfinal : ∀ ω'', covFlat (S : Set ℤ) ((Ztup ω'' ⟨k - 1, by omega⟩).set : Set ℤ) ≤
      ((2 ^ ((k * r) ^ 16900) : ℕ) : ℕ∞)) :
    ∀ ω'' : Fin P''.N, propG_goodR r A X proj z' Z' z'' Ztup ω'' →
      ∀ s : ℕ, s ≤ r →
        1 / (k : ℝ) ^ 552 / 2 ≤ cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A := by
  classical
  let kr : ℕ := k * r
  have hkr2 : 2 ≤ kr := by dsimp only [kr]; nlinarith
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hkr2R : (2 : ℝ) ≤ (kr : ℝ) := by exact_mod_cast hkr2
  have hk_le_krR : (k : ℝ) ≤ (kr : ℝ) := by exact_mod_cast (show k ≤ kr by dsimp [kr]; exact Nat.le_mul_of_pos_right k hr)
  have h2powK : ∀ n : ℕ, (2 : ℝ) ^ n ≤ (k : ℝ) ^ n := fun n => pow_le_pow_left₀ (by norm_num) hk2 n
  have h2powKR : ∀ n : ℕ, (2 : ℝ) ^ n ≤ (kr : ℝ) ^ n := fun n => pow_le_pow_left₀ (by norm_num) hkr2R n
  let ν₀ : ℝ := 1 / (k : ℝ) ^ 552
  let ε₀ : ℝ := 1 / (16 * (k : ℝ) ^ 2)
  let α₀ : ℝ := ν₀ / 2
  let τ₁ : ℝ := α₀ / (8 * (k : ℝ))
  let δ₁ : ℝ := α₀ ^ 4 / (256 * (k : ℝ) ^ 4)
  let δ₀ : ℝ := 1 / (kr : ℝ) ^ 2800
  have hε₀_pos : 0 < ε₀ := by dsimp only [ε₀]; positivity
  have hα₀_pos : 0 < α₀ := by dsimp only [α₀, ν₀]; positivity
  have hτ₁_pos : 0 < τ₁ := by dsimp only [τ₁, α₀, ν₀]; positivity
  have hδ₁_pos : 0 < δ₁ := by dsimp only [δ₁, α₀, ν₀]; positivity
  have hν₀_le_ε₀ : ν₀ ≤ ε₀ := by
    dsimp only [ν₀, ε₀]
    apply one_div_le_one_div_of_le (by positivity)
    have h16 : (16 : ℝ) ≤ (k : ℝ) ^ 4 := (by norm_num : (16 : ℝ) = (2 : ℝ) ^ 4).le.trans (h2powK 4)
    calc 16 * (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 * (k : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h16 (by positivity)
      _ = (k : ℝ) ^ 6 := by ring
      _ ≤ (k : ℝ) ^ 552 := pow_le_pow_right₀ (by linarith) (by omega)
  have hτ₁_le_ε₀ : τ₁ ≤ ε₀ / 4 := by
    have h1 : τ₁ = 1 / (16 * (k : ℝ) ^ 553) := by dsimp only [τ₁, α₀, ν₀]; field_simp; ring
    have h2 : ε₀ / 4 = 1 / (64 * (k : ℝ) ^ 2) := by dsimp only [ε₀]; field_simp; ring
    rw [h1, h2]
    apply one_div_le_one_div_of_le (by positivity)
    have h4 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := (by norm_num : (4 : ℝ) = (2 : ℝ) ^ 2).le.trans (h2powK 2)
    calc 64 * (k : ℝ) ^ 2 = 16 * (4 * (k : ℝ) ^ 2) := by ring
      _ ≤ 16 * ((k : ℝ) ^ 2 * (k : ℝ) ^ 2) := by gcongr
      _ = 16 * (k : ℝ) ^ 4 := by ring
      _ ≤ 16 * (k : ℝ) ^ 553 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (by omega)) (by norm_num)
  have hδ₀_le_τ₁ : δ₀ ≤ τ₁ := by
    have h1 : τ₁ = 1 / (16 * (k : ℝ) ^ 553) := by dsimp only [τ₁, α₀, ν₀]; field_simp; ring
    rw [h1]; dsimp only [δ₀]
    apply one_div_le_one_div_of_le (by positivity)
    have h16 : (16 : ℝ) ≤ (kr : ℝ) ^ 4 := (by norm_num : (16 : ℝ) = (2 : ℝ) ^ 4).le.trans (h2powKR 4)
    calc 16 * (k : ℝ) ^ 553 ≤ (kr : ℝ) ^ 4 * (kr : ℝ) ^ 553 := by gcongr
      _ = (kr : ℝ) ^ 557 := by ring
      _ ≤ (kr : ℝ) ^ 2800 := pow_le_pow_right₀ (by linarith) (by omega)
  let mZ' : ℕ → Fin P''.N → ℝ := fun s ω'' =>
    cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A
  intro ω'' hR s
  induction s with
  | zero => intro _; exact hR.1
  | succ s ih =>
    intro hs1
    have hα_lb : α₀ ≤ mZ' s ω'' := ih (by omega)
    have hex_i : ∃ i : Fin k, ε₀ < cosetDens ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i) X := by
      by_contra hno
      push Not at hno
      have h2eq : 2 * ((2 : ℤ) ^ s * z'' ω'') = (2 : ℤ) ^ (s + 1) * z'' ω'' := by rw [pow_succ]; ring
      have hX_all : ∀ i : Fin k, cosetDens (2 * ((2 : ℤ) ^ s * z'' ω'')) (Ztup ω'' i) X ≤ ε₀ := fun i => by
        rw [h2eq]; exact hno i
      have hU2_all : ∀ i j : Fin k, i < j →
          ((Ztup ω'' i).set.card : ℝ)⁻¹ *
            ∑ u ∈ coset (2 * ((2 : ℤ) ^ s * z'' ω'')) (Ztup ω'' i),
              (cosetConvInd ((2 : ℤ) ^ s * z'' ω'') (Ztup ω'' i) (Ztup ω'' j) A u - (mZ' s ω'') ^ 2) ^ 2 ≤ δ₁ :=
        fun i j hij => by
          rw [h2eq]; exact hR.2.2.2 s (Finset.mem_range.mpr (by omega)) i j hij
      have hZk_le := lem_c_summing hk (hα₀_pos.trans_le hα_lb) (cosetDens_le_one _ _ _)
        hτ₁_pos.le hε₀_pos.le (by dsimp only [ε₀]; rw [div_le_one (by positivity)]; nlinarith) hδ₁_pos.le hsum
        (fun i hi => isClosedPair_mono_tau (hZcl ω'' i hi) hδ₀_le_τ₁)
        (hZsub ω'')
        (fun i => hR.2.2.1 s (Finset.mem_range.mpr (by omega)) i)
        hX_all hU2_all
        (by have h1 : 8 * (k : ℝ) * τ₁ = α₀ := by dsimp only [τ₁]; field_simp
            rw [h1]; exact hα_lb)
        (by have h1 : 16 * (k : ℝ) ^ 2 * ε₀ = 1 := by dsimp only [ε₀]; field_simp
            linarith)
        (by have h1 : 256 * (k : ℝ) ^ 4 * δ₁ = α₀ ^ 4 := by dsimp only [δ₁]; field_simp
            rw [h1]; exact pow_le_pow_left₀ hα₀_pos.le hα_lb 4)
      have hS_le_Zk : (S.card : ℝ) ≤ (2 : ℝ) ^ (kr ^ 16900) * ((Ztup ω'' ⟨k - 1, by omega⟩).set.card : ℝ) := by
        have h1 := covNum_card_le (X := S) (Y := (Ztup ω'' ⟨k - 1, by omega⟩).set)
          (fun _ => (Ztup ω'' ⟨k - 1, by omega⟩).nonempty)
        have hcov : covNum (S : Set ℤ) ((Ztup ω'' ⟨k - 1, by omega⟩).set : Set ℤ) ≤
            ((2 ^ (kr ^ 16900) : ℕ) : ℕ∞) := (covNum_le_covFlat _ _).trans (hDfinal ω'')
        have hnat : S.card ≤ 2 ^ (kr ^ 16900) * (Ztup ω'' ⟨k - 1, by omega⟩).set.card := by
          have he := h1.trans (mul_le_mul' hcov le_rfl)
          rw [← Nat.cast_mul] at he
          exact ENat.natCast_le_natCast.mp he
        exact_mod_cast hnat
      have hαk_inv : 1 / (mZ' s ω'') ^ k ≤ (2 * (k : ℝ) ^ 552) ^ k := by
        have h1 : α₀ ^ k ≤ (mZ' s ω'') ^ k := pow_le_pow_left₀ hα₀_pos.le hα_lb k
        have h2 : 1 / (mZ' s ω'') ^ k ≤ 1 / α₀ ^ k := one_div_le_one_div_of_le (pow_pos hα₀_pos k) h1
        have hαeq : α₀ = (2 * (k : ℝ) ^ 552)⁻¹ := by dsimp only [α₀, ν₀]; field_simp
        have h3 : 1 / α₀ ^ k = (2 * (k : ℝ) ^ 552) ^ k := by rw [hαeq, inv_pow, one_div, inv_inv]
        linarith
      have hA_ub : (A.card : ℝ) ≤ (2 : ℝ) ^ (kr ^ 16905) := by
        have hk2k : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
        have hfac : (k : ℝ) ^ 10 * (2 * (k : ℝ) ^ 2 * (2 * (k : ℝ) ^ 552) ^ k) ≤ (2 : ℝ) ^ (kr ^ 16900) := by
          have h1 : (k : ℝ) ^ 10 ≤ (2 : ℝ) ^ (10 * k) := by
            calc (k : ℝ) ^ 10 ≤ ((2 : ℝ) ^ k) ^ 10 := pow_le_pow_left₀ hk_pos.le hk2k 10
              _ = (2 : ℝ) ^ (10 * k) := by rw [← pow_mul, mul_comm]
          have h2 : (k : ℝ) ^ 2 ≤ (2 : ℝ) ^ (2 * k) := by
            calc (k : ℝ) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 := pow_le_pow_left₀ hk_pos.le hk2k 2
              _ = (2 : ℝ) ^ (2 * k) := by rw [← pow_mul, mul_comm]
          have h3 : (2 * (k : ℝ) ^ 552) ^ k ≤ (2 : ℝ) ^ (k + 552 * k * k) := by
            have h552 : (k : ℝ) ^ 552 ≤ (2 : ℝ) ^ (552 * k) := by
              calc (k : ℝ) ^ 552 ≤ ((2 : ℝ) ^ k) ^ 552 := pow_le_pow_left₀ hk_pos.le hk2k 552
                _ = (2 : ℝ) ^ (552 * k) := by rw [← pow_mul, mul_comm]
            calc (2 * (k : ℝ) ^ 552) ^ k ≤ ((2 : ℝ) ^ 1 * (2 : ℝ) ^ (552 * k)) ^ k :=
                  pow_le_pow_left₀ (by positivity) (by linarith) k
              _ = ((2 : ℝ) ^ (1 + 552 * k)) ^ k := by rw [← pow_add]
              _ = (2 : ℝ) ^ ((1 + 552 * k) * k) := by rw [← pow_mul]
              _ = (2 : ℝ) ^ (k + 552 * k * k) := by congr 1; ring
          have hexp : 10 * k + 1 + 2 * k + (k + 552 * k * k) ≤ kr ^ 16900 := by
            have h566 : 10 * k + 1 + 2 * k + (k + 552 * k * k) ≤ 566 * kr * kr := by
              have hk1 : k ≤ kr := by dsimp [kr]; exact Nat.le_mul_of_pos_right k hr
              nlinarith
            have h566p : 566 ≤ kr ^ 10 := (by norm_num : 566 ≤ 2 ^ 10).trans (Nat.pow_le_pow_left hkr2 10)
            calc 10 * k + 1 + 2 * k + (k + 552 * k * k)
                ≤ 566 * kr * kr := h566
              _ ≤ kr ^ 10 * kr * kr := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h566p)
              _ = kr ^ 12 := by ring
              _ ≤ kr ^ 16900 := Nat.pow_le_pow_right (by omega) (by omega)
          calc (k : ℝ) ^ 10 * (2 * (k : ℝ) ^ 2 * (2 * (k : ℝ) ^ 552) ^ k)
              ≤ (2 : ℝ) ^ (10 * k) * ((2 : ℝ) ^ 1 * (2 : ℝ) ^ (2 * k) * (2 : ℝ) ^ (k + 552 * k * k)) := by
                rw [pow_one]; gcongr
            _ = (2 : ℝ) ^ (10 * k + 1 + 2 * k + (k + 552 * k * k)) := by
                rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
            _ ≤ (2 : ℝ) ^ (kr ^ 16900) := pow_le_pow_right₀ (by norm_num) hexp
        have hZk_bound : ((Ztup ω'' ⟨k - 1, by omega⟩).set.card : ℝ) ≤ 2 * (k : ℝ) ^ 2 * (2 * (k : ℝ) ^ 552) ^ k := by
          have h1 : 2 * (k : ℝ) ^ 2 / (mZ' s ω'') ^ k = 2 * (k : ℝ) ^ 2 * (1 / (mZ' s ω'') ^ k) := by ring
          rw [h1] at hZk_le
          exact hZk_le.trans (mul_le_mul_of_nonneg_left hαk_inv (by positivity))
        have h2exp : kr ^ 16900 + kr ^ 16900 ≤ kr ^ 16905 := by
          calc kr ^ 16900 + kr ^ 16900 = 2 * kr ^ 16900 := by ring
            _ ≤ kr * kr ^ 16900 := Nat.mul_le_mul_right _ hkr2
            _ = kr ^ 16901 := by rw [← pow_succ']
            _ ≤ kr ^ 16905 := Nat.pow_le_pow_right (by omega) (by omega)
        calc (A.card : ℝ) ≤ (k : ℝ) ^ 10 * (S.card : ℝ) := hAS
          _ ≤ (k : ℝ) ^ 10 * ((2 : ℝ) ^ (kr ^ 16900) * ((Ztup ω'' ⟨k - 1, by omega⟩).set.card : ℝ)) := by gcongr
          _ ≤ (2 : ℝ) ^ (kr ^ 16900) * ((k : ℝ) ^ 10 * (2 * (k : ℝ) ^ 2 * (2 * (k : ℝ) ^ 552) ^ k)) := by
              have := mul_le_mul_of_nonneg_left hZk_bound (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 10 * (2 : ℝ) ^ (kr ^ 16900))
              linarith
          _ ≤ (2 : ℝ) ^ (kr ^ 16900) * (2 : ℝ) ^ (kr ^ 16900) := by gcongr
          _ = (2 : ℝ) ^ (kr ^ 16900 + kr ^ 16900) := by rw [← pow_add]
          _ ≤ (2 : ℝ) ^ (kr ^ 16905) := pow_le_pow_right₀ (by norm_num) h2exp
      have h2exp_le : (2 : ℝ) ^ (kr ^ 16905) ≤ Real.exp (((k * r : ℕ) : ℝ) ^ 16905) := by
        have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        calc (2 : ℝ) ^ (kr ^ 16905) ≤ (Real.exp 1) ^ (kr ^ 16905) := pow_le_pow_left₀ (by norm_num) h2e _
          _ = Real.exp (((kr ^ 16905 : ℕ) : ℝ) * 1) := (Real.exp_nat_mul 1 _).symm
          _ = Real.exp (((k * r : ℕ) : ℝ) ^ 16905) := by dsimp only [kr]; rw [mul_one, Nat.cast_pow]
      linarith
    obtain ⟨i, hiX⟩ := hex_i
    have hiL := hR.2.1 (s + 1) (Finset.mem_Icc.mpr ⟨by omega, hs1⟩) i
    have hiF := hR.2.2.1 (s + 1) (Finset.mem_range.mpr (by omega)) i
    have hA_ge_X : cosetDens ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i) X -
        cosetDens ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i) (X \ A) ≤
        cosetDens ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i) A := by
      unfold cosetDens
      rw [← sub_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have hsub : X ∩ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i) ⊆
          (A ∩ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i)) ∪
          ((X \ A) ∩ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i)) := by
        intro x hx
        obtain ⟨hxX, hxC⟩ := Finset.mem_inter.mp hx
        by_cases hxA : x ∈ A
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxA, hxC⟩)
        · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨hxX, hxA⟩, hxC⟩)
      have hnat : (X ∩ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i)).card ≤
          (A ∩ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i)).card +
          ((X \ A) ∩ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i)).card :=
        (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hR' : ((X ∩ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i)).card : ℝ) ≤
          ((A ∩ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i)).card : ℝ) +
          (((X \ A) ∩ coset ((2 : ℤ) ^ (s + 1) * z'' ω'') (Ztup ω'' i)).card : ℝ) := by exact_mod_cast hnat
      linarith
    have hF_lb := (abs_le.mp hiF).2
    change ν₀ / 2 ≤ mZ' (s + 1) ω''
    linarith

private lemma propG : PropGSpec := by
  classical
  refine ⟨580, 16905, 1104, 10, 552, 1108, ?_⟩
  intro k r η A X hk hr hη0 hη1 hAne hAX hXA hsum
  let kr : ℕ := k * r
  have hkr2 : 2 ≤ kr := by dsimp only [kr]; nlinarith
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkr2R : (2 : ℝ) ≤ (kr : ℝ) := by exact_mod_cast hkr2
  have hkr_pos : (0 : ℝ) < (kr : ℝ) := by positivity
  have hk_le_krR : (k : ℝ) ≤ (kr : ℝ) := by exact_mod_cast (show k ≤ kr by dsimp [kr]; exact Nat.le_mul_of_pos_right k hr)
  have hr1_le_krR : ((r + 1 : ℕ) : ℝ) ≤ (kr : ℝ) := by exact_mod_cast (show r + 1 ≤ kr by dsimp [kr]; nlinarith)
  have h2powK : ∀ n : ℕ, (2 : ℝ) ^ n ≤ (k : ℝ) ^ n := fun n => pow_le_pow_left₀ (by norm_num) hk2 n
  have h2powKR : ∀ n : ℕ, (2 : ℝ) ^ n ≤ (kr : ℝ) ^ n := fun n => pow_le_pow_left₀ (by norm_num) hkr2R n
  by_cases hη_big : 1 / η ≤ ((k * r : ℕ) : ℝ) ^ 580
  · exact Or.inl hη_big
  push Not at hη_big
  by_cases hA_small : (A.card : ℝ) ≤ Real.exp (((k * r : ℕ) : ℝ) ^ 16905)
  · exact Or.inr (Or.inl hA_small)
  push Not at hA_small
  right; right
  have hXle2A : (X.card : ℝ) ≤ 2 * (A.card : ℝ) := by
    have hcard : X.card = A.card + (X \ A).card := by
      have := Finset.card_sdiff_add_card_eq_card hAX; omega
    have hR : (X.card : ℝ) = (A.card : ℝ) + ((X \ A).card : ℝ) := by exact_mod_cast hcard
    nlinarith
  let ν₀ : ℝ := 1 / (k : ℝ) ^ 552
  let α₀ : ℝ := ν₀ / 2
  let δ₀ : ℝ := 1 / (kr : ℝ) ^ 2800
  let τ₀ : ℝ := 1 / (kr : ℝ) ^ 5620
  have hα₀_pos : 0 < α₀ := by dsimp only [α₀, ν₀]; positivity
  have hδ₀_pos : 0 < δ₀ := by dsimp only [δ₀]; positivity
  have hτ₀_pos : 0 < τ₀ := by dsimp only [τ₀]; positivity
  have hδ₀_le_half : δ₀ ≤ 1 / 2 := by
    dsimp only [δ₀]
    rw [one_div_le_one_div (by positivity) (by norm_num)]
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by ring
      _ ≤ (kr : ℝ) ^ 1 := h2powKR 1
      _ ≤ (kr : ℝ) ^ 2800 := pow_le_pow_right₀ (by linarith) (by omega)
  have hτ₀_le_half : τ₀ ≤ 1 / 2 := by
    dsimp only [τ₀]
    rw [one_div_le_one_div (by positivity) (by norm_num)]
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by ring
      _ ≤ (kr : ℝ) ^ 1 := h2powKR 1
      _ ≤ (kr : ℝ) ^ 5620 := pow_le_pow_right₀ (by linarith) (by omega)
  have hτ₀_le_δ₀ : τ₀ ≤ δ₀ := by
    dsimp only [τ₀, δ₀]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by linarith) (by omega))
  have hτ₀_small : 32768 * ((r + 1 : ℕ) : ℝ) * τ₀ ≤ δ₀ ^ 2 := by
    dsimp only [τ₀, δ₀]
    rw [one_div_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h32 : (32768 : ℝ) ≤ (kr : ℝ) ^ 15 := (by norm_num : (32768 : ℝ) = (2 : ℝ) ^ 15).le.trans (h2powKR 15)
    have heq : ((kr : ℝ) ^ 2800) ^ 2 = (kr : ℝ) ^ 5600 := by ring
    calc 32768 * ((r + 1 : ℕ) : ℝ) * ((kr : ℝ) ^ 2800) ^ 2
        ≤ (kr : ℝ) ^ 15 * (kr : ℝ) * (kr : ℝ) ^ 5600 := by rw [heq]; gcongr
      _ = (kr : ℝ) ^ 5616 := by ring
      _ ≤ 1 * (kr : ℝ) ^ 5620 := by rw [one_mul]; exact pow_le_pow_right₀ (by linarith) (by omega)
  obtain ⟨S, P0, z0, Z0, T0, hT0, d0, D0, hSne, hHE_S, hAS, hSA, hAS_inter, htv_P0_S, hd0_le, hD0_le,
    hZT0, hT0dim, hT0cov⟩ := lem_gs hk hAne hXle2A hsum hτ₀_pos hτ₀_le_half
  obtain ⟨P', z', Z', P'', proj, z'', Ztup, hpull, htv_P'_P0, htv_P''_P', hU1, hU2, hZcl, hZsub, hZcov⟩ :=
    cor_iju (A := A) hT0 hk hr hτ₀_pos hδ₀_pos hδ₀_le_half hτ₀_small hZT0 hT0dim hT0cov
  have hDfinal : ∀ ω'', covFlat (S : Set ℤ) ((Ztup ω'' ⟨k - 1, by omega⟩).set : Set ℤ) ≤
      ((2 ^ (kr ^ 16900) : ℕ) : ℕ∞) := fun ω'' =>
    (hZcov ω'').trans (ENat.natCast_le_natCast.mpr (Nat.pow_le_pow_right (by norm_num)
      (propG_Dfinal_bound hk hr hd0_le hD0_le)))
  have htv_P'_S : tvLe (fun x => P'.expect (fun ω' => unifMeas (coset (z' ω') (Z' ω')) x)) (unifMeas S) (δ₀ + τ₀) :=
    tvLe_trans htv_P'_P0 htv_P0_S
  have hER_lb := propG_goodR_expect hk hr hη0 hη_big hSne hAS hXA hAS_inter hpull htv_P'_S htv_P''_P' hU1 hU2
  have hind := propG_induct_dens (P' := P') (proj := proj) (z' := z') (Z' := Z') (z'' := z'')
    hk hr hA_small hsum hAS hZcl hZsub hDfinal
  refine ⟨S, hSne, hHE_S, hAS, hSA, ?_⟩
  intro j hj
  have hjr : j ≤ r := (Finset.mem_Icc.mp hj).2
  have htv_j := tvLe_pushScale2 j htv_P'_S
  have hev_j := tvLe_eval htv_j A
  let mZ' : ℕ → Fin P''.N → ℝ := fun s ω'' =>
    cosetDens ((2 : ℤ) ^ s * z' (proj ω'')) ((Z' (proj ω'')).scale2 s) A
  have hL_j : ∑ x ∈ A, pushScale2 j (fun u => P'.expect (fun ω' => unifMeas (coset (z' ω') (Z' ω')) u)) x =
      P''.expect (fun ω'' => mZ' j ω'') := by
    simp_rw [expect_pushScale2_coset]
    have h1 : ∑ x ∈ A, P'.expect (fun ω' => unifMeas (coset ((2 : ℤ) ^ j * z' ω') ((Z' ω').scale2 j)) x) =
        P'.expect (fun ω' => cosetDens ((2 : ℤ) ^ j * z' ω') ((Z' ω').scale2 j) A) := by
      unfold FinProb.expect; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ω' _ => by rw [← Finset.mul_sum, ← cosetDens_eq_sum]
    rw [h1]
    exact (hpull (fun ω' => cosetDens ((2 : ℤ) ^ j * z' ω') ((Z' ω').scale2 j) A)).symm
  rw [hL_j, sum_pushScale2_unifMeas] at hev_j
  have hEj_lb : ν₀ ^ 2 / 8 ≤ P''.expect (fun ω'' => mZ' j ω'') := by
    have hpt : ∀ ω'' : Fin P''.N,
        (if propG_goodR r A X proj z' Z' z'' Ztup ω'' then mZ' 0 ω'' else 0) * α₀ ≤ mZ' j ω'' := by
      intro ω''
      by_cases hR : propG_goodR r A X proj z' Z' z'' Ztup ω''
      · rw [if_pos hR]
        have h1 : mZ' 0 ω'' ≤ 1 := cosetDens_le_one _ _ _
        have h2 : α₀ ≤ mZ' j ω'' := hind ω'' hR j hjr
        nlinarith [cosetDens_nonneg ((2 : ℤ) ^ 0 * z' (proj ω'')) ((Z' (proj ω'')).scale2 0) A]
      · rw [if_neg hR, zero_mul]; exact cosetDens_nonneg _ _ _
    calc ν₀ ^ 2 / 8 = (ν₀ / 4) * α₀ := by dsimp only [α₀]; ring
      _ ≤ P''.expect (fun ω'' => if propG_goodR r A X proj z' Z' z'' Ztup ω'' then mZ' 0 ω'' else 0) * α₀ :=
          mul_le_mul_of_nonneg_right hER_lb hα₀_pos.le
      _ = P''.expect (fun ω'' => (if propG_goodR r A X proj z' Z' z'' Ztup ω'' then mZ' 0 ω'' else 0) * α₀) := by
          rw [mul_comm, ← P''.expect_mul_const]; congr 1; ext ω''; ring
      _ ≤ P''.expect (fun ω'' => mZ' j ω'') := P''.expect_mono hpt
  have hδτ_le : δ₀ + τ₀ ≤ ν₀ ^ 2 / 16 := by
    have h2δ : δ₀ + τ₀ ≤ 2 * δ₀ := by linarith
    refine h2δ.trans ?_
    dsimp only [δ₀, ν₀]
    have h32 : (32 : ℝ) ≤ (kr : ℝ) ^ 5 := (by norm_num : (32 : ℝ) = (2 : ℝ) ^ 5).le.trans (h2powKR 5)
    have hlhs : 2 * (1 / (kr : ℝ) ^ 2800) = 2 / (kr : ℝ) ^ 2800 := by ring
    have hrhs : (1 / (k : ℝ) ^ 552) ^ 2 / 16 = 1 / (16 * (k : ℝ) ^ 1104) := by field_simp
    rw [hlhs, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
    calc 2 * (16 * (k : ℝ) ^ 1104) = 32 * (k : ℝ) ^ 1104 := by ring
      _ ≤ (kr : ℝ) ^ 5 * (kr : ℝ) ^ 1104 := by gcongr
      _ = (kr : ℝ) ^ 1109 := by ring
      _ ≤ 1 * (kr : ℝ) ^ 2800 := by rw [one_mul]; exact pow_le_pow_right₀ (by linarith) (by omega)
  have hdens_lb : ν₀ ^ 2 / 16 ≤ ((scale2Finset j S ∩ A).card : ℝ) / (S.card : ℝ) := by
    linarith [(abs_le.mp hev_j).2]
  have hSpos : (0 : ℝ) < (S.card : ℝ) := Nat.cast_pos.mpr hSne.card_pos
  have h16k : 16 * (k : ℝ) ^ 1104 ≤ (k : ℝ) ^ 1108 := by
    have h16 : (16 : ℝ) ≤ (k : ℝ) ^ 4 := (by norm_num : (16 : ℝ) = (2 : ℝ) ^ 4).le.trans (h2powK 4)
    calc 16 * (k : ℝ) ^ 1104 ≤ (k : ℝ) ^ 4 * (k : ℝ) ^ 1104 := mul_le_mul_of_nonneg_right h16 (by positivity)
      _ = (k : ℝ) ^ 1108 := by ring
  have h1 : (S.card : ℝ) ≤ 16 * (k : ℝ) ^ 1104 * ((scale2Finset j S ∩ A).card : ℝ) := by
    have heq : ν₀ ^ 2 / 16 = 1 / (16 * (k : ℝ) ^ 1104) := by dsimp only [ν₀]; field_simp
    rw [heq, div_le_div_iff₀ (by positivity) hSpos] at hdens_lb
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_right h16k (Nat.cast_nonneg _))

end Erdos787Sanders

theorem OMA.solution : type_of% @Erdos787.erdos_787.variants.sanders :=
  Erdos787Sanders.sanders_of_prop27 (Erdos787Sanders.prop27_of_propG Erdos787Sanders.propG)
