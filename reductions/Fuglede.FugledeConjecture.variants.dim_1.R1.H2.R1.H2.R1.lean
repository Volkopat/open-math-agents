import OMAReductions.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H2_R1
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Fintype.BigOperators

/-!
Reduce cyclic universal spectra to prime-power Fourier zeros and their closure
under products of powers of distinct primes.
-/

-- Credit: @Alewawa

open Finset
open scoped BigOperators

namespace OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H2_R1_H2_R1

private lemma prime_power_data {n : ℕ} (hn : IsPrimePow n) :
    ∃ e : ℕ, 0 < e ∧ n.minFac.Prime ∧ n.minFac ^ e = n := by
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  exact ⟨e, he, by rwa [hp.pow_minFac he.ne'], by rw [hp.pow_minFac he.ne']⟩

private lemma sum_order_of_prime_powers {ι G : Type} [AddCommGroup G] [Finite G]
    (q : ι → ℕ) (v : ι → G) (s : Finset ι)
    (hpowers : ∀ i ∈ s, IsPrimePow (q i)) (hq : Set.InjOn q s)
    (horder : ∀ i ∈ s, addOrderOf (v i) = q i) :
    ∃ t ⊆ s, Set.InjOn (fun i => (q i).minFac) t ∧
      (s.Nonempty → t.Nonempty) ∧
      addOrderOf (∑ i ∈ s, v i) = ∏ i ∈ t, q i := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s.Nonempty
    swap
    · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      exact ⟨∅, by simp, by simp [Set.InjOn], by simp, by simp⟩
    obtain ⟨i, hi, hmax⟩ := s.exists_max_image q hs
    let p := (q i).minFac
    obtain ⟨e, he, hp, hqe⟩ := prime_power_data (hpowers i hi)
    change p.Prime at hp
    change p ^ e = q i at hqe
    let u := s.filter (fun j => (q j).minFac = p)
    let w := s.filter (fun j => (q j).minFac ≠ p)
    have hu : u ⊆ s := filter_subset _ _
    have hw : w ⊆ s := filter_subset _ _
    have hiu : i ∈ u := mem_filter.mpr ⟨hi, rfl⟩
    have hiw : i ∉ w := fun h => (mem_filter.mp h).2 rfl
    have hws : w ⊂ s := (ssubset_iff_of_subset hw).mpr ⟨i, hi, hiw⟩
    obtain ⟨t, ht, htinj, _, htorder⟩ := ih w hws
      (fun j hj => hpowers j (hw hj)) (hq.mono hw)
      (fun j hj => horder j (hw hj))
    have hordersmall : addOrderOf (∑ j ∈ u.erase i, v j) ∣ p ^ (e - 1) := by
      rw [addOrderOf_dvd_iff_nsmul_eq_zero, Finset.smul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      obtain ⟨hji, hju⟩ := mem_erase.mp hj
      have hjs := hu hju
      rw [← addOrderOf_dvd_iff_nsmul_eq_zero, horder j hjs]
      obtain ⟨d, _, _, hqd⟩ := prime_power_data (hpowers j hjs)
      have hjp : (q j).minFac = p := (mem_filter.mp hju).2
      rw [hjp] at hqd
      have hqji : q j < q i := lt_of_le_of_ne (hmax j hjs)
        (fun h => hji (hq hjs hi h))
      have hd : d < e := (Nat.pow_lt_pow_iff_right hp.one_lt).mp (by simpa [hqd, hqe] using hqji)
      rw [← hqd]
      exact Nat.pow_dvd_pow p (by omega)
    have huorder : addOrderOf (∑ j ∈ u, v j) = q i := by
      rw [← Finset.sum_erase_add u v hiu, ← horder i hi]
      apply (AddCommute.all _ _).addOrderOf_add_eq_right_of_forall_prime_mul_dvd
        (isOfFinAddOrder_of_finite _)
      intro r hr hrd
      have hrp : r = p :=
        (hp.eq_one_or_self_of_dvd _ (hr.dvd_of_dvd_pow (hrd.trans hordersmall))).resolve_left hr.ne_one
      have hqeq : p * p ^ (e - 1) = q i := by
        rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ e by omega), hqe]
      rw [hrp, horder i hi, ← hqeq]
      exact Nat.mul_dvd_mul_left _ hordersmall
    have hco : (q i).Coprime (∏ j ∈ t, q j) := by
      rw [Nat.coprime_prod_right_iff]
      intro j hj
      obtain ⟨d, _, hpj, hqd⟩ := prime_power_data (hpowers j (hw (ht hj)))
      have hne := (mem_filter.mp (ht hj)).2
      rw [← hqe, ← hqd]
      apply Nat.Coprime.pow
      apply hp.coprime_iff_not_dvd.mpr
      intro h
      exact hne ((hpj.eq_one_or_self_of_dvd _ h).resolve_left hp.ne_one).symm
    have hit : i ∉ t := fun h => hiw (ht h)
    refine ⟨insert i t, ?_, ?_, fun _ => ⟨i, mem_insert_self _ _⟩, ?_⟩
    · intro j hj
      rcases mem_insert.mp hj with rfl | h
      · exact hi
      · exact hw (ht h)
    · intro j hj k hk h
      rcases mem_insert.mp hj with rfl | hjt
      · rcases mem_insert.mp hk with rfl | hkt
        · rfl
        · exact ((mem_filter.mp (ht hkt)).2 h.symm).elim
      · rcases mem_insert.mp hk with rfl | hkt
        · exact ((mem_filter.mp (ht hjt)).2 h).elim
        · exact htinj hjt hkt h
    · have hsums : (∑ j ∈ u, v j) + (∑ j ∈ w, v j) = ∑ j ∈ s, v j :=
        sum_filter_add_sum_filter_not _ (fun j => (q j).minFac = p) _
      rw [← hsums, (AddCommute.all _ _).addOrderOf_add_eq_mul_addOrderOf_of_coprime
        (by rw [huorder, htorder]; exact hco), huorder, htorder, prod_insert hit]

private lemma digit_difference_order {G : Type} [AddCommGroup G] [Finite G]
    {x : G} {s : ℕ} (hs : IsPrimePow s) (hx : addOrderOf x = s)
    (a b : Fin s.minFac) (hab : a ≠ b) :
    addOrderOf (a.val • x - b.val • x) = s := by
  obtain ⟨e, _, hp, he⟩ := prime_power_data hs
  wlog hle : b.val ≤ a.val generalizing a b with H
  · rw [← addOrderOf_neg, neg_sub]
    exact H b a hab.symm (by omega)
  have hlt : b.val < a.val := lt_of_le_of_ne hle (fun h => hab (Fin.ext h.symm))
  have hdiff : 0 < a.val - b.val := Nat.sub_pos_of_lt hlt
  have hsmall : a.val - b.val < s.minFac := (Nat.sub_le ..).trans_lt a.isLt
  have hco : s.Coprime (a.val - b.val) := by
    have hc := ((hp.coprime_iff_not_dvd).mpr
      (fun h => (not_le_of_gt hsmall) (Nat.le_of_dvd hdiff h))).pow_left e
    exact (congrArg (fun n => n.Coprime (a.val - b.val)) he).mp hc
  have hd : a.val • x - b.val • x = (a.val - b.val) • x := by
    apply (sub_eq_iff_eq_add).2
    rw [← add_nsmul, Nat.sub_add_cancel hle]
  rw [hd, addOrderOf_nsmul, hx, show s.gcd (a.val - b.val) = 1 from hco, Nat.div_one]

private lemma prime_power_digit_spectrum {L : ℕ} [NeZero L] (S : Finset ℕ)
    (hpow : ∀ s ∈ S, IsPrimePow s) (hdvd : ∀ s ∈ S, s ∣ L) :
    ∃ Γ : Finset (ZMod L), 0 ∈ Γ ∧ Γ.card = ∏ s ∈ S, s.minFac ∧
      ∀ g ∈ Γ, ∀ j ∈ Γ, g ≠ j →
        ∃ T ⊆ S, T.Nonempty ∧ Set.InjOn Nat.minFac T ∧
          addOrderOf (g - j) = ∏ s ∈ T, s := by
  classical
  let x (s : S) : ZMod L := (L / s.val : ℕ)
  have hx (s : S) : addOrderOf (x s) = s.val := by
    have h := hdvd s s.prop
    simp only [x, ZMod.addOrderOf_coe _ (NeZero.ne L),
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd h), Nat.div_div_self h (NeZero.ne L)]
  let freq (a : (s : S) → Fin s.val.minFac) : ZMod L := ∑ s, (a s).val • x s
  have hdiff (a b : (s : S) → Fin s.val.minFac) (hab : a ≠ b) :
      ∃ T ⊆ S, T.Nonempty ∧ Set.InjOn Nat.minFac T ∧
        addOrderOf (freq a - freq b) = ∏ s ∈ T, s := by
    let D : Finset S := univ.filter (fun s => a s ≠ b s)
    let v (s : S) := (a s).val • x s - (b s).val • x s
    have hD : D.Nonempty := by
      by_contra h
      apply hab
      funext s
      by_contra hne
      exact h ⟨s, mem_filter.mpr ⟨mem_univ _, hne⟩⟩
    have heq : freq a - freq b = ∑ s ∈ D, v s := by
      rw [show freq a - freq b = ∑ s : S, v s by exact (sum_sub_distrib ..).symm]
      symm
      apply sum_subset (filter_subset _ _)
      intro s _ hs
      simp [v] at hs ⊢
      rw [hs, sub_self]
    obtain ⟨t, _, htinj, htne, htorder⟩ :=
      sum_order_of_prime_powers (fun s : S => s.val) v D
        (fun s _ => hpow s s.prop) Subtype.val_injective.injOn
        (fun s hs => digit_difference_order (hpow s s.prop) (hx s) _ _ (mem_filter.mp hs).2)
    refine ⟨t.image Subtype.val, ?_, (htne hD).image _, ?_, ?_⟩
    · intro s hs
      obtain ⟨u, _, rfl⟩ := mem_image.mp hs
      exact u.prop
    · intro s hs j hj h
      obtain ⟨u, hu, rfl⟩ := mem_image.mp hs
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hj
      exact congrArg Subtype.val (htinj hu hw h)
    · rw [heq, htorder, prod_image Subtype.val_injective.injOn]
  have hf : Function.Injective freq := by
    intro a b hh
    by_contra hab
    obtain ⟨T, ht, hne, _, h⟩ := hdiff a b hab
    rw [hh, sub_self, addOrderOf_zero] at h
    obtain ⟨s, hs⟩ := hne
    have hsdiv : s ∣ ∏ t ∈ T, t := Finset.dvd_prod_of_mem id hs
    rw [← h] at hsdiv
    exact (hpow s (ht hs)).one_lt.ne' (Nat.dvd_one.mp hsdiv)
  let (s : S) : NeZero s.val.minFac :=
    ⟨(prime_power_data (hpow s s.prop)).choose_spec.2.1.ne_zero⟩
  refine ⟨univ.image freq, ?_, ?_, ?_⟩
  · exact mem_image.mpr ⟨fun _ => 0, mem_univ _, by simp [freq]⟩
  · simp only [card_image_of_injective _ hf, card_univ, Fintype.card_pi, Fintype.card_fin]
    exact (Finset.prod_subtype S (fun _ => Iff.rfl) Nat.minFac).symm
  · intro g hg j hj hgj
    obtain ⟨a, _, rfl⟩ := mem_image.mp hg
    obtain ⟨b, _, rfl⟩ := mem_image.mp hj
    exact hdiff a b (fun h => hgj (congrArg freq h))

/-- The complements of a fixed tile share their prime-power vanishing orders,
whose underlying primes multiply to the complement cardinality. -/
def H1 : Prop :=
  ∀ (L : ℕ) [NeZero L], L % 2 = 0 →
    ∀ (χ : AddChar (ZMod L) ℂ), (∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) →
    ∀ (A : Finset (ZMod L)) (ℬ : Finset (Finset (ZMod L))), 3 ≤ A.card →
      (∀ B ∈ ℬ, 4 ≤ B.card ∧ ∀ z : ZMod L,
        ∃! p : A × B, p.1.1 + p.2.1 = z) →
      ∃ S : Finset ℕ, (∀ s ∈ S, IsPrimePow s ∧ s ∣ L) ∧
        (∀ B ∈ ℬ, B.card = ∏ s ∈ S, s.minFac) ∧
        (∀ B ∈ ℬ, ∀ k : ZMod L, addOrderOf k ∈ S → ∑ b ∈ B, χ (k * b) = 0)

/-- The mixed-prime part of the Coven–Meyerowitz condition for a single
complement. Vanishing at selected prime-power orders forces vanishing at
the product order when the primes are distinct. -/
def H2 : Prop :=
  ∀ (L : ℕ) [NeZero L], L % 2 = 0 →
    ∀ (χ : AddChar (ZMod L) ℂ), (∀ z : ℤ, χ (z : ZMod L) =
      Complex.exp (2 * Real.pi * Complex.I * (z : ℂ) / (L : ℂ))) →
    ∀ (A B : Finset (ZMod L)), 3 ≤ A.card → 4 ≤ B.card →
      (∀ z : ZMod L, ∃! p : A × B, p.1.1 + p.2.1 = z) →
      ∀ T : Finset ℕ, 2 ≤ T.card →
        (∀ s ∈ T, IsPrimePow s ∧ s ∣ L) → Set.InjOn Nat.minFac T →
        (∀ k : ZMod L, addOrderOf k ∈ T → ∑ b ∈ B, χ (k * b) = 0) →
        ∀ k : ZMod L, addOrderOf k = (∏ s ∈ T, s) → ∑ b ∈ B, χ (k * b) = 0

theorem main : H1 → H2 → OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H2_R1.H2 := by
  intro h1 h2 L _ heven χ hχ A ℬ hA htiling
  obtain ⟨S, hS, hcard, hzero⟩ := h1 L heven χ hχ A ℬ hA htiling
  obtain ⟨Γ, hΓ, hΓcard, hdiff⟩ := prime_power_digit_spectrum S
    (fun s hs => (hS s hs).1) (fun s hs => (hS s hs).2)
  refine ⟨Γ, hΓ, fun B hB => hΓcard.trans (hcard B hB).symm, ?_⟩
  intro B hB g hg j hj hne
  obtain ⟨T, hTS, hT, hTin, horder⟩ := hdiff g hg j hj hne
  by_cases ht : 2 ≤ T.card
  · exact h2 L heven χ hχ A B hA (htiling B hB).1 (htiling B hB).2 T ht
      (fun s hs => hS s (hTS hs)) hTin (fun k hk => hzero B hB k (hTS hk)) (g - j) horder
  · have hpos := Finset.card_pos.mpr hT
    obtain ⟨s, rfl⟩ := Finset.card_eq_one.mp (show T.card = 1 by omega)
    exact hzero B hB (g - j) (hTS (by simp [horder]))

end OMA.R_Fuglede_FugledeConjecture_variants_dim_1_R1_H2_R1_H2_R1
