import OMAStatements.S_mo_101886
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Order.Lattice.Nat

/-
The averaging lower bound is due to Sam Hopkins in the source question.
The matching upper bound uses a half-sized subfamily of the star at a fixed point.
Every image lies in another star, so two-star counting gives the required limit.
-/

namespace OMA.S_mo_101886

/-- The symmetric group acts transitively on each layer of the Boolean lattice. -/
theorem same_card_perm {n : ℕ} (s t : Finset (Fin n)) (h : s.card = t.card) :
    ∃ p : Equiv.Perm (Fin n), s.image p = t := by
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_map_finset_eq s t h
  exact ⟨p, by simpa only [Finset.map_eq_image, Equiv.coe_toEmbedding] using hp⟩

end OMA.S_mo_101886

namespace MO101886LowerCore

open Finset OMA.S_mo_101886

lemma family_image_comp {n : ℕ} (F : Finset (Finset (Fin n)))
    (p q : Equiv.Perm (Fin n)) :
    F.image (fun s => s.image (q * p)) =
      (F.image (fun s => s.image p)).image (fun s => s.image q) := by
  simp only [image_image]
  congr 1
  funext s
  simp only [image_image, Equiv.Perm.coe_mul, Function.comp_def]

lemma image_family_mem {n : ℕ} (F : Finset (Finset (Fin n)))
    (s : Finset (Fin n)) (p q : Equiv.Perm (Fin n)) :
    s.image q ∈ F.image (fun t => t.image (q * p)) ↔
      s ∈ F.image (fun t => t.image p) := by
  rw [family_image_comp]
  constructor
  · intro h
    obtain ⟨t, ht, heq⟩ := mem_image.mp h
    have heq' : t = s := image_injective q.injective heq
    exact heq' ▸ ht
  · intro hs
    exact mem_image_of_mem (fun t : Finset (Fin n) => t.image q) hs

noncomputable def hits {n : ℕ} (F : Finset (Finset (Fin n)))
    (s : Finset (Fin n)) : ℕ :=
  ∑ p : Equiv.Perm (Fin n), if s ∈ F.image (fun t => t.image p) then 1 else 0

lemma hits_image {n : ℕ} (F : Finset (Finset (Fin n)))
    (s : Finset (Fin n)) (q : Equiv.Perm (Fin n)) :
    hits F (s.image q) = hits F s := by
  classical
  unfold hits
  symm
  apply Fintype.sum_equiv (Equiv.mulLeft q)
  intro p
  change (if s ∈ F.image (fun t => t.image p) then 1 else 0) =
    (if s.image q ∈ F.image (fun t => t.image (q * p)) then 1 else 0)
  simp only [image_family_mem]

lemma hits_same {n : ℕ} (F : Finset (Finset (Fin n)))
    (s t : Finset (Fin n)) (h : s.card = t.card) : hits F s = hits F t := by
  obtain ⟨q, rfl⟩ := same_card_perm s t h
  exact (hits_image F s q).symm

lemma image_family_subset {n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : F ⊆ middleLayer n) (p : Equiv.Perm (Fin n)) :
    F.image (fun s => s.image p) ⊆ middleLayer n := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
  apply mem_powersetCard.mpr
  refine ⟨subset_univ _, ?_⟩
  rw [card_image_of_injective _ p.injective]
  exact (mem_powersetCard.mp (hF hs)).2

lemma sum_hits_layer {n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : F ⊆ middleLayer n) :
    ∑ s ∈ middleLayer n, hits F s = Fintype.card (Equiv.Perm (Fin n)) * F.card := by
  classical
  unfold hits
  rw [sum_comm]
  have hcard (p : Equiv.Perm (Fin n)) :
      ∑ s ∈ middleLayer n, (if s ∈ F.image (fun t => t.image p) then 1 else 0) = F.card := by
    rw [← card_filter]
    have heq : (middleLayer n).filter (fun s => s ∈ F.image (fun t => t.image p)) =
        F.image (fun t => t.image p) := by
      ext s
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun hs => image_family_subset F hF p hs)
    rw [heq, card_image_of_injective _ (image_injective p.injective)]
  simp_rw [hcard]
  simp

lemma sum_hits_inter {n : ℕ} (F : Finset (Finset (Fin n))) :
    ∑ s ∈ F, hits F s =
      ∑ p : Equiv.Perm (Fin n), (F ∩ F.image (fun s => s.image p)).card := by
  classical
  unfold hits
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [← card_filter, filter_mem_eq_inter]

theorem family_bound {n : ℕ} (F : Finset (Finset (Fin n)))
    (hF : F ⊆ middleLayer n) :
    2 * (middleLayer n).card * F.card ≤
      (middleLayer n).card * largestUnion F + F.card ^ 2 := by
  classical
  by_cases hne : F.Nonempty
  · obtain ⟨s₀, hs₀⟩ := hne
    have hconst : ∀ s ∈ middleLayer n, hits F s = hits F s₀ := by
      intro s hs
      apply hits_same
      exact (mem_powersetCard.mp hs).2.trans (mem_powersetCard.mp (hF hs₀)).2.symm
    have htotal : (middleLayer n).card * hits F s₀ =
        Fintype.card (Equiv.Perm (Fin n)) * F.card := by
      rw [← sum_const_nat hconst]
      exact sum_hits_layer F hF
    have hinter : (∑ p : Equiv.Perm (Fin n), (F ∩ F.image (fun s => s.image p)).card) =
        F.card * hits F s₀ := by
      rw [← sum_hits_inter]
      exact sum_const_nat (fun s hs => hconst s (hF hs))
    have hpoint (p : Equiv.Perm (Fin n)) :
        2 * F.card ≤ largestUnion F + (F ∩ F.image (fun s => s.image p)).card := by
      have hcard := card_union_add_card_inter F (F.image (fun s => s.image p))
      rw [card_image_of_injective _ (image_injective p.injective)] at hcard
      have hmax : (F ∪ F.image (fun s => s.image p)).card ≤ largestUnion F :=
        le_sup (f := fun q : Equiv.Perm (Fin n) => (F ∪ F.image (fun s => s.image q)).card)
          (mem_univ p)
      omega
    have hsum := sum_le_sum (fun p (_ : p ∈ (univ : Finset (Equiv.Perm (Fin n)))) => hpoint p)
    simp only [sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul, hinter] at hsum
    have hscaled : Fintype.card (Equiv.Perm (Fin n)) * (2 * (middleLayer n).card * F.card) ≤
        Fintype.card (Equiv.Perm (Fin n)) *
          ((middleLayer n).card * largestUnion F + F.card ^ 2) := by
      calc
        _ = (middleLayer n).card * (Fintype.card (Equiv.Perm (Fin n)) * (2 * F.card)) := by ring
        _ ≤ (middleLayer n).card *
          (Fintype.card (Equiv.Perm (Fin n)) * largestUnion F + F.card * hits F s₀) :=
            Nat.mul_le_mul_left _ hsum
        _ = (middleLayer n).card * Fintype.card (Equiv.Perm (Fin n)) * largestUnion F +
          F.card * ((middleLayer n).card * hits F s₀) := by ring
        _ = _ := by rw [htotal]; ring
    exact Nat.le_of_mul_le_mul_left hscaled (Fintype.card_pos)
  · have hzero : F = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [hzero]

end MO101886LowerCore

namespace MO101886Upper

open Finset OMA.S_mo_101886

def star (n : ℕ) (a : Fin n) : Finset (Finset (Fin n)) :=
  (middleLayer n).filter (fun s => a ∈ s)

lemma card_star {n : ℕ} (hn : 1 ≤ n) (a : Fin n) :
    (star n a).card = (n - 1).choose ((n + 1) / 2 - 1) := by
  have h := card_filter_powersetCard_subset ({a} : Finset (Fin n))
    univ ((n + 1) / 2) (subset_univ _) (by simp; omega)
  simpa only [card_singleton, card_univ, Fintype.card_fin, singleton_subset_iff,
    star, middleLayer] using h

lemma card_star_inter {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) (hab : a ≠ b) :
    (star n a ∩ star n b).card = (n - 2).choose ((n + 1) / 2 - 2) := by
  have heq : star n a ∩ star n b =
      (middleLayer n).filter (fun s => ({a, b} : Finset (Fin n)) ⊆ s) := by
    ext s
    simp only [star, mem_inter, mem_filter, insert_subset_iff, singleton_subset_iff]
    tauto
  rw [heq]
  have h := card_filter_powersetCard_subset ({a, b} : Finset (Fin n))
    univ ((n + 1) / 2) (subset_univ _) (by simp [hab]; omega)
  simpa only [card_pair hab, card_univ, Fintype.card_fin, middleLayer] using h

lemma card_star_inter_ge {n : ℕ} (hn : 3 ≤ n) (a b : Fin n) :
    (n - 2).choose ((n + 1) / 2 - 2) ≤ (star n a ∩ star n b).card := by
  by_cases hab : a = b
  · subst b
    rw [inter_self, card_star (by omega)]
    have h := Nat.choose_succ_succ' (n - 2) ((n + 1) / 2 - 2)
    have hn' : n - 2 + 1 = n - 1 := by omega
    have hr' : (n + 1) / 2 - 2 + 1 = (n + 1) / 2 - 1 := by omega
    rw [hn', hr'] at h
    omega
  · exact (card_star_inter hn a b hab).ge

lemma half_layer_le_star {n : ℕ} (hn : 1 ≤ n) (a : Fin n) :
    (middleLayer n).card / 2 ≤ (star n a).card := by
  rw [card_star hn, middleLayer, card_powersetCard, card_univ, Fintype.card_fin]
  have h := Nat.choose_succ_left (n - 1) ((n + 1) / 2) (by omega)
  have hn' : n - 1 + 1 = n := by omega
  rw [hn'] at h
  have hr' : (n - 1) / 2 = (n + 1) / 2 - 1 := by omega
  have hm := Nat.choose_le_middle ((n + 1) / 2) (n - 1)
  rw [hr'] at hm
  omega

lemma image_subset_star {n : ℕ} {a : Fin n} {F : Finset (Finset (Fin n))}
    (hF : F ⊆ star n a) (p : Equiv.Perm (Fin n)) :
    F.image (fun s => s.image p) ⊆ star n (p a) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := mem_image.mp ht
  have hsa := mem_filter.mp (hF hs)
  apply mem_filter.mpr
  refine ⟨?_, mem_image_of_mem p hsa.2⟩
  rw [middleLayer, mem_powersetCard]
  refine ⟨subset_univ _, ?_⟩
  rw [card_image_of_injective _ p.injective]
  exact (mem_powersetCard.mp hsa.1).2

lemma union_bound {n : ℕ} (hn : 3 ≤ n) {a : Fin n}
    {F : Finset (Finset (Fin n))} (hF : F ⊆ star n a)
    (p : Equiv.Perm (Fin n)) :
    (F ∪ F.image (fun s => s.image p)).card +
      (n - 2).choose ((n + 1) / 2 - 2) ≤
      2 * (n - 1).choose ((n + 1) / 2 - 1) := by
  have hc := card_le_card (union_subset_union hF (image_subset_star hF p))
  have hi := card_star_inter_ge hn a (p a)
  have hu := card_union_add_card_inter (star n a) (star n (p a))
  rw [card_star (by omega), card_star (by omega)] at hu
  omega

lemma largestUnion_bound {n : ℕ} (hn : 3 ≤ n) {a : Fin n}
    {F : Finset (Finset (Fin n))} (hF : F ⊆ star n a) :
    largestUnion F + (n - 2).choose ((n + 1) / 2 - 2) ≤
      2 * (n - 1).choose ((n + 1) / 2 - 1) := by
  obtain ⟨p, _, hp⟩ := exists_mem_eq_sup (univ : Finset (Equiv.Perm (Fin n)))
    univ_nonempty (fun p => (F ∪ F.image (fun s => s.image p)).card)
  change (univ.sup (fun p : Equiv.Perm (Fin n) =>
    (F ∪ F.image (fun s => s.image p)).card)) + _ ≤ _
  rw [hp]
  exact union_bound hn hF p

theorem upper_bound (n : ℕ) (hn : 3 ≤ n) :
    minMaxUnion n ((middleLayer n).card / 2) +
      (n - 2).choose ((n + 1) / 2 - 2) ≤
      2 * (n - 1).choose ((n + 1) / 2 - 1) := by
  let a : Fin n := ⟨0, by omega⟩
  obtain ⟨F, hF, hcard⟩ := exists_subset_card_eq (half_layer_le_star (by omega) a)
  have hFm : F ⊆ middleLayer n := hF.trans (filter_subset _ _)
  have hmem : F ∈ (middleLayer n).powersetCard ((middleLayer n).card / 2) :=
    mem_powersetCard.mpr ⟨hFm, hcard⟩
  have hmin : minMaxUnion n ((middleLayer n).card / 2) ≤ largestUnion F :=
    Nat.sInf_le ⟨F, hmem, rfl⟩
  exact (Nat.add_le_add_right hmin _).trans (largestUnion_bound hn hF)

end MO101886Upper

open Filter
open scoped Topology

namespace MO101886Asymptotic

def rank (n : ℕ) : ℕ := (n + 1) / 2
def layer (n : ℕ) : ℕ := n.choose (rank n)
def star (n : ℕ) : ℕ := (n - 1).choose (rank n - 1)
def doubleStar (n : ℕ) : ℕ := (n - 2).choose (rank n - 2)

lemma rank_le (n : ℕ) : rank n ≤ n := by unfold rank; omega

lemma layer_ge (n : ℕ) : n ≤ layer n := by
  have h := Nat.choose_le_middle 1 n
  have heq : n - rank n = n / 2 := by unfold rank; omega
  simpa only [Nat.choose_one_right, layer, ← heq, Nat.choose_symm (rank_le n)] using h

lemma layer_pos {n : ℕ} (hn : 0 < n) : 0 < layer n := hn.trans_le (layer_ge n)

lemma half_ratio_tendsto (m : ℕ → ℕ) (hm : ∀ n, n ≤ m n) :
    Tendsto (fun n : ℕ => ((m n / 2 : ℕ) : ℝ) / (m n : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlo : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) - 1 / n ≤ ((m n / 2 : ℕ) : ℝ) / (m n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hmge : (n : ℝ) ≤ m n := by exact_mod_cast hm n
    have hmpos : (0 : ℝ) < m n := hnpos.trans_le hmge
    have hfloor : (m n : ℝ) ≤ 2 * ((m n / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast (show m n ≤ 2 * (m n / 2) + 1 by omega)
    have hlow : (1 / 2 : ℝ) - 1 / (m n : ℝ) ≤
        ((m n / 2 : ℕ) : ℝ) / (m n : ℝ) := by
      apply (le_div_iff₀ hmpos).mpr
      rw [sub_mul, div_mul_cancel₀ _ hmpos.ne']
      linarith
    have hinv := one_div_le_one_div_of_le hnpos hmge
    linarith
  have hhi : ∀ᶠ n : ℕ in atTop,
      ((m n / 2 : ℕ) : ℝ) / (m n : ℝ) ≤ (1 / 2 : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hmpos : (0 : ℝ) < m n := by
      exact_mod_cast (show 0 < m n from (show 0 < n by omega).trans_le (hm n))
    apply (div_le_iff₀ hmpos).mpr
    have hfloor : 2 * ((m n / 2 : ℕ) : ℝ) ≤ (m n : ℝ) := by
      exact_mod_cast (show 2 * (m n / 2) ≤ m n by omega)
    linarith
  have hlowlim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) - 1 / n) atTop
      (𝓝 (1 / 2 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact hlowlim.squeeze' tendsto_const_nhds hlo hhi

lemma rank_ratio_tendsto :
    Tendsto (fun n : ℕ => (rank n : ℝ) / (n : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlo : ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ (rank n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (le_div_iff₀ hnpos).mpr
    have hr : (n : ℝ) ≤ 2 * (rank n : ℝ) := by
      exact_mod_cast (show n ≤ 2 * rank n by unfold rank; omega)
    linarith
  have hhi : ∀ᶠ n : ℕ in atTop,
      (rank n : ℝ) / (n : ℝ) ≤ (1 / 2 : ℝ) + 1 / n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (div_le_iff₀ hnpos).mpr
    rw [add_mul, div_mul_cancel₀ _ hnpos.ne']
    have hr : 2 * (rank n : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast (show 2 * rank n ≤ n + 1 by unfold rank; omega)
    linarith
  have huplim : Tendsto (fun n : ℕ => (1 / 2 : ℝ) + 1 / n) atTop
      (𝓝 (1 / 2 : ℝ)) := by
    simpa using (tendsto_const_nhds (x := (1 / 2 : ℝ))).add
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_const_nhds.squeeze' huplim hlo hhi

lemma rank_prev_ratio_tendsto :
    Tendsto (fun n : ℕ => ((rank n : ℝ) - 1) / ((n : ℝ) - 1)) atTop
      (𝓝 (1 / 2 : ℝ)) := by
  have h := (rank_ratio_tendsto.sub
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).div
    ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))) (by norm_num)
  have hlim : Tendsto (fun n : ℕ =>
      ((rank n : ℝ) / n - 1 / n) / (1 - 1 / (n : ℝ))) atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa only [Pi.div_apply, sub_zero, div_one] using! h
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnpos : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  field_simp

lemma star_identity {n : ℕ} (hn : 3 ≤ n) : layer n * rank n = n * star n := by
  have hr : 1 ≤ rank n := by unfold rank; omega
  simpa [layer, star, Nat.choose_one_right] using
    (Nat.choose_mul (n := n) (k := rank n) (s := 1) hr)

lemma double_star_identity {n : ℕ} (hn : 3 ≤ n) :
    star n * (rank n - 1) = (n - 1) * doubleStar n := by
  have hr : 1 ≤ rank n - 1 := by unfold rank; omega
  simpa [star, doubleStar, Nat.choose_one_right, Nat.sub_sub] using
    (Nat.choose_mul (n := n - 1) (k := rank n - 1) (s := 1) hr)

lemma star_ratio {n : ℕ} (hn : 3 ≤ n) :
    (star n : ℝ) / (layer n : ℝ) = (rank n : ℝ) / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hmpos : (0 : ℝ) < layer n := by exact_mod_cast layer_pos (show 0 < n by omega)
  apply (div_eq_div_iff hmpos.ne' hnpos.ne').mpr
  have h : (layer n : ℝ) * (rank n : ℝ) = (n : ℝ) * (star n : ℝ) := by
    exact_mod_cast star_identity hn
  nlinarith [h]

lemma double_star_ratio {n : ℕ} (hn : 3 ≤ n) :
    (doubleStar n : ℝ) / (layer n : ℝ) =
      ((star n : ℝ) / (layer n : ℝ)) * (((rank n : ℝ) - 1) / ((n : ℝ) - 1)) := by
  have hnpos : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hmpos : (0 : ℝ) < layer n := by exact_mod_cast layer_pos (show 0 < n by omega)
  have hr : 1 ≤ rank n := by unfold rank; omega
  have h : (star n : ℝ) * ((rank n : ℝ) - 1) =
      ((n : ℝ) - 1) * (doubleStar n : ℝ) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (double_star_identity hn)
    simpa only [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_sub (show 1 ≤ n by omega),
      Nat.cast_one] using h
  field_simp
  nlinarith [h]

lemma star_ratio_tendsto :
    Tendsto (fun n : ℕ => (star n : ℝ) / (layer n : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := by
  apply rank_ratio_tendsto.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (star_ratio hn).symm

lemma double_star_ratio_tendsto :
    Tendsto (fun n : ℕ => (doubleStar n : ℝ) / (layer n : ℝ)) atTop (𝓝 (1 / 4 : ℝ)) := by
  have h := star_ratio_tendsto.mul rank_prev_ratio_tendsto
  have hlim : Tendsto (fun n : ℕ => ((star n : ℝ) / (layer n : ℝ)) *
      (((rank n : ℝ) - 1) / ((n : ℝ) - 1))) atTop (𝓝 (1 / 4 : ℝ)) := by
    convert h using 1; norm_num
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  exact (double_star_ratio hn).symm

theorem squeeze_minimax (u : ℕ → ℕ)
    (hlo : ∀ n : ℕ, 3 ≤ n →
      2 * layer n * (layer n / 2) ≤ layer n * u n + (layer n / 2) ^ 2)
    (hhi : ∀ n : ℕ, 3 ≤ n → u n + doubleStar n ≤ 2 * star n) :
    Tendsto (fun n : ℕ => (u n : ℝ) / (layer n : ℝ)) atTop (𝓝 (3 / 4 : ℝ)) := by
  let q : ℕ → ℝ := fun n => ((layer n / 2 : ℕ) : ℝ) / (layer n : ℝ)
  have hq : Tendsto q atTop (𝓝 (1 / 2 : ℝ)) := half_ratio_tendsto layer layer_ge
  have hlow : Tendsto (fun n : ℕ => 2 * q n - (q n) ^ 2) atTop (𝓝 (3 / 4 : ℝ)) := by
    have h := (hq.const_mul 2).sub (hq.pow 2)
    convert h using 1; norm_num
  have hupp : Tendsto (fun n : ℕ =>
      2 * ((star n : ℝ) / (layer n : ℝ)) - (doubleStar n : ℝ) / (layer n : ℝ))
      atTop (𝓝 (3 / 4 : ℝ)) := by
    have h := (star_ratio_tendsto.const_mul 2).sub double_star_ratio_tendsto
    convert h using 1; norm_num
  apply hlow.squeeze' hupp
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hmpos : (0 : ℝ) < layer n := by exact_mod_cast layer_pos (show 0 < n by omega)
    have h : 2 * (layer n : ℝ) * ((layer n / 2 : ℕ) : ℝ) ≤
        (layer n : ℝ) * (u n : ℝ) + ((layer n / 2 : ℕ) : ℝ) ^ 2 := by
      exact_mod_cast hlo n hn
    dsimp only [q]
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hmpos)).mp
    field_simp
    nlinarith [h]
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hmpos : (0 : ℝ) < layer n := by exact_mod_cast layer_pos (show 0 < n by omega)
    have h : (u n : ℝ) + (doubleStar n : ℝ) ≤ 2 * (star n : ℝ) := by
      exact_mod_cast hhi n hn
    apply (mul_le_mul_iff_right₀ hmpos).mp
    field_simp
    linarith

end MO101886Asymptotic

open Finset OMA.S_mo_101886 Filter
open scoped Topology

namespace MO101886FinishLower

theorem lower_bound (n : ℕ) :
    2 * (middleLayer n).card * ((middleLayer n).card / 2) ≤
      (middleLayer n).card * minMaxUnion n ((middleLayer n).card / 2) +
        ((middleLayer n).card / 2) ^ 2 := by
  classical
  have hne : {v : ℕ | ∃ F ∈ (middleLayer n).powersetCard ((middleLayer n).card / 2),
      v = largestUnion F}.Nonempty := by
    obtain ⟨F, hF⟩ := powersetCard_nonempty.mpr (Nat.div_le_self (middleLayer n).card 2)
    exact ⟨largestUnion F, F, hF, rfl⟩
  obtain ⟨F, hF, hmin⟩ := Nat.sInf_mem hne
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hF
  have h := MO101886LowerCore.family_bound F hsub
  rw [hcard, ← hmin] at h
  exact h

theorem solution :
    Tendsto (fun n : ℕ =>
      (minMaxUnion n ((middleLayer n).card / 2) : ℝ) /
        ((middleLayer n).card : ℝ)) atTop (𝓝 (3 / 4 : ℝ)) := by
  have hcard (n : ℕ) : (middleLayer n).card = MO101886Asymptotic.layer n := by
    simp [middleLayer, MO101886Asymptotic.layer, MO101886Asymptotic.rank]
  have h := MO101886Asymptotic.squeeze_minimax
    (fun n => minMaxUnion n ((middleLayer n).card / 2))
    (fun n _ => by simpa only [← hcard n] using lower_bound n)
    (fun n hn => by
      simpa only [MO101886Asymptotic.doubleStar, MO101886Asymptotic.star,
        MO101886Asymptotic.rank] using MO101886Upper.upper_bound n hn)
  simpa only [← hcard] using h

end MO101886FinishLower

theorem OMA.solution : type_of% @OMA.S_mo_101886.main := by
  exact MO101886FinishLower.solution
