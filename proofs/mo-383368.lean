import OMAStatements.S_mo_383368
import Mathlib

/-!
# A counterexample to the graph ordering inequality

Take seven mutually adjacent vertices and attach 29 leaves to each one.
Number all leaves before the seven centers. In this order the sum of squared
outdegrees is 294.

In any vertex order, a center with `i` earlier centers has `6 - i` later
centers. It is the middle of `i * (6 - i)` directed paths whose endpoints
are centers. Each private leaf forms at least `min i (6 - i)` further
paths through this center. The sum over the seven center positions is 296.

Source: https://mathoverflow.net/questions/383368
Credit: @jacklarmer
-/

namespace OMA.Graph383368

open OMA.S_mo_383368

def center (i : Fin 7) : Fin 210 := ⟨203 + i.val, by omega⟩

def linked (v w : Fin 210) : Prop :=
  v ≠ w ∧ (203 ≤ v.val ∧ 203 ≤ w.val ∨
    v.val < 203 ∧ w.val = 203 + v.val / 29 ∨
    w.val < 203 ∧ v.val = 203 + w.val / 29)

def G : SimpleGraph (Fin 210) where
  Adj := linked
  symm := by
    constructor
    intro v w h
    obtain ⟨hne, h⟩ := h
    refine ⟨hne.symm, ?_⟩
    rcases h with ⟨a,b⟩ | h | h
    · exact Or.inl ⟨b,a⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless := ⟨fun a h => h.1 rfl⟩

instance : DecidableRel G.Adj := fun v w =>
  inferInstanceAs (Decidable (v ≠ w ∧ (203 ≤ v.val ∧ 203 ≤ w.val ∨
    v.val < 203 ∧ w.val = 203 + v.val / 29 ∨
    w.val < 203 ∧ v.val = 203 + w.val / 29)))

lemma center_inj : Function.Injective center := by
  intro i j h
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

lemma center_adj {i j : Fin 7} (h : i ≠ j) : G.Adj (center i) (center j) := by
  exact ⟨fun he => h (center_inj he), Or.inl ⟨by simp [center], by simp [center]⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma center_degree (i : Fin 7) :
    (Finset.univ.filter (fun w => G.Adj (center i) w)).card = 35 := by
  revert i
  decide +kernel

def forwardCount (v : Fin 210) : ℕ :=
  (Finset.univ.filter (fun w => G.Adj v w ∧ v < w)).card

lemma forwardCount_eq (v : Fin 210) :
    outDegree G (Equiv.refl _) v = forwardCount v := by
  unfold outDegree forwardCount
  apply congrArg Finset.card
  apply Finset.filter_congr_decidable

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
lemma original_cost :
    (∑ v, outDegree G (Equiv.refl (Fin 210)) v ^ 2) = 294 := by
  simp only [forwardCount_eq]
  decide +kernel

end OMA.Graph383368

namespace OMA.Graph383368

lemma center_order (r : Fin 7 → Fin 210) (hr : Function.Injective r) :
    ∃ e : Fin 7 ≃ Fin 7, ∀ i, (Finset.univ.filter (fun j => r j < r i)).card = (e i).val := by
  let before (i : Fin 7) := Finset.univ.filter (fun j => r j < r i)
  have hnot (i : Fin 7) : i ∉ before i := by simp [before]
  have hbound (i : Fin 7) : (before i).card < 7 := by
    have hsub : before i ⊂ Finset.univ :=
      lt_of_le_of_ne (Finset.subset_univ _) (fun h => hnot i (h ▸ Finset.mem_univ i))
    simpa using Finset.card_lt_card hsub
  have hlt {i j : Fin 7} (h : r i < r j) : (before i).card < (before j).card := by
    apply Finset.card_lt_card
    apply lt_of_le_of_ne
    · intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hk).2 h⟩
    · intro heq
      have hi : i ∈ before j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      exact hnot i (heq ▸ hi)
  let f (i : Fin 7) : Fin 7 := ⟨(before i).card, hbound i⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    have hc : (before i).card = (before j).card := congrArg Fin.val hij
    apply hr
    rcases lt_trichotomy (r i) (r j) with h | h | h
    · exact False.elim ((hlt h).ne hc)
    · exact h
    · exact False.elim ((hlt h).ne hc.symm)
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj), fun _ => rfl⟩

lemma sum_bound (r : Fin 7 → Fin 210) (hr : Function.Injective r) :
    296 ≤ ∑ i : Fin 7, (let a := (Finset.univ.filter (fun j => r j < r i)).card;
                         a * (6 - a) + 29 * min a (6 - a)) := by
  obtain ⟨e, he⟩ := center_order r hr
  let cost (i : Fin 7) := i.val * (6 - i.val) + 29 * min i.val (6 - i.val)
  have hsum : (∑ i : Fin 7, cost i) = 296 := by
    norm_num [cost, Fin.sum_univ_succ]
  simp_rw [he]
  change 296 ≤ ∑ i : Fin 7, cost (e i)
  rw [e.sum_comp cost, hsum]

open OMA.S_mo_383368

lemma ranked_neighbor_partition {α : Type*} [Fintype α] (r : α → Fin 210)
    (hr : Function.Injective r) (v : α) (p : α → Prop) [DecidablePred p] (hv : ¬ p v) :
    (Finset.univ.filter (fun w => p w ∧ r w < r v)).card +
      (Finset.univ.filter (fun w => p w ∧ r v < r w)).card =
        (Finset.univ.filter p).card := by
  classical
  have hh := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter p) (fun w => r w < r v)
  simp only [Finset.filter_filter] at hh
  convert hh using 2
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro w _
  by_cases h : p w
  · have hne : r v ≠ r w := fun he => hv (hr he ▸ h)
    simp only [h, true_and, not_lt]
    exact lt_iff_le_and_ne.trans (and_iff_left hne)
  · simp [h]

lemma local_bound (G : SimpleGraph (Fin 210)) [DecidableRel G.Adj]
    (c : Fin 7 → Fin 210) (hc : Function.Injective c)
    (hadj : ∀ {i j}, i ≠ j → G.Adj (c i) (c j))
    (hdeg : ∀ i, (Finset.univ.filter (fun w => G.Adj (c i) w)).card = 35)
    (rank : Fin 210 ≃ Fin 210) (i : Fin 7) :
    (let a := (Finset.univ.filter (fun j => rank (c j) < rank (c i))).card
     a * (6-a) + 29 * min a (6-a)) ≤ outDegree G rank (c i) * inDegree G rank (c i) := by
  classical
  let a := (Finset.univ.filter (fun j => rank (c j) < rank (c i))).card
  let b := (Finset.univ.filter (fun j => rank (c i) < rank (c j))).card
  have hIn : inDegree G rank (c i) =
      (Finset.univ.filter (fun w => G.Adj (c i) w ∧ rank w < rank (c i))).card := by
    unfold inDegree
    exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)
  have hOut : outDegree G rank (c i) =
      (Finset.univ.filter (fun w => G.Adj (c i) w ∧ rank (c i) < rank w)).card := by
    unfold outDegree
    exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)
  have ha : a ≤ inDegree G rank (c i) := by
    rw [hIn]
    unfold a
    apply Finset.card_le_card_of_injOn c _ hc.injOn
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj (fun e => by subst j; exact lt_irrefl _ h), h⟩
  have hb : b ≤ outDegree G rank (c i) := by
    rw [hOut]
    unfold b
    apply Finset.card_le_card_of_injOn c _ hc.injOn
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj (fun e => by subst j; exact lt_irrefl _ h), h⟩
  have ht : inDegree G rank (c i) + outDegree G rank (c i) = 35 := by
    rw [hIn, hOut]
    exact (ranked_neighbor_partition rank rank.injective (c i) (G.Adj (c i))
      (G.loopless.irrefl _)).trans (hdeg i)
  have hab : a + b = 6 := by
    have h := ranked_neighbor_partition (fun j => rank (c j)) (rank.injective.comp hc) i
      (fun j => j ≠ i) (by simp)
    have hin : (fun j => j ≠ i ∧ rank (c j) < rank (c i)) =
        (fun j => rank (c j) < rank (c i)) := by
      funext j
      exact propext (and_iff_right_of_imp (fun h e => by subst j; exact lt_irrefl _ h))
    have hout : (fun j => j ≠ i ∧ rank (c i) < rank (c j)) =
        (fun j => rank (c i) < rank (c j)) := by
      funext j
      exact propext (and_iff_right_of_imp (fun h e => by subst j; exact lt_irrefl _ h))
    simpa only [hin, hout, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin] using h
  change a * (6-a) + 29 * min a (6-a) ≤ _
  have hba : 6 - a = b := by omega
  rw [hba]
  obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨y, hy⟩ := Nat.exists_eq_add_of_le hb
  have hxy : 29 = x + y := by omega
  rw [hxy, hx, hy]
  have hm₁ := Nat.mul_le_mul_left x (min_le_right a b)
  have hm₂ := Nat.mul_le_mul_left y (min_le_left a b)
  nlinarith [Nat.zero_le (x*y)]

end OMA.Graph383368

namespace OMA.Graph383368

open OMA.S_mo_383368

/-- Restricting a sum of natural numbers to the seven distinct centers gives a lower bound. -/
lemma center_sum_le (f : Fin 210 → ℕ) :
    (∑ i : Fin 7, f (center i)) ≤ ∑ v : Fin 210, f v := by
  classical
  calc
    (∑ i : Fin 7, f (center i)) = ∑ v ∈ Finset.univ.image center, f v := by
      rw [Finset.sum_image (fun _ _ _ _ h => center_inj h)]
    _ ≤ ∑ v : Fin 210, f v := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma mixed_cost (rank : Fin 210 ≃ Fin 210) :
    296 ≤ ∑ v : Fin 210, outDegree G rank v * inDegree G rank v := by
  classical
  calc
    296 ≤ ∑ i : Fin 7,
        (let a := (Finset.univ.filter (fun j => rank (center j) < rank (center i))).card
         a * (6 - a) + 29 * min a (6 - a)) :=
      sum_bound (fun i => rank (center i)) (rank.injective.comp center_inj)
    _ ≤ ∑ i : Fin 7, outDegree G rank (center i) * inDegree G rank (center i) := by
      exact Finset.sum_le_sum fun i _ => local_bound G center center_inj center_adj center_degree rank i
    _ ≤ ∑ v : Fin 210, outDegree G rank v * inDegree G rank v :=
      center_sum_le (fun v => outDegree G rank v * inDegree G rank v)

end OMA.Graph383368

open OMA.Graph383368 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_383368.main) := by
  intro h
  obtain ⟨rank, hle⟩ := h 210 G (Equiv.refl (Fin 210))
  have hlo := mixed_cost rank
  rw [original_cost] at hle
  omega
