import OMAStatements.S_oeis_a090335
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Fintype.Powerset

open scoped BigOperators

namespace A090335Dyadic

theorem dyadic_abundance (K : ℕ) :
    ∃ r : ℕ, 0 < r ∧ K ≤ ((Finset.Ico (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime).card := by
  classical
  by_contra! h
  let f : ℕ → ℝ := Set.indicator {p | Nat.Prime p} (fun n : ℕ => (1 : ℝ) / n)
  have hf (n : ℕ) : 0 ≤ f n := Set.indicator_nonneg (fun _ _ => by positivity) _
  have hcard (r : ℕ) : ((Finset.Ico (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime).card ≤ K := by
    cases r with
    | zero =>
      have hz : ((Finset.Ico 1 2).filter Nat.Prime).card = 0 := by decide
      simpa only [pow_zero, Nat.zero_add, pow_one, hz] using Nat.zero_le K
    | succ r => exact (h (r + 1) (Nat.succ_pos r)).le
  have hblock (r : ℕ) :
      ∑ p ∈ Finset.Ico (2 ^ r) (2 ^ (r + 1)), f p ≤ (K : ℝ) * (1 / 2) ^ r := by
    let s := Finset.Ico (2 ^ r) (2 ^ (r + 1))
    calc
      (∑ p ∈ s, f p) = ∑ p ∈ s.filter Nat.Prime, (1 : ℝ) / p := by
        simp [f, Set.indicator_apply, Finset.sum_filter]
      _ ≤ ∑ _p ∈ s.filter Nat.Prime, (1 / 2 : ℝ) ^ r := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : (2 : ℝ) ^ r ≤ (p : ℝ) := by
          exact_mod_cast (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1
        rw [one_div_pow]
        exact one_div_le_one_div_of_le (by positivity) hp'
      _ = ((s.filter Nat.Prime).card : ℝ) * (1 / 2) ^ r := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (K : ℝ) * (1 / 2) ^ r :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard r) (by positivity)
  have hprefix (r : ℕ) :
      ∑ p ∈ Finset.range (2 ^ r), f p ≤ (K : ℝ) * ∑ j ∈ Finset.range r, (1 / 2) ^ j := by
    induction r with
    | zero => simp [f, Set.indicator_apply]
    | succ r ih =>
      rw [← Finset.sum_range_add_sum_Ico f (Nat.pow_le_pow_right (by decide) (Nat.le_succ r)),
        Finset.sum_range_succ, mul_add]
      exact add_le_add ih (hblock r)
  apply not_summable_one_div_on_primes
  apply summable_of_sum_range_le hf (c := (K : ℝ) * 2)
  intro n
  calc
    (∑ p ∈ Finset.range n, f p) ≤ ∑ p ∈ Finset.range (2 ^ n), f p :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_subset_range.mpr n.lt_two_pow_self.le) (fun p _ _ => hf p)
    _ ≤ (K : ℝ) * ∑ j ∈ Finset.range n, (1 / 2) ^ j := hprefix n
    _ ≤ (K : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) (by positivity)

end A090335Dyadic

namespace OMA.A090335Fibers

/-- Fix the coordinates other than `i`. If at most `C` values at `i` make a
tuple bad, then the total number of bad tuples is at most `C` times the number
of assignments to the remaining coordinates. -/
theorem card_filter_le {n : ℕ} {α : Type*} [Fintype α] (i : Fin n)
    (bad : (Fin n → α) → Prop) [DecidablePred bad] (C : ℕ)
    (h : ∀ f : Fin n → α,
      (Finset.univ.filter fun a : α => bad (Function.update f i a)).card ≤ C) :
    (Finset.univ.filter bad).card ≤ C * (Fintype.card α) ^ (n - 1) := by
  classical
  let K := {j : Fin n // j ≠ i} → α
  let rest (f : Fin n → α) : K := fun j => f j
  let s := Finset.univ.filter bad
  let fiber (k : K) := s.filter (fun f => rest f = k)
  have agrees {f g : Fin n → α} (hfg : rest f = rest g) {j : Fin n} (hj : j ≠ i) :
      f j = g j := congrFun hfg ⟨j, hj⟩
  have bound (k : K) : (fiber k).card ≤ C := by
    rcases (fiber k).eq_empty_or_nonempty with he | ⟨f, hf⟩
    · simp [he]
    · have into : (fiber k : Set (Fin n → α)).MapsTo (fun g => g i)
          (Finset.univ.filter fun a : α => bad (Function.update f i a)) := by
        intro g hg
        have hg' := Finset.mem_filter.1 (show g ∈ fiber k from hg)
        have hf' := (Finset.mem_filter.1 hf).2
        have he : Function.update f i (g i) = g := by
          funext j
          by_cases hj : j = i
          · subst j
            simp
          · rw [Function.update_of_ne hj]
            exact agrees (hf'.trans hg'.2.symm) hj
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, he.symm ▸ (Finset.mem_filter.1 hg'.1).2⟩
      have inj : (fiber k : Set (Fin n → α)).InjOn (fun g => g i) := by
        intro g hg q hq he
        funext j
        by_cases hj : j = i
        · simpa only [hj] using he
        · have hg' := (Finset.mem_filter.1 (show g ∈ fiber k from hg)).2
          have hq' := (Finset.mem_filter.1 (show q ∈ fiber k from hq)).2
          exact agrees (hg'.trans hq'.symm) hj
      exact (Finset.card_le_card_of_injOn (fun g => g i) into inj).trans (h f)
  have htotal := Finset.card_le_mul_card_image_of_maps_to (f := rest) (s := s) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _) C (fun k _ => bound k)
  have hi : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
    rw [Fintype.card_subtype_compl (fun j : Fin n => j = i), Fintype.card_subtype_eq,
      Fintype.card_fin]
  simpa [s, K, hi] using htotal

end OMA.A090335Fibers

open scoped Classical

namespace OMA.A090335Select

/-- Avoid finitely many bad events when each event restricts one coordinate to at most `B` values. -/
theorem exists_injective_avoiding {n : ℕ} {α β : Type*} [Fintype α] [Fintype β]
    (bad : β → (Fin n → α) → Prop) (B : ℕ)
    (hbad : ∀ b, ∃ i : Fin n, ∀ f : Fin n → α,
      ((Finset.univ : Finset α).filter (fun x => bad b (Function.update f i x))).card ≤ B)
    (hsize : n * n + Fintype.card β * B < Fintype.card α) :
    ∃ f : Fin n → α, Function.Injective f ∧ ∀ b, ¬ bad b f := by
  classical
  by_cases hn : 0 < n
  · let same (p : Fin n × Fin n) (f : Fin n → α) := p.1 ≠ p.2 ∧ f p.1 = f p.2
    let repeats := (Finset.univ : Finset (Fin n × Fin n)).biUnion fun p =>
      Finset.univ.filter (same p)
    let collisions := (Finset.univ : Finset β).biUnion fun b =>
      Finset.univ.filter (bad b)
    have hr : repeats.card ≤ n * n * Fintype.card α ^ (n - 1) := by
      have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin n × Fin n))
        (fun p => Finset.univ.filter (same p)) (Fintype.card α ^ (n - 1)) ?_
      · simpa [repeats] using h
      · intro p _
        simpa only [one_mul] using OMA.A090335Fibers.card_filter_le p.1 (same p) 1 (by
          intro f
          by_cases hp : p.1 = p.2
          · simp [same, hp]
          · refine (Finset.card_le_card (t := {f p.2}) ?_).trans (by simp)
            intro x hx
            simpa [same, hp, Function.update_of_ne (Ne.symm hp)] using hx)
    have hc : collisions.card ≤ Fintype.card β * (B * Fintype.card α ^ (n - 1)) := by
      have h := Finset.card_biUnion_le_card_mul (Finset.univ : Finset β)
        (fun b => Finset.univ.filter (bad b)) (B * Fintype.card α ^ (n - 1)) ?_
      · simpa [collisions] using h
      · intro b _
        obtain ⟨i, hi⟩ := hbad b
        exact OMA.A090335Fibers.card_filter_le i (bad b) B hi
    have hpow : Fintype.card α ^ n = Fintype.card α * Fintype.card α ^ (n - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    have htotal : (repeats ∪ collisions).card < Fintype.card (Fin n → α) := by
      calc
        _ ≤ repeats.card + collisions.card := Finset.card_union_le _ _
        _ ≤ (n * n + Fintype.card β * B) * Fintype.card α ^ (n - 1) := by
          simpa only [Nat.add_mul, Nat.mul_assoc] using Nat.add_le_add hr hc
        _ < Fintype.card α * Fintype.card α ^ (n - 1) :=
          Nat.mul_lt_mul_of_pos_right hsize (Nat.pow_pos (Nat.zero_lt_of_lt hsize))
        _ = Fintype.card (Fin n → α) := by rw [Fintype.card_fun, Fintype.card_fin, hpow]
    have hex : ∃ f : Fin n → α, f ∉ repeats ∪ collisions := by
      by_contra! h
      exact (not_le_of_gt htotal) (by
        simpa using Finset.card_le_card (s := Finset.univ) (fun f _ => h f))
    obtain ⟨f, hf⟩ := hex
    refine ⟨f, ?_, ?_⟩
    · intro i j hij
      by_contra hne
      apply hf
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨(i, j), Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne, hij⟩⟩)
    · intro b hb
      apply hf
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨b, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩)
  · have hz : n = 0 := by omega
    subst n
    refine ⟨Fin.elim0, (fun {i} => Fin.elim0 i), ?_⟩
    intro b
    exact Fin.elim0 (hbad b).choose

end OMA.A090335Select

namespace OMA.A090335Avoidance

open Finset
open scoped Classical

private lemma card_le_two_of_close (s : Finset ℕ)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → y ≤ x+1) : s.card ≤ 2 := by
  by_cases hs : s.Nonempty
  · let x := s.min' hs
    have hx : x ∈ s := s.min'_mem hs
    have hsub : s ⊆ Icc x (x+1) := by
      intro y hy
      have hxy : x ≤ y := s.min'_le _ hy
      exact mem_Icc.mpr ⟨hxy, h x hx y hy hxy⟩
    exact (card_le_card hsub).trans (by simp only [Nat.card_Icc]; omega)
  · simp [not_nonempty_iff_eq_empty.mp hs]

private lemma card_exists_le_four (s : Finset ℕ) (P : ℕ → ℕ → Prop)
    (hexp : ∀ x ∈ s, ∀ y ∈ s, ∀ k l, P x k → P y l → l ≤ k+1)
    (hchoice : ∀ x ∈ s, ∀ y ∈ s, ∀ k, P x k → P y k → x ≤ y → y ≤ x+1) :
    (s.filter fun x => ∃ k, P x k).card ≤ 4 := by
  by_cases h : ∃ k, ∃ x ∈ s, P x k
  · let k₀ := Nat.find h
    obtain ⟨x₀,hx₀,hP₀⟩ := Nat.find_spec h
    have cover : (s.filter fun x => ∃ k, P x k) ⊆
        (Icc k₀ (k₀+1)).biUnion (fun k => s.filter (fun x => P x k)) := by
      intro x hx
      obtain ⟨hx,k,hP⟩ := mem_filter.mp hx
      exact mem_biUnion.mpr ⟨k, mem_Icc.mpr ⟨Nat.find_min' h ⟨x,hx,hP⟩,
        hexp x₀ hx₀ x hx k₀ k hP₀ hP⟩, mem_filter.mpr ⟨hx,hP⟩⟩
    refine (card_le_card cover).trans ((card_biUnion_le_card_mul _ _ 2 ?_).trans ?_)
    · intro k _
      apply card_le_two_of_close
      intro x hx y hy hxy
      exact hchoice x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 k (mem_filter.mp hx).2
        (mem_filter.mp hy).2 hxy
    · simp only [Nat.card_Icc]; omega
  · rw [filter_eq_empty_iff.mpr (fun x hx ⟨k,hP⟩ => h ⟨k,x,hx,hP⟩), card_empty]
    decide

private lemma div_bounds {u v k : ℕ} (h : u / 2^k = v) :
    v * 2^k ≤ u ∧ u < (v+1) * 2^k := by
  have hk : 0 < (2:ℕ)^k := by positivity
  exact ⟨(Nat.le_div_iff_mul_le hk).mp h.ge, (Nat.div_lt_iff_lt_mul hk).mp (by omega)⟩

private lemma four_pow_le {k l : ℕ} (h : k+2 ≤ l) : 4 * 2^k ≤ (2:ℕ)^l := by
  have h' := Nat.pow_le_pow_right (show 0 < (2:ℕ) by decide) h
  rw [pow_add] at h'
  simpa [mul_comm] using h'

private lemma product_subinterval {x y C : ℕ} (h : y < 2*x) (hC : 0 < C) :
    y*C < 2*(x*C) := by
  simpa [mul_assoc] using Nat.mul_lt_mul_of_pos_right h hC

private lemma right_card (s : Finset ℕ) (R a C : ℕ)
    (hR : 0 < R) (ha : R ≤ a) (hC : 0 < C)
    (hs : ∀ x ∈ s, R ≤ x ∧ x < 2*R) :
    (s.filter fun x => ∃ k : ℕ, (x*C)/2^k = a).card ≤ 4 := by
  apply card_exists_le_four
  · intro x hx y hy k l h₁ h₂
    have hxy : y*C < 2*(x*C) :=
      product_subinterval (by have := (hs x hx).1; have := (hs y hy).2; omega) hC
    have hup := (div_bounds h₁).2
    have hlo := (div_bounds h₂).1
    by_contra! hb
    have hp := Nat.mul_le_mul_left a (four_pow_le (show k+2 ≤ l by omega))
    have ha' := Nat.mul_le_mul_right ((2:ℕ)^k) (show a+1 ≤ 2*a by omega)
    nlinarith
  · intro x hx y _ k h₁ h₂ _
    have hlo := (div_bounds h₁).1
    have hy := (div_bounds h₂).2
    have hwidth : (2:ℕ)^k < 2*C := by
      have hleft := Nat.mul_le_mul_right ((2:ℕ)^k) ha
      have hright := Nat.mul_lt_mul_of_pos_right (hs x hx).2 hC
      by_contra! hb
      have := Nat.mul_le_mul_left R hb
      nlinarith
    by_contra! hb
    have := Nat.mul_le_mul_right C (show x+2 ≤ y by omega)
    nlinarith

private lemma left_card (s : Finset ℕ) (R b C : ℕ)
    (hC : 0 < C) (hs : ∀ x ∈ s, R ≤ x ∧ x < 2*R) :
    (s.filter fun x => ∃ k : ℕ, b/2^k = x*C).card ≤ 4 := by
  apply card_exists_le_four
  · intro x hx y hy k l h₁ h₂
    have hxy : x*C < 2*(y*C) :=
      product_subinterval (by have := (hs y hy).1; have := (hs x hx).2; omega) hC
    have hup := (div_bounds h₁).2
    have hlo := (div_bounds h₂).1
    by_contra! hb
    have hp := Nat.mul_le_mul_left (y*C) (four_pow_le (show k+2 ≤ l by omega))
    have hmain := Nat.mul_le_mul_right ((2:ℕ)^k) (show x*C+1 ≤ 2*(y*C) by omega)
    have hpos : 0 < y*C := by
      have hy' : 0 < y := by have := (hs y hy).2; have := (hs y hy).1; omega
      exact Nat.mul_pos hy' hC
    have hlt := Nat.mul_lt_mul_of_pos_right (show 2*(y*C) < 4*(y*C) by omega)
      (show 0 < (2:ℕ)^k by positivity)
    nlinarith
  · intro x _ y _ k h₁ h₂ _
    have he : x = y := Nat.eq_of_mul_eq_mul_right hC (h₁.symm.trans h₂)
    omega

private lemma prod_update_out {n : ℕ} {pool : Finset ℕ} (f : Fin n → ↥pool)
    (A : Finset (Fin n)) {i : Fin n} (x : ↥pool) (hi : i ∉ A) :
    (∏ j ∈ A, ((Function.update f i x j : ↥pool) : ℕ)) = ∏ j ∈ A, (f j : ℕ) := by
  apply prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun e => hi (e ▸ hj)
  rw [Function.update_of_ne hji]

private lemma prod_update_in {n : ℕ} {pool : Finset ℕ} (f : Fin n → ↥pool)
    (A : Finset (Fin n)) {i : Fin n} (x : ↥pool) (hi : i ∈ A) :
    (∏ j ∈ A, ((Function.update f i x j : ↥pool) : ℕ)) =
      (x : ℕ) * (∏ j ∈ A.erase i, (f j : ℕ)) := by
  rw [← mul_prod_erase A _ hi, Function.update_self, prod_update_out f _ x (notMem_erase _ _)]

/-- Fixing all but one exclusive coordinate leaves at most four choices for a
binary-prefix collision between two distinct nonempty subsets. -/
theorem collision_fiber (pool : Finset ℕ) (R : ℕ) (hR : 0 < R)
    (hpool : ∀ x ∈ pool, R ≤ x ∧ x < 2*R) {n : ℕ} (A B : Finset (Fin n))
    (hA : A.Nonempty) (_hB : B.Nonempty) (hne : A ≠ B) :
    ∃ i : Fin n, ∀ f : Fin n → ↥pool,
      (univ.filter (fun x : ↥pool => ∃ k : ℕ,
        (∏ j ∈ B, ((Function.update f i x j : ↥pool) : ℕ)) / 2^k =
          ∏ j ∈ A, ((Function.update f i x j : ↥pool) : ℕ))).card ≤ 4 := by
  by_cases hab : A ⊆ B
  · obtain ⟨i,hiB,hiA⟩ := Finset.not_subset.mp (show ¬B ⊆ A from fun hba => hne (Subset.antisymm hab hba))
    refine ⟨i, fun f => ?_⟩
    have hpos (j : Fin n) : 0 < (f j : ℕ) := hR.trans_le (hpool _ (f j).property).1
    obtain ⟨j,hj⟩ := hA
    have ha : R ≤ ∏ j ∈ A, (f j : ℕ) :=
      (hpool _ (f j).property).1.trans (by
        rw [← Finset.prod_erase_mul A (fun k => (f k : ℕ)) hj]
        exact Nat.le_mul_of_pos_left _ (Finset.prod_pos (fun k _ => hpos k)))
    have hc : 0 < ∏ j ∈ B.erase i, (f j : ℕ) := Finset.prod_pos (fun k _ => hpos k)
    refine le_trans ?_ (right_card pool R _ _ hR ha hc hpool)
    apply card_le_card_of_injOn (fun x : ↥pool => (x : ℕ))
    · intro x hx
      obtain ⟨_,k,hk⟩ := mem_filter.mp (mem_coe.mp hx)
      rw [prod_update_in f B x hiB, prod_update_out f A x hiA] at hk
      exact mem_filter.mpr ⟨x.property,k,hk⟩
    · intro x _ y _ e
      exact Subtype.ext e
  · obtain ⟨i,hiA,hiB⟩ := Finset.not_subset.mp hab
    refine ⟨i, fun f => ?_⟩
    have hc : 0 < ∏ j ∈ A.erase i, (f j : ℕ) :=
      Finset.prod_pos (fun j _ => hR.trans_le (hpool _ (f j).property).1)
    refine le_trans ?_ (left_card pool R (∏ j ∈ B, (f j : ℕ)) _ hc hpool)
    apply card_le_card_of_injOn (fun x : ↥pool => (x : ℕ))
    · intro x hx
      obtain ⟨_,k,hk⟩ := mem_filter.mp (mem_coe.mp hx)
      rw [prod_update_out f B x hiB, prod_update_in f A x hiA] at hk
      exact mem_filter.mpr ⟨x.property,k,hk⟩
    · intro x _ y _ e
      exact Subtype.ext e

end OMA.A090335Avoidance

namespace OMA.S_oeis_a090335

private theorem eligible_of_tuple {n : ℕ} (p : Fin n → ℕ)
    (hinj : Function.Injective p) (hprime : ∀ i, (p i).Prime)
    (hprefix : ∀ s t : Finset (Fin n), s.Nonempty → t.Nonempty → ∀ k : ℕ,
      (∏ i ∈ t, p i) / 2 ^ k = ∏ i ∈ s, p i → s = t) :
    ∃ m, eligible n m := by
  let S : Finset ℕ := Finset.univ.image p
  let m := ∏ q ∈ S, q
  have hS (q : ℕ) (hq : q ∈ S) : q.Prime := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hq
    exact hprime i
  have hpos : 0 < m := Finset.prod_pos fun q hq => (hS q hq).pos
  have hpf : m.primeFactors = S := Nat.primeFactors_prod hS
  have hsq : Squarefree m :=
    Finset.squarefree_prod_of_pairwise_isCoprime
      (fun q hq r hr hne => Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (hS q hq) (hS r hr)).2 hne))
      (fun q hq => (hS q hq).prime.squarefree)
  have hcard : m.primeFactors.card = n := by
    rw [hpf, show S = Finset.univ.image p from rfl, Finset.card_image_of_injective _ hinj]
    simp
  have hdiv (a : ℕ) (ha : a ∣ m) (hgt : 1 < a) :
      ∃ s : Finset (Fin n), s.Nonempty ∧ (∏ i ∈ s, p i) = a := by
    have hsubset : a.primeFactors ⊆ S := hpf ▸ Nat.primeFactors_mono ha hpos.ne'
    let s : Finset (Fin n) := Finset.univ.filter (fun i => p i ∈ a.primeFactors)
    have himage : s.image p = a.primeFactors := by
      ext q
      simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hq
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 (hsubset hq)
        exact ⟨i, hq, rfl⟩
    have hprod : (∏ i ∈ s, p i) = a := by
      calc
        _ = ∏ q ∈ s.image p, q := (Finset.prod_image (fun _ _ _ _ h => hinj h)).symm
        _ = a := by rw [himage, Nat.prod_primeFactors_of_squarefree (hsq.squarefree_of_dvd ha)]
    refine ⟨s, Finset.nonempty_iff_ne_empty.2 fun he => ?_, hprod⟩
    rw [he, Finset.prod_empty] at hprod
    exact hgt.ne hprod
  refine ⟨m, hpos, hcard, ?_⟩
  intro a ha hgt b hb hgt' k hk
  obtain ⟨s, hs, es⟩ := hdiv a ha hgt
  obtain ⟨t, ht, et⟩ := hdiv b hb hgt'
  have hst := hprefix s t hs ht k (by rw [es, et, hk])
  rw [← es, ← et, hst]

private theorem least_of_eligible {n : ℕ} (h : ∃ m, eligible n m) :
    ∃ m, IsLeast {x : ℕ | eligible n x} m := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun _ hmem => Nat.find_min' h hmem⟩

end OMA.S_oeis_a090335

namespace OMA.S_oeis_a090335

private theorem exists_eligible (n : ℕ) : ∃ m, eligible n m := by
  classical
  let Pairs := {b : Finset (Fin n) × Finset (Fin n) //
    b.1.Nonempty ∧ b.2.Nonempty ∧ b.1 ≠ b.2}
  obtain ⟨r, _, hr⟩ := A090335Dyadic.dyadic_abundance (n * n + Fintype.card Pairs * 4 + 1)
  let pool := (Finset.Ico (2 ^ r) (2 ^ (r + 1))).filter Nat.Prime
  let bad (b : Pairs) (q : Fin n → ↥pool) : Prop :=
    ∃ k : ℕ, (∏ i ∈ b.val.2, (q i : ℕ)) / 2 ^ k = ∏ i ∈ b.val.1, (q i : ℕ)
  have hpool (x : ℕ) (hx : x ∈ pool) : 2 ^ r ≤ x ∧ x < 2 * 2 ^ r := by
    simpa only [pow_succ'] using Finset.mem_Ico.mp (Finset.mem_filter.mp hx).1
  have hfiber (b : Pairs) : ∃ i : Fin n, ∀ q : Fin n → ↥pool,
      (Finset.univ.filter (fun x : ↥pool => bad b (Function.update q i x))).card ≤ 4 :=
    OMA.A090335Avoidance.collision_fiber pool (2 ^ r) (by positivity) hpool
      b.val.1 b.val.2 b.property.1 b.property.2.1 b.property.2.2
  have hsize : n * n + Fintype.card Pairs * 4 < Fintype.card ↥pool := by
    rw [Fintype.card_coe]
    exact Nat.lt_of_succ_le hr
  obtain ⟨q, hinj, hgood⟩ := OMA.A090335Select.exists_injective_avoiding bad 4 hfiber hsize
  refine eligible_of_tuple (fun i => (q i : ℕ)) (fun _ _ h => hinj (Subtype.ext h)) ?_ ?_
  · intro i
    exact (Finset.mem_filter.mp (q i).property).2
  · intro s t hs ht k hk
    by_contra hne
    exact hgood ⟨(s, t), hs, ht, hne⟩ ⟨k, hk⟩

end OMA.S_oeis_a090335

/-- Choose primes from a populous dyadic interval and avoid all prefix collisions. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a090335.main := fun n =>
  OMA.S_oeis_a090335.least_of_eligible (OMA.S_oeis_a090335.exists_eligible n)
