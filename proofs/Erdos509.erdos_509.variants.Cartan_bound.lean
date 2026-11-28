import FormalConjectures.ErdosProblems.«509»
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Multiset.Fintype

/-! Cartan's covering bound via a greedy disc cover and root-multiplicity product estimate. -/

open scoped BigOperators
open Polynomial

theorem OMA.solution : type_of% @Erdos509.erdos_509.variants.Cartan_bound := by
  classical
  intro f hf hd
  have hn : 0 < f.natDegree := Nat.pos_of_ne_zero hd
  have hnR : (0 : ℝ) < f.natDegree := by exact_mod_cast hn
  let δ := Real.exp 1 / (f.natDegree : ℝ)
  have hδ : 0 < δ := div_pos (Real.exp_pos _) hnR
  have hsplit : f.Splits := IsAlgClosed.splits f
  let a (i : f.roots) : ℂ := i
  let ind (S : Finset f.roots) (z : ℂ) (r : ℝ) := S.filter fun i => dist z (a i) ≤ r
  have hcover (S : Finset f.roots) : ∃ D : List (ℂ × ℝ), (∀ d ∈ D, 0 < d.2) ∧
      (D.map Prod.snd).sum ≤ 2 * δ * S.card ∧
      ∀ (z : ℂ) (j : ℕ), 0 < j → j ≤ (ind S z (δ * j)).card → ∃ d ∈ D, dist z d.1 ≤ d.2 := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hS : S.Nonempty
      · let P (k : ℕ) := ∃ c : ℂ, k ≤ (ind S c (δ * k)).card
        obtain ⟨i, hi⟩ := hS
        have hS1 : 1 ≤ S.card := Finset.one_le_card.2 ⟨i, hi⟩
        have hP1 : P 1 := ⟨a i, Finset.one_le_card.2 ⟨i, Finset.mem_filter.2 ⟨hi, by simpa using hδ.le⟩⟩⟩
        let k := Nat.findGreatest P S.card
        have hk1 : 1 ≤ k := Nat.le_findGreatest hS1 hP1
        have hkS : k ≤ S.card := Nat.findGreatest_le (P := P) _
        obtain ⟨c, hc⟩ : P k := Nat.findGreatest_spec hS1 hP1
        obtain ⟨U, hU, hUk⟩ := Finset.exists_subset_card_eq hc
        have hUS : U ⊆ S := hU.trans (Finset.filter_subset _ _)
        let T := S \ U
        have hTc : T.card = S.card - k := by rw [show T = S \ U from rfl, Finset.card_sdiff_of_subset hUS, hUk]
        have hTsub : T ⊂ S := Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, fun h => by rw [h] at hTc; omega⟩
        obtain ⟨D, hDp, hDs, hDc⟩ := ih T hTsub
        let R := 2 * δ * (k : ℝ)
        have hR : 0 < R := by dsimp [R]; positivity
        refine ⟨(c, R) :: D, fun d hd => (List.mem_cons.1 hd).elim (· ▸ hR) (hDp d), ?_, fun z j hj0 hj => ?_⟩
        · have ht : (T.card : ℝ) + k = S.card := by exact_mod_cast (show T.card + k = S.card by omega)
          simp only [List.map_cons, List.sum_cons]
          change R + (D.map Prod.snd).sum ≤ _; rw [← ht, mul_add]; dsimp [R]; linarith
        · by_cases hhit : ∃ i ∈ U, i ∈ ind S z (δ * j)
          · obtain ⟨i, hiU, hiZ⟩ := hhit
            have hjk : j ≤ k := Nat.le_findGreatest (hj.trans (Finset.card_le_card (Finset.filter_subset _ _))) ⟨z, hj⟩
            refine ⟨(c, R), List.mem_cons_self, ?_⟩
            have hjkr : (j : ℝ) ≤ k := by exact_mod_cast hjk
            have := mul_le_mul_of_nonneg_left hjkr hδ.le
            calc dist z c ≤ dist z (a i) + dist (a i) c := dist_triangle _ _ _
              _ ≤ δ * j + δ * k := add_le_add (Finset.mem_filter.1 hiZ).2 (by rw [dist_comm]; exact (Finset.mem_filter.1 (hU hiU)).2)
              _ ≤ R := by dsimp [R]; linarith
          · have hs : ind S z (δ * j) ⊆ ind T z (δ * j) := fun i hi => by
              obtain ⟨hiS, hiz⟩ := Finset.mem_filter.1 hi
              exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hiS, fun hm => hhit ⟨i, hm, hi⟩⟩, hiz⟩
            obtain ⟨d, hd, hzd⟩ := hDc z j hj0 (hj.trans (Finset.card_le_card hs))
            exact ⟨d, List.mem_cons_of_mem _ hd, hzd⟩
      · rw [Finset.not_nonempty_iff_eq_empty.1 hS]
        exact ⟨[], by simp, by simp, fun _ _ _ hj => by simp [ind] at hj; omega⟩
  have hprod (z : ℂ) (S : Finset f.roots) :
      (∀ j : ℕ, 0 < j → (ind S z (δ * j)).card < j) →
      δ ^ S.card * (S.card.factorial : ℝ) ≤ ∏ i ∈ S, dist z (a i) ∧
        (S.Nonempty → δ ^ S.card * (S.card.factorial : ℝ) < ∏ i ∈ S, dist z (a i)) := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      intro hs; by_cases hS : S.Nonempty
      · obtain ⟨i, hi, hil⟩ : ∃ i ∈ S, δ * S.card < dist z (a i) := by
          by_contra! hno
          have hall : S ⊆ ind S z (δ * S.card) := fun i hi => Finset.mem_filter.2 ⟨hi, hno i hi⟩
          exact (not_lt_of_ge (Finset.card_le_card hall)) (hs S.card (Finset.card_pos.2 hS))
        let T := S.erase i
        have hTsub : T ⊂ S := Finset.erase_ssubset hi
        have hTc : T.card + 1 = S.card := Finset.card_erase_add_one hi
        have htd := (ih T hTsub fun j hj =>
          (Finset.card_le_card (Finset.filter_subset_filter _ hTsub.le)).trans_lt (hs j hj)).1
        have hp : 0 < δ ^ T.card * (T.card.factorial : ℝ) :=
          mul_pos (pow_pos hδ _) (by exact_mod_cast Nat.factorial_pos T.card)
        have hsp : δ ^ S.card * (S.card.factorial : ℝ) = (δ * S.card) * (δ ^ T.card * T.card.factorial) := by
          rw [← hTc, pow_succ, Nat.factorial_succ, Nat.cast_mul]; ring
        have hlt : δ ^ S.card * (S.card.factorial : ℝ) < ∏ j ∈ S, dist z (a j) := calc
          _ = _ := hsp
          _ < dist z (a i) * (δ ^ T.card * T.card.factorial) := mul_lt_mul_of_pos_right hil hp
          _ ≤ dist z (a i) * ∏ j ∈ T, dist z (a j) := mul_le_mul_of_nonneg_left htd dist_nonneg
          _ = _ := Finset.mul_prod_erase S (fun j => dist z (a j)) hi
        exact ⟨hlt.le, fun _ => hlt⟩
      · rw [Finset.not_nonempty_iff_eq_empty.1 hS]; simp
  let S : Finset f.roots := Finset.univ
  have hS : S.card = f.natDegree := by
    change Fintype.card f.roots = f.natDegree
    rw [Multiset.card_coe, hsplit.natDegree_eq_card_roots]
  have hEval (z : ℂ) : ‖f.eval z‖ = ∏ i ∈ S, dist z (a i) := by
    have hp : f.eval z = ∏ i ∈ S, (z - a i) := by
      rw [hsplit.eval_eq_prod_roots_of_monic hf, Finset.prod]
      change (f.roots.map (z - ·)).prod = ((Finset.univ : Finset f.roots).val.map fun i : f.roots => z - (i : ℂ)).prod
      rw [Multiset.map_univ]
    simp only [hp, norm_prod, dist_eq_norm]
  obtain ⟨D, hDp, hDs, hDc⟩ := hcover S
  refine ⟨Fin D.length, ⟨⟨fun i => (D.get i).1, fun i => (D.get i).2, fun z hz => ?_,
    (hasSum_fintype _).summable, ?_, fun i => hDp (D.get i) (List.get_mem D i)⟩⟩⟩
  · change ‖f.eval z‖ ≤ 1 at hz
    obtain ⟨j, hj0, hj⟩ : ∃ j : ℕ, 0 < j ∧ j ≤ (ind S z (δ * j)).card := by
      by_contra! hnone
      have hgt := (hprod z S hnone).2 (Finset.card_pos.1 (hS ▸ hn))
      rw [hS, ← hEval] at hgt
      have hfac : 1 ≤ δ ^ f.natDegree * (f.natDegree.factorial : ℝ) := by
        have hfp : (0 : ℝ) < f.natDegree.factorial := by exact_mod_cast Nat.factorial_pos f.natDegree
        have hb := Real.pow_div_factorial_le_exp (f.natDegree : ℝ) hnR.le f.natDegree
        rw [show Real.exp (f.natDegree : ℝ) = Real.exp 1 ^ f.natDegree by simp [← Real.exp_nat_mul]] at hb
        rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hnR _)]
        simpa using (div_le_iff₀ hfp).1 hb
      exact (not_lt_of_ge hz) (hfac.trans_lt hgt)
    obtain ⟨d, hdD, hzd⟩ := hDc z j hj0 hj
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 hdD
    exact Set.mem_iUnion.2 ⟨i, Metric.mem_closedBall.2 hzd⟩
  · rw [tsum_fintype]
    calc (∑ i : Fin D.length, (D.get i).2) = (D.map Prod.snd).sum := by
          rw [← Fin.sum_ofFn]; congr 1; exact List.ofFn_getElem_eq_map D Prod.snd
      _ ≤ 2 * δ * S.card := hDs
      _ = 2 * Real.exp 1 := by rw [hS, mul_assoc, div_mul_cancel₀ _ hnR.ne']
