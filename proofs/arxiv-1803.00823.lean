import OMAStatements.S_arxiv_1803_00823

/-!
A five-match counterexample to Conjecture 4.2 of P. Hegarty, A. Martinsson
and E. Wedin (https://arxiv.org/abs/1803.00823).

The two-tier matrix and the first-coordinate obstruction were suggested by
@tatashbar's statement in https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8195.
The five-match schedule and lottery below are a separate construction.

Credit: @grp06
-/

open scoped BigOperators

namespace OMA.P_arxiv_1803_00823

open OMA.S_arxiv_1803_00823

private abbrev Player := Fin 4
private abbrev Game := Player × Player
private abbrev Perm := Equiv.Perm Player

private def schedule : List Game := [(0, 3), (0, 3), (1, 2), (1, 2), (2, 3)]

private def bit (b : Bool) : ℕ := if b then 1 else 0

/-- The lottery is given in thirds. The first two arguments count wins of
roles 0 and 1 in their respective two matches. The last records a win of role 2. -/
private def lottery : ℕ → ℕ → Bool → Player → ℕ
  | 0, 1, false => ![0, 1, 0, 2]
  | 0, 1, true  => ![0, 2, 0, 1]
  | 1, 0, false => ![2, 0, 1, 0]
  | 1, 0, true  => ![1, 0, 2, 0]
  | 1, 1, false => ![0, 1, 1, 1]
  | 1, 1, true  => ![1, 0, 1, 1]
  | 1, 2, true  => ![1, 1, 1, 0]
  | 2, 1, false => ![1, 1, 0, 1]
  | _, _, false => ![2, 1, 0, 0]
  | _, _, true  => ![1, 2, 0, 0]

private def tickets : List Bool → Player → ℕ
  | [a, b, c, d, e] => lottery (bit a + bit b) (bit c + bit d) e
  | _ => ![3, 0, 0, 0]

private noncomputable def weights (h : List Bool) (k : Player) : ℝ :=
  (tickets h k : ℝ) / 3

private def rationalWeights (h : List Bool) (k : Player) : ℚ :=
  (tickets h k : ℚ) / 3

/-- Play the given schedule in the renamed roles, and apply the lottery
at the end. A true result means that the first role in that match wins. -/
private noncomputable def tree (σ : Perm) : List Game → List Bool → Tournament 4
  | [], h => .chance 4 (weights h) (fun k => .declare (σ k))
  | g :: s, h => .play (σ g.1) (σ g.2) (tree σ s (h ++ [true])) (tree σ s (h ++ [false]))

private def evaluate {R : Type} [Semiring R] (w : List Bool → Player → R)
    (P : Matrix Player Player R) (k : Player) : List Game → List Bool → R
  | [], h => w h k
  | g :: s, h =>
    P g.1 g.2 * evaluate w P k s (h ++ [true]) +
    P g.2 g.1 * evaluate w P k s (h ++ [false])

private theorem tree_evaluate (σ : Perm) (P : Matrix Player Player ℝ) (k : Player)
    (s : List Game) (h : List Bool) :
    (tree σ s h).winProb P k = evaluate weights (P.submatrix σ σ) (σ.symm k) s h := by
  induction s generalizing h with
  | nil =>
      have heq (w : Player) : (k = σ w) ↔ (w = σ.symm k) := by
        constructor
        · intro e
          rw [e, σ.symm_apply_apply]
        · intro e
          rw [e, σ.apply_symm_apply]
      simp [tree, Tournament.winProb, evaluate, heq, mul_ite]
  | cons g s ih =>
      simp [tree, Tournament.winProb, evaluate, Matrix.submatrix_apply, ih]

private def completions : List Game → List (List Bool)
  | [] => [[]]
  | _ :: s => (completions s).map (true :: ·) ++ (completions s).map (false :: ·)

/-- Check normalization at each leaf and both monotonicity inequalities
for each match, separately for every possible continuation of its results. -/
private def checks : List Game → List Bool → Bool
  | [], h => decide ((∑ k : Player, tickets h k) = 3)
  | g :: s, h =>
    decide (g.1 ≠ g.2) &&
      ((completions s).all (fun t =>
        decide (tickets ((h ++ [false]) ++ t) g.1 ≤ tickets ((h ++ [true]) ++ t) g.1 ∧
                tickets ((h ++ [true]) ++ t) g.2 ≤ tickets ((h ++ [false]) ++ t) g.2)) &&
        (checks s (h ++ [true]) && checks s (h ++ [false])))

private theorem schedule_checks : checks schedule [] = true := by decide +kernel

private theorem evaluate_mono (P : Matrix Player Player ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (k : Player) (s : List Game) (h h' : List Bool)
    (hle : ∀ t ∈ completions s, tickets (h ++ t) k ≤ tickets (h' ++ t) k) :
    evaluate weights P k s h ≤ evaluate weights P k s h' := by
  induction s generalizing h h' with
  | nil =>
      have ht : tickets h k ≤ tickets h' k := by
        simpa using hle [] (by simp [completions])
      exact div_le_div_of_nonneg_right (by exact_mod_cast ht) (by norm_num)
  | cons g s ih =>
      rw [evaluate, evaluate]
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (hP _ _)
        apply ih
        intro t ht
        have hm : true :: t ∈ completions (g :: s) :=
          List.mem_append_left _ (List.mem_map_of_mem ht)
        simpa [List.append_assoc] using hle (true :: t) hm
      · apply mul_le_mul_of_nonneg_left _ (hP _ _)
        apply ih
        intro t ht
        have hm : false :: t ∈ completions (g :: s) :=
          List.mem_append_right _ (List.mem_map_of_mem ht)
        simpa [List.append_assoc] using hle (false :: t) hm

private theorem tree_valid (σ : Perm) (s : List Game) (h : List Bool)
    (hc : checks s h = true) : (tree σ s h).WellFormed ∧ (tree σ s h).Honest := by
  induction s generalizing h with
  | nil =>
      have hn : (∑ k : Player, tickets h k) = 3 := by
        simpa only [checks, decide_eq_true_eq] using hc
      refine ⟨?_, ?_⟩
      · refine ⟨fun k => div_nonneg (Nat.cast_nonneg _) (by norm_num), ?_, fun _ => trivial⟩
        simp only [weights, ← Finset.sum_div, ← Nat.cast_sum, hn]
        norm_num
      · exact fun _ _ => trivial
  | cons g s ih =>
      simp only [checks, Bool.and_eq_true_iff, decide_eq_true_eq] at hc
      obtain ⟨hne, hmono, ht, hf⟩ := hc
      obtain ⟨hwt, hht⟩ := ih _ ht
      obtain ⟨hwf, hhf⟩ := ih _ hf
      refine ⟨⟨fun e => hne (σ.injective e), hwt, hwf⟩, ⟨?_, hht, hhf⟩⟩
      intro P hP
      have mp := (show (∀ i j, 0 ≤ P i j ∧ P i j ≤ 1) ∧
                        ∀ i j, P i j + P j i = 1 from hP).1
      simp only [tree_evaluate, Equiv.symm_apply_apply]
      have hn (i j : Player) : 0 ≤ (P.submatrix σ σ) i j := (mp (σ i) (σ j)).1
      have hm (t : List Bool) (ht' : t ∈ completions s) :
          tickets ((h ++ [false]) ++ t) g.1 ≤ tickets ((h ++ [true]) ++ t) g.1 ∧
          tickets ((h ++ [true]) ++ t) g.2 ≤ tickets ((h ++ [false]) ++ t) g.2 :=
        of_decide_eq_true (List.all_eq_true.mp hmono t ht')
      exact ⟨evaluate_mono _ hn _ _ _ _ (fun t ht' => (hm t ht').1),
        evaluate_mono _ hn _ _ _ _ (fun t ht' => (hm t ht').2)⟩

-- Use the computable permutation enumeration for the final rational sum.
local instance : Fintype Perm := fintypePerm

private theorem perm_card : Fintype.card Perm = 24 := by decide +kernel

private noncomputable def enumeration : Fin 24 ≃ Perm :=
  (Fintype.equivFinOfCardEq perm_card).symm

private noncomputable def tournament : Tournament 4 :=
  .chance 24 (fun _ => 1 / 24) (fun j => tree (enumeration j) schedule [])

private theorem tournament_valid : tournament.WellFormed ∧ tournament.Honest := by
  constructor
  · refine ⟨fun _ => by norm_num, ?_, fun j => (tree_valid (enumeration j) _ _ schedule_checks).1⟩
    norm_num [Finset.sum_const, Fintype.card_fin]
  · exact fun j _ => (tree_valid (enumeration j) _ _ schedule_checks).2

private theorem tournament_evaluate (P : Matrix Player Player ℝ) (k : Player) :
    tournament.winProb P k =
      (∑ σ : Perm, evaluate weights (P.submatrix σ σ) (σ.symm k) schedule []) / 24 := by
  simp only [tournament, Tournament.winProb, tree_evaluate]
  simp_rw [one_div_mul_eq_div]
  rw [← Finset.sum_div]
  exact congrArg (fun z : ℝ => z / 24)
    (enumeration.sum_comp (fun σ : Perm =>
      evaluate weights (P.submatrix σ σ) (σ.symm k) schedule []))

private theorem tournament_symmetric : tournament.Symmetric := by
  intro P _ τ k
  rw [tournament_evaluate, tournament_evaluate]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ ?_
  intro σ
  have happly (i : Player) : (Equiv.mulLeft τ σ) i = τ (σ i) := rfl
  have hmatrix :
      (P.submatrix τ.symm τ.symm).submatrix (Equiv.mulLeft τ σ) (Equiv.mulLeft τ σ) =
        P.submatrix σ σ := by
    ext i j
    simp only [Matrix.submatrix_apply, happly, Equiv.symm_apply_apply]
  have hplayer : (Equiv.mulLeft τ σ).symm (τ k) = σ.symm k := by
    apply (Equiv.mulLeft τ σ).injective
    simp
  rw [hmatrix, hplayer]

private def rationalMatrix (i j : Player) : ℚ :=
  if i.val / 2 = j.val / 2 then 1 / 2 else if i.val < j.val then 1 else 0

private noncomputable def matrix : Matrix Player Player ℝ := fun i j => rationalMatrix i j

private theorem rationalMatrix_valid :
    (∀ i j, 0 ≤ rationalMatrix i j ∧ rationalMatrix i j ≤ 1 ∧
      rationalMatrix i j + rationalMatrix j i = 1) ∧
    (∀ i i' j, i ≤ i' → rationalMatrix i' j ≤ rationalMatrix i j) ∧
    (∀ i j j', j ≤ j' → rationalMatrix i j ≤ rationalMatrix i j') := by
  decide +kernel

private theorem matrix_valid : matrix ∈ doublyMonotonic 4 := by
  obtain ⟨h, hr, hc⟩ := rationalMatrix_valid
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j
    change 0 ≤ (rationalMatrix i j : ℝ) ∧ (rationalMatrix i j : ℝ) ≤ 1
    exact ⟨by exact_mod_cast (h i j).1, by exact_mod_cast (h i j).2.1⟩
  · intro i j
    change (rationalMatrix i j : ℝ) + (rationalMatrix j i : ℝ) = 1
    exact_mod_cast (h i j).2.2
  · intro i i' j hij
    exact Rat.cast_le.mpr (hr i i' j hij)
  · intro i j j' hjj
    exact Rat.cast_le.mpr (hc i j j' hjj)

private theorem evaluate_cast (Q : Matrix Player Player ℚ) (k : Player)
    (s : List Game) (h : List Bool) :
    ((evaluate (R := ℚ) rationalWeights Q k s h : ℚ) : ℝ) =
      evaluate weights (fun i j => (Q i j : ℝ)) k s h := by
  induction s generalizing h with
  | nil => simp [evaluate, rationalWeights, weights]
  | cons g s ih => simp [evaluate, ih]

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
private theorem rational_result :
    (∑ σ : Perm,
      evaluate rationalWeights
        (fun i j => rationalMatrix (σ i) (σ j)) (σ.symm 0) schedule []) / 24 =
      17 / 72 := by
  decide +kernel

private theorem first_probability : tournament.winProb matrix 0 = 17 / 72 := by
  rw [tournament_evaluate]
  calc
    _ = (∑ σ : Perm, ((evaluate rationalWeights
          (fun i j => rationalMatrix (σ i) (σ j)) (σ.symm 0) schedule [] : ℚ) : ℝ)) / 24 := by
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      exact (evaluate_cast (fun i j => rationalMatrix (σ i) (σ j))
        (σ.symm 0) schedule []).symm
    _ = _ := by
      have h := congrArg (fun q : ℚ => (q : ℝ)) rational_result
      simpa only [Rat.cast_div, Rat.cast_sum, Rat.cast_ofNat] using h

/-- Each of the two arcs out of role 0 must point back to role 0. -/
private theorem first_lower_bound {x : Player → ℝ} (hx : x ∈ setAStar 4) : 1 / 4 ≤ x 0 := by
  let H : Set (Player → ℝ) := {v | 1 / 4 ≤ v 0}
  have hconv : Convex ℝ H := by
    apply convex_iff_add_mem.mpr
    intro u hu v hv a b ha hb hab
    change (1 / 4 : ℝ) ≤ u 0 at hu
    change (1 / 4 : ℝ) ≤ v 0 at hv
    change (1 / 4 : ℝ) ≤ a * u 0 + b * v 0
    calc
      (1 / 4 : ℝ) = a * (1 / 4) + b * (1 / 4) := by linarith
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hu ha) (mul_le_mul_of_nonneg_left hv hb)
  have hsub : starPoints 4 ⊆ H := by
    intro v hv
    obtain ⟨a, b, hrule, hv⟩ := hv
    have ha : a 0 = 0 := le_antisymm (hrule 0).1 (Fin.zero_le _)
    have hb : b 0 = 0 := le_antisymm (hrule 0).2.1 (Fin.zero_le _)
    have hcard (f : Player → Player) (hf : f 0 = 0) :
        (1 : ℕ) ≤ (Finset.univ.filter fun k => f k = 0).card :=
      Finset.one_le_card.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hf⟩⟩
    have ha' : (1 : ℝ) ≤ ((Finset.univ.filter fun k => a k = 0).card : ℝ) := by
      exact_mod_cast hcard a ha
    have hb' : (1 : ℝ) ≤ ((Finset.univ.filter fun k => b k = 0).card : ℝ) := by
      exact_mod_cast hcard b hb
    change (1 / 4 : ℝ) ≤ v 0
    rw [hv 0]
    calc
      (1 / 4 : ℝ) = (1 + 1) / (2 * (4 : ℕ)) := by norm_num
      _ ≤ _ := div_le_div_of_nonneg_right (add_le_add ha' hb') (by positivity)
  exact (convexHull_min hsub hconv) hx

theorem disproof_core : ¬ (type_of% @OMA.S_arxiv_1803_00823.main) := by
  intro h
  have hac : tournament.winProb matrix ∈ achievable 4 :=
    ⟨tournament, tournament_valid.1, tournament_symmetric, tournament_valid.2,
      matrix, matrix_valid, rfl⟩
  have hA : tournament.winProb matrix ∈ setA 4 := subset_closure hac
  have hStar : tournament.winProb matrix ∈ setAStar 4 := by
    rw [h 4 (by decide)]
    exact hA
  have hbound := first_lower_bound hStar
  rw [first_probability] at hbound
  norm_num at hbound

end OMA.P_arxiv_1803_00823

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_1803_00823.main) :=
  OMA.P_arxiv_1803_00823.disproof_core
