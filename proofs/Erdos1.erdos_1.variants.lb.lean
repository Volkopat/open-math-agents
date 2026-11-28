import FormalConjectures.ErdosProblems.«1»
import Mathlib.Algebra.BigOperators.Fin

-- Problem: Erdős Problem 1 — lb
-- The variance identity and the integer spacing lemma are from @michielkosters's proof.

lemma oma_variance_identity (A : Finset ℕ) :
    ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) ^ 2 =
      (2 : ℝ) ^ A.card * ∑ a ∈ A, (a : ℝ) ^ 2 := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert x A hx ih =>
    rw [Finset.powerset_insert]
    have hdisj : Disjoint A.powerset (A.powerset.image (insert x)) := by
      rw [Finset.disjoint_left]
      intro S hS1 hS2
      rw [Finset.mem_powerset] at hS1
      rw [Finset.mem_image] at hS2
      rcases hS2 with ⟨T, _, rfl⟩
      exact hx (hS1 (Finset.mem_insert_self x T))
    rw [Finset.sum_union hdisj]
    have hinj : Set.InjOn (insert x) (A.powerset : Set (Finset ℕ)) := by
      intro S hS T hT hST
      rw [Finset.mem_coe, Finset.mem_powerset] at hS hT
      have hxS : x ∉ S := fun h => hx (hS h)
      have hxT : x ∉ T := fun h => hx (hT h)
      have := congrArg (fun U => Finset.erase U x) hST
      simpa [Finset.erase_insert hxS, Finset.erase_insert hxT] using this
    rw [Finset.sum_image (fun S hS T hT h => hinj hS hT h)]
    have hsumA : ∑ a ∈ insert x A, (a : ℝ) = (x : ℝ) + ∑ a ∈ A, (a : ℝ) :=
      Finset.sum_insert hx
    have hsum1 : ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ insert x A, (a : ℝ)) ^ 2 =
        ∑ S ∈ A.powerset, ((2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) - (x : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl fun S _ => ?_
      rw [hsumA]
      ring
    have hsum2 : ∑ S ∈ A.powerset, (2 * (∑ a ∈ insert x S, (a : ℝ)) - ∑ a ∈ insert x A, (a : ℝ)) ^ 2 =
        ∑ S ∈ A.powerset, ((2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) + (x : ℝ)) ^ 2 := by
      refine Finset.sum_congr rfl fun S hS => ?_
      have hxS : x ∉ S := fun h => hx ((Finset.mem_powerset.mp hS) h)
      rw [Finset.sum_insert hxS, hsumA]
      ring
    rw [hsum1, hsum2, ← Finset.sum_add_distrib]
    have hcombine : ∑ S ∈ A.powerset,
        (((2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) - (x : ℝ)) ^ 2 +
         ((2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) + (x : ℝ)) ^ 2) =
        ∑ S ∈ A.powerset, (2 * (2 * (∑ a ∈ S, (a : ℝ)) - ∑ a ∈ A, (a : ℝ)) ^ 2 + 2 * (x : ℝ) ^ 2) := by
      refine Finset.sum_congr rfl fun S _ => by ring
    rw [hcombine, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_powerset,
      nsmul_eq_mul, ih, Finset.card_insert_of_notMem hx, Finset.sum_insert hx]
    push_cast
    ring

lemma oma_strictMono_diff {m : ℕ} (g : Fin m → ℕ) (hg : StrictMono g) :
    ∀ i j : ℕ, (hij : i ≤ j) → (hj : j < m) → g ⟨i, hij.trans_lt hj⟩ + (j - i) ≤ g ⟨j, hj⟩ := by
  intro i j hij hj
  induction j generalizing i with
  | zero =>
    have : i = 0 := by omega
    subst this
    simp
  | succ j ih =>
    by_cases hij' : i = j + 1
    · subst hij'; simp
    · have hij2 : i ≤ j := by omega
      have hj' : j < m := by omega
      have h1 := ih i hij2 hj'
      have hlt : g ⟨j, hj'⟩ < g ⟨j + 1, hj⟩ := hg (Fin.mk_lt_mk.mpr (Nat.lt_succ_self j))
      omega

/-- Pair each of the first m integers in the ordered list with the entry m places later. -/
lemma OMA.half_pair_energy {m : ℕ} (g : Fin (m + m) → ℕ) (hg : StrictMono g) (center : ℝ) :
    2 * (m : ℝ) ^ 3 ≤ ∑ i, (2 * (g i : ℝ) - center) ^ 2 := by
  let cost (i : Fin (m + m)) : ℝ := (2 * (g i : ℝ) - center) ^ 2
  have pairCost (i : Fin m) :
      2 * (m : ℝ) ^ 2 ≤ cost (Fin.castAdd m i) + cost (Fin.natAdd m i) := by
    have h := oma_strictMono_diff g hg i.val (m + i.val) (by omega)
      (Nat.add_lt_add_left i.isLt m)
    rw [show m + i.val - i.val = m by omega] at h
    have gap : g (Fin.castAdd m i) + m ≤ g (Fin.natAdd m i) := h
    have gapR : (g (Fin.castAdd m i) : ℝ) + m ≤ (g (Fin.natAdd m i) : ℝ) := by
      exact_mod_cast gap
    have diff : (m : ℝ) ≤ (g (Fin.natAdd m i) : ℝ) - (g (Fin.castAdd m i) : ℝ) := by
      linarith
    have gapSq := (sq_le_sq₀ (Nat.cast_nonneg m) ((Nat.cast_nonneg m).trans diff)).2 diff
    dsimp only [cost]
    nlinarith [sq_nonneg ((g (Fin.castAdd m i) : ℝ) + (g (Fin.natAdd m i) : ℝ) - center)]
  change 2 * (m : ℝ) ^ 3 ≤ ∑ i, cost i
  rw [Fin.sum_univ_add, ← Finset.sum_add_distrib]
  calc
    2 * (m : ℝ) ^ 3 = ∑ _i : Fin m, 2 * (m : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ _ := Finset.sum_le_sum fun i _ => pairCost i

/-- The pairing gives the uniform coefficient 1/2 for sets with distinct subset sums. -/
lemma OMA.sumDistinct_half_bound (N : ℕ) (A : Finset ℕ) (hA : Erdos1.IsSumDistinctSet A N) :
    (1 / 2 : ℝ) * 2 ^ A.card / Real.sqrt (A.card : ℝ) ≤ N := by
  classical
  obtain ⟨hAsub, hAinj⟩ := hA
  set n := A.card
  by_cases hn : n = 0
  · simp [hn]
  let m : ℕ := 2 ^ (n - 1)
  have h2m : 2 * m = 2 ^ n := by
    change 2 * 2 ^ (n - 1) = 2 ^ n
    rw [← pow_succ']
    congr 1
    omega
  have hreal : (2 : ℝ) ^ n = 2 * (m : ℝ) := by exact_mod_cast h2m.symm
  let T : Finset ℕ := A.powerset.image (fun S => S.sum id)
  have hinj_set : Set.InjOn (fun S : Finset ℕ => S.sum id) (A.powerset : Set (Finset ℕ)) := by
    intro S hS T' hT' hST
    have := @hAinj ⟨S, Finset.mem_coe.mp hS⟩ ⟨T', Finset.mem_coe.mp hT'⟩ hST
    exact congrArg Subtype.val this
  have hTcard : T.card = m + m := by
    calc
      T.card = 2 ^ n := by rw [Finset.card_image_of_injOn hinj_set, Finset.card_powerset]
      _ = m + m := h2m.symm.trans (two_mul m)
  let e := T.orderIsoOfFin hTcard
  let g : Fin (m + m) → ℕ := fun i => (e i : ℕ)
  have hg : StrictMono g := fun i j hij => e.strictMono hij
  let center : ℝ := ∑ a ∈ A, (a : ℝ)
  have hmass : 2 * (m : ℝ) ^ 3 ≤ (2 : ℝ) ^ n * ∑ a ∈ A, (a : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ i : Fin (m + m), (2 * (g i : ℝ) - center) ^ 2 :=
        OMA.half_pair_energy g hg center
      _ = ∑ x ∈ T, (2 * (x : ℝ) - center) ^ 2 := by
        rw [← Finset.sum_coe_sort T]
        exact Fintype.sum_equiv e.toEquiv _ _ (fun _ => rfl)
      _ = ∑ S ∈ A.powerset, (2 * (∑ a ∈ S, (a : ℝ)) - center) ^ 2 := by
        dsimp only [T]
        rw [Finset.sum_image hinj_set]
        refine Finset.sum_congr rfl fun S _ => ?_
        simp [Nat.cast_sum]
      _ = _ := oma_variance_identity A
  have hupper : (∑ a ∈ A, (a : ℝ) ^ 2) ≤ (n : ℝ) * (N : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _a ∈ A, (N : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun a ha => ?_
        apply (sq_le_sq₀ (Nat.cast_nonneg a) (Nat.cast_nonneg N)).2
        exact_mod_cast (Finset.mem_Icc.mp (hAsub ha)).2
      _ = _ := by simp [n]
  have hmpos : 0 < m := by dsimp [m]; positivity
  have hmposR : (0 : ℝ) < 2 * (m : ℝ) := mul_pos (by norm_num) (by exact_mod_cast hmpos)
  rw [hreal] at hmass
  have hcancel : (2 * (m : ℝ)) * (m : ℝ) ^ 2 ≤
      (2 * (m : ℝ)) * (∑ a ∈ A, (a : ℝ) ^ 2) := by
    calc
      _ = 2 * (m : ℝ) ^ 3 := by ring
      _ ≤ _ := hmass
  have hsquare := (le_of_mul_le_mul_left hcancel hmposR).trans hupper
  have hnR : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [div_le_iff₀ (Real.sqrt_pos.2 hnR), hreal,
    show (1 / 2 : ℝ) * (2 * (m : ℝ)) = m by ring]
  have hnonneg : 0 ≤ (N : ℝ) * Real.sqrt (n : ℝ) := by positivity
  apply (sq_le_sq₀ (Nat.cast_nonneg m) hnonneg).mp
  calc
    (m : ℝ) ^ 2 ≤ (n : ℝ) * (N : ℝ) ^ 2 := hsquare
    _ = ((N : ℝ) * Real.sqrt (n : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hnR.le]
      ring

theorem OMA.solution : type_of% @Erdos1.erdos_1.variants.lb := by
  refine ⟨fun _ => (0 : ℝ), by simp, ?_⟩
  intro N A h
  simp only [sub_zero]
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
      (by positivity : (0 : ℝ) ≤ 2 ^ A.card)) (Real.sqrt_nonneg _)).trans
    (OMA.sumDistinct_half_bound N A h)
