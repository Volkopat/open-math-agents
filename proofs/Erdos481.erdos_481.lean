import FormalConjectures.ErdosProblems.«481»
import Mathlib.NumberTheory.Harmonic.Bounds

-- Problem: Erdős Problem 481
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/481.lean:57 (declaration Erdos481.erdos_481)
-- Credit: @michielkosters (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

private def pairs {r : ℕ} (a b : Fin r → ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => [(1, 1)]
  | k + 1 =>
    (List.finRange r).flatMap (fun i =>
      (pairs a b k).map (fun p => (a i * p.1 + b i, a i * p.2)))

private lemma pairs_fst {r : ℕ} (a b : Fin r → ℕ) (k : ℕ) :
    (pairs a b k).map Prod.fst = (Erdos481.T a b)^[k] [1] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((List.finRange r).flatMap _).map Prod.fst =
      (List.finRange r).flatMap (fun i =>
        ((Erdos481.T a b)^[k] [1]).map (fun x => a i * x + b i))
    rw [List.map_flatMap]
    congr 1
    funext i
    rw [List.map_map, ← ih, List.map_map]
    rfl

private lemma list_sum_map_const {α : Type*} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons _ xs ih => simp [Nat.succ_mul, add_comm]

private lemma pairs_length {r : ℕ} (a b : Fin r → ℕ) (k : ℕ) :
    (pairs a b k).length = r ^ k := by
  induction k with
  | zero => simp [pairs]
  | succ k ih =>
    simp only [pairs, List.length_flatMap, List.length_map, ih]
    rw [list_sum_map_const, List.length_finRange, ← pow_succ']

private lemma pairs_bound {r : ℕ} (a b : Fin r → ℕ) (ha : ∀ i, 0 < a i) (k : ℕ) :
    ∀ p ∈ pairs a b k, 1 ≤ p.1 ∧ 1 ≤ p.2 ∧ p.1 ≤ (1 + k * ∑ i, b i) * p.2 := by
  induction k with
  | zero =>
    intro p hp
    simp only [pairs, List.mem_singleton] at hp
    subst hp
    simp
  | succ k ih =>
    intro p hp
    simp only [pairs, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hp
    rcases hp with ⟨i, q, hq, rfl⟩
    rcases ih q hq with ⟨hq1, hq2, hqb⟩
    have hbi : b i ≤ ∑ j, b j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (b j)) (Finset.mem_univ i)
    refine ⟨?_, ?_, ?_⟩
    · have : 1 ≤ a i * q.1 := Nat.mul_pos (ha i) hq1
      omega
    · exact Nat.mul_pos (ha i) hq2
    · calc a i * q.1 + b i
          ≤ a i * ((1 + k * ∑ j, b j) * q.2) + ∑ j, b j :=
            Nat.add_le_add (Nat.mul_le_mul_left (a i) hqb) hbi
        _ ≤ a i * ((1 + k * ∑ j, b j) * q.2) + (∑ j, b j) * (a i * q.2) :=
            Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (Nat.mul_pos (ha i) hq2)) _
        _ = (1 + (k + 1) * ∑ j, b j) * (a i * q.2) := by ring

private lemma list_sum_flatMap {α β : Type*} [AddCommMonoid β] (l : List α) (f : α → List β) :
    (l.flatMap f).sum = (l.map (fun x => (f x).sum)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [List.flatMap_cons, List.sum_append, ih]

private lemma list_sum_map_mul_left {γ : Type*} (l : List γ) (c : ℝ) (f : γ → ℝ) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, mul_add]

private lemma list_sum_finRange {r : ℕ} (g : Fin r → ℝ) :
    ((List.finRange r).map g).sum = ∑ i : Fin r, g i := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, Fin.sum_univ_succ,
      ← ih (fun i => g i.succ)]
    rfl

private lemma pairs_inv_sum {r : ℕ} (a b : Fin r → ℕ) (k : ℕ) :
    ((pairs a b k).map (fun p => (1 : ℝ) / p.2)).sum = (∑ i : Fin r, (1 : ℝ) / a i) ^ k := by
  induction k with
  | zero => simp [pairs]
  | succ k ih =>
    simp only [pairs]
    rw [List.map_flatMap, list_sum_flatMap]
    have hfun : (fun i : Fin r =>
        (((pairs a b k).map (fun p => (a i * p.1 + b i, a i * p.2))).map
          (fun p => (1 : ℝ) / p.2)).sum) =
        (fun i : Fin r => ((1 : ℝ) / a i) * (∑ j : Fin r, (1 : ℝ) / a j) ^ k) := by
      ext i
      rw [List.map_map]
      have hmap : ((pairs a b k).map ((fun p : ℕ × ℕ => (1 : ℝ) / p.2) ∘
          (fun p => (a i * p.1 + b i, a i * p.2)))).sum =
          ((pairs a b k).map (fun p => ((1 : ℝ) / a i) * ((1 : ℝ) / p.2))).sum := by
        congr 1
        ext p
        simp [Function.comp_def, Nat.cast_mul, mul_comm]
      rw [hmap, list_sum_map_mul_left, ih]
    simp_rw [hfun]
    rw [list_sum_finRange, ← Finset.sum_mul, ← pow_succ']

private lemma list_sum_map_le {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

private lemma list_sum_map_eq_finset_sum {α : Type*} [DecidableEq α] (l : List α)
    (hl : l.Nodup) (f : α → ℝ) : (l.map f).sum = ∑ x ∈ l.toFinset, f x := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simpa using hl.1), ih hl.2]

private lemma harmonic_subset_le (s : Finset ℕ) (m : ℕ) (hm : 0 < m)
    (hcard : s.card = m) (hpos : ∀ x ∈ s, 1 ≤ x) :
    ∑ x ∈ s, (1 : ℝ) / x ≤ ∑ n ∈ Finset.Ico 1 (m + 1), (1 : ℝ) / n := by
  set u := Finset.Ico 1 (m + 1)
  have hu_card : u.card = m := by simp [u]
  have hdiff_card : (s \ u).card = (u \ s).card := by
    have h1 := Finset.card_sdiff_add_card_inter s u
    have h2 := Finset.card_sdiff_add_card_inter u s
    rw [Finset.inter_comm] at h2
    omega
  have hs_split : ∑ x ∈ s, (1 : ℝ) / x =
      ∑ x ∈ s ∩ u, (1 : ℝ) / x + ∑ x ∈ s \ u, (1 : ℝ) / x := by
    have hd : Disjoint (s ∩ u) (s \ u) := Finset.disjoint_left.mpr (by simp +contextual)
    have hu_eq : (s ∩ u) ∪ (s \ u) = s := by ext x; simp; tauto
    rw [← Finset.sum_union hd, hu_eq]
  have hu_split : ∑ y ∈ u, (1 : ℝ) / y =
      ∑ y ∈ u ∩ s, (1 : ℝ) / y + ∑ y ∈ u \ s, (1 : ℝ) / y := by
    have hd : Disjoint (u ∩ s) (u \ s) := Finset.disjoint_left.mpr (by simp +contextual)
    have hs_eq : (u ∩ s) ∪ (u \ s) = u := by ext y; simp; tauto
    rw [← Finset.sum_union hd, hs_eq]
  have hs_diff : ∑ x ∈ s \ u, (1 : ℝ) / x ≤ ((s \ u).card : ℝ) * (1 / m) := by
    calc ∑ x ∈ s \ u, (1 : ℝ) / x
        ≤ ∑ _x ∈ s \ u, (1 : ℝ) / m := by
          apply Finset.sum_le_sum
          intro x hx
          rw [Finset.mem_sdiff] at hx
          have hx1 := hpos x hx.1
          have hxm : m < x := by
            by_contra hle
            exact hx.2 (Finset.mem_Ico.mpr ⟨hx1, by omega⟩)
          exact one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast hxm.le)
      _ = ((s \ u).card : ℝ) * (1 / m) := by simp
  have hu_diff : ((u \ s).card : ℝ) * (1 / m) ≤ ∑ y ∈ u \ s, (1 : ℝ) / y := by
    calc ((u \ s).card : ℝ) * (1 / m)
        = ∑ _y ∈ u \ s, (1 : ℝ) / m := by simp
      _ ≤ ∑ y ∈ u \ s, (1 : ℝ) / y := by
          apply Finset.sum_le_sum
          intro y hy
          rw [Finset.mem_sdiff] at hy
          have hy_mem := Finset.mem_Ico.mp hy.1
          exact one_div_le_one_div_of_le (by exact_mod_cast hy_mem.1) (by exact_mod_cast (by omega : y ≤ m))
  rw [hdiff_card] at hs_diff
  rw [hs_split, hu_split, Finset.inter_comm s u]
  linarith [hs_diff, hu_diff]

theorem OMA.solution : type_of% @Erdos481.erdos_481 := by
  intro r a b ha hab
  have hr : 0 < r := by
    by_contra h
    have hr0 : r = 0 := by omega
    subst hr0
    simp at hab
    linarith
  by_contra hNodup
  push Not at hNodup
  set S : ℝ := ∑ i : Fin r, (1 : ℝ) / a i
  set ε : ℝ := S - 1
  have hε : 0 < ε := by linarith
  set B : ℕ := ∑ i : Fin r, b i
  obtain ⟨m0, hm0⟩ := exists_nat_gt (((3 * (r : ℝ) + 1) * (3 * (B : ℝ) + 1)) / ε ^ 3)
  set m : ℕ := max m0 1
  have hm_ge : 1 ≤ m := le_max_right m0 1
  have hm_gt : ((3 * (r : ℝ) + 1) * (3 * (B : ℝ) + 1)) / ε ^ 3 < (m : ℝ) :=
    lt_of_lt_of_le hm0 (by exact_mod_cast le_max_left m0 1)
  set k : ℕ := 3 * m
  have hlower : ((1 : ℝ) / (1 + (k : ℝ) * (B : ℝ))) * S ^ k ≤
      (((Erdos481.T a b)^[k] [1]).map (fun x : ℕ => (1 : ℝ) / (x : ℝ))).sum := by
    rw [← pairs_fst a b k, List.map_map, ← pairs_inv_sum a b k, ← list_sum_map_mul_left]
    apply list_sum_map_le
    intro p hp
    rcases pairs_bound a b ha k p hp with ⟨hp1, hp2, hpb⟩
    have hp1_pos : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast hp1
    have hpb_real : (p.1 : ℝ) ≤ (1 + (k : ℝ) * (B : ℝ)) * (p.2 : ℝ) := by
      exact_mod_cast hpb
    have hinv : (1 : ℝ) / ((1 + (k : ℝ) * (B : ℝ)) * (p.2 : ℝ)) ≤ (1 : ℝ) / (p.1 : ℝ) :=
      one_div_le_one_div_of_le hp1_pos hpb_real
    calc ((1 : ℝ) / (1 + (k : ℝ) * (B : ℝ))) * ((1 : ℝ) / (p.2 : ℝ))
        = (1 : ℝ) / ((1 + (k : ℝ) * (B : ℝ)) * (p.2 : ℝ)) := by
          rw [div_mul_div_comm, one_mul]
      _ ≤ (1 : ℝ) / (p.1 : ℝ) := hinv
  have hupper : (((Erdos481.T a b)^[k] [1]).map (fun x : ℕ => (1 : ℝ) / (x : ℝ))).sum ≤
      ((r * k : ℕ) : ℝ) + 1 := by
    have hk_nodup := hNodup k
    rw [list_sum_map_eq_finset_sum _ hk_nodup]
    have hcard : ((Erdos481.T a b)^[k] [1]).toFinset.card = r ^ k := by
      rw [List.toFinset_card_of_nodup hk_nodup, ← pairs_fst a b k, List.length_map, pairs_length]
    have hpos : ∀ x ∈ ((Erdos481.T a b)^[k] [1]).toFinset, 1 ≤ x := by
      intro x hx
      rw [List.mem_toFinset, ← pairs_fst a b k, List.mem_map] at hx
      rcases hx with ⟨p, hp, rfl⟩
      exact (pairs_bound a b ha k p hp).1
    have h1 := harmonic_subset_le ((Erdos481.T a b)^[k] [1]).toFinset (r ^ k)
      (pow_pos hr k) hcard hpos
    have harmonic_bound := harmonic_le_one_add_log (r ^ k)
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
      Nat.cast_pow, Real.log_pow] at harmonic_bound
    rw [Finset.Ico_add_one_right_eq_Icc] at h1
    simp only [one_div] at h1
    have hlog : Real.log (r : ℝ) ≤ r :=
      (Real.log_le_sub_one_of_pos (by exact_mod_cast hr)).trans (by linarith)
    push_cast
    simp only [one_div]
    nlinarith only [h1.trans harmonic_bound,
      mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg k)]
  have hS_upper : S ^ k ≤ (((r * k : ℕ) : ℝ) + 1) * (1 + (k : ℝ) * (B : ℝ)) := by
    have hden : (0 : ℝ) < 1 + (k : ℝ) * (B : ℝ) := by positivity
    have hcomb := hlower.trans hupper
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hden] at hcomb
    exact hcomb
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge
  have hpoly : (((r * k : ℕ) : ℝ) + 1) * (1 + (k : ℝ) * (B : ℝ)) ≤
      (3 * (r : ℝ) + 1) * (3 * (B : ℝ) + 1) * (m : ℝ) ^ 2 := by
    have h_rk : ((r * k : ℕ) : ℝ) + 1 ≤ (3 * (r : ℝ) + 1) * (m : ℝ) := by
      have : ((r * k : ℕ) : ℝ) = 3 * (r : ℝ) * (m : ℝ) := by
        simp only [k]; push_cast; ring
      nlinarith
    have h_kB : 1 + (k : ℝ) * (B : ℝ) ≤ (3 * (B : ℝ) + 1) * (m : ℝ) := by
      have : (k : ℝ) * (B : ℝ) = 3 * (B : ℝ) * (m : ℝ) := by
        simp only [k]; push_cast; ring
      nlinarith
    calc (((r * k : ℕ) : ℝ) + 1) * (1 + (k : ℝ) * (B : ℝ))
        ≤ ((3 * (r : ℝ) + 1) * (m : ℝ)) * ((3 * (B : ℝ) + 1) * (m : ℝ)) :=
          mul_le_mul h_rk h_kB (by positivity) (by positivity)
      _ = (3 * (r : ℝ) + 1) * (3 * (B : ℝ) + 1) * (m : ℝ) ^ 2 := by ring
  have hS_lower : (m : ℝ) ^ 3 * ε ^ 3 ≤ S ^ k := by
    have hb : 1 + (m : ℝ) * ε ≤ S ^ m := by
      have hS_eq : S = 1 + ε := by dsimp [ε]; ring
      rw [hS_eq]
      exact one_add_mul_le_pow (by linarith) m
    have hme : (m : ℝ) * ε ≤ S ^ m := by linarith
    have hpow : ((m : ℝ) * ε) ^ 3 ≤ (S ^ m) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hme 3
    calc (m : ℝ) ^ 3 * ε ^ 3 = ((m : ℝ) * ε) ^ 3 := by ring
      _ ≤ (S ^ m) ^ 3 := hpow
      _ = S ^ k := by simp only [k, mul_comm 3 m, pow_mul]
  have hlt : (3 * (r : ℝ) + 1) * (3 * (B : ℝ) + 1) * (m : ℝ) ^ 2 < (m : ℝ) ^ 3 * ε ^ 3 := by
    have hmul := (div_lt_iff₀ (by positivity : (0 : ℝ) < ε ^ 3)).mp hm_gt
    have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    calc (3 * (r : ℝ) + 1) * (3 * (B : ℝ) + 1) * (m : ℝ) ^ 2
        < ((m : ℝ) * ε ^ 3) * (m : ℝ) ^ 2 := mul_lt_mul_of_pos_right hmul hm2
      _ = (m : ℝ) ^ 3 * ε ^ 3 := by ring
  exact not_le_of_gt hlt (hS_lower.trans (hS_upper.trans hpoly))
