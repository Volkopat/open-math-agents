import OMAStatements.S_oeis_a204707
import Mathlib.Tactic

/-!
For common permanent 1, the row `101` can precede all four rows with middle bit
one. Each of those rows can precede `101` and one other middle-bit-one row.
This gives two scalar counts. The common permanent 2 contributes one array.

Original proof by @Volkopat.
-/
namespace OMA.P_oeis_a204707

open OMA.S_oeis_a204707
open scoped BigOperators

private def adj (r1 r2 : Bool × Bool × Bool) : Bool :=
  decide (blockPerm r1.1 r1.2.1 r2.1 r2.2.1 = 1 ∧ blockPerm r1.2.1 r1.2.2 r2.2.1 r2.2.2 = 1)

private def stepVec (v : Bool × Bool × Bool → ℤ) (r2 : Bool × Bool × Bool) : ℤ :=
  ∑ r1 : Bool × Bool × Bool, if adj r1 r2 then v r1 else 0

private def isValid1 (n : ℕ) (A : Fin (n + 1) × Fin 3 → Bool) : Prop :=
  ∀ (i : Fin n) (j : Fin 2),
    blockPerm (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩))
      (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩))
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩))
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)) = 1

private instance (n : ℕ) (A : Fin (n + 1) × Fin 3 → Bool) : Decidable (isValid1 n A) := by
  unfold isValid1; infer_instance

private def perm1Count (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 3 → Bool => isValid1 n A)).card

private lemma blockPerm_le_two (a b c d : Bool) : blockPerm a b c d ≤ 2 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma blockPerm_eq_two_iff (a b c d : Bool) :
    blockPerm a b c d = 2 ↔ a = true ∧ b = true ∧ c = true ∧ d = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

open scoped Classical in
private lemma A204707_eq_one_add_perm1Count (n : ℕ) (hn : 1 ≤ n) :
    A204707 n = 1 + perm1Count n := by
  unfold A204707 perm1Count
  set S1 := Finset.univ.filter (fun A : Fin (n + 1) × Fin 3 → Bool => isValid1 n A)
  set allTrue : Fin (n + 1) × Fin 3 → Bool := fun _ => true
  have hS_eq :
      (Finset.univ.filter (fun A : Fin (n + 1) × Fin 3 → Bool =>
        ∃ p : ℕ, p ≠ 0 ∧
          ∀ (i : Fin n) (j : Fin 2),
            blockPerm (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩))
              (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩))
              (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩))
              (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)) = p)) = insert allTrue S1 := by
    ext A
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, isValid1]
    constructor
    · rintro ⟨p, hp0, hA⟩
      have hle : p ≤ 2 := by
        have h0 := hA ⟨0, by omega⟩ ⟨0, by omega⟩
        rw [← h0]; exact blockPerm_le_two _ _ _ _
      have hp12 : p = 1 ∨ p = 2 := by omega
      rcases hp12 with rfl | rfl
      · exact Or.inr hA
      · left
        funext ⟨x, y⟩
        by_cases hx : x.1 < n
        · by_cases hy : y.1 < 2
          · have h := (blockPerm_eq_two_iff _ _ _ _).mp (hA ⟨x.1, hx⟩ ⟨y.1, hy⟩)
            exact h.1
          · have hy2 : y = ⟨2, by omega⟩ := Fin.ext (by have := y.isLt; dsimp; omega)
            rw [hy2]
            have h := (blockPerm_eq_two_iff _ _ _ _).mp (hA ⟨x.1, hx⟩ ⟨1, by omega⟩)
            exact h.2.1
        · have hx1 : x = ⟨n, by omega⟩ := Fin.ext (by have := x.isLt; dsimp; omega)
          rw [hx1]
          by_cases hy : y.1 < 2
          · have h := (blockPerm_eq_two_iff _ _ _ _).mp (hA ⟨n - 1, by omega⟩ ⟨y.1, hy⟩)
            have hidx : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ :=
              Fin.ext (by dsimp; omega)
            simpa [hidx] using h.2.2.1
          · have hy2 : y = ⟨2, by omega⟩ := Fin.ext (by have := y.isLt; dsimp; omega)
            rw [hy2]
            have h := (blockPerm_eq_two_iff _ _ _ _).mp (hA ⟨n - 1, by omega⟩ ⟨1, by omega⟩)
            have hidx : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = ⟨n, by omega⟩ :=
              Fin.ext (by dsimp; omega)
            simpa [hidx] using h.2.2.2
    · rintro (rfl | h1)
      · exact ⟨2, by omega, fun i j => by simp [allTrue, blockPerm]⟩
      · exact ⟨1, by omega, h1⟩
  have hnotmem : allTrue ∉ S1 := by
    rw [Finset.mem_filter]
    rintro ⟨_, h⟩
    have h0 := h ⟨0, by omega⟩ ⟨0, by omega⟩
    simp [allTrue, blockPerm] at h0
  have hcard_eq := congrArg Finset.card hS_eq
  rw [hcard_eq, Finset.card_insert_of_notMem hnotmem]
  omega

private def rowCount (n : ℕ) (r : Bool × Bool × Bool) : ℤ :=
  ∑ A : Fin (n + 1) × Fin 3 → Bool,
    if isValid1 n A ∧
       (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1),
        A (⟨n, Nat.lt_succ_self n⟩, 2)) = r
    then 1 else 0

private lemma perm1Count_eq_sum_rowCount (n : ℕ) :
    (perm1Count n : ℤ) = ∑ r : Bool × Bool × Bool, rowCount n r := by
  unfold perm1Count rowCount
  rw [Finset.sum_comm]
  have hcard : ∀ S : Finset (Fin (n + 1) × Fin 3 → Bool),
      (S.card : ℤ) = ∑ A : Fin (n + 1) × Fin 3 → Bool, if A ∈ S then (1 : ℤ) else 0 := by
    intro S; simp
  rw [hcard]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hA : isValid1 n A
  · rw [if_pos hA]
    rw [Finset.sum_eq_single
      (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1),
       A (⟨n, Nat.lt_succ_self n⟩, 2))]
    · simp [hA]
    · intro r _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  · rw [if_neg hA]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    simp [hA]

private lemma rowCount_zero (r : Bool × Bool × Bool) : rowCount 0 r = 1 := by
  unfold rowCount isValid1
  let A0 : Fin 1 × Fin 3 → Bool := fun p =>
    if p.2 = 0 then r.1 else if p.2 = 1 then r.2.1 else r.2.2
  rw [Finset.sum_eq_single A0]
  · simp [A0]
  · intro A _ hne
    rw [if_neg]
    rintro ⟨_, hr⟩
    apply hne
    funext ⟨i, j⟩
    fin_cases i; fin_cases j
    · exact congrArg Prod.fst hr
    · exact congrArg (fun x => x.2.1) hr
    · exact congrArg (fun x => x.2.2) hr
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma rowCount_succ (n : ℕ) (r : Bool × Bool × Bool) :
    rowCount (n + 1) r = stepVec (rowCount n) r := by
  let e : (Fin (n + 2) × Fin 3 → Bool) ≃
      ((Fin (n + 1) × Fin 3 → Bool) × (Bool × Bool × Bool)) :=
    { toFun := fun A =>
        (fun p => A (⟨p.1.1, by omega⟩, p.2),
         (A (⟨n + 1, Nat.lt_succ_self _⟩, 0), A (⟨n + 1, Nat.lt_succ_self _⟩, 1),
          A (⟨n + 1, Nat.lt_succ_self _⟩, 2)))
      invFun := fun ⟨A', r'⟩ p =>
        if h : p.1.1 < n + 1 then A' (⟨p.1.1, h⟩, p.2)
        else if p.2 = 0 then r'.1 else if p.2 = 1 then r'.2.1 else r'.2.2
      left_inv := fun A => by
        funext ⟨i, j⟩
        by_cases h : i.1 < n + 1
        · simp [h]
        · have hi : i = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
          subst hi; fin_cases j <;> simp
      right_inv := fun ⟨A', r'⟩ => by
        apply Prod.ext
        · funext ⟨i, j⟩; simp [i.isLt]
        · simp }
  have hiff : ∀ A : Fin (n + 2) × Fin 3 → Bool,
      (isValid1 (n + 1) A ∧
       (A (⟨n + 1, Nat.lt_succ_self _⟩, 0), A (⟨n + 1, Nat.lt_succ_self _⟩, 1),
        A (⟨n + 1, Nat.lt_succ_self _⟩, 2)) = r) ↔
      (isValid1 n (e A).1 ∧
       adj ((e A).1 (⟨n, Nat.lt_succ_self n⟩, 0), (e A).1 (⟨n, Nat.lt_succ_self n⟩, 1),
            (e A).1 (⟨n, Nat.lt_succ_self n⟩, 2)) (e A).2 = true ∧
       (e A).2 = r) := by
    intro A
    simp only [e, Equiv.coe_fn_mk, isValid1, adj, decide_eq_true_eq]
    constructor
    · rintro ⟨hA, hr⟩
      refine ⟨fun i j => hA ⟨i.1, by omega⟩ j,
        ⟨hA ⟨n, Nat.lt_succ_self n⟩ ⟨0, by omega⟩, hA ⟨n, Nat.lt_succ_self n⟩ ⟨1, by omega⟩⟩, hr⟩
    · rintro ⟨hA', ⟨hlast0, hlast1⟩, hr⟩
      refine ⟨fun i j => ?_, hr⟩
      by_cases hi : i.1 < n
      · exact hA' ⟨i.1, hi⟩ j
      · have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
        subst hieq
        fin_cases j
        · exact hlast0
        · exact hlast1
  unfold rowCount stepVec
  rw [Fintype.sum_equiv e _ (fun p =>
      if isValid1 n p.1 ∧
         adj (p.1 (⟨n, Nat.lt_succ_self n⟩, 0), p.1 (⟨n, Nat.lt_succ_self n⟩, 1),
              p.1 (⟨n, Nat.lt_succ_self n⟩, 2)) p.2 = true ∧
         p.2 = r then (1 : ℤ) else 0)
      (fun A => by simp only [hiff A])]
  rw [Fintype.sum_prod_type]
  have hr_sum : ∀ A' : Fin (n + 1) × Fin 3 → Bool,
      (∑ r' : Bool × Bool × Bool,
        if isValid1 n A' ∧
           adj (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1),
                A' (⟨n, Nat.lt_succ_self n⟩, 2)) r' = true ∧
           r' = r then (1 : ℤ) else 0) =
      if isValid1 n A' ∧
         adj (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1),
              A' (⟨n, Nat.lt_succ_self n⟩, 2)) r = true
      then (1 : ℤ) else 0 := by
    intro A'
    rw [Finset.sum_eq_single r]
    · simp
    · intro r' _ hne; simp [hne]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  simp_rw [hr_sum]
  symm
  trans ∑ r1 : Bool × Bool × Bool, ∑ A' : Fin (n + 1) × Fin 3 → Bool,
      if isValid1 n A' ∧
         (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1),
          A' (⟨n, Nat.lt_succ_self n⟩, 2)) = r1 ∧
         adj r1 r = true then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun r1 _ => ?_
    by_cases hadj : adj r1 r = true
    · simp [hadj]
    · simp [hadj]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A' _ => ?_
    rw [Finset.sum_eq_single
      (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1),
       A' (⟨n, Nat.lt_succ_self n⟩, 2))]
    · simp
    · intro r1 _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim

/-- Active rows have middle bit one, or are the single row 101. -/
private def classCount (u v : ℤ) (r : Bool × Bool × Bool) : ℤ :=
  if r.2.1 then v else if r.1 && r.2.2 then u else 0

private lemma class_step (u v : ℤ) (r : Bool × Bool × Bool) :
    stepVec (classCount u v) r = classCount (4 * v) (u + v) r := by
  simp only [stepVec, Fintype.sum_prod_type, Fintype.sum_bool]
  rcases r with ⟨a, b, c⟩
  cases a <;> cases b <;> cases c <;>
    simp [adj, blockPerm, classCount] <;> ring

private lemma class_sum (u v : ℤ) : (∑ r : Bool × Bool × Bool, classCount u v r) = u + 4 * v := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  simp [classCount]
  ring

private def counts : ℕ → ℤ × ℤ
  | 0 => (4, 2)
  | m + 1 => let c := counts m; (4 * c.2, c.1 + c.2)

private lemma rowCount_formula (m : ℕ) :
    rowCount (m + 1) = classCount (counts m).1 (counts m).2 := by
  induction m with
  | zero =>
    funext r
    rw [rowCount_succ, funext rowCount_zero]
    revert r
    decide
  | succ m ih =>
    funext r
    rw [rowCount_succ, ih, class_step]
    rfl

private lemma perm1Count_formula (m : ℕ) :
    (perm1Count (m + 1) : ℤ) = (counts m).1 + 4 * (counts m).2 := by
  rw [perm1Count_eq_sum_rowCount, rowCount_formula, class_sum]

private lemma perm1Count_rec (m : ℕ) :
    (perm1Count (m + 3) : ℤ) = perm1Count (m + 2) + 4 * perm1Count (m + 1) := by
  rw [perm1Count_formula (m + 2), perm1Count_formula (m + 1), perm1Count_formula m]
  simp only [counts]
  ring

private lemma perm1Count_small : perm1Count 1 = 12 ∧ perm1Count 2 = 32 ∧ perm1Count 3 = 80 := by
  have h1 := perm1Count_formula 0
  have h2 := perm1Count_formula 1
  have h3 := perm1Count_formula 2
  norm_num [counts] at h1 h2 h3
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩


private lemma A204707_small : A204707 1 = 13 ∧ A204707 2 = 33 ∧ A204707 3 = 81 := by
  obtain ⟨h1, h2, h3⟩ := perm1Count_small
  rw [A204707_eq_one_add_perm1Count 1 (by omega), A204707_eq_one_add_perm1Count 2 (by omega),
    A204707_eq_one_add_perm1Count 3 (by omega), h1, h2, h3]
  exact ⟨rfl, rfl, rfl⟩

private lemma A204707_rec (m : ℕ) :
    (A204707 (m + 4) : ℤ) =
      2 * A204707 (m + 3) + 3 * A204707 (m + 2) - 4 * A204707 (m + 1) := by
  have h (k : ℕ) : (A204707 (k + 1) : ℤ) = 1 + perm1Count (k + 1) := by
    exact_mod_cast A204707_eq_one_add_perm1Count (k + 1) (by omega)
  rw [h (m + 3), h (m + 2), h (m + 1), h m]
  linarith [perm1Count_rec m, perm1Count_rec (m + 1)]


private lemma A204707_gf :
    (1 - PowerSeries.X) * (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A204707 n : ℤ)) =
      PowerSeries.X * (13 + 7 * PowerSeries.X - 24 * PowerSeries.X ^ 2) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A204707 n : ℤ))
  have hlhs : (1 - PowerSeries.X) * (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 2 * (PowerSeries.X ^ 1 * F) -
        PowerSeries.C 3 * (PowerSeries.X ^ 2 * F) + PowerSeries.C 4 * (PowerSeries.X ^ 3 * F) := by
    simp only [map_ofNat]
    ring
  have hrhs : (PowerSeries.X : PowerSeries ℤ) *
        (13 + 7 * PowerSeries.X - 24 * PowerSeries.X ^ 2) =
      PowerSeries.C 13 * PowerSeries.X + PowerSeries.C 7 * PowerSeries.X ^ 2 -
      PowerSeries.C 24 * PowerSeries.X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3⟩ := A204707_small
  by_cases hn3 : n ≤ 3
  · interval_cases n <;> simp [F, h1, h2, h3]
  · simp (disch := omega) only [F, PowerSeries.coeff_mk, if_pos, if_neg,
      mul_zero, sub_zero, add_zero]
    have hrec := A204707_rec (n - 4)
    simp only [show n - 4 + 4 = n by omega, show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 2 = n - 2 by omega, show n - 4 + 1 = n - 3 by omega] at hrec
    linarith

private lemma A204707_binet (n : ℕ) (hn : 1 ≤ n) :
    (A204707 n : ℝ) =
      1 + ((2 : ℝ) ^ (-1 - (n : ℤ)) *
        ((1 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) +
         (1 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17))) / Real.sqrt 17 := by
  have hs_pos : (0 : ℝ) < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 17
  set r1 : ℝ := (1 + s) / 2
  set r2 : ℝ := (1 - s) / 2
  have hA : (A204707 n : ℝ) = 1 + (perm1Count n : ℝ) := by
    exact_mod_cast A204707_eq_one_add_perm1Count n hn
  rw [hA]
  congr 1
  have hbinet_eq : ∀ k : ℕ,
      ((2 : ℝ) ^ (-1 - (k : ℤ)) *
        ((1 - s) ^ k * (-19 + 5 * s) + (1 + s) ^ k * (19 + 5 * s))) / s =
      ((-19 + 5 * s) * r2 ^ k + (19 + 5 * s) * r1 ^ k) / (2 * s) := by
    intro k
    have hpow : (2 : ℝ) ^ (-1 - (k : ℤ)) = ((2 : ℝ) ^ k)⁻¹ / 2 := by
      rw [show (-1 : ℤ) - (k : ℤ) = -(k : ℤ) + (-1) by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        zpow_neg, zpow_natCast]
      norm_num; ring
    have hr1k : r1 ^ k = (1 + s) ^ k * ((2 : ℝ) ^ k)⁻¹ := by
      simp only [r1, div_eq_mul_inv, mul_pow, inv_pow]
    have hr2k : r2 ^ k = (1 - s) ^ k * ((2 : ℝ) ^ k)⁻¹ := by
      simp only [r2, div_eq_mul_inv, mul_pow, inv_pow]
    rw [hpow, hr1k, hr2k]; ring
  rw [hbinet_eq n]
  suffices h : ∀ k : ℕ,
      (perm1Count (k + 1) : ℝ) * (2 * s) =
        (-19 + 5 * s) * r2 ^ (k + 1) + (19 + 5 * s) * r1 ^ (k + 1) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [eq_div_iff (by positivity : (2 : ℝ) * s ≠ 0)]
    exact h k
  have hr1_sq : r1 ^ 2 = r1 + 4 := by
    have : r1 ^ 2 - (r1 + 4) = (s ^ 2 - 17) / 4 := by simp only [r1]; ring
    linarith [this, hs]
  have hr2_sq : r2 ^ 2 = r2 + 4 := by
    have : r2 ^ 2 - (r2 + 4) = (s ^ 2 - 17) / 4 := by simp only [r2]; ring
    linarith [this, hs]
  have root_rec (r : ℝ) (hr : r ^ 2 = r + 4) (m : ℕ) :
      r ^ (m + 3) = r ^ (m + 2) + 4 * r ^ (m + 1) := by
    calc
      _ = r ^ 2 * r ^ (m + 1) := by ring
      _ = (r + 4) * r ^ (m + 1) := by rw [hr]
      _ = _ := by ring
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    obtain ⟨h1, h2, _⟩ := perm1Count_small
    rcases k with _ | _ | m
    · rw [show (0 : ℕ) + 1 = 1 by rfl, h1]
      have : (-19 + 5 * s) * r2 ^ 1 + (19 + 5 * s) * r1 ^ 1 - (12 : ℝ) * (2 * s) = 0 := by
        simp only [r1, r2, pow_one]; ring
      norm_num; linarith
    · rw [show (1 : ℕ) + 1 = 2 by rfl, h2]
      have : (-19 + 5 * s) * r2 ^ 2 + (19 + 5 * s) * r1 ^ 2 - (32 : ℝ) * (2 * s) =
          (5 * (s ^ 2 - 17) / 2) * s := by
        simp only [r1, r2]; ring
      norm_num
      have h0 : (5 * (s ^ 2 - 17) / 2) * s = 0 := by rw [hs]; ring
      linarith
    · have hrec : (perm1Count (m + 3) : ℝ) = perm1Count (m + 2) + 4 * perm1Count (m + 1) := by
        exact_mod_cast perm1Count_rec m
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      rw [show m + 2 + 1 = m + 3 by omega, hrec, root_rec r1 hr1_sq, root_rec r2 hr2_sq]
      rw [show m + 1 + 1 = m + 2 by omega] at ih1
      linarith

end OMA.P_oeis_a204707

theorem OMA.solution : type_of% @OMA.S_oeis_a204707.main :=
  ⟨OMA.P_oeis_a204707.A204707_gf, OMA.P_oeis_a204707.A204707_binet⟩
