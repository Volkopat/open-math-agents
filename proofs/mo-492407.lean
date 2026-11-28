import OMAStatements.S_mo_492407

/-!
# Proof of MathOverflow 492407: Variational problem of minimizing sum of Frobenius norms

This file gives a self-contained elementary proof of `OMA.S_mo_492407.main`:
1. For rectangular full-rank `1 x 2` data `X₁ = X₂ = Y₂ = [1, 0]` and `Y₁ = [2, 0]`, every
   invertible pair `(A, B)` has strictly positive loss, while explicit shear inverse pairs
   achieve loss `δ^2` for arbitrarily small `δ > 0`.
2. When both `X₂` and `Y₂` admit left inverses, entrywise coercivity confines sublevel sets
   of the loss to a compact closed box in `Mat d d × Mat d d`, yielding a global minimizer.
   Algebraic elementary right variations `A * (1 + t • E)` and `(1 - s • E) * B` (with
   `s = t / (1 + t)` on the diagonal and `s = t` off the diagonal) derive the exact
   polynomial first-order optimality equations `critical` without calculus, characterizing
   all global minimizers as least-loss critical points.
3. For the scalar orthogonal restriction `a^2 = 1`, `a = 1` minimizes `scalarOrthogonalLoss`
   while violating the proposed Sylvester equation `1 * a + a * 1 = 1 * 2 + 2 * 1`.

Credit: @PrimordialAA
-/

namespace OMA.MO492407

open Matrix OMA.S_mo_492407

private lemma froSq_nonneg {m d : ℕ} (U : Mat m d) : 0 ≤ froSq U :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma froSq_eq_zero_iff {m d : ℕ} (U : Mat m d) : froSq U = 0 ↔ U = 0 := by
  constructor
  · intro h
    ext i j
    have hi : ∑ j' : Fin d, (U i j') ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
        Finset.sum_nonneg fun l _ => sq_nonneg (U k l)).mp h i (Finset.mem_univ i)
    have hij : (U i j) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun l _ => sq_nonneg (U i l)).mp hi j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hij
  · rintro rfl
    simp [froSq]

private lemma froSq_add_smul {m d : ℕ} (U V : Mat m d) (t : ℝ) :
    froSq (U + t • V) = froSq U + 2 * t * froInner U V + t ^ 2 * froSq V := by
  simp only [froSq, froInner, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have hterm : ∀ i j, (U i j + t * V i j) ^ 2 =
      (U i j) ^ 2 + 2 * t * (U i j * V i j) + t ^ 2 * (V i j) ^ 2 := fun i j => by ring
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.mul_sum]

private lemma froSq_sub_smul {m d : ℕ} (U V : Mat m d) (t : ℝ) :
    froSq (U - t • V) = froSq U - 2 * t * froInner U V + t ^ 2 * froSq V := by
  have h : U - t • V = U + (-t) • V := by ext i j; simp; ring
  rw [h, froSq_add_smul]
  ring

private lemma rank_one_of_ne_zero (M : Mat 1 2) (h0 : M 0 0 ≠ 0) : M.rank = 1 := by
  have hle : M.rank ≤ 1 := by
    calc M.rank = Module.finrank ℝ (LinearMap.range M.mulVecLin) := rfl
      _ ≤ Module.finrank ℝ (Fin 1 → ℝ) := Submodule.finrank_le _
      _ = 1 := by simp
  have hpos : 0 < M.rank := by
    rw [Matrix.rank, Module.finrank_pos_iff_exists_ne_zero]
    refine ⟨⟨M.mulVecLin (Pi.single 0 1), ⟨Pi.single 0 1, rfl⟩⟩, ?_⟩
    intro hzero
    have hval : (M.mulVecLin (Pi.single 0 1)) 0 = 0 := by
      have := congrArg (fun v => v.val 0) hzero
      exact this
    simp [Matrix.mulVec, dotProduct, Pi.single_apply] at hval
    exact h0 hval
  omega

private lemma part1 :
    ∃ X₁ X₂ Y₁ Y₂ : Mat 1 2, X₁.rank = 1 ∧ X₂.rank = 1 ∧ Y₁.rank = 1 ∧ Y₂.rank = 1 ∧
      (∀ A B, inversePair A B → 0 < loss X₁ X₂ Y₁ Y₂ A B) ∧
      ∀ ε : ℝ, 0 < ε → ∃ A B, inversePair A B ∧ loss X₁ X₂ Y₁ Y₂ A B < ε := by
  let X₁ : Mat 1 2 := !![1, 0]
  let Y₁ : Mat 1 2 := !![2, 0]
  refine ⟨X₁, X₁, Y₁, X₁,
    rank_one_of_ne_zero X₁ (by simp [X₁]),
    rank_one_of_ne_zero X₁ (by simp [X₁]),
    rank_one_of_ne_zero Y₁ (by simp [Y₁]),
    rank_one_of_ne_zero X₁ (by simp [X₁]), ?_, ?_⟩
  · intro A B hAB
    have hnn : 0 ≤ loss X₁ X₁ Y₁ X₁ A B := by
      unfold loss
      linarith [froSq_nonneg (X₁ - X₁ * A), froSq_nonneg (Y₁ - X₁ * B)]
    rcases lt_or_eq_of_le hnn with hlt | heq
    · exact hlt
    · exfalso
      have hsum : froSq (X₁ - X₁ * A) + froSq (Y₁ - X₁ * B) = 0 := by
        unfold loss at heq; linarith
      have h1 : froSq (X₁ - X₁ * A) = 0 := by
        linarith [froSq_nonneg (X₁ - X₁ * A), froSq_nonneg (Y₁ - X₁ * B)]
      have h2 : froSq (Y₁ - X₁ * B) = 0 := by
        linarith [froSq_nonneg (X₁ - X₁ * A), froSq_nonneg (Y₁ - X₁ * B)]
      have hXA : X₁ * A = X₁ := (sub_eq_zero.mp ((froSq_eq_zero_iff _).mp h1)).symm
      have hXB : X₁ * B = Y₁ := (sub_eq_zero.mp ((froSq_eq_zero_iff _).mp h2)).symm
      have hXY : X₁ = Y₁ := by
        calc X₁ = X₁ * 1 := (Matrix.mul_one X₁).symm
          _ = X₁ * (A * B) := by rw [hAB.1]
          _ = (X₁ * A) * B := (Matrix.mul_assoc X₁ A B).symm
          _ = X₁ * B := by rw [hXA]
          _ = Y₁ := hXB
      have h00 := congrArg (fun M : Mat 1 2 => M 0 0) hXY
      simp [X₁, Y₁] at h00
  · intro ε hε
    let δ : ℝ := min 1 (ε / 2)
    have hδpos : 0 < δ := lt_min one_pos (half_pos hε)
    have hδne : δ ≠ 0 := ne_of_gt hδpos
    let A : Mat 2 2 := !![1, δ; δ⁻¹, 2]
    let B : Mat 2 2 := !![2, -δ; -δ⁻¹, 1]
    refine ⟨A, B, ?_, ?_⟩
    · constructor
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_apply, Fin.sum_univ_two] <;>
          field_simp [hδne] <;> ring
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [A, B, Matrix.mul_apply, Fin.sum_univ_two] <;>
          field_simp [hδne] <;> ring
    · have hloss : loss X₁ X₁ Y₁ X₁ A B = δ ^ 2 := by
        unfold loss froSq
        simp [X₁, Y₁, A, B, Fin.sum_univ_two]
      rw [hloss]
      have hδ1 : δ ≤ 1 := min_le_left _ _
      have hδ2 : δ ≤ ε / 2 := min_le_right _ _
      nlinarith

private lemma abs_le_sq_add_one (x : ℝ) : |x| ≤ x ^ 2 + 1 := by
  rcases le_or_gt |x| 1 with h | h
  · linarith [sq_nonneg x]
  · have : |x| ≤ |x| ^ 2 := by nlinarith
    rw [sq_abs] at this
    linarith

private lemma entry_sq_le_froSq {m d : ℕ} (U : Mat m d) (i : Fin m) (j : Fin d) :
    (U i j) ^ 2 ≤ froSq U := by
  have h1 : (U i j) ^ 2 ≤ ∑ j' : Fin d, (U i j') ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (U i l)) (Finset.mem_univ j)
  have h2 : ∑ j' : Fin d, (U i j') ^ 2 ≤ froSq U :=
    Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg (U k l))
      (Finset.mem_univ i)
  linarith

private lemma entry_bound_of_left_inv {m d : ℕ} {X₁ X₂ : Mat m d} {L : Mat d m}
    (hL : L * X₂ = 1) {A : Mat d d} {C : ℝ} (hC : froSq (X₁ - X₂ * A) ≤ C) :
    ∀ i j : Fin d, |A i j| ≤
      ∑ i' : Fin d, ∑ j' : Fin d, ∑ k : Fin m, |L i' k| * (|X₁ k j'| + C + 1) := by
  intro i j
  have hA : A = L * (X₂ * A) := by
    rw [← Matrix.mul_assoc, hL, Matrix.one_mul]
  have hterm : ∀ k : Fin m, |L i k * (X₂ * A) k j| ≤ |L i k| * (|X₁ k j| + C + 1) := by
    intro k
    rw [abs_mul]
    have hdiff : |(X₁ - X₂ * A) k j| ≤ C + 1 := by
      have hsq := entry_sq_le_froSq (X₁ - X₂ * A) k j
      have habs := abs_le_sq_add_one ((X₁ - X₂ * A) k j)
      linarith
    have hXA : |(X₂ * A) k j| ≤ |X₁ k j| + C + 1 := by
      have htri : (X₂ * A) k j = X₁ k j - (X₁ - X₂ * A) k j := by simp
      rw [htri]
      have := abs_sub (X₁ k j) ((X₁ - X₂ * A) k j)
      linarith
    exact mul_le_mul_of_nonneg_left hXA (abs_nonneg _)
  have h1 : |A i j| ≤ ∑ k : Fin m, |L i k| * (|X₁ k j| + C + 1) := by
    calc |A i j| = |(L * (X₂ * A)) i j| := by rw [← hA]
      _ = |∑ k : Fin m, L i k * (X₂ * A) k j| := by simp [Matrix.mul_apply]
      _ ≤ ∑ k : Fin m, |L i k * (X₂ * A) k j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin m, |L i k| * (|X₁ k j| + C + 1) := Finset.sum_le_sum fun k _ => hterm k
  have hnn : ∀ i' j' : Fin d,
      0 ≤ ∑ k : Fin m, |L i' k| * (|X₁ k j'| + C + 1) := fun i' j' =>
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _)
      (by linarith [abs_nonneg (X₁ k j'), froSq_nonneg (X₁ - X₂ * A)])
  have h2 : ∑ k : Fin m, |L i k| * (|X₁ k j| + C + 1) ≤
      ∑ j' : Fin d, ∑ k : Fin m, |L i k| * (|X₁ k j'| + C + 1) :=
    Finset.single_le_sum (fun j' _ => hnn i j') (Finset.mem_univ j)
  have h3 : ∑ j' : Fin d, ∑ k : Fin m, |L i k| * (|X₁ k j'| + C + 1) ≤
      ∑ i' : Fin d, ∑ j' : Fin d, ∑ k : Fin m, |L i' k| * (|X₁ k j'| + C + 1) :=
    Finset.single_le_sum (fun i' _ => Finset.sum_nonneg fun j' _ => hnn i' j') (Finset.mem_univ i)
  linarith

private lemma continuous_mat_mul {m k n : ℕ} :
    Continuous (fun p : Mat m k × Mat k n => p.1 * p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply]
  refine continuous_finsetSum _ fun l _ => Continuous.mul ?_ ?_
  · exact ((continuous_apply l).comp ((continuous_apply i).comp continuous_fst))
  · exact ((continuous_apply j).comp ((continuous_apply l).comp continuous_snd))

private lemma continuous_froSq {m d : ℕ} : Continuous (froSq : Mat m d → ℝ) := by
  unfold froSq
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp (continuous_apply i)).pow 2

private lemma continuous_loss {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d) :
    Continuous (fun p : Mat d d × Mat d d => loss X₁ X₂ Y₁ Y₂ p.1 p.2) := by
  unfold loss
  have h1 : Continuous (fun p : Mat d d × Mat d d => X₁ - X₂ * p.1) :=
    continuous_const.sub (continuous_mat_mul.comp (continuous_const.prodMk continuous_fst))
  have h2 : Continuous (fun p : Mat d d × Mat d d => Y₁ - Y₂ * p.2) :=
    continuous_const.sub (continuous_mat_mul.comp (continuous_const.prodMk continuous_snd))
  exact ((continuous_froSq.comp h1).add (continuous_froSq.comp h2)).div_const 2

private lemma isClosed_inversePair (d : ℕ) :
    IsClosed {p : Mat d d × Mat d d | inversePair p.1 p.2} := by
  have h1 : IsClosed {p : Mat d d × Mat d d | p.1 * p.2 = 1} :=
    isClosed_eq continuous_mat_mul continuous_const
  have h2 : IsClosed {p : Mat d d × Mat d d | p.2 * p.1 = 1} :=
    isClosed_eq (continuous_mat_mul.comp continuous_swap) continuous_const
  exact h1.inter h2

private def matBox (d : ℕ) (R : ℝ) : Set (Mat d d) :=
  {A : Mat d d | ∀ i j : Fin d, A i j ∈ Set.Icc (-R) R}

private lemma isCompact_matBox (d : ℕ) (R : ℝ) : IsCompact (matBox d R) := by
  have hEq : matBox d R =
      Set.pi Set.univ (fun _ : Fin d => Set.pi Set.univ (fun _ : Fin d => Set.Icc (-R) R)) := by
    ext A
    exact ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
  rw [hEq]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc

private lemma exists_optimal_of_bound {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d)
    (R : ℝ) (h1R : 1 ≤ R)
    (hbound : ∀ U V, inversePair U V → loss X₁ X₂ Y₁ Y₂ U V ≤ loss X₁ X₂ Y₁ Y₂ 1 1 →
      U ∈ matBox d R ∧ V ∈ matBox d R) :
    ∃ A B, optimal X₁ X₂ Y₁ Y₂ A B := by
  have hKcomp : IsCompact ((matBox d R ×ˢ matBox d R) ∩ {p | inversePair p.1 p.2}) :=
    ((isCompact_matBox d R).prod (isCompact_matBox d R)).inter_right (isClosed_inversePair d)
  have h1Box : (1 : Mat d d) ∈ matBox d R := by
    intro i j
    simp only [Matrix.one_apply, Set.mem_Icc]
    split_ifs <;> constructor <;> linarith
  have h1K : ((1 : Mat d d), (1 : Mat d d)) ∈
      (matBox d R ×ˢ matBox d R) ∩ {p | inversePair p.1 p.2} :=
    ⟨⟨h1Box, h1Box⟩, ⟨Matrix.one_mul 1, Matrix.one_mul 1⟩⟩
  obtain ⟨⟨A₀, B₀⟩, hAB₀K, hmin⟩ :=
    hKcomp.exists_isMinOn ⟨(1, 1), h1K⟩ (continuous_loss X₁ X₂ Y₁ Y₂).continuousOn
  rw [isMinOn_iff] at hmin
  refine ⟨A₀, B₀, hAB₀K.2, fun U V hUV => ?_⟩
  by_cases hle : loss X₁ X₂ Y₁ Y₂ U V ≤ loss X₁ X₂ Y₁ Y₂ 1 1
  · rcases hbound U V hUV hle with ⟨hU, hV⟩
    exact hmin (U, V) ⟨⟨hU, hV⟩, hUV⟩
  · exact le_trans (hmin (1, 1) h1K) (le_of_not_ge hle)

private lemma exists_optimal {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d)
    (hX₂ : ∃ L : Mat d m, L * X₂ = 1) (hY₂ : ∃ L : Mat d n, L * Y₂ = 1) :
    ∃ A B, optimal X₁ X₂ Y₁ Y₂ A B := by
  rcases hX₂ with ⟨L₁, hL₁⟩
  rcases hY₂ with ⟨L₂, hL₂⟩
  let C₀ : ℝ := loss X₁ X₂ Y₁ Y₂ 1 1
  let R₁ : ℝ := ∑ i' : Fin d, ∑ j' : Fin d, ∑ k : Fin m, |L₁ i' k| * (|X₁ k j'| + 2 * C₀ + 1)
  let R₂ : ℝ := ∑ i' : Fin d, ∑ j' : Fin d, ∑ k : Fin n, |L₂ i' k| * (|Y₁ k j'| + 2 * C₀ + 1)
  let R : ℝ := max (max R₁ R₂) 1
  have hR1 : R₁ ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hR2 : R₂ ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  refine exists_optimal_of_bound X₁ X₂ Y₁ Y₂ R (le_max_right _ _) fun U V _ hle => ?_
  have hfx : froSq (X₁ - X₂ * U) ≤ 2 * C₀ := by
    have hlossU : (froSq (X₁ - X₂ * U) + froSq (Y₁ - Y₂ * V)) / 2 ≤ C₀ := hle
    have hnn := froSq_nonneg (Y₁ - Y₂ * V)
    linarith only [hlossU, hnn]
  have hfy : froSq (Y₁ - Y₂ * V) ≤ 2 * C₀ := by
    have hlossU : (froSq (X₁ - X₂ * U) + froSq (Y₁ - Y₂ * V)) / 2 ≤ C₀ := hle
    have hnn := froSq_nonneg (X₁ - X₂ * U)
    linarith only [hlossU, hnn]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · have hb := abs_le.mp (entry_bound_of_left_inv hL₁ hfx i j)
    exact ⟨le_trans (neg_le_neg hR1) hb.1, le_trans hb.2 hR1⟩
  · have hb := abs_le.mp (entry_bound_of_left_inv hL₂ hfy i j)
    exact ⟨le_trans (neg_le_neg hR2) hb.1, le_trans hb.2 hR2⟩

private lemma single_mul_single_self {d : ℕ} (i j : Fin d) :
    Matrix.single i j (1 : ℝ) * Matrix.single i j (1 : ℝ) =
      if i = j then Matrix.single i j (1 : ℝ) else 0 := by
  ext r c
  simp only [Matrix.mul_apply, Matrix.single_apply]
  split_ifs with hij
  · subst hij
    rw [Finset.sum_eq_single i]
    · simp only [Matrix.single_apply]
      by_cases hri : i = r <;> by_cases hci : i = c <;> simp [hri, hci]
    · intro b _ hb
      have : ¬ (i = b) := hb.symm
      simp [this]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  · simp only [Matrix.zero_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hbi : i = b
    · subst hbi
      have : ¬ (j = i) := fun h => hij h.symm
      simp [this]
    · simp [hbi]

private lemma diag_critical_eq {α β p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hineq : ∀ t : ℝ, 1 + t ≠ 0 →
      0 ≤ -2 * t * α + t ^ 2 * p + 2 * (t / (1 + t)) * β + (t / (1 + t)) ^ 2 * q) :
    α = β := by
  have hle1 : α ≤ β := by
    by_contra hlt
    push Not at hlt
    let M : ℝ := 2 * |β| + p + 4 * q + 1
    have hM : 0 < M := by positivity
    let t : ℝ := min (1 / 2) ((α - β) / M)
    have htpos : 0 < t := lt_min (by norm_num) (div_pos (by linarith) hM)
    have ht1 : t ≤ 1 / 2 := min_le_left _ _
    have ht2 : t ≤ (α - β) / M := min_le_right _ _
    have h1t : 0 < 1 + t := by linarith
    have hspec := hineq t (ne_of_gt h1t)
    have hdiv : 1 ≤ 1 + t := by linarith
    have hfrac1 : 2 * (t / (1 + t)) * β ≤ 2 * t * β + 2 * t ^ 2 * |β| := by
      have hbound : |-(t ^ 2 / (1 + t)) * β| ≤ t ^ 2 * |β| := by
        rw [abs_mul, abs_neg, abs_div, abs_of_nonneg (sq_nonneg t), abs_of_pos h1t]
        have : t ^ 2 / (1 + t) ≤ t ^ 2 := div_le_self (sq_nonneg t) hdiv
        exact mul_le_mul_of_nonneg_right this (abs_nonneg β)
      have := (abs_le.mp hbound).2
      have hmul : 2 * (t / (1 + t)) * β - 2 * t * β = 2 * (-(t ^ 2 / (1 + t)) * β) := by
        field_simp [ne_of_gt h1t]; ring
      linarith
    have hfrac2 : (t / (1 + t)) ^ 2 * q ≤ 4 * t ^ 2 * q := by
      have hsq : (t / (1 + t)) ^ 2 ≤ t ^ 2 := by
        rw [div_pow]
        exact div_le_self (sq_nonneg t) (by nlinarith)
      nlinarith
    have hcomb : 0 ≤ t * (-2 * (α - β) + t * M) := by
      have : -2 * t * α + t ^ 2 * p + 2 * (t / (1 + t)) * β + (t / (1 + t)) ^ 2 * q ≤
          t * (-2 * (α - β) + t * M) := by
        dsimp [M]; nlinarith
      linarith
    have hneg : -2 * (α - β) + t * M < 0 := by
      have : t * M ≤ α - β := (le_div_iff₀ hM).mp ht2
      linarith
    nlinarith
  have hle2 : β ≤ α := by
    by_contra hlt
    push Not at hlt
    let M : ℝ := 4 * |β| + p + 4 * q + 1
    have hM : 0 < M := by positivity
    let u : ℝ := min (1 / 2) ((β - α) / M)
    have hupos : 0 < u := lt_min (by norm_num) (div_pos (by linarith) hM)
    have hu1 : u ≤ 1 / 2 := min_le_left _ _
    have hu2 : u ≤ (β - α) / M := min_le_right _ _
    have h1u : 1 / 2 ≤ 1 - u := by linarith
    have hspec := hineq (-u) (by linarith)
    have hfrac1 : 2 * (-u / (1 + -u)) * β ≤ -2 * u * β + 4 * u ^ 2 * |β| := by
      have h1ne : 1 - u ≠ 0 := by linarith
      have hbound : |-(u ^ 2 / (1 - u)) * β| ≤ 2 * u ^ 2 * |β| := by
        rw [abs_mul, abs_neg, abs_div, abs_of_nonneg (sq_nonneg u), abs_of_pos (by linarith : 0 < 1 - u)]
        have : u ^ 2 / (1 - u) ≤ 2 * u ^ 2 := by
          rw [div_le_iff₀ (by linarith : 0 < 1 - u)]; nlinarith
        exact mul_le_mul_of_nonneg_right this (abs_nonneg β)
      have := (abs_le.mp hbound).2
      have hmul : 2 * (-u / (1 + -u)) * β - (-2 * u * β) = 2 * (-(u ^ 2 / (1 - u)) * β) := by
        have : 1 + -u = 1 - u := by ring
        rw [this]; field_simp [h1ne]; ring
      linarith
    have hfrac2 : (-u / (1 + -u)) ^ 2 * q ≤ 4 * u ^ 2 * q := by
      have hsq : (-u / (1 + -u)) ^ 2 ≤ 4 * u ^ 2 := by
        have : 1 + -u = 1 - u := by ring
        have hq4 : (1 / 4 : ℝ) ≤ (1 - u) ^ 2 := by nlinarith
        rw [this, div_pow, div_le_iff₀ (by linarith : 0 < (1 - u) ^ 2)]
        nlinarith [sq_nonneg u]
      nlinarith
    have hcomb : 0 ≤ u * (-2 * (β - α) + u * M) := by
      have : -2 * (-u) * α + (-u) ^ 2 * p + 2 * (-u / (1 + -u)) * β + (-u / (1 + -u)) ^ 2 * q ≤
          u * (-2 * (β - α) + u * M) := by
        dsimp [M]; nlinarith
      linarith
    have hneg : -2 * (β - α) + u * M < 0 := by
      have : u * M ≤ β - α := (le_div_iff₀ hM).mp hu2
      linarith
    nlinarith
  linarith

private lemma optimal_imp_critical_diag {m n d : ℕ} {X₁ X₂ : Mat m d} {Y₁ Y₂ : Mat n d}
    {A B : Mat d d} (hopt : optimal X₁ X₂ Y₁ Y₂ A B) (i : Fin d) :
    froInner (X₁ - X₂ * A) ((X₂ * A) * Matrix.single i i (1 : ℝ)) =
    froInner (Y₁ - Y₂ * B) ((Y₂ * Matrix.single i i (1 : ℝ)) * B) := by
  let E : Mat d d := Matrix.single i i (1 : ℝ)
  have hEE : E * E = E := by
    have := single_mul_single_self i i
    simp [E] at this ⊢
  refine diag_critical_eq (froSq_nonneg ((X₂ * A) * E)) (froSq_nonneg ((Y₂ * E) * B)) ?_
  intro t ht
  let s : ℝ := t / (1 + t)
  have hs : t - s - t * s = 0 := by
    dsimp [s]; field_simp [ht]; ring
  let U : Mat d d := A * (1 + t • E)
  let V : Mat d d := (1 - s • E) * B
  have h12 : (1 + t • E) * (1 - s • E) = 1 := by
    calc (1 + t • E) * (1 - s • E)
        = 1 - s • E + t • E - (t * s) • (E * E) := by
            simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
              Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, mul_comm s t]
            abel
      _ = 1 + (t - s - t * s) • E := by
            rw [hEE, sub_smul, sub_smul]; abel
      _ = 1 := by rw [hs, zero_smul, add_zero]
  have h21 : (1 - s • E) * (1 + t • E) = 1 := by
    calc (1 - s • E) * (1 + t • E)
        = 1 + t • E - s • E - (s * t) • (E * E) := by
            simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
              Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul, mul_comm t s]
            abel
      _ = 1 + (t - s - t * s) • E := by
            rw [hEE, mul_comm s t, sub_smul, sub_smul]; abel
      _ = 1 := by rw [hs, zero_smul, add_zero]
  have hUV : inversePair U V := by
    constructor
    · calc U * V = A * ((1 + t • E) * (1 - s • E)) * B := by simp only [U, V, Matrix.mul_assoc]
        _ = A * B := by rw [h12, Matrix.mul_one]
        _ = 1 := hopt.1.1
    · calc V * U = (1 - s • E) * (B * A) * (1 + t • E) := by simp only [U, V, Matrix.mul_assoc]
        _ = (1 - s • E) * (1 + t • E) := by rw [hopt.1.2, Matrix.mul_one]
        _ = 1 := h21
  have hXU : X₁ - X₂ * U = (X₁ - X₂ * A) - t • ((X₂ * A) * E) := by
    simp only [U, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_assoc]
    abel
  have hYV : Y₁ - Y₂ * V = (Y₁ - Y₂ * B) + s • ((Y₂ * E) * B) := by
    simp only [V, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.mul_smul, Matrix.mul_assoc]
    abel
  have hle := hopt.2 U V hUV
  unfold loss at hle
  rw [hXU, hYV, froSq_sub_smul, froSq_add_smul] at hle
  dsimp [s] at hle ⊢
  linarith

private lemma optimal_imp_critical_offdiag {m n d : ℕ} {X₁ X₂ : Mat m d} {Y₁ Y₂ : Mat n d}
    {A B : Mat d d} (hopt : optimal X₁ X₂ Y₁ Y₂ A B) {i j : Fin d} (hij : i ≠ j) :
    froInner (X₁ - X₂ * A) ((X₂ * A) * Matrix.single i j (1 : ℝ)) =
    froInner (Y₁ - Y₂ * B) ((Y₂ * Matrix.single i j (1 : ℝ)) * B) := by
  let E : Mat d d := Matrix.single i j (1 : ℝ)
  let α : ℝ := froInner (X₁ - X₂ * A) ((X₂ * A) * E)
  let β : ℝ := froInner (Y₁ - Y₂ * B) ((Y₂ * E) * B)
  let p : ℝ := froSq ((X₂ * A) * E)
  let q : ℝ := froSq ((Y₂ * E) * B)
  have hp : 0 ≤ p := froSq_nonneg _
  have hq : 0 ≤ q := froSq_nonneg _
  have hEE : E * E = 0 := by
    have := single_mul_single_self i j
    simpa [E, hij] using this
  have hquad : ∀ t : ℝ, 0 ≤ 2 * t * (β - α) + t ^ 2 * (p + q) := by
    intro t
    let U : Mat d d := A * (1 + t • E)
    let V : Mat d d := (1 - t • E) * B
    have h12 : (1 + t • E) * (1 - t • E) = 1 := by
      calc (1 + t • E) * (1 - t • E)
          = 1 - t • E + t • E - (t * t) • (E * E) := by
              simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
                Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]; abel
        _ = 1 := by rw [hEE, smul_zero]; abel
    have h21 : (1 - t • E) * (1 + t • E) = 1 := by
      calc (1 - t • E) * (1 + t • E)
          = 1 + t • E - t • E - (t * t) • (E * E) := by
              simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
                Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]; abel
        _ = 1 := by rw [hEE, smul_zero]; abel
    have hUV : inversePair U V := by
      constructor
      · calc U * V = A * ((1 + t • E) * (1 - t • E)) * B := by simp only [U, V, Matrix.mul_assoc]
          _ = A * B := by rw [h12, Matrix.mul_one]
          _ = 1 := hopt.1.1
      · calc V * U = (1 - t • E) * (B * A) * (1 + t • E) := by simp only [U, V, Matrix.mul_assoc]
          _ = (1 - t • E) * (1 + t • E) := by rw [hopt.1.2, Matrix.mul_one]
          _ = 1 := h21
    have hXU : X₁ - X₂ * U = (X₁ - X₂ * A) - t • ((X₂ * A) * E) := by
      simp only [U, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_assoc]
      abel
    have hYV : Y₁ - Y₂ * V = (Y₁ - Y₂ * B) + t • ((Y₂ * E) * B) := by
      simp only [V, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub,
        Matrix.mul_smul, Matrix.mul_assoc]
      abel
    have hle := hopt.2 U V hUV
    unfold loss at hle
    rw [hXU, hYV, froSq_sub_smul, froSq_add_smul] at hle
    dsimp [α, β, p, q] at hle ⊢
    linarith
  change α = β
  by_contra hne
  have hdiff : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  let M : ℝ := p + q + 1
  have hM : 0 < M := by linarith
  have hspec := hquad (-(β - α) / M)
  have hsimp : 2 * (-(β - α) / M) * (β - α) + (-(β - α) / M) ^ 2 * (p + q) =
      -((β - α) ^ 2 * (p + q + 2)) / M ^ 2 := by
    dsimp [M]; field_simp [ne_of_gt hM]; ring
  rw [hsimp] at hspec
  have hnum : 0 < (β - α) ^ 2 * (p + q + 2) :=
    mul_pos (sq_pos_of_ne_zero hdiff) (by linarith)
  have hden : 0 < M ^ 2 := sq_pos_of_pos hM
  have : -((β - α) ^ 2 * (p + q + 2)) / M ^ 2 < 0 := by
    rw [neg_div]
    exact neg_lt_zero.mpr (div_pos hnum hden)
  linarith

private lemma optimal_imp_critical {m n d : ℕ} {X₁ X₂ : Mat m d} {Y₁ Y₂ : Mat n d}
    {A B : Mat d d} (hopt : optimal X₁ X₂ Y₁ Y₂ A B) :
    critical X₁ X₂ Y₁ Y₂ A B := by
  refine ⟨hopt.1, fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    exact optimal_imp_critical_diag hopt i
  · exact optimal_imp_critical_offdiag hopt hij

private lemma part2 {m n d : ℕ} (X₁ X₂ : Mat m d) (Y₁ Y₂ : Mat n d)
    (hX₂ : ∃ L : Mat d m, L * X₂ = 1) (hY₂ : ∃ L : Mat d n, L * Y₂ = 1) :
    (∃ A B, optimal X₁ X₂ Y₁ Y₂ A B) ∧
    ∀ A B, optimal X₁ X₂ Y₁ Y₂ A B ↔ critical X₁ X₂ Y₁ Y₂ A B ∧
      ∀ U V, critical X₁ X₂ Y₁ Y₂ U V → loss X₁ X₂ Y₁ Y₂ A B ≤ loss X₁ X₂ Y₁ Y₂ U V := by
  have hex := exists_optimal X₁ X₂ Y₁ Y₂ hX₂ hY₂
  refine ⟨hex, fun A B => ⟨fun hopt => ⟨optimal_imp_critical hopt, fun U V hU => hopt.2 U V hU.1⟩, ?_⟩⟩
  rintro ⟨hcrit, hle⟩
  rcases hex with ⟨A₀, B₀, hopt₀⟩
  have hcrit₀ := optimal_imp_critical hopt₀
  refine ⟨hcrit.1, fun U V hUV => le_trans (hle A₀ B₀ hcrit₀) (hopt₀.2 U V hUV)⟩

private lemma part3 :
    ∃ a : ℝ, a ^ 2 = 1 ∧ (∀ b : ℝ, b ^ 2 = 1 → scalarOrthogonalLoss a ≤ scalarOrthogonalLoss b) ∧
      1 * a + a * 1 ≠ 1 * 2 + 2 * 1 := by
  refine ⟨1, by norm_num, fun b hb => ?_, by norm_num⟩
  have hfac : (b - 1) * (b + 1) = 0 := by linarith
  rcases mul_eq_zero.mp hfac with h1 | h2
  · have : b = 1 := by linarith
    subst this; exact le_rfl
  · have : b = -1 := by linarith
    subst this; unfold scalarOrthogonalLoss; norm_num

end OMA.MO492407

theorem OMA.solution : type_of% @OMA.S_mo_492407.main :=
  ⟨OMA.MO492407.part1,
   fun X₁ X₂ Y₁ Y₂ hX₂ hY₂ => OMA.MO492407.part2 X₁ X₂ Y₁ Y₂ hX₂ hY₂,
   OMA.MO492407.part3⟩
