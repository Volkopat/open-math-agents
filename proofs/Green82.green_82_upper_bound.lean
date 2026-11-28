import FormalConjectures.GreensOpenProblems.«82»

/-!
# Cosine sums with few zeros (Green 82, upper bound)

For every `n` we exhibit `n` positive integers `A` such that `∑ a ∈ A, cos (2π a θ)` has at most
`C (n log n)^(2/3)` zeros in `[0, 1)`. The frequencies are `A = [1, N] \ B` with `B ⊆ [1, m]`,
`m = ⌈(n log n)^(2/3)⌉` and `N = n + |B|`, in the spirit of Borwein–Erdélyi–Ferguson–Lockhart and
Juškevičius–Sahasrabudhe. The proof below is self-contained.

* `ident`: with `t = 2πθ`, `2 sin (t/2) ∑ a ∈ A, cos (a t) = sin ((N + 1/2) t) - R_B (t)`,
  where `R_B (t) = sin (t/2) (1 + 2 ∑ k ∈ B, cos (k t))`. A zero forces `|R_B (t)| ≤ 1`.
* `cell_zeros`: in each half-period cell of `sin ((N + 1/2) t)` there are at most five zeros
  (Rolle four times; the fourth derivative is a small perturbation of `sin`).
* `zeros_le`: a cell containing a zero either contains a solution of `|R_B| = 1` (at most `4m + 2`
  of these, by a root count for a polynomial in `cos (t/2)`), or lies inside `{|R_B| ≤ 1}` and then
  contains a point of a fixed grid at which `|R_B| ≤ 1`.
* `lo_diam`, `lo_interval`: Erdős' Littlewood–Offord bound via Sperner's theorem. At a fixed grid
  point `x`, the proportion of `B ⊆ [1, m]` with `|R_B (x)| ≤ 1` is `O((1 + 1/sin (x/2)) / √m)`.
* `good_B`: averaging over `B`, some `B` has `O(M log M / √m)` such grid points.
* `main_bound`: the choice of parameters. For the finitely many `n` where `m` is not yet small
  compared with `n`, the plain Dirichlet kernel `A = [1, n]` is used instead.
-/

namespace OMA.Green82

open Finset Real Polynomial

/-- Rolle counting: between any two zeros of `f` in an interval there is a zero of `f'`. -/
lemma rolle_card (I : Set ℝ) (hI : I.OrdConnected) (f f' : ℝ → ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (k : ℕ)
    (hk : ∀ G : Finset ℝ, (∀ y ∈ G, y ∈ I ∧ f' y = 0) → G.card ≤ k) :
    ∀ F : Finset ℝ, (∀ x ∈ F, x ∈ I ∧ f x = 0) → F.card ≤ k + 1 := by
  intro F hF
  by_contra hcon
  obtain ⟨n, hn⟩ : ∃ n, F.card = n + 1 := ⟨F.card - 1, by omega⟩
  have hmem : ∀ i, F.orderEmbOfFin hn i ∈ F := fun i => F.orderEmbOfFin_mem hn i
  have hex : ∀ i : Fin n, ∃ y, F.orderEmbOfFin hn i.castSucc < y ∧
      y < F.orderEmbOfFin hn i.succ ∧ f' y = 0 := by
    intro i
    have hlt : F.orderEmbOfFin hn i.castSucc < F.orderEmbOfFin hn i.succ :=
      (F.orderEmbOfFin hn).strictMono Fin.castSucc_lt_succ
    obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hlt
      (fun x _ => (hf x).continuousAt.continuousWithinAt)
      (by rw [(hF _ (hmem _)).2, (hF _ (hmem _)).2]) (fun x _ => hf x)
    exact ⟨c, hc.1, hc.2, hc0⟩
  choose y hy1 hy2 hy0 using hex
  have hmono : StrictMono y := by
    intro i j hij
    have hle : i.succ ≤ j.castSucc := by
      rw [Fin.le_def]
      have := Fin.lt_def.mp hij
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    exact (hy2 i).trans_le (((F.orderEmbOfFin hn).monotone hle).trans (hy1 j).le)
  have hG := hk (univ.image y) (by
    intro z hz
    obtain ⟨i, _, rfl⟩ := mem_image.mp hz
    exact ⟨hI.out (hF _ (hmem _)).1 (hF _ (hmem _)).1 ⟨(hy1 i).le, (hy2 i).le⟩, hy0 i⟩)
  rw [card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin] at hG
  omega

/-- Iterated Rolle counting along a chain of derivatives. -/
lemma rolle_iter (I : Set ℝ) (hI : I.OrdConnected) (H : ℕ → ℝ → ℝ)
    (hH : ∀ i x, HasDerivAt (H i) (H (i + 1) x) x) (r : ℕ) :
    ∀ k : ℕ, (∀ G : Finset ℝ, (∀ y ∈ G, y ∈ I ∧ H r y = 0) → G.card ≤ k) →
    ∀ F : Finset ℝ, (∀ x ∈ F, x ∈ I ∧ H 0 x = 0) → F.card ≤ k + r := by
  induction r with
  | zero => intro k hk F hF; simpa using hk F hF
  | succ r ih =>
    intro k hk F hF
    have h1 := ih (k + 1) (rolle_card I hI (H r) (H (r + 1)) (hH r) k hk) F hF
    omega

/-- The `i`-th derivative of `t ↦ sin (lam * t)`. -/
noncomputable def S (lam : ℝ) (i : ℕ) (t : ℝ) : ℝ := lam ^ i * sin (lam * t + i * (π / 2))

lemma S_deriv (lam : ℝ) (i : ℕ) (t : ℝ) : HasDerivAt (S lam i) (S lam (i + 1) t) t := by
  have h1 : HasDerivAt (fun t : ℝ => lam * t + i * (π / 2)) lam t := by
    simpa using ((hasDerivAt_id t).const_mul lam).add_const ((i : ℝ) * (π / 2))
  have h2 := (h1.sin).const_mul (lam ^ i)
  have e : S lam (i + 1) t = lam ^ i * (cos (lam * t + i * (π / 2)) * lam) := by
    unfold S
    have : lam * t + ((i + 1 : ℕ) : ℝ) * (π / 2) = (lam * t + i * (π / 2)) + π / 2 := by
      push_cast; ring
    rw [this, sin_add_pi_div_two]
    ring
  rw [e]
  exact h2

lemma S_abs_le (lam : ℝ) (i : ℕ) (t : ℝ) : |S lam i t| ≤ |lam| ^ i := by
  unfold S
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_right (by positivity) (abs_sin_le_one _)

lemma S_zero (lam t : ℝ) : S lam 0 t = sin (lam * t) := by
  unfold S; simp

/-- Derivatives of the perturbation `R_B (t) = sin (t/2) * (1 + 2 * ∑ k ∈ B, cos (k t))`. -/
noncomputable def Rd (B : Finset ℕ) (i : ℕ) (t : ℝ) : ℝ :=
  S (1 / 2) i t + ∑ k ∈ B, (S ((k : ℝ) + 1 / 2) i t - S ((k : ℝ) - 1 / 2) i t)

lemma Rd_deriv (B : Finset ℕ) (i : ℕ) (t : ℝ) :
    HasDerivAt (Rd B i) (Rd B (i + 1) t) t := by
  unfold Rd
  have h := (S_deriv (1 / 2) i t).add
    (HasDerivAt.fun_sum (u := B) (A := fun k t => S ((k : ℝ) + 1 / 2) i t - S ((k : ℝ) - 1 / 2) i t)
      (A' := fun k => S ((k : ℝ) + 1 / 2) (i + 1) t - S ((k : ℝ) - 1 / 2) (i + 1) t)
      (fun k _ => (S_deriv _ i t).sub (S_deriv _ i t)))
  exact h

lemma Rd_abs_le (B : Finset ℕ) (m : ℕ) (hB : B ⊆ Icc 1 m) (i : ℕ) (t : ℝ) :
    |Rd B i t| ≤ 2 * ((m : ℝ) + 1) ^ (i + 1) := by
  unfold Rd
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : |S (1 / 2) i t| ≤ ((m : ℝ) + 1) ^ i := by
    refine (S_abs_le _ i t).trans ?_
    exact pow_le_pow_left₀ (abs_nonneg _) (by rw [abs_of_pos (by norm_num)]; linarith) i
  have h2 : ∀ k ∈ B, |S ((k : ℝ) + 1 / 2) i t - S ((k : ℝ) - 1 / 2) i t| ≤
      2 * ((m : ℝ) + 1) ^ i := by
    intro k hk
    have hk' := mem_Icc.mp (hB hk)
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk'.1
    have hk2 : (k : ℝ) ≤ m := by exact_mod_cast hk'.2
    have ha : |S ((k : ℝ) + 1 / 2) i t| ≤ ((m : ℝ) + 1) ^ i :=
      (S_abs_le _ i t).trans (pow_le_pow_left₀ (abs_nonneg _)
        (by rw [abs_of_pos (by linarith)]; linarith) i)
    have hb : |S ((k : ℝ) - 1 / 2) i t| ≤ ((m : ℝ) + 1) ^ i :=
      (S_abs_le _ i t).trans (pow_le_pow_left₀ (abs_nonneg _)
        (by rw [abs_of_pos (by linarith)]; linarith) i)
    calc |S ((k : ℝ) + 1 / 2) i t - S ((k : ℝ) - 1 / 2) i t|
        ≤ |S ((k : ℝ) + 1 / 2) i t| + |S ((k : ℝ) - 1 / 2) i t| := abs_sub _ _
      _ ≤ 2 * ((m : ℝ) + 1) ^ i := by linarith
  have h3 : |∑ k ∈ B, (S ((k : ℝ) + 1 / 2) i t - S ((k : ℝ) - 1 / 2) i t)| ≤
      (m : ℝ) * (2 * ((m : ℝ) + 1) ^ i) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    refine (sum_le_card_nsmul _ _ _ h2).trans ?_
    rw [nsmul_eq_mul]
    have hc : (B.card : ℝ) ≤ m := by
      have := card_le_card hB
      rw [Nat.card_Icc] at this
      exact_mod_cast (by omega : B.card ≤ m)
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hp : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ i := by positivity
  calc |S (1 / 2) i t + ∑ k ∈ B, (S ((k : ℝ) + 1 / 2) i t - S ((k : ℝ) - 1 / 2) i t)|
      ≤ |S (1 / 2) i t| + |∑ k ∈ B, (S ((k : ℝ) + 1 / 2) i t - S ((k : ℝ) - 1 / 2) i t)| :=
        abs_add_le _ _
    _ ≤ ((m : ℝ) + 1) ^ i + (m : ℝ) * (2 * ((m : ℝ) + 1) ^ i) := by linarith
    _ ≤ 2 * ((m : ℝ) + 1) ^ (i + 1) := by rw [pow_succ]; nlinarith


/-- The function whose zeros we count: `sin (L t) - R_B (t)` and its derivatives. -/
noncomputable def Hd (L : ℝ) (B : Finset ℕ) (i : ℕ) (t : ℝ) : ℝ := S L i t - Rd B i t

lemma Hd_deriv (L : ℝ) (B : Finset ℕ) (i : ℕ) (t : ℝ) :
    HasDerivAt (Hd L B i) (Hd L B (i + 1) t) t :=
  (S_deriv L i t).sub (Rd_deriv B i t)

/-- The index of the half-period cell of `sin (L t)` containing `t`. -/
noncomputable def cell (L : ℝ) (t : ℝ) : ℤ := ⌊L * t / π + 1 / 2⌋

lemma cell_mono (L : ℝ) (hL : 0 < L) : Monotone (cell L) := by
  intro s t hst
  unfold cell
  apply Int.floor_le_floor
  have : L * s / π ≤ L * t / π :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hst hL.le) pi_pos.le
  linarith

lemma cell_bounds (L : ℝ) (t : ℝ) (j : ℤ) (h : cell L t = j) :
    -(π / 2) ≤ L * t - j * π ∧ L * t - j * π < π / 2 := by
  unfold cell at h
  rw [Int.floor_eq_iff] at h
  have hπ := pi_pos
  have e : L * t = (L * t / π) * π := by field_simp
  constructor
  · have : ((j : ℝ) - 1 / 2) * π ≤ (L * t / π) * π :=
      mul_le_mul_of_nonneg_right (by linarith [h.1]) hπ.le
    linarith
  · have : (L * t / π) * π < ((j : ℝ) + 1 / 2) * π :=
      mul_lt_mul_of_pos_right (by linarith [h.2]) hπ
    linarith

/-- In one half-period cell, `sin (L t) = R_B (t)` has at most five solutions, as soon as
`L` is large compared with the degree of `R_B`. -/
lemma cell_zeros (L : ℝ) (hL : 0 < L) (B : Finset ℕ) (m : ℕ) (hB : B ⊆ Icc 1 m)
    (h4 : 4 * ((m : ℝ) + 1) ^ 5 ≤ L ^ 4) (hmL : (m : ℝ) + 1 ≤ L) (j : ℤ)
    (F : Finset ℝ) (hF : ∀ t ∈ F, cell L t = j ∧ Hd L B 0 t = 0) : F.card ≤ 5 := by
  have hI : Set.OrdConnected {t : ℝ | cell L t = j} := by
    have : {t : ℝ | cell L t = j} = cell L ⁻¹' {j} := rfl
    rw [this]
    exact Set.OrdConnected.preimage_mono Set.ordConnected_singleton (cell_mono L hL)
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hL4 : (0 : ℝ) < L ^ 4 := by positivity
  have hL5 : (0 : ℝ) < L ^ 5 := by positivity
  have h5 : 4 * ((m : ℝ) + 1) ^ 6 ≤ L ^ 5 := by
    calc 4 * ((m : ℝ) + 1) ^ 6 = (4 * ((m : ℝ) + 1) ^ 5) * ((m : ℝ) + 1) := by ring
      _ ≤ L ^ 4 * L := mul_le_mul h4 hmL hm1.le hL4.le
      _ = L ^ 5 := by ring
  have key : ∀ G : Finset ℝ, (∀ y ∈ G, y ∈ {t : ℝ | cell L t = j} ∧ Hd L B 4 y = 0) →
      G.card ≤ 1 := by
    intro G hG
    by_contra hcon
    have hcard : 1 < G.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hcard
    -- two distinct zeros `t₁ < t₂` of the fourth derivative
    obtain ⟨t₁, t₂, h1, h2, hlt⟩ : ∃ t₁ t₂ : ℝ, t₁ ∈ G ∧ t₂ ∈ G ∧ t₁ < t₂ := by
      rcases lt_or_gt_of_ne hab with h | h
      · exact ⟨a, b, ha, hb, h⟩
      · exact ⟨b, a, hb, ha, h⟩
    obtain ⟨y, hy, hy0⟩ := exists_hasDerivAt_eq_zero hlt
      (fun x _ => (Hd_deriv L B 4 x).continuousAt.continuousWithinAt)
      (by rw [(hG _ h1).2, (hG _ h2).2]) (fun x _ => Hd_deriv L B 4 x)
    have hc1 : cell L t₁ = j := (hG _ h1).1
    have hc2 : cell L t₂ = j := (hG _ h2).1
    have hcy : cell L y = j := hI.out hc1 hc2 ⟨hy.1.le, hy.2.le⟩
    -- size of sin at the zeros of the fourth derivative
    have hsin : ∀ t, Hd L B 4 t = 0 → |sin (L * t)| ≤ 1 / 2 := by
      intro t ht
      have e : Hd L B 4 t = L ^ 4 * sin (L * t) - Rd B 4 t := by
        unfold Hd S
        have : L * t + ((4 : ℕ) : ℝ) * (π / 2) = L * t + 2 * π := by push_cast; ring
        rw [this, sin_add_two_pi]
      rw [e] at ht
      have hR : |Rd B 4 t| ≤ 2 * ((m : ℝ) + 1) ^ 5 := Rd_abs_le B m hB 4 t
      have h' : L ^ 4 * |sin (L * t)| ≤ L ^ 4 * (1 / 2) := by
        have : L ^ 4 * |sin (L * t)| = |Rd B 4 t| := by
          rw [← abs_of_pos hL4, ← abs_mul]
          congr 1
          linarith
        rw [this]
        linarith
      exact le_of_mul_le_mul_left h' hL4
    have hcos : |cos (L * y)| ≤ 1 / 2 := by
      have e : Hd L B 5 y = L ^ 5 * cos (L * y) - Rd B 5 y := by
        unfold Hd S
        have : L * y + ((5 : ℕ) : ℝ) * (π / 2) = (L * y + π / 2) + 2 * π := by push_cast; ring
        rw [this, sin_add_two_pi, sin_add_pi_div_two]
      rw [e] at hy0
      have hR : |Rd B 5 y| ≤ 2 * ((m : ℝ) + 1) ^ 6 := Rd_abs_le B m hB 5 y
      have h' : L ^ 5 * |cos (L * y)| ≤ L ^ 5 * (1 / 2) := by
        have : L ^ 5 * |cos (L * y)| = |Rd B 5 y| := by
          rw [← abs_of_pos hL5, ← abs_mul]
          congr 1
          linarith
        rw [this]
        linarith
      exact le_of_mul_le_mul_left h' hL5
    -- move to the local variable `u = L t - j π`
    have hsu : ∀ t, |sin (L * t - j * π)| = |sin (L * t)| := by
      intro t
      have : L * t = (L * t - j * π) + j * π := by ring
      rw [this, sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
      congr 2
      ring
    have hcu : |cos (L * y - j * π)| = |cos (L * y)| := by
      have : L * y = (L * y - j * π) + j * π := by ring
      rw [this, cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
      congr 2
      ring
    have b1 := cell_bounds L t₁ j hc1
    have b2 := cell_bounds L t₂ j hc2
    have by' := cell_bounds L y j hcy
    have hu1 : L * t₁ - j * π ≤ L * y - j * π := by nlinarith [hy.1]
    have hu2 : L * y - j * π ≤ L * t₂ - j * π := by nlinarith [hy.2]
    have hs1 : sin (L * t₁ - j * π) ≤ sin (L * y - j * π) :=
      sin_le_sin_of_le_of_le_pi_div_two b1.1 by'.2.le hu1
    have hs2 : sin (L * y - j * π) ≤ sin (L * t₂ - j * π) :=
      sin_le_sin_of_le_of_le_pi_div_two by'.1 b2.2.le hu2
    have a1 := abs_le.mp ((hsu t₁).le.trans (hsin t₁ (hG _ h1).2))
    have a2 := abs_le.mp ((hsu t₂).le.trans (hsin t₂ (hG _ h2).2))
    have a3 := abs_le.mp (hcu.le.trans hcos)
    have hsq := sin_sq_add_cos_sq (L * y - j * π)
    nlinarith
  have := rolle_iter {t : ℝ | cell L t = j} hI (Hd L B) (Hd_deriv L B) 4 1 key F hF
  omega

/-- Telescoping form of the Dirichlet kernel. -/
lemma two_sin_mul_cos (k t : ℝ) :
    2 * sin (t / 2) * cos (k * t) = sin ((k + 1 / 2) * t) - sin ((k - 1 / 2) * t) := by
  have e1 : (k + 1 / 2) * t = k * t + t / 2 := by ring
  have e2 : (k - 1 / 2) * t = k * t - t / 2 := by ring
  rw [e1, e2, sin_add, sin_sub]
  ring

lemma dirichlet_sum (N : ℕ) (t : ℝ) :
    ∑ k ∈ Icc 1 N, (sin (((k : ℝ) + 1 / 2) * t) - sin (((k : ℝ) - 1 / 2) * t)) =
      sin (((N : ℝ) + 1 / 2) * t) - sin (t / 2) := by
  induction N with
  | zero =>
    simp
    ring_nf
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    have : ((N : ℝ) + 1 - 1 / 2) * t = ((N : ℝ) + 1 / 2) * t := by ring
    rw [this]
    ring

lemma Rd_zero (B : Finset ℕ) (t : ℝ) :
    Rd B 0 t = sin (t / 2) + ∑ k ∈ B, 2 * sin (t / 2) * cos (k * t) := by
  unfold Rd
  rw [S_zero]
  congr 1
  · congr 1; ring
  · apply sum_congr rfl
    intro k _
    rw [S_zero, S_zero, two_sin_mul_cos, mul_comm ((k : ℝ) + 1 / 2), mul_comm ((k : ℝ) - 1 / 2)]

/-- The basic identity: `2 sin (t/2) * ∑_{k ∈ [1, N] \ B} cos (k t) = sin ((N + 1/2) t) - R_B (t)`. -/
lemma ident (N : ℕ) (B : Finset ℕ) (hB : B ⊆ Icc 1 N) (t : ℝ) :
    2 * sin (t / 2) * ∑ k ∈ Icc 1 N \ B, cos (k * t) = Hd ((N : ℝ) + 1 / 2) B 0 t := by
  have h1 : ∑ k ∈ Icc 1 N \ B, cos (k * t) + ∑ k ∈ B, cos (k * t) = ∑ k ∈ Icc 1 N, cos (k * t) :=
    sum_sdiff hB
  have h2 : ∑ k ∈ Icc 1 N, 2 * sin (t / 2) * cos (k * t) =
      sin (((N : ℝ) + 1 / 2) * t) - sin (t / 2) := by
    rw [← dirichlet_sum]
    exact sum_congr rfl (fun k _ => two_sin_mul_cos k t)
  have h3 : ∑ k ∈ Icc 1 N \ B, cos (k * t) = ∑ k ∈ Icc 1 N, cos (k * t) - ∑ k ∈ B, cos (k * t) := by
    linarith
  unfold Hd
  rw [S_zero, Rd_zero, ← mul_sum, h3, mul_sub, mul_sum, h2]
  ring

/-- The polynomial with `qpoly B (cos u) = 1 + 2 * ∑ k ∈ B, cos (2 k u)`. -/
noncomputable def qpoly (B : Finset ℕ) : Polynomial ℝ :=
  1 + C 2 * ∑ k ∈ B, Chebyshev.T ℝ ((2 * k : ℕ) : ℤ)

/-- The polynomial vanishing at `cos (t / 2)` whenever `|R_B (t)| = 1`. -/
noncomputable def Ppoly (B : Finset ℕ) : Polynomial ℝ :=
  (1 - X ^ 2) * qpoly B ^ 2 - 1

lemma q_eval (B : Finset ℕ) (t : ℝ) :
    (qpoly B).eval (cos (t / 2)) = 1 + 2 * ∑ k ∈ B, cos (k * t) := by
  unfold qpoly
  simp only [eval_add, eval_one, eval_mul, eval_C,
    eval_finsetSum, Chebyshev.T_real_cos]
  congr 2
  apply sum_congr rfl
  intro k _
  congr 1
  push_cast
  ring

lemma Rd_eq (B : Finset ℕ) (t : ℝ) :
    Rd B 0 t = sin (t / 2) * (qpoly B).eval (cos (t / 2)) := by
  rw [Rd_zero, q_eval, mul_sum, mul_add, mul_one, mul_sum]
  congr 1
  apply sum_congr rfl
  intro k _
  ring

lemma P_eval (B : Finset ℕ) (t : ℝ) :
    (Ppoly B).eval (cos (t / 2)) = Rd B 0 t ^ 2 - 1 := by
  rw [Rd_eq]
  unfold Ppoly
  simp only [eval_sub, eval_mul, eval_one, eval_pow,
    eval_X]
  have := sin_sq_add_cos_sq (t / 2)
  have e : 1 - cos (t / 2) ^ 2 = sin (t / 2) ^ 2 := by linarith
  rw [e]
  ring

lemma P_ne (B : Finset ℕ) : Ppoly B ≠ 0 := by
  intro h
  have : (Ppoly B).eval 1 = -1 := by
    unfold Ppoly
    simp
  rw [h] at this
  simp at this

lemma q_deg (B : Finset ℕ) (m : ℕ) (hB : B ⊆ Icc 1 m) :
    (qpoly B).natDegree ≤ 2 * m := by
  unfold qpoly
  apply natDegree_add_le_of_degree_le
  · simp
  · refine (natDegree_C_mul_le _ _).trans ?_
    apply natDegree_sum_le_of_forall_le
    intro k hk
    rw [Chebyshev.natDegree_T]
    have := (mem_Icc.mp (hB hk)).2
    simp only [Int.natAbs_natCast]
    omega

lemma P_deg (B : Finset ℕ) (m : ℕ) (hB : B ⊆ Icc 1 m) :
    (Ppoly B).natDegree ≤ 4 * m + 2 := by
  unfold Ppoly
  have h1 : (1 - X ^ 2 : Polynomial ℝ).natDegree ≤ 2 :=
    (natDegree_sub_le_of_le (m := 0) (n := 2) (by simp)
      (natDegree_X_pow_le 2)).trans (by simp)
  have h2 := natDegree_pow_le_of_le 2 (q_deg B m hB)
  have h3 := natDegree_mul_le_of_le h1 h2
  have h4 : ((1 - X ^ 2) * qpoly B ^ 2).natDegree ≤ 4 * m + 2 := by omega
  exact (natDegree_sub_le_of_le (n := 0) h4 (by simp)).trans (by simp)

/-- The solutions of `|R_B| = 1` in `(0, 2π)`. -/
noncomputable abbrev P1 (B : Finset ℕ) : Set ℝ := {t : ℝ | 0 < t ∧ t < 2 * π ∧ |Rd B 0 t| = 1}

/-- The equation `|R_B (t)| = 1` has at most `4 m + 2` solutions in `(0, 2π)`. -/
lemma P1_card (B : Finset ℕ) (m : ℕ) (hB : B ⊆ Icc 1 m) :
    (P1 B).Finite ∧
      (P1 B).ncard ≤ 4 * m + 2 := by
  have hmaps : ∀ t ∈ P1 B,
      cos (t / 2) ∈ ((Ppoly B).roots.toFinset : Set ℝ) := by
    intro t ht
    obtain ⟨_, _, h1⟩ := ht
    rw [mem_coe, Multiset.mem_toFinset, mem_roots (P_ne B),
      IsRoot, P_eval]
    have : Rd B 0 t ^ 2 = 1 := by rw [← sq_abs, h1]; norm_num
    linarith
  have hinj : Set.InjOn (fun t : ℝ => cos (t / 2)) (P1 B) := by
    intro s hs t ht hst
    have h1 : s / 2 ∈ Set.Icc 0 π := ⟨by linarith [hs.1], by linarith [hs.2.1]⟩
    have h2 : t / 2 ∈ Set.Icc 0 π := ⟨by linarith [ht.1], by linarith [ht.2.1]⟩
    have := injOn_cos h1 h2 hst
    linarith
  refine ⟨Set.Finite.of_injOn hmaps hinj (finite_toSet _), ?_⟩
  calc (P1 B).ncard
      ≤ ((Ppoly B).roots.toFinset : Set ℝ).ncard :=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj (finite_toSet _)
    _ = (Ppoly B).roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card (Ppoly B).roots := Multiset.toFinset_card_le _
    _ ≤ (Ppoly B).natDegree := card_roots' _
    _ ≤ 4 * m + 2 := P_deg B m hB

/-- The grid points `2π i / M`, `0 < i < M`, at which `|R_B| ≤ 1`. -/
noncomputable abbrev bad (B : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (Ioo 0 M).filter (fun i : ℕ => |Rd B 0 (2 * π * i / M)| ≤ 1)

lemma Rd_cont (B : Finset ℕ) : Continuous (Rd B 0) :=
  continuous_iff_continuousAt.mpr (fun t => (Rd_deriv B 0 t).continuousAt)

/-- A cell strictly inside the period contains a point of the grid `2π i / M`. -/
lemma grid_point (L : ℝ) (hL : 0 < L) (M : ℕ) (hM : 2 * L ≤ M) (j : ℤ) (hj1 : 1 ≤ j)
    (hj2 : (j : ℝ) + 1 / 2 ≤ 2 * L) :
    ∃ i : ℕ, 0 < i ∧ i < M ∧ cell L (2 * π * i / M) = j := by
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by positivity) hM
  have hj1' : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hr : 0 < ((j : ℝ) - 1 / 2) * M / (2 * L) := by
    apply div_pos (mul_pos (by linarith) hMpos) (by positivity)
  refine ⟨⌈((j : ℝ) - 1 / 2) * M / (2 * L)⌉₊, Nat.ceil_pos.mpr hr, ?_, ?_⟩
  · have h1 := Nat.ceil_lt_add_one hr.le
    have h2 : ((j : ℝ) - 1 / 2) * M / (2 * L) + 1 ≤ M := by
      rw [div_add_one (by positivity), div_le_iff₀ (by positivity)]
      nlinarith
    have h3 : ((⌈((j : ℝ) - 1 / 2) * M / (2 * L)⌉₊ : ℕ) : ℝ) < M := lt_of_lt_of_le h1 h2
    exact_mod_cast h3
  · have h0 := Nat.le_ceil (((j : ℝ) - 1 / 2) * M / (2 * L))
    have h1 := Nat.ceil_lt_add_one hr.le
    obtain ⟨i, hi⟩ : ∃ i : ℕ, i = ⌈((j : ℝ) - 1 / 2) * M / (2 * L)⌉₊ := ⟨_, rfl⟩
    rw [← hi] at h0 h1 ⊢
    unfold cell
    rw [Int.floor_eq_iff]
    have e : L * (2 * π * i / M) / π = 2 * L * i / M := by
      field_simp
    rw [e]
    have hiL : (i : ℝ) * (2 * L) < ((j : ℝ) - 1 / 2) * M + 2 * L := by
      have h := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < 2 * L by positivity)
      have e2 : (((j : ℝ) - 1 / 2) * M / (2 * L) + 1) * (2 * L) =
          ((j : ℝ) - 1 / 2) * M + 2 * L := by
        field_simp
      linarith
    have h0' : ((j : ℝ) - 1 / 2) * M ≤ i * (2 * L) := by
      have h := mul_le_mul_of_nonneg_right h0 (show (0 : ℝ) ≤ 2 * L by positivity)
      have e2 : ((j : ℝ) - 1 / 2) * M / (2 * L) * (2 * L) = ((j : ℝ) - 1 / 2) * M := by
        field_simp
      linarith
    constructor
    · rw [← sub_le_iff_le_add, le_div_iff₀ hMpos]
      linarith
    · rw [← lt_sub_iff_add_lt, div_lt_iff₀ hMpos]
      linarith

/-- Deterministic zero count: the zeros of `sin (L t) - R_B (t)` in `[0, 2π)` are controlled
by the number of grid points where `|R_B| ≤ 1`, plus the degree of `R_B`. -/
theorem zeros_le (N m M : ℕ) (B : Finset ℕ) (hB : B ⊆ Icc 1 m)
    (h4 : 4 * ((m : ℝ) + 1) ^ 5 ≤ ((N : ℝ) + 1 / 2) ^ 4)
    (hmL : (m : ℝ) + 1 ≤ (N : ℝ) + 1 / 2) (hM : 2 * N + 1 ≤ M)
    (F : Finset ℝ)
    (hF : ∀ t ∈ F, 0 ≤ t ∧ t < 2 * π ∧ Hd ((N : ℝ) + 1 / 2) B 0 t = 0) :
    F.card ≤ 5 * ((bad B M).card + (4 * m + 2) + 2) := by
  classical
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = (N : ℝ) + 1 / 2 := ⟨_, rfl⟩
  rw [← hLdef] at h4 hmL hF
  have hL : 0 < L := by rw [hLdef]; positivity
  have hML : 2 * L ≤ (M : ℝ) := by
    have : ((2 * N + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hM
    push_cast at this
    rw [hLdef]; linarith
  have hπ := pi_pos
  have hI : ∀ j : ℤ, Set.OrdConnected {t : ℝ | cell L t = j} := by
    intro j
    have : {t : ℝ | cell L t = j} = cell L ⁻¹' {j} := rfl
    rw [this]
    exact Set.OrdConnected.preimage_mono Set.ordConnected_singleton (cell_mono L hL)
  obtain ⟨hfin, hcard⟩ := P1_card B m hB
  have step1 : F.card ≤ 5 * (F.image (cell L)).card := by
    apply card_le_mul_card_image
    intro b _
    apply cell_zeros L hL B m hB h4 hmL b
    intro t ht
    obtain ⟨htF, htb⟩ := mem_filter.mp ht
    exact ⟨htb, (hF t htF).2.2⟩
  have step2 : F.image (cell L) ⊆ ({0, (2 * N + 1 : ℤ)} : Finset ℤ) ∪
      (bad B M).image
        (fun i : ℕ => cell L (2 * π * i / M)) ∪ hfin.toFinset.image (cell L) := by
    intro j hj
    obtain ⟨t, htF, rfl⟩ := mem_image.mp hj
    obtain ⟨ht0, ht1, htz⟩ := hF t htF
    have hRt : |Rd B 0 t| ≤ 1 := by
      have : Rd B 0 t = sin (L * t) := by
        unfold Hd at htz
        rw [S_zero] at htz
        linarith
      rw [this]
      exact abs_sin_le_one _
    have hb := cell_bounds L t (cell L t) rfl
    have hLt0 : 0 ≤ L * t := mul_nonneg hL.le ht0
    have hLt1 : L * t < L * (2 * π) := mul_lt_mul_of_pos_left ht1 hL
    have h2L : L * (2 * π) = (2 * (N : ℝ) + 1) * π := by rw [hLdef]; ring
    have hj0 : (0 : ℝ) ≤ (cell L t : ℝ) := by
      by_contra hneg
      have hneg' : cell L t < 0 := by exact_mod_cast not_le.mp hneg
      have h1 : (cell L t : ℝ) ≤ -1 := by
        have : cell L t ≤ -1 := by omega
        exact_mod_cast this
      have h2 := mul_le_mul_of_nonneg_right h1 hπ.le
      linarith [hb.2]
    have hj2 : (cell L t : ℝ) ≤ 2 * N + 1 := by
      by_contra hbig
      have hbig' : (2 * N + 1 : ℤ) < cell L t := by exact_mod_cast not_le.mp hbig
      have h1 : (2 * (N : ℝ) + 2) ≤ (cell L t : ℝ) := by
        have : (2 * N + 2 : ℤ) ≤ cell L t := by omega
        exact_mod_cast this
      have h2 := mul_le_mul_of_nonneg_right h1 hπ.le
      linarith [hb.1]
    by_cases hend : cell L t = 0 ∨ cell L t = 2 * N + 1
    · apply mem_union_left
      apply mem_union_left
      rw [mem_insert, mem_singleton]
      exact hend
    · rw [not_or] at hend
      have hj0' : 0 ≤ cell L t := by exact_mod_cast hj0
      have hj2' : cell L t ≤ 2 * N + 1 := by exact_mod_cast hj2
      have hj1 : 1 ≤ cell L t := by omega
      have hj3 : cell L t ≤ 2 * N := by omega
      have hj3' : (cell L t : ℝ) ≤ 2 * N := by exact_mod_cast hj3
      obtain ⟨i, hi0, hiM, hic⟩ := grid_point L hL M hML (cell L t) hj1
        (by have : 2 * L = 2 * (N : ℝ) + 1 := by rw [hLdef]; ring
            linarith)
      by_cases hRx : |Rd B 0 (2 * π * i / M)| ≤ 1
      · apply mem_union_left
        apply mem_union_right
        exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_Ioo.mpr ⟨hi0, hiM⟩, hRx⟩,
          hic⟩
      · have hRx' : 1 ≤ |Rd B 0 (2 * π * i / M)| := (not_le.mp hRx).le
        apply mem_union_right
        have hcont : ContinuousOn (fun s : ℝ => |Rd B 0 s|) (Set.uIcc t (2 * π * i / M)) :=
          (continuous_abs.comp (Rd_cont B)).continuousOn
        have hmem : (1 : ℝ) ∈ Set.uIcc (|Rd B 0 t|) (|Rd B 0 (2 * π * i / M)|) :=
          Set.mem_uIcc.mpr (Or.inl ⟨hRt, hRx'⟩)
        obtain ⟨s, hs, hs1⟩ := intermediate_value_uIcc hcont hmem
        have hcs : cell L s = cell L t :=
          (hI (cell L t)).uIcc_subset (show t ∈ {t' : ℝ | cell L t' = cell L t} from rfl) hic hs
        have hbs := cell_bounds L s (cell L t) hcs
        have hj1' : (1 : ℝ) ≤ (cell L t : ℝ) := by exact_mod_cast hj1
        have hjm := mul_le_mul_of_nonneg_right hj1' hπ.le
        have hjM := mul_le_mul_of_nonneg_right hj3' hπ.le
        have hs0 : 0 < s := by
          have h : 0 < L * s := by linarith [hbs.1]
          by_contra hneg
          have := mul_nonpos_of_nonneg_of_nonpos hL.le (not_lt.mp hneg)
          linarith
        have hs2 : s < 2 * π := by
          have h : L * s < L * (2 * π) := by linarith [hbs.2]
          exact lt_of_mul_lt_mul_left h hL.le
        exact mem_image.mpr ⟨s, hfin.mem_toFinset.mpr ⟨hs0, hs2, hs1⟩, hcs⟩
  have hc1 : (F.image (cell L)).card ≤ 2 + (bad B M).card + (4 * m + 2) := by
    refine (card_le_card step2).trans ?_
    refine (card_union_le _ _).trans ?_
    have a1 := card_union_le ({0, (2 * N + 1 : ℤ)} : Finset ℤ)
      ((bad B M).image
        (fun i : ℕ => cell L (2 * π * i / M)))
    have a2 : (({0, (2 * N + 1 : ℤ)} : Finset ℤ)).card ≤ 2 := card_le_two
    have a3 := card_image_le (s := bad B M) (f := fun i : ℕ => cell L (2 * π * i / M))
    have a4 := card_image_le (s := hfin.toFinset) (f := cell L)
    have a5 : hfin.toFinset.card ≤ 4 * m + 2 := by
      rw [← Set.ncard_eq_toFinset_card _ hfin]
      exact hcard
    omega
  omega

lemma sperner (A : Finset ℕ) (𝒜 : Finset (Finset ℕ)) (hsub : ∀ B ∈ 𝒜, B ⊆ A)
    (hanti : ∀ B ∈ 𝒜, ∀ B' ∈ 𝒜, B ⊆ B' → B = B') : 𝒜.card ≤ A.card.choose (A.card / 2) := by
  classical
  have hmono : ∀ B ∈ 𝒜, ∀ B' : Finset ℕ,
      B.subtype (fun x => x ∈ A) ⊆ B'.subtype (fun x => x ∈ A) → B ⊆ B' := by
    intro B hB B' hle x hx
    have hxA := hsub B hB hx
    have h1 : (⟨x, hxA⟩ : {x // x ∈ A}) ∈ B.subtype (fun x => x ∈ A) :=
      mem_subtype.2 hx
    exact mem_subtype.1 (hle h1)
  have hinj : Set.InjOn (fun B : Finset ℕ => B.subtype (fun x => x ∈ A))
      (𝒜 : Set (Finset ℕ)) := by
    intro B hB B' hB' h
    have h' : B.subtype (fun x => x ∈ A) = B'.subtype (fun x => x ∈ A) := h
    exact Subset.antisymm (hmono B hB B' (by rw [h']))
      (hmono B' hB' B (by rw [h']))
  have hcard : (𝒜.image (fun B : Finset ℕ => B.subtype (fun x => x ∈ A))).card = 𝒜.card :=
    card_image_of_injOn hinj
  have hanti' : IsAntichain (· ⊆ ·)
      (SetLike.coe (𝒜.image (fun B : Finset ℕ => B.subtype (fun x => x ∈ A)))) := by
    intro C hC C' hC' hne
    show ¬ (C ⊆ C')
    intro hle
    have hCm : C ∈ 𝒜.image (fun B : Finset ℕ => B.subtype (fun x => x ∈ A)) := hC
    have hCm' : C' ∈ 𝒜.image (fun B : Finset ℕ => B.subtype (fun x => x ∈ A)) := hC'
    obtain ⟨B, hB, hBC⟩ := mem_image.1 hCm
    obtain ⟨B', hB', hBC'⟩ := mem_image.1 hCm'
    apply hne
    have hBB' : B ⊆ B' := hmono B hB B' (by rw [hBC, hBC']; exact hle)
    rw [← hBC, ← hBC', hanti B hB B' hB' hBB']
  have h := hanti'.sperner
  rw [hcard, Fintype.card_coe] at h
  exact h

lemma cb_sq (m : ℕ) : m.centralBinom ^ 2 * (2 * m + 1) ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := Nat.succ_mul_centralBinom_succ m
    have key : (m + 1) ^ 2 * ((m + 1).centralBinom ^ 2 * (2 * (m + 1) + 1)) ≤
        (m + 1) ^ 2 * 16 ^ (m + 1) := by
      have e : (m + 1) ^ 2 * ((m + 1).centralBinom ^ 2 * (2 * (m + 1) + 1)) =
          (2 * (2 * m + 1) * m.centralBinom) ^ 2 * (2 * m + 3) := by
        rw [← h]
        ring
      rw [e]
      calc (2 * (2 * m + 1) * m.centralBinom) ^ 2 * (2 * m + 3)
          = (4 * (2 * m + 1) * (2 * m + 3)) * (m.centralBinom ^ 2 * (2 * m + 1)) := by ring
        _ ≤ (4 * (2 * m + 1) * (2 * m + 3)) * 16 ^ m := Nat.mul_le_mul_left _ ih
        _ ≤ (16 * (m + 1) ^ 2) * 16 ^ m := Nat.mul_le_mul_right _ (by nlinarith)
        _ = (m + 1) ^ 2 * 16 ^ (m + 1) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

lemma ch_sq (r : ℕ) : (r.choose (r / 2)) ^ 2 * (r + 1) ≤ 4 * 4 ^ r := by
  obtain ⟨M, hM⟩ : ∃ M, M = (r + 1) / 2 := ⟨_, rfl⟩
  have h1 : r.choose (r / 2) ≤ M.centralBinom :=
    (Nat.choose_le_choose (r / 2) (by omega : r ≤ 2 * M)).trans
      (Nat.choose_le_centralBinom (r / 2) M)
  have h2 := cb_sq M
  have h3 : (16 : ℕ) ^ M ≤ 4 * 4 ^ r := by
    have e : (16 : ℕ) ^ M = 4 ^ (2 * M) := by
      rw [pow_mul]
      norm_num
    rw [e, ← pow_succ']
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  calc (r.choose (r / 2)) ^ 2 * (r + 1)
      ≤ M.centralBinom ^ 2 * (2 * M + 1) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left h1 2) (by omega)
    _ ≤ 16 ^ M := h2
    _ ≤ 4 * 4 ^ r := h3

/-- Erdős' form of the Littlewood–Offord lemma: at most `2^(|E|-|Gd|) * C(|Gd|, |Gd|/2)` subset
sums land in a set of diameter less than `α`, if the steps indexed by `Gd` all have the same sign
and size at least `α`. -/
lemma lo_diam (E Gd : Finset ℕ) (hG : Gd ⊆ E) (a : ℕ → ℝ) (α : ℝ)
    (hsign : (∀ k ∈ Gd, α ≤ a k) ∨ (∀ k ∈ Gd, a k ≤ -α)) (hα : 0 < α)
    (P : ℝ → Prop) [DecidablePred P] (hP : ∀ s s' : ℝ, P s → P s' → |s - s'| < α) :
    (E.powerset.filter (fun B => P (∑ k ∈ B, a k))).card ≤
      Gd.card.choose (Gd.card / 2) * 2 ^ (E.card - Gd.card) := by
  classical
  have hcard : ((E \ Gd).powerset).card = 2 ^ (E.card - Gd.card) := by
    rw [card_powerset, card_sdiff_of_subset hG]
  rw [← hcard]
  apply card_le_mul_card_image_of_maps_to (f := fun B => B \ Gd)
  · intro B hB
    rw [mem_powerset]
    exact sdiff_subset_sdiff (mem_powerset.mp (mem_filter.mp hB).1) le_rfl
  · intro B₀ _
    have hsplit : ∀ B : Finset ℕ, ∑ k ∈ B, a k = ∑ k ∈ B ∩ Gd, a k + ∑ k ∈ B \ Gd, a k :=
      fun B => (sum_inter_add_sum_sdiff B Gd a).symm
    have hinj : Set.InjOn (fun B : Finset ℕ => B ∩ Gd)
        (((E.powerset.filter (fun B => P (∑ k ∈ B, a k))).filter
          (fun B => B \ Gd = B₀) : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
      intro B₁ h₁ B₂ h₂ h
      have e₁ := (mem_filter.mp h₁).2
      have e₂ := (mem_filter.mp h₂).2
      have h' : B₁ ∩ Gd = B₂ ∩ Gd := h
      rw [← sdiff_union_inter B₁ Gd, ← sdiff_union_inter B₂ Gd, e₁, e₂, h']
    rw [← card_image_of_injOn hinj]
    apply sperner Gd
    · intro C hC
      obtain ⟨B, _, rfl⟩ := mem_image.mp hC
      exact inter_subset_right
    · intro C hC C' hC' hCC'
      obtain ⟨B₁, h₁, rfl⟩ := mem_image.mp hC
      obtain ⟨B₂, h₂, rfl⟩ := mem_image.mp hC'
      by_contra hne
      obtain ⟨k, hk, hk'⟩ := exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hCC', hne⟩)
      have e₁ := (mem_filter.mp h₁).2
      have e₂ := (mem_filter.mp h₂).2
      have p₁ := (mem_filter.mp (mem_filter.mp h₁).1).2
      have p₂ := (mem_filter.mp (mem_filter.mp h₂).1).2
      have hdiff := abs_lt.mp (hP _ _ p₂ p₁)
      have hsd := sum_sdiff (f := a) hCC'
      have hD : ∑ i ∈ B₂, a i - ∑ i ∈ B₁, a i = ∑ i ∈ (B₂ ∩ Gd) \ (B₁ ∩ Gd), a i := by
        rw [hsplit B₂, hsplit B₁, e₁, e₂]
        linarith
      have hkmem : k ∈ (B₂ ∩ Gd) \ (B₁ ∩ Gd) := mem_sdiff.mpr ⟨hk, hk'⟩
      have hsubG : ∀ i ∈ (B₂ ∩ Gd) \ (B₁ ∩ Gd), i ∈ Gd := fun i hi =>
        (mem_inter.mp (mem_sdiff.mp hi).1).2
      rcases hsign with hpos | hneg
      · have := single_le_sum (f := a)
          (fun i hi => hα.le.trans (hpos i (hsubG i hi))) hkmem
        have := hpos k (hsubG k hkmem)
        linarith
      · have := single_le_sum (f := fun i => -a i)
          (fun i hi => by have := hneg i (hsubG i hi); linarith) hkmem
        rw [sum_neg_distrib] at this
        have := hneg k (hsubG k hkmem)
        linarith

/-- Interval form: the number of `B ⊆ E` with `|c₀ + ∑_{k ∈ B} a k| ≤ 1`. -/
lemma lo_interval (E Gd : Finset ℕ) (hG : Gd ⊆ E) (a : ℕ → ℝ) (α : ℝ)
    (hsign : (∀ k ∈ Gd, α ≤ a k) ∨ (∀ k ∈ Gd, a k ≤ -α)) (hα : 0 < α) (c₀ : ℝ) :
    (((E.powerset.filter (fun B => |c₀ + ∑ k ∈ B, a k| ≤ 1)).card : ℕ) : ℝ) ≤
      (2 / α + 1) * ((Gd.card.choose (Gd.card / 2) * 2 ^ (E.card - Gd.card) : ℕ) : ℝ) := by
  classical
  have h2α : 0 ≤ 2 / α := by positivity
  have hnat : (E.powerset.filter (fun B => |c₀ + ∑ k ∈ B, a k| ≤ 1)).card ≤
      (Gd.card.choose (Gd.card / 2) * 2 ^ (E.card - Gd.card)) *
        (range (⌊2 / α⌋₊ + 1)).card := by
    apply card_le_mul_card_image_of_maps_to
      (f := fun B : Finset ℕ => ⌊(c₀ + ∑ k ∈ B, a k + 1) / α⌋₊)
    · intro B hB
      have hb := abs_le.mp (mem_filter.mp hB).2
      rw [mem_range, Nat.lt_succ_iff]
      apply Nat.floor_le_floor
      exact div_le_div_of_nonneg_right (by linarith [hb.2]) hα.le
    · intro i _
      refine le_trans (card_le_card ?_)
        (lo_diam E Gd hG a α hsign hα
          (fun s => 0 ≤ c₀ + s + 1 ∧ ⌊(c₀ + s + 1) / α⌋₊ = i) ?_)
      · intro B hB
        obtain ⟨hB1, hB2⟩ := mem_filter.mp hB
        obtain ⟨hB3, hB4⟩ := mem_filter.mp hB1
        have hb := abs_le.mp hB4
        exact mem_filter.mpr ⟨hB3, by linarith [hb.1], hB2⟩
      · rintro s s' ⟨h0, hf⟩ ⟨h0', hf'⟩
        rw [Nat.floor_eq_iff (div_nonneg h0 hα.le)] at hf
        rw [Nat.floor_eq_iff (div_nonneg h0' hα.le)] at hf'
        rw [le_div_iff₀ hα, div_lt_iff₀ hα] at hf hf'
        rw [abs_lt]
        constructor <;> nlinarith [hf.1, hf.2, hf'.1, hf'.2]
  have hreal : (((E.powerset.filter (fun B => |c₀ + ∑ k ∈ B, a k| ≤ 1)).card : ℕ) : ℝ) ≤
      ((Gd.card.choose (Gd.card / 2) * 2 ^ (E.card - Gd.card) : ℕ) : ℝ) *
        ((⌊2 / α⌋₊ : ℝ) + 1) := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    rw [card_range] at this
    push_cast at this ⊢
    exact this
  have hfl : ((⌊2 / α⌋₊ : ℝ) + 1) ≤ 2 / α + 1 := by linarith [Nat.floor_le h2α]
  calc _ ≤ _ := hreal
    _ ≤ ((Gd.card.choose (Gd.card / 2) * 2 ^ (E.card - Gd.card) : ℕ) : ℝ) * (2 / α + 1) :=
        mul_le_mul_of_nonneg_left hfl (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

/-- A positive proportion of the indices `k ≤ m` have `|cos (k x)| ≥ 1/2`. -/
lemma good_count (m : ℕ) (x : ℝ) :
    m / 2 - m / 4 ≤ ((Icc 1 m).filter (fun k : ℕ => 1 / 2 ≤ cos (k * x))).card +
      ((Icc 1 m).filter (fun k : ℕ => cos (k * x) ≤ -(1 / 2))).card := by
  classical
  have hcard : (Ioc (m / 4) (m / 2)).card = m / 2 - m / 4 := Nat.card_Ioc _ _
  rw [← hcard]
  refine le_trans ?_ (card_union_le _ _)
  apply card_le_card_of_injOn (fun k : ℕ => if 1 / 2 ≤ |cos (k * x)| then k else 2 * k)
  · intro k hk
    have hk' := mem_Ioc.mp hk
    show (if 1 / 2 ≤ |cos (k * x)| then k else 2 * k) ∈ _
    split_ifs with h
    · rw [mem_coe, mem_union, mem_filter, mem_filter, mem_Icc]
      rcases le_abs.mp h with h' | h'
      · exact Or.inl ⟨⟨by omega, by omega⟩, h'⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, by linarith⟩
    · rw [mem_coe, mem_union, mem_filter, mem_filter, mem_Icc]
      right
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hlt := abs_lt.mp (not_le.mp h)
      have e : ((2 * k : ℕ) : ℝ) * x = 2 * (k * x) := by push_cast; ring
      rw [e, cos_two_mul]
      nlinarith [hlt.1, hlt.2]
  · intro k₁ h₁ k₂ h₂ h
    have h₁' := mem_Ioc.mp h₁
    have h₂' := mem_Ioc.mp h₂
    simp only at h
    split_ifs at h <;> omega

/-- At a fixed point `x`, only a proportion `O((1 + 1/sin (x/2)) / √m)` of the sets `B ⊆ [1, m]`
have `|R_B (x)| ≤ 1`. -/
lemma bad_card (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 < sin (x / 2)) :
    ((((Icc 1 m).powerset.filter (fun B => |Rd B 0 x| ≤ 1)).card : ℕ) : ℝ) ≤
      (2 / sin (x / 2) + 1) * (2 ^ m * (6 / √m)) := by
  classical
  have hgc := good_count m x
  obtain ⟨Gd, hGsub, hsign, hg⟩ : ∃ Gd : Finset ℕ, Gd ⊆ Icc 1 m ∧
      ((∀ k ∈ Gd, sin (x / 2) ≤ (fun k : ℕ => 2 * sin (x / 2) * cos (k * x)) k) ∨
        (∀ k ∈ Gd, (fun k : ℕ => 2 * sin (x / 2) * cos (k * x)) k ≤ -sin (x / 2))) ∧
      m / 2 - m / 4 ≤ 2 * Gd.card := by
    by_cases hc : ((Icc 1 m).filter (fun k : ℕ => cos (k * x) ≤ -(1 / 2))).card ≤
        ((Icc 1 m).filter (fun k : ℕ => 1 / 2 ≤ cos (k * x))).card
    · refine ⟨(Icc 1 m).filter (fun k : ℕ => 1 / 2 ≤ cos (k * x)), filter_subset _ _,
        Or.inl ?_, by omega⟩
      intro k hk
      have := (mem_filter.mp hk).2
      show sin (x / 2) ≤ 2 * sin (x / 2) * cos (k * x)
      nlinarith
    · refine ⟨(Icc 1 m).filter (fun k : ℕ => cos (k * x) ≤ -(1 / 2)), filter_subset _ _,
        Or.inr ?_, by omega⟩
      intro k hk
      have := (mem_filter.mp hk).2
      show 2 * sin (x / 2) * cos (k * x) ≤ -sin (x / 2)
      nlinarith
  have hlo := lo_interval (Icc 1 m) Gd hGsub (fun k : ℕ => 2 * sin (x / 2) * cos (k * x))
    (sin (x / 2)) hsign hx (sin (x / 2))
  have hfe : (Icc 1 m).powerset.filter (fun B => |Rd B 0 x| ≤ 1) =
      (Icc 1 m).powerset.filter
        (fun B => |sin (x / 2) + ∑ k ∈ B, (fun k : ℕ => 2 * sin (x / 2) * cos (k * x)) k| ≤ 1) :=
    filter_congr (fun B _ => by rw [Rd_zero])
  rw [hfe]
  refine hlo.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hEm : (Icc 1 m).card = m := by rw [Nat.card_Icc]; omega
  rw [hEm]
  have hgm : Gd.card ≤ m := by
    have := card_le_card hGsub
    omega
  obtain ⟨g, hgdef⟩ : ∃ g : ℕ, g = Gd.card := ⟨_, rfl⟩
  rw [← hgdef] at hg hgm ⊢
  have hsm : 0 < √m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hsg : 0 < √((g : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  have h1 : ((g.choose (g / 2) : ℕ) : ℝ) ^ 2 * ((g : ℝ) + 1) ≤ 4 * 4 ^ g := by
    exact_mod_cast ch_sq g
  have h2 : ((g.choose (g / 2) : ℕ) : ℝ) * √((g : ℝ) + 1) ≤ 2 * 2 ^ g := by
    rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt (by positivity)]
    calc ((g.choose (g / 2) : ℕ) : ℝ) ^ 2 * ((g : ℝ) + 1) ≤ 4 * 4 ^ g := h1
      _ = (2 * 2 ^ g) ^ 2 := by rw [mul_pow, ← pow_mul, mul_comm g 2, pow_mul]; norm_num
  have h3 : √m ≤ 3 * √((g : ℝ) + 1) := by
    rw [← pow_le_pow_iff_left₀ hsm.le (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have : m ≤ 9 * (g + 1) := by omega
    have : (m : ℝ) ≤ 9 * ((g : ℝ) + 1) := by exact_mod_cast this
    linarith
  have h4 : (2 : ℝ) ^ (m - g) * 2 ^ g = 2 ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hgm]
  rw [show (2 : ℝ) ^ m * (6 / √m) = 6 * 2 ^ m / √m by ring, le_div_iff₀ hsm]
  push_cast
  have hc0 : (0 : ℝ) ≤ ((g.choose (g / 2) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hp0 : (0 : ℝ) < 2 ^ (m - g) := by positivity
  calc ((g.choose (g / 2) : ℕ) : ℝ) * 2 ^ (m - g) * √m
      ≤ ((g.choose (g / 2) : ℕ) : ℝ) * 2 ^ (m - g) * (3 * √((g : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 3 * 2 ^ (m - g) * (((g.choose (g / 2) : ℕ) : ℝ) * √((g : ℝ) + 1)) := by ring
    _ ≤ 3 * 2 ^ (m - g) * (2 * 2 ^ g) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 6 * ((2 : ℝ) ^ (m - g) * 2 ^ g) := by ring
    _ = 6 * 2 ^ m := by rw [h4]

lemma harm (K : ℕ) (hK : 1 ≤ K) : ∑ i ∈ Icc 1 K, 1 / (i : ℝ) ≤ 1 + log K := by
  induction K, hK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < K / (K + 1) by positivity)
    rw [Real.log_div hKpos.ne' (by positivity)] at h
    have e : (K : ℝ) / (K + 1) - 1 = -(1 / ((K : ℝ) + 1)) := by
      field_simp
      ring
    push_cast
    linarith

lemma two_div_sin (M i : ℕ) (hi : 0 < i) (hiM : i < M) :
    0 < sin (π * i / M) ∧
      2 / sin (π * i / M) ≤ (M : ℝ) * (1 / i + 1 / ((M - i : ℕ) : ℝ)) := by
  have hi' : (0 : ℝ) < i := by exact_mod_cast hi
  have hM' : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMi : (0 : ℝ) < ((M - i : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < M - i)
  have hcast : ((M - i : ℕ) : ℝ) = (M : ℝ) - i := by rw [Nat.cast_sub hiM.le]
  have hiM' : (i : ℝ) < M := by exact_mod_cast hiM
  have hy0 : 0 < π * i / M := by positivity
  have hy1 : π * i / M < π := by
    rw [div_lt_iff₀ hM']
    nlinarith [pi_pos]
  have hpos := sin_pos_of_pos_of_lt_pi hy0 hy1
  refine ⟨hpos, ?_⟩
  rw [div_le_iff₀ hpos]
  by_cases hc : π * i / M ≤ π / 2
  · have h := mul_le_sin hy0.le hc
    have e : 2 / π * (π * i / M) = 2 * i / M := by
      field_simp
    rw [e] at h
    have h1 : (M : ℝ) * (1 / i) ≤ (M : ℝ) * (1 / i + 1 / ((M - i : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [one_div_pos.mpr hMi]) hM'.le
    calc (2 : ℝ) = M * (1 / i) * (2 * i / M) := by field_simp
      _ ≤ M * (1 / i + 1 / ((M - i : ℕ) : ℝ)) * sin (π * i / M) :=
          mul_le_mul h1 h (by positivity) (by positivity)
  · have hc' : π - π * i / M ≤ π / 2 := by linarith [not_le.mp hc]
    have h := mul_le_sin (by linarith : 0 ≤ π - π * i / M) hc'
    rw [sin_pi_sub] at h
    have e : 2 / π * (π - π * i / M) = 2 * ((M : ℝ) - i) / M := by
      field_simp
    rw [e, ← hcast] at h
    have h1 : (M : ℝ) * (1 / ((M - i : ℕ) : ℝ)) ≤ (M : ℝ) * (1 / i + 1 / ((M - i : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [one_div_pos.mpr hi']) hM'.le
    calc (2 : ℝ) = M * (1 / ((M - i : ℕ) : ℝ)) * (2 * ((M - i : ℕ) : ℝ) / M) := by field_simp
      _ ≤ M * (1 / i + 1 / ((M - i : ℕ) : ℝ)) * sin (π * i / M) :=
          mul_le_mul h1 h (by positivity) (by positivity)

lemma sum_inv_sin (M : ℕ) (hM : 1 ≤ M) :
    ∑ i ∈ Ioo 0 M, (2 / sin (π * i / M) + 1) ≤ (M : ℝ) * (3 + 2 * log M) := by
  have hrefl : ∑ i ∈ Ioo 0 M, 1 / ((M - i : ℕ) : ℝ) =
      ∑ i ∈ Ioo 0 M, 1 / (i : ℝ) := by
    apply sum_nbij' (fun i => M - i) (fun i => M - i)
    · intro i hi; rw [mem_Ioo] at hi ⊢; omega
    · intro i hi; rw [mem_Ioo] at hi ⊢; omega
    · intro i hi; rw [mem_Ioo] at hi; omega
    · intro i hi; rw [mem_Ioo] at hi; omega
    · intro i hi; rfl
  have hharm : ∑ i ∈ Ioo 0 M, 1 / (i : ℝ) ≤ 1 + log M := by
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ ?_) (harm M hM)
    · intro i hi; rw [mem_Ioo] at hi; rw [mem_Icc]; omega
    · intro i _ _; positivity
  have h1 : ∑ i ∈ Ioo 0 M, (2 / sin (π * i / M) + 1) ≤
      ∑ i ∈ Ioo 0 M, ((M : ℝ) * (1 / i + 1 / ((M - i : ℕ) : ℝ)) + 1) := by
    apply sum_le_sum
    intro i hi
    rw [mem_Ioo] at hi
    linarith [(two_div_sin M i hi.1 hi.2).2]
  refine h1.trans ?_
  rw [sum_add_distrib, ← mul_sum, sum_add_distrib, hrefl, sum_const,
    Nat.card_Ioo, nsmul_eq_mul, mul_one]
  have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hc : ((M - 0 - 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast (by omega : M - 0 - 1 ≤ M)
  nlinarith

/-- Averaging over `B ⊆ [1, m]`: some `B` has few grid points with `|R_B| ≤ 1`. -/
theorem good_B (m M : ℕ) (hm : 1 ≤ m) (hM : 1 ≤ M) :
    ∃ B : Finset ℕ, B ⊆ Icc 1 m ∧
      (((bad B M).card : ℕ) : ℝ) ≤
        6 / √m * ((M : ℝ) * (3 + 2 * log M)) := by
  have hsm : 0 < √m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  have hcardP : ((Icc 1 m).powerset).card = 2 ^ m := by
    rw [card_powerset, Nat.card_Icc]
    congr 1
  have hsum : ∑ B ∈ (Icc 1 m).powerset,
      (((bad B M).card : ℕ) : ℝ) ≤
      ∑ _B ∈ (Icc 1 m).powerset, 6 / √m * ((M : ℝ) * (3 + 2 * log M)) := by
    have hswap : ∑ B ∈ (Icc 1 m).powerset,
        (((bad B M).card : ℕ) : ℝ) =
        ∑ i ∈ Ioo 0 M,
          ((((Icc 1 m).powerset.filter (fun B => |Rd B 0 (2 * π * i / M)| ≤ 1)).card : ℕ) : ℝ) := by
      simp_rw [natCast_card_filter]
      exact sum_comm
    rw [hswap, sum_const, hcardP, nsmul_eq_mul]
    have hb : ∀ i ∈ Ioo 0 M,
        ((((Icc 1 m).powerset.filter (fun B => |Rd B 0 (2 * π * i / M)| ≤ 1)).card : ℕ) : ℝ) ≤
          (2 / sin (π * i / M) + 1) * (2 ^ m * (6 / √m)) := by
      intro i hi
      rw [mem_Ioo] at hi
      have hs := (two_div_sin M i hi.1 hi.2).1
      have e : 2 * π * i / M / 2 = π * i / M := by ring
      have := bad_card m hm (2 * π * i / M) (by rw [e]; exact hs)
      rw [e] at this
      exact this
    refine (sum_le_sum hb).trans ?_
    rw [← sum_mul]
    have h := sum_inv_sin M hM
    have hpos : (0 : ℝ) ≤ 2 ^ m * (6 / √m) := by positivity
    calc (∑ i ∈ Ioo 0 M, (2 / sin (π * i / M) + 1)) * (2 ^ m * (6 / √m))
        ≤ ((M : ℝ) * (3 + 2 * log M)) * (2 ^ m * (6 / √m)) :=
          mul_le_mul_of_nonneg_right h hpos
      _ = ((2 ^ m : ℕ) : ℝ) * (6 / √m * ((M : ℝ) * (3 + 2 * log M))) := by
          push_cast; ring
  obtain ⟨B, hB, hle⟩ := exists_le_of_sum_le ⟨∅, empty_mem_powerset _⟩ hsum
  exact ⟨B, mem_powerset.mp hB, hle⟩

/-- The frequency set `[1, N] \ B`, as a set of integers. -/
noncomputable def freq (N : ℕ) (B : Finset ℕ) : Finset ℤ := (Icc 1 N \ B).map Nat.castEmbedding

lemma freq_card (N : ℕ) (B : Finset ℕ) (hB : B ⊆ Icc 1 N) : (freq N B).card = N - B.card := by
  unfold freq
  rw [card_map, card_sdiff_of_subset hB, Nat.card_Icc]
  omega

lemma freq_sum (N : ℕ) (B : Finset ℕ) (θ : ℝ) :
    ∑ a ∈ freq N B, cos (2 * π * a * θ) = ∑ k ∈ Icc 1 N \ B, cos (k * (2 * π * θ)) := by
  unfold freq
  rw [sum_map]
  apply sum_congr rfl
  intro k _
  rw [Nat.castEmbedding_apply, Int.cast_natCast]
  congr 1
  ring

lemma ncard_le (S : Set ℝ) (K : ℕ)
    (h : ∀ F : Finset ℝ, (∀ x ∈ F, x ∈ S) → F.card ≤ K) : S.ncard ≤ K := by
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨F, hFS, hFc⟩ := Set.Infinite.exists_subset_card_eq hinf (K + 1)
    have := h F (fun x hx => hFS hx)
    omega
  have := h hfin.toFinset (fun x hx => hfin.mem_toFinset.mp hx)
  rwa [← Set.ncard_eq_toFinset_card S hfin] at this

/-- Zero count for the cosine sum with frequencies `[1, N] \ B`, in the variable `θ ∈ [0, 1)`. -/
theorem zero_set (N m M : ℕ) (B : Finset ℕ) (hB : B ⊆ Icc 1 m) (hmN : m ≤ N)
    (h4 : 4 * ((m : ℝ) + 1) ^ 5 ≤ ((N : ℝ) + 1 / 2) ^ 4)
    (hmL : (m : ℝ) + 1 ≤ (N : ℝ) + 1 / 2) (hM : 2 * N + 1 ≤ M) :
    {θ : ℝ | θ ∈ Set.Ico 0 1 ∧ ∑ a ∈ freq N B, cos (2 * π * a * θ) = 0}.ncard ≤
      5 * ((bad B M).card + (4 * m + 2) + 2) := by
  classical
  apply ncard_le
  intro F hF
  have hBN : B ⊆ Icc 1 N := hB.trans (Icc_subset_Icc_right hmN)
  have hinj : Function.Injective (fun θ : ℝ => 2 * π * θ) :=
    mul_right_injective₀ (by positivity)
  rw [← card_image_of_injective F hinj]
  apply zeros_le N m M B hB h4 hmL hM
  intro t ht
  obtain ⟨θ, hθ, rfl⟩ := mem_image.mp ht
  obtain ⟨hθI, hθz⟩ := hF θ hθ
  have hπ := pi_pos
  refine ⟨by have := hθI.1; positivity, by nlinarith [hθI.2], ?_⟩
  rw [← ident N B hBN, ← freq_sum, hθz, mul_zero]

/-- **Cosine sums with few zeros.** For every `n` there is a set `A` of `n` integers such that
`∑ a ∈ A, cos (2π a θ)` has at most `C (n log n)^(2/3)` zeros in `[0, 1)`. -/
theorem main_bound : ∃ C > (0 : ℝ), ∀ n ≥ 1, ∃ A : Finset ℤ, A.card = n ∧
    ((({θ : ℝ | θ ∈ Set.Ico 0 1 ∧ ∑ a ∈ A, cos (2 * π * a * θ) = 0} : Set ℝ).ncard : ℕ) : ℕ∞) ≤
      ((⌊C * (n * log n) ^ (2 / 3 : ℝ)⌋₊ : ℕ) : ℕ∞) := by
  refine ⟨10 ^ 21, by positivity, ?_⟩
  intro n hn
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    refine ⟨{0}, by simp, ?_⟩
    have hempty : {θ : ℝ | θ ∈ Set.Ico 0 1 ∧
        ∑ a ∈ ({0} : Finset ℤ), cos (2 * π * a * θ) = 0} = ∅ := by
      ext θ
      simp
    rw [hempty]
    simp
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast h2
    have hlog2 : (6931 / 10000 : ℝ) < log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlogn : log 2 ≤ log n := Real.log_le_log (by norm_num) hnR
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = log n := ⟨_, rfl⟩
    rw [← hℓ]
    have hℓ1 : (6931 / 10000 : ℝ) < ℓ := by rw [hℓ]; linarith
    have hnl : 1 ≤ (n : ℝ) * ℓ := by nlinarith
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ((n : ℝ) * ℓ) ^ (2 / 3 : ℝ) := ⟨_, rfl⟩
    rw [← hX]
    have hX1 : 1 ≤ X := by
      rw [hX]
      exact Real.one_le_rpow hnl (by norm_num)
    have hX3 : X ^ 3 = ((n : ℝ) * ℓ) ^ 2 := by
      have e : (2 / 3 : ℝ) * ((3 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
      rw [hX, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), e, Real.rpow_natCast]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, m = ⌈X⌉₊ := ⟨_, rfl⟩
    have hmX : X ≤ m := by rw [hm]; exact Nat.le_ceil X
    have hmX1 : (m : ℝ) < X + 1 := by rw [hm]; exact Nat.ceil_lt_add_one (by linarith)
    have hm1R : (1 : ℝ) ≤ m := hX1.trans hmX
    have hm1 : 1 ≤ m := by exact_mod_cast hm1R
    have hCX : ∀ k : ℕ, (k : ℝ) ≤ 10 ^ 21 * X →
        ((k : ℕ) : ℕ∞) ≤ ((⌊(10 : ℝ) ^ 21 * X⌋₊ : ℕ) : ℕ∞) := by
      intro k hk
      exact_mod_cast Nat.le_floor hk
    by_cases hcase : 4 * ((m : ℝ) + 1) ^ 5 ≤ (n : ℝ) ^ 4
    · -- the main case: the perturbed Dirichlet kernel
      have hmn : (m : ℝ) + 1 ≤ n := by
        by_contra hc
        have hc' : (n : ℝ) < m + 1 := not_le.mp hc
        have h1 : (n : ℝ) ^ 4 < ((m : ℝ) + 1) ^ 4 :=
          pow_lt_pow_left₀ hc' (by positivity) (by norm_num)
        have h2 : ((m : ℝ) + 1) ^ 4 ≤ 4 * ((m : ℝ) + 1) ^ 5 := by
          have := pow_pos (show (0 : ℝ) < (m : ℝ) + 1 by positivity) 4
          nlinarith
        linarith
      have hmn' : m + 1 ≤ n := by exact_mod_cast hmn
      obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 2 * (n + m) + 1 := ⟨_, rfl⟩
      obtain ⟨B, hB, hcnt⟩ := good_B m M hm1 (by omega)
      have hBc : B.card ≤ m := by
        have := card_le_card hB
        rw [Nat.card_Icc] at this
        omega
      have hBR : (0 : ℝ) ≤ (B.card : ℝ) := Nat.cast_nonneg _
      refine ⟨freq (n + B.card) B, ?_, ?_⟩
      · rw [freq_card _ _ (hB.trans (Icc_subset_Icc_right (by omega)))]
        omega
      · have hNR : (n : ℝ) ≤ ((n + B.card : ℕ) : ℝ) + 1 / 2 := by push_cast; linarith
        have hz := zero_set (n + B.card) m M B hB (by omega)
          (hcase.trans (pow_le_pow_left₀ (by positivity) hNR 4)) (by linarith) (by omega)
        apply hCX
        have hzR := (Nat.cast_le (α := ℝ)).mpr hz
        push_cast at hzR
        -- estimate the grid count
        have hMR : (M : ℝ) ≤ 5 * n := by exact_mod_cast (by omega : M ≤ 5 * n)
        have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
        have h8 : log 8 = 3 * log 2 := by
          rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
          norm_num
        have h5 : log 5 ≤ 3 * ℓ := by
          have : log 5 ≤ log 8 := Real.log_le_log (by norm_num) (by norm_num)
          rw [hℓ]
          linarith
        have hlogM : log M ≤ 4 * ℓ := by
          have h := Real.log_le_log (by linarith) hMR
          rw [Real.log_mul (by norm_num) (by positivity), ← hℓ] at h
          linarith
        have hlogM0 : 0 ≤ log M := Real.log_nonneg hM1
        have hprod : (M : ℝ) * (3 + 2 * log M) ≤
            5 * n * (13 * ℓ) :=
          mul_le_mul hMR (by linarith) (by linarith) (by positivity)
        have hsm : 0 < √m := Real.sqrt_pos.mpr (by linarith)
        have hsq : (n : ℝ) * ℓ ≤ m * √m := by
          rw [← pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero, ← hX3, mul_pow,
            Real.sq_sqrt (by positivity)]
          calc X ^ 3 ≤ (m : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) hmX 3
            _ = (m : ℝ) ^ 2 * m := by ring
        have hcnt2 : 6 / √m *
            ((M : ℝ) * (3 + 2 * log M)) ≤ 390 * m := by
          calc 6 / √m *
              ((M : ℝ) * (3 + 2 * log M))
              ≤ 6 / √m * (5 * n * (13 * ℓ)) :=
                mul_le_mul_of_nonneg_left hprod (by positivity)
            _ = 6 / √m * (65 * ((n : ℝ) * ℓ)) := by ring
            _ ≤ 6 / √m * (65 * (m * √m)) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = 390 * m := by field_simp; ring
        linarith
    · -- small `n`: the plain Dirichlet kernel
      refine ⟨freq n ∅, ?_, ?_⟩
      · rw [freq_card _ _ (empty_subset _)]
        simp
      · have h4' : 4 * (((0 : ℕ) : ℝ) + 1) ^ 5 ≤ ((n : ℝ) + 1 / 2) ^ 4 := by
          calc 4 * (((0 : ℕ) : ℝ) + 1) ^ 5 ≤ (2 : ℝ) ^ 4 := by norm_num
            _ ≤ ((n : ℝ) + 1 / 2) ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
        have hz := zero_set n 0 (2 * n + 1) ∅ (empty_subset _) (Nat.zero_le _) h4'
          (by push_cast; linarith) le_rfl
        have hcf : (bad ∅ (2 * n + 1)).card ≤ 2 * n := by
          refine (card_filter_le _ _).trans ?_
          rw [Nat.card_Ioo]
          omega
        apply hCX
        have hzR := (Nat.cast_le (α := ℝ)).mpr (hz.trans (by omega : _ ≤ 20 * n))
        push_cast at hzR
        refine hzR.trans ?_
        -- `n` is bounded in this case
        have hnpos : (0 : ℝ) < n := by linarith
        have hlt : (n : ℝ) ^ 4 < 972 * X ^ 5 := by
          have h1 : (n : ℝ) ^ 4 < 4 * ((m : ℝ) + 1) ^ 5 := not_le.mp hcase
          have h2 : ((m : ℝ) + 1) ^ 5 ≤ (3 * X) ^ 5 :=
            pow_le_pow_left₀ (by positivity) (by linarith) 5
          have h3 : (3 * X) ^ 5 = 243 * X ^ 5 := by ring
          linarith
        have h12 : ((n : ℝ) ^ 4) ^ 3 < (972 * X ^ 5) ^ 3 :=
          pow_lt_pow_left₀ hlt (by positivity) (by norm_num)
        have hn2 : (n : ℝ) ^ 2 < 918330048 * ℓ ^ 10 := by
          have e1 : (972 * X ^ 5) ^ 3 = (n : ℝ) ^ 10 * (918330048 * ℓ ^ 10) := by
            calc (972 * X ^ 5) ^ 3 = 918330048 * (X ^ 3) ^ 5 := by ring
              _ = (n : ℝ) ^ 10 * (918330048 * ℓ ^ 10) := by rw [hX3]; ring
          have e2 : ((n : ℝ) ^ 4) ^ 3 = (n : ℝ) ^ 10 * (n : ℝ) ^ 2 := by ring
          rw [e1, e2] at h12
          exact lt_of_mul_lt_mul_left h12 (by positivity)
        have hℓy : ℓ ≤ 10 * (n : ℝ) ^ (1 / 10 : ℝ) := by
          have h := Real.log_le_rpow_div (Nat.cast_nonneg n) (show (0 : ℝ) < 1 / 10 by norm_num)
          rw [← hℓ] at h
          have e : (n : ℝ) ^ (1 / 10 : ℝ) / (1 / 10) = 10 * (n : ℝ) ^ (1 / 10 : ℝ) := by ring
          linarith
        have hy10 : ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 10 = n := by
          have e : (1 / 10 : ℝ) * ((10 : ℕ) : ℝ) = 1 := by norm_num
          rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), e, Real.rpow_one]
        have hℓ10 : ℓ ^ 10 ≤ 10 ^ 10 * (n : ℝ) := by
          calc ℓ ^ 10 ≤ (10 * (n : ℝ) ^ (1 / 10 : ℝ)) ^ 10 :=
                pow_le_pow_left₀ (by linarith) hℓy 10
            _ = 10 ^ 10 * (n : ℝ) := by rw [mul_pow, hy10]
        have hnb : (n : ℝ) < 918330048 * 10 ^ 10 := by
          have h : (n : ℝ) * n < n * (918330048 * 10 ^ 10) := by nlinarith
          exact lt_of_mul_lt_mul_left h hnpos.le
        have := mul_le_mul_of_nonneg_left hX1 (show (0 : ℝ) ≤ 10 ^ 21 by positivity)
        linarith

end OMA.Green82

theorem OMA.solution : type_of% @Green82.green_82_upper_bound := OMA.Green82.main_bound
