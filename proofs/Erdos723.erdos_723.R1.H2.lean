import OMAReductions.R_Erdos723_erdos_723_R1
import Mathlib

-- Step H2 of reduction Erdos723.erdos_723.R1 (Erdos Problem 723): the Bruck-Ryser theorem.
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Claim: if a finite projective plane has order n with n = 1 or 2 mod 4, then n is a sum of
-- two squares.
-- Proof sketch (the classical argument, in a linear-algebra form):
-- 1. For x : P -> Q: sum over lines l of (sum of x_p for p on l)^2 = n * sum x_p^2 + (sum x_p)^2.
-- 2. The plane has N = n^2 + n + 1 points, and 4 divides N + 1. Add one variable t. With
--    n = a^2 + b^2 + c^2 + d^2 (Lagrange) and the Euler four-square matrix on blocks of four
--    variables, there are N + 1 linear forms y_i with sum y_i^2 = n * (sum x_p^2 + t^2).
-- 3. Sign matching (lemma elim): signs e_l can be chosen such that a vector with
--    L_l = e_l * y_(s l) for all lines l and y_(i0) = 0 is zero. The N equations
--    L_l = e_l * y_(s l) have a nonzero solution in dimension N + 1, so y_(i0) is not 0 there.
-- 4. For this solution n * t^2 = y_(i0)^2 + (sum x_p)^2 with t not 0, so n is a sum of two
--    rational squares, hence of two integer squares (Nat.eq_sq_add_sq_iff).

namespace OMA.P_Erdos723_R1_H2

/-- Sign matching: the signs `ε` can be chosen so that a vector that satisfies
`Lf l v = ε l * y (σ l) v` for `l ∈ S` and has `y i v = 0` outside `σ '' S` is zero. -/
lemma elim {V κ ι : Type} [AddCommGroup V] [Module ℚ V] [DecidableEq κ] [DecidableEq ι]
    (y : ι → V →ₗ[ℚ] ℚ) (Lf : κ → V →ₗ[ℚ] ℚ) (σ : κ → ι)
    (hy : ∀ v : V, (∀ i, y i v = 0) → v = 0) (S : Finset κ) :
    ∃ ε : κ → ℚ, (∀ l, ε l * ε l = 1) ∧
      ∀ v : V, (∀ l ∈ S, Lf l v = ε l * y (σ l) v) →
        (∀ i, i ∉ S.image σ → y i v = 0) → v = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => 1, fun _ => by norm_num, fun v _ h => hy v (fun i => h i (by simp))⟩
  | insert l S hl ih =>
    obtain ⟨ε, hε, hS⟩ := ih
    have key : ∀ v : V, (∀ l' ∈ S, Lf l' v = ε l' * y (σ l') v) →
        (∀ i, i ∉ (insert l S).image σ → y i v = 0) → y (σ l) v = 0 → v = 0 := by
      intro v h1 h2 h3
      apply hS v h1
      intro i hi
      by_cases hil : i = σ l
      · rw [hil]; exact h3
      · apply h2 i
        simp only [Finset.image_insert, Finset.mem_insert, not_or]
        exact ⟨hil, hi⟩
    have restr : ∀ (c : ℚ) (v : V),
        (∀ l' ∈ insert l S, Lf l' v = Function.update ε l c l' * y (σ l') v) →
        (∀ l' ∈ S, Lf l' v = ε l' * y (σ l') v) ∧ Lf l v = c * y (σ l) v := by
      intro c v h1
      refine ⟨fun l' hl' => ?_, ?_⟩
      · have hne : l' ≠ l := fun h => hl (h ▸ hl')
        have := h1 l' (Finset.mem_insert_of_mem hl')
        rwa [Function.update_of_ne hne] at this
      · have := h1 l (Finset.mem_insert_self l S)
        rwa [Function.update_self] at this
    have sq : ∀ c : ℚ, c * c = 1 → ∀ l', Function.update ε l c l' * Function.update ε l c l' = 1 := by
      intro c hc l'
      by_cases h : l' = l
      · subst h; simpa using hc
      · rw [Function.update_of_ne h]; exact hε l'
    by_cases hplus : ∀ v : V, (∀ l' ∈ S, Lf l' v = ε l' * y (σ l') v) →
        (∀ i, i ∉ (insert l S).image σ → y i v = 0) → Lf l v = y (σ l) v → v = 0
    · refine ⟨Function.update ε l 1, sq 1 (by norm_num), ?_⟩
      intro v h1 h2
      obtain ⟨h1', hl1⟩ := restr 1 v h1
      rw [one_mul] at hl1
      exact hplus v h1' h2 hl1
    · push Not at hplus
      obtain ⟨u, hu1, hu2, hu3, hu0⟩ := hplus
      refine ⟨Function.update ε l (-1), sq (-1) (by norm_num), ?_⟩
      intro v h1 h2
      obtain ⟨h1', hl1⟩ := restr (-1) v h1
      have ha : y (σ l) u ≠ 0 := fun h => hu0 (key u hu1 hu2 h)
      have hz : (y (σ l) v) • u - (y (σ l) u) • v = 0 := by
        apply key
        · intro l' hl'
          simp only [map_sub, map_smul, smul_eq_mul, hu1 l' hl', h1' l' hl']
          ring
        · intro i hi
          simp only [map_sub, map_smul, smul_eq_mul, hu2 i hi, h2 i hi]
          ring
        · simp only [map_sub, map_smul, smul_eq_mul]
          ring
      have hL : y (σ l) v * Lf l u - y (σ l) u * Lf l v = 0 := by
        have := congrArg (Lf l) hz
        simpa only [map_sub, map_smul, smul_eq_mul, map_zero] using this
      rw [hu3, hl1] at hL
      have h2' : 2 * (y (σ l) u * y (σ l) v) = 0 := by linarith
      have ha' : y (σ l) v = 0 := by
        rcases mul_eq_zero.mp h2' with h | h
        · norm_num at h
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h ha
          · exact h
      exact key v h1' h2 ha'

/-- A natural number that is a sum of two rational squares up to a nonzero square factor is a
sum of two integer squares. -/
lemma two_sq (n : ℕ) (t u w : ℚ) (ht : t ≠ 0) (h : (n : ℚ) * t ^ 2 = u ^ 2 + w ^ 2) :
    ∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, 0, by norm_num⟩
  -- clear denominators
  obtain ⟨T, U, W, hT, hI⟩ : ∃ T U W : ℤ, T ≠ 0 ∧ (n : ℤ) * T ^ 2 = U ^ 2 + W ^ 2 := by
    refine ⟨t.num * u.den * w.den, u.num * t.den * w.den, w.num * t.den * u.den, ?_, ?_⟩
    · have := Rat.num_ne_zero.mpr ht
      have h1 : (u.den : ℤ) ≠ 0 := by exact_mod_cast u.den_ne_zero
      have h2 : (w.den : ℤ) ≠ 0 := by exact_mod_cast w.den_ne_zero
      exact mul_ne_zero (mul_ne_zero this h1) h2
    · have e1 : t = t.num / t.den := (Rat.num_div_den t).symm
      have e2 : u = u.num / u.den := (Rat.num_div_den u).symm
      have e3 : w = w.num / w.den := (Rat.num_div_den w).symm
      have d1 : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_ne_zero
      have d2 : (u.den : ℚ) ≠ 0 := by exact_mod_cast u.den_ne_zero
      have d3 : (w.den : ℚ) ≠ 0 := by exact_mod_cast w.den_ne_zero
      rw [e1, e2, e3] at h
      field_simp at h
      have : ((n : ℤ) * (t.num * u.den * w.den) ^ 2 : ℚ)
          = ((u.num * t.den * w.den) ^ 2 + (w.num * t.den * u.den) ^ 2 : ℚ) := by
        linear_combination h
      exact_mod_cast this
  have hN : n * T.natAbs ^ 2 = U.natAbs ^ 2 + W.natAbs ^ 2 := by
    zify
    simpa [sq_abs] using hI
  have hT' : T.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hT
  have hm := (Nat.eq_sq_add_sq_iff (n := n * T.natAbs ^ 2)).mp ⟨_, _, hN⟩
  apply Nat.eq_sq_add_sq_iff.mpr
  intro q hq hq3
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqp⟩
  have hmem : q ∈ (n * T.natAbs ^ 2).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hqp, Dvd.dvd.mul_right (Nat.dvd_of_mem_primeFactors hq) _,
      mul_ne_zero hn.ne' (pow_ne_zero 2 hT')⟩
  have hev := hm q hmem hq3
  rw [padicValNat.mul hn.ne' (pow_ne_zero 2 hT'), pow_two, padicValNat.mul hT' hT'] at hev
  obtain ⟨k, hk⟩ := hev
  exact ⟨k - padicValNat q T.natAbs, by omega⟩

end OMA.P_Erdos723_R1_H2

namespace OMA.P_Erdos723_R1_H2

open Configuration

/-- Two distinct points lie on exactly one line; a point lies on `order + 1` lines. -/
lemma card_lines_through {P L : Type} [Membership P L] [Fintype P] [Fintype L]
    [DecidableEq P] [DecidablePred fun pl : P × L => pl.1 ∈ pl.2]
    (pp : ProjectivePlane P L) (p q : P) [DecidablePred fun l : L => p ∈ l ∧ q ∈ l] :
    (Finset.univ.filter (fun l : L => p ∈ l ∧ q ∈ l)).card
      = if p = q then pp.order + 1 else 1 := by
  classical
  split_ifs with h
  · subst h
    have h1 := ProjectivePlane.lineCount_eq (P := P) (L := L) p
    unfold lineCount at h1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1
    rw [← h1]
    congr 1
    ext l
    simp
  · rw [Finset.card_eq_one]
    refine ⟨HasLines.mkLine h, ?_⟩
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hl
      rcases Nondegenerate.eq_or_eq hl.1 hl.2 (HasLines.mkLine_ax h).1 (HasLines.mkLine_ax h).2
        with h' | h'
      · exact absurd h' h
      · exact h'
    · intro hl
      rw [hl]
      exact HasLines.mkLine_ax h

/-- The basic quadratic identity of a projective plane of order `n`:
`∑_l (∑_{p ∈ l} x_p)² = n ∑_p x_p² + (∑_p x_p)²`. -/
lemma plane_identity {P L : Type} [Membership P L] [Fintype P] [Fintype L]
    (pp : ProjectivePlane P L) (x : P → ℚ) [∀ (p : P) (l : L), Decidable (p ∈ l)] :
    ∑ l : L, (∑ p : P, if p ∈ l then x p else 0) ^ 2
      = (pp.order : ℚ) * ∑ p, x p ^ 2 + (∑ p, x p) ^ 2 := by
  classical
  have h1 : ∀ l : L, (∑ p : P, if p ∈ l then x p else 0) ^ 2
      = ∑ p : P, ∑ q : P, if p ∈ l ∧ q ∈ l then x p * x q else 0 := by
    intro l
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    by_cases hp : p ∈ l <;> by_cases hq : q ∈ l <;> simp [hp, hq]
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ p : P, ∑ l : L, ∑ q : P, (if p ∈ l ∧ q ∈ l then x p * x q else 0)
      = ∑ q : P, x p * x q * (if p = q then (pp.order : ℚ) + 1 else 1) := by
    intro p
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_lines_through pp p q]
    split_ifs <;> push_cast <;> ring
  simp_rw [h2]
  have h3 : ∀ p : P, ∑ q : P, x p * x q * (if p = q then (pp.order : ℚ) + 1 else 1)
      = x p * ∑ q, x q + (pp.order : ℚ) * x p ^ 2 := by
    intro p
    have h4 : ∀ q : P, x p * x q * (if p = q then (pp.order : ℚ) + 1 else 1)
        = x p * x q + (if p = q then (pp.order : ℚ) * x p ^ 2 else 0) := by
      intro q
      split_ifs with h
      · subst h; ring
      · ring
    simp_rw [h4]
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_ite_eq]
    simp
  simp_rw [h3]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, pow_two]
  ring

end OMA.P_Erdos723_R1_H2

namespace OMA.P_Erdos723_R1_H2

open Configuration

/-- The Euler four-square matrix of `(a, b, c, d)`. -/
def euler (a b c d : ℚ) : Fin 4 → Fin 4 → ℚ :=
  ![![a, b, c, d], ![-b, a, -d, c], ![-c, d, a, -b], ![-d, -c, b, a]]

lemma euler_norm (a b c d : ℚ) (u : Fin 4 → ℚ) :
    ∑ r : Fin 4, (∑ s : Fin 4, euler a b c d r s * u s) ^ 2
      = (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) * ∑ s : Fin 4, u s ^ 2 := by
  simp [Fin.sum_univ_four, euler]
  ring

/-- Bruck-Ryser: the order of a finite projective plane that is `1` or `2` mod `4` is a sum of
two squares. -/
theorem bruck_ryser {P L : Type} [Membership P L] [Fintype P] [Fintype L]
    (pp : ProjectivePlane P L) (hmod : pp.order % 4 = 1 ∨ pp.order % 4 = 2) :
    ∃ a b : ℕ, pp.order = a ^ 2 + b ^ 2 := by
  classical
  let _ : ProjectivePlane P L := pp
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares pp.order
  have hn1 : 1 < pp.order := ProjectivePlane.one_lt_order P L
  have hcardP : Fintype.card P = pp.order ^ 2 + pp.order + 1 := ProjectivePlane.card_points P L
  have hcardL : Fintype.card P = Fintype.card L := ProjectivePlane.card_points_eq_card_lines P L
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Fintype.card (Option P) = k * 4 := by
    rw [Fintype.card_option, hcardP]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, pp.order = 4 * m + 1 ∨ pp.order = 4 * m + 2 :=
      ⟨pp.order / 4, by omega⟩
    rcases hm with hm | hm
    · exact ⟨4 * m ^ 2 + 3 * m + 1, by rw [hm]; ring⟩
    · exact ⟨4 * m ^ 2 + 5 * m + 2, by rw [hm]; ring⟩
  let e : Option P ≃ Fin k × Fin 4 := Fintype.equivOfCardEq (by simp [hk])
  let τ : L ≃ P := Fintype.equivOfCardEq hcardL.symm
  let M := euler a b c d
  let y : Fin k × Fin 4 → (Option P → ℚ) →ₗ[ℚ] ℚ :=
    fun i => ∑ s : Fin 4, M i.2 s • LinearMap.proj (e.symm (i.1, s))
  let Lf : L → (Option P → ℚ) →ₗ[ℚ] ℚ :=
    fun l => ∑ p : P, if p ∈ l then LinearMap.proj (some p) else 0
  have hyv : ∀ i v, y i v = ∑ s : Fin 4, M i.2 s * v (e.symm (i.1, s)) := by
    intro i v
    simp [y, LinearMap.sum_apply]
  have hLv : ∀ l v, Lf l v = ∑ p : P, if p ∈ l then v (some p) else 0 := by
    intro l v
    simp only [Lf, LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs <;> simp
  have hnq : ((pp.order : ℕ) : ℚ) = (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 + (d : ℚ) ^ 2 := by
    rw [← habcd]; push_cast; ring
  have hnorm : ∀ v : Option P → ℚ,
      ∑ i, (y i v) ^ 2 = (pp.order : ℚ) * ∑ o, v o ^ 2 := by
    intro v
    rw [Fintype.sum_prod_type]
    have h1 : ∀ j : Fin k, ∑ r : Fin 4, (y (j, r) v) ^ 2
        = (pp.order : ℚ) * ∑ s : Fin 4, v (e.symm (j, s)) ^ 2 := by
      intro j
      simp only [hyv]
      rw [hnq]
      exact euler_norm a b c d (fun s => v (e.symm (j, s)))
    simp_rw [h1]
    rw [← Finset.mul_sum, ← Fintype.sum_prod_type (f := fun i : Fin k × Fin 4 => v (e.symm i) ^ 2)]
    congr 1
    exact Equiv.sum_comp e.symm (fun o => v o ^ 2)
  have hn0 : (pp.order : ℚ) ≠ 0 := by
    have : pp.order ≠ 0 := by omega
    exact_mod_cast this
  have hy0 : ∀ v : Option P → ℚ, (∀ i, y i v = 0) → v = 0 := by
    intro v hv
    have h1 := hnorm v
    simp only [hv] at h1
    have h2 : ∑ o, v o ^ 2 = 0 := by
      have : (pp.order : ℚ) * ∑ o, v o ^ 2 = 0 := by rw [← h1]; simp
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hn0
      · exact h
    funext o
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun o _ => sq_nonneg (v o))).mp h2 o (Finset.mem_univ o)
    simpa using this
  let σ : L → Fin k × Fin 4 := fun l => e (some (τ l))
  obtain ⟨ε, hε, hε2⟩ := elim y Lf σ hy0 Finset.univ
  let f : (Option P → ℚ) →ₗ[ℚ] (L → ℚ) := LinearMap.pi (fun l => Lf l - ε l • y (σ l))
  have hfin : Module.finrank ℚ (L → ℚ) < Module.finrank ℚ (Option P → ℚ) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_option]
    omega
  obtain ⟨v, hvker, hv0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hfin)
  have hvl : ∀ l, Lf l v = ε l * y (σ l) v := by
    intro l
    have h1 : f v l = 0 := by rw [LinearMap.mem_ker.mp hvker]; rfl
    have h2 : f v l = Lf l v - ε l * y (σ l) v := by simp [f]
    linarith
  have hi0 : y (e none) v ≠ 0 := by
    intro h
    apply hv0
    apply hε2 v (fun l _ => hvl l)
    intro i hi
    have hi' : i = e none := by
      by_contra hne
      apply hi
      rw [Finset.mem_image]
      rcases ho : e.symm i with _ | p
      · exact absurd (by rw [← ho]; simp) hne
      · exact ⟨τ.symm p, Finset.mem_univ _, by simp [σ, ← ho]⟩
    rw [hi']; exact h
  -- the two evaluations of the sum over the lines
  have hA : ∑ l : L, (Lf l v) ^ 2
      = (pp.order : ℚ) * ∑ p : P, v (some p) ^ 2 + (∑ p : P, v (some p)) ^ 2 := by
    simp_rw [hLv]
    exact plane_identity pp (fun p => v (some p))
  have hB : ∑ l : L, (Lf l v) ^ 2 = ∑ l : L, (y (σ l) v) ^ 2 := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hvl l, mul_pow, pow_two (ε l), hε l, one_mul]
  have hC : ∑ i, (y i v) ^ 2 = (y (e none) v) ^ 2 + ∑ l : L, (y (σ l) v) ^ 2 := by
    rw [← Equiv.sum_comp e (fun i => (y i v) ^ 2), Fintype.sum_option]
    congr 1
    exact (Equiv.sum_comp τ (fun p => (y (e (some p)) v) ^ 2)).symm
  have hD := hnorm v
  rw [Fintype.sum_option] at hD
  have hfinal : (pp.order : ℚ) * (v none) ^ 2
      = (y (e none) v) ^ 2 + (∑ p : P, v (some p)) ^ 2 := by
    linarith
  have ht : v none ≠ 0 := by
    intro h
    rw [h] at hfinal
    have h1 : 0 < (y (e none) v) ^ 2 := by positivity
    have h2 : 0 ≤ (∑ p : P, v (some p)) ^ 2 := sq_nonneg _
    nlinarith
  exact two_sq pp.order (v none) (y (e none) v) (∑ p : P, v (some p)) ht hfinal

end OMA.P_Erdos723_R1_H2

theorem OMA.solution : OMA.R_Erdos723_erdos_723_R1.H2 := by
  intro P L _ _ _ pp hmod
  exact OMA.P_Erdos723_R1_H2.bruck_ryser pp hmod
