import OMAStatements.S_mo_278672
import Mathlib

namespace OMA.Helpers

open Matrix OMA.S_mo_278672

/-- Entries of powers of an entrywise nonnegative matrix are nonnegative. -/
theorem zdiag_pow_nonneg {n : ℕ} (A : Mat n) (hA : ∀ i j, 0 ≤ A i j) :
    ∀ m i j, 0 ≤ (A ^ m) i j := by
  intro m
  induction m with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ m ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (ih i k) (hA k j))

/-- A walk of length `m` from `i` to `j` makes the `(i, j)` entry of the `m`-th power positive. -/
theorem zdiag_walk_pos {n : ℕ} (G : SimpleGraph (Fin n)) (A : Mat n) (hA : ∀ i j, 0 ≤ A i j)
    (hpos : ∀ i j, G.Adj i j → 0 < A i j) :
    ∀ {i j : Fin n} (p : G.Walk i j), 0 < (A ^ p.length) i j := by
  intro i j p
  induction p with
  | nil =>
    rw [SimpleGraph.Walk.length_nil, pow_zero, Matrix.one_apply_eq]
    norm_num
  | @cons a b c h p ih =>
    rw [SimpleGraph.Walk.length_cons, pow_succ', Matrix.mul_apply]
    have hterm : 0 < A a b * (A ^ p.length) b c := mul_pos (hpos a b h) ih
    have hle : A a b * (A ^ p.length) b c ≤ ∑ k, A a k * (A ^ p.length) k c :=
      Finset.single_le_sum (f := fun k => A a k * (A ^ p.length) k c)
        (fun k _ => mul_nonneg (hA a k) (zdiag_pow_nonneg A hA _ k c)) (Finset.mem_univ b)
    exact lt_of_lt_of_le hterm hle

/-- A nonsymmetric positive weighting of the adjacency matrix. -/
noncomputable def zdiagWt {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) : Mat n := by
  classical
  exact Matrix.of fun i j => if G.Adj i j then (if i = u ∧ j = v then (2 : ℝ) else 1) else 0

theorem zdiagWt_apply {n : ℕ} (G : SimpleGraph (Fin n)) (u v i j : Fin n) [Decidable (G.Adj i j)] :
    zdiagWt G u v i j = if G.Adj i j then (if i = u ∧ j = v then (2 : ℝ) else 1) else 0 := by
  unfold zdiagWt
  simp only [Matrix.of_apply]
  congr 1

theorem zdiagWt_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (u v i j : Fin n) :
    0 ≤ zdiagWt G u v i j := by
  classical
  rw [zdiagWt_apply]
  split_ifs <;> norm_num

theorem zdiagWt_pos {n : ℕ} (G : SimpleGraph (Fin n)) (u v i j : Fin n) (h : G.Adj i j) :
    0 < zdiagWt G u v i j := by
  classical
  rw [zdiagWt_apply, if_pos h]
  split_ifs <;> norm_num

theorem zdiagWt_pattern {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    pattern G (zdiagWt G u v) := by
  classical
  intro i j
  rw [zdiagWt_apply]
  split_ifs with h1 h2 <;> simp [h1]

theorem zdiagWt_not_symm {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) (h : G.Adj u v) :
    ¬ (zdiagWt G u v).IsSymm := by
  classical
  intro hs
  have e := congrFun (congrFun hs u) v
  rw [Matrix.transpose_apply, zdiagWt_apply, zdiagWt_apply, if_pos h.symm, if_pos h] at e
  have huv : u ≠ v := G.ne_of_adj h
  rw [if_neg (fun hc => huv hc.2), if_pos ⟨rfl, rfl⟩] at e
  norm_num at e

/-- The sign vector of a two-colouring. -/
noncomputable def zdiagSign {n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin 2)) (i : Fin n) : ℝ :=
  if c i = 0 then 1 else -1

theorem zdiagSign_sq {n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin 2)) (i : Fin n) :
    zdiagSign c i * zdiagSign c i = 1 := by
  unfold zdiagSign
  split_ifs <;> norm_num

theorem zdiagSign_flip {n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin 2)) (A : Mat n)
    (hA : pattern G A) (i j : Fin n) :
    zdiagSign c i * A i j * zdiagSign c j = - A i j := by
  by_cases hij : G.Adj i j
  · have hne : c i ≠ c j := c.valid hij
    have key : zdiagSign c i * zdiagSign c j = -1 := by
      unfold zdiagSign
      have h0 := (c i).isLt
      have h1 := (c j).isLt
      have hne' : (c i).val ≠ (c j).val := fun e => hne (Fin.ext e)
      by_cases hi : c i = 0 <;> by_cases hj : c j = 0
      · exact absurd (hi.trans hj.symm) hne
      · rw [if_pos hi, if_neg hj]; norm_num
      · rw [if_neg hi, if_pos hj]; norm_num
      · exfalso
        have hi' : (c i).val ≠ 0 := fun e => hi (Fin.ext e)
        have hj' : (c j).val ≠ 0 := fun e => hj (Fin.ext e)
        omega
    linear_combination (A i j) * key
  · have h0 : A i j = 0 := by
      by_contra hc
      exact hij ((hA i j).mp hc)
    rw [h0]
    ring

theorem zdiagSign_pow {n : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin 2)) (A : Mat n)
    (hA : pattern G A) : ∀ m i j,
    zdiagSign c i * (A ^ m) i j * zdiagSign c j = (-1) ^ m * (A ^ m) i j := by
  intro m
  induction m with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [pow_zero, mul_one, one_mul, zdiagSign_sq]
    · ring
  | succ m ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have e1 := ih i k
    have e2 := zdiagSign_flip c A hA k j
    have e3 := zdiagSign_sq c k
    linear_combination (zdiagSign c i * (A ^ m) i k * zdiagSign c k) * e2 +
      (-(A k j)) * e1 + (zdiagSign c i * (A ^ m) i k * A k j * zdiagSign c j) * (-e3)

theorem zdiag_forward {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsBipartite) (A : Mat n)
    (hA : pattern G A) : oddDiagonal A := by
  obtain ⟨c⟩ := hG
  intro k i
  have e := zdiagSign_pow c A hA (2 * k + 1) i i
  have e3 := zdiagSign_sq c i
  have hneg : ((-1 : ℝ)) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, rfl⟩
  rw [hneg] at e
  have : 2 * (A ^ (2 * k + 1)) i i = 0 := by
    linear_combination e - ((A ^ (2 * k + 1)) i i) * e3
  linarith

theorem zdiag_backward {n : ℕ} (G : SimpleGraph (Fin n))
    (H : ∀ A : Mat n, pattern G A → ¬A.IsSymm → oddDiagonal A) : G.IsBipartite := by
  rw [SimpleGraph.IsBipartite, SimpleGraph.two_colorable_iff_forall_loop_even]
  intro u w
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  cases w with
  | nil => simp at hodd
  | @cons _ v _ h p =>
    have hd := H (zdiagWt G u v) (zdiagWt_pattern G u v) (zdiagWt_not_symm G u v h)
    obtain ⟨k, hk⟩ := hodd
    have hpos := zdiag_walk_pos G (zdiagWt G u v) (zdiagWt_nonneg G u v) (zdiagWt_pos G u v)
      (SimpleGraph.Walk.cons h p)
    rw [hk, hd k u] at hpos
    exact lt_irrefl _ hpos

theorem zdiag_reflect {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.IsBipartite) (A : Mat n)
    (hA : pattern G A) : reflected (numRange A) := by
  obtain ⟨c⟩ := hG
  rintro z ⟨x, hx, hz⟩
  set s : Fin n → ℝ := zdiagSign c with hsdef
  refine ⟨fun i => (s i : ℂ) * star (x i), ?_, ?_⟩
  · intro h0
    apply hx
    funext i
    have e := congrFun h0 i
    simp only [Pi.zero_apply] at e ⊢
    have hs : (s i : ℂ) ≠ 0 := by
      have := zdiagSign_sq c i
      intro hc
      rw [Complex.ofReal_eq_zero] at hc
      rw [hsdef] at hc
      rw [hc] at this
      norm_num at this
    have : star (x i) = 0 := (mul_eq_zero.mp e).resolve_left hs
    simpa using this
  · have key2 : ∀ i j, (s i : ℂ) * (A i j : ℂ) * (s j : ℂ) = -(A i j : ℂ) := by
      intro i j
      have := zdiagSign_flip c A hA i j
      exact_mod_cast this
    have sq2 : ∀ i, (s i : ℂ) * (s i : ℂ) = 1 := by
      intro i
      have := zdiagSign_sq c i
      exact_mod_cast this
    have hN : (star fun i => (s i : ℂ) * star (x i)) ⬝ᵥ (fun i => (s i : ℂ) * star (x i)) =
        star x ⬝ᵥ x := by
      simp only [dotProduct, Pi.star_apply, star_mul', Complex.star_def, Complex.conj_ofReal,
        Complex.conj_conj]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      linear_combination (x i * (starRingEnd ℂ) (x i)) * sq2 i
    have hNs : star (star x ⬝ᵥ x) = star x ⬝ᵥ x := by
      simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have hS : (star fun i => (s i : ℂ) * star (x i)) ⬝ᵥ
        ((A.map Complex.ofReal) *ᵥ (fun i => (s i : ℂ) * star (x i))) =
        -star (star x ⬝ᵥ ((A.map Complex.ofReal) *ᵥ x)) := by
      simp only [dotProduct, mulVec, Matrix.map_apply, Pi.star_apply, star_sum, star_mul',
        Complex.star_def, Complex.conj_ofReal, Complex.conj_conj, Finset.mul_sum,
        ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      linear_combination (x i * (starRingEnd ℂ) (x j)) * key2 i j
    rw [hS, hN, hz, star_mul', hNs]
    ring

/-- The example matrix satisfies `A^3 = -5 A`. -/
theorem zdiag_cube : exampleA * exampleA * exampleA = (-5 : ℝ) • exampleA := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, exampleA] <;> norm_num

theorem zdiag_odd_pow : ∀ k : ℕ, exampleA ^ (2 * k + 1) = ((-5 : ℝ) ^ k) • exampleA := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, pow_succ, pow_succ, ih,
      smul_mul_assoc, smul_mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc, zdiag_cube,
      smul_smul, pow_succ]

theorem zdiag_example_diag (i : Fin 3) : exampleA i i = 0 := by
  fin_cases i <;> simp [exampleA]

theorem zdiag_six (a b c d e f g h : ℝ)
    (H : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2 + g ^ 2 + h ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  have ha := sq_nonneg a
  have hb := sq_nonneg b
  have hc := sq_nonneg c
  have hd := sq_nonneg d
  have he := sq_nonneg e
  have hf := sq_nonneg f
  have hg := sq_nonneg g
  have hh := sq_nonneg h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (pow_eq_zero_iff two_ne_zero).1 (by linarith)
  · exact (pow_eq_zero_iff two_ne_zero).1 (by linarith)
  · exact (pow_eq_zero_iff two_ne_zero).1 (by linarith)
  · exact (pow_eq_zero_iff two_ne_zero).1 (by linarith)
  · exact (pow_eq_zero_iff two_ne_zero).1 (by linarith)
  · exact (pow_eq_zero_iff two_ne_zero).1 (by linarith)

end OMA.Helpers

open OMA.Helpers OMA.S_mo_278672 Matrix in
theorem OMA.solution : type_of% @OMA.S_mo_278672.main := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro n G
    exact ⟨fun hG A hA _ => zdiag_forward G hG A hA, zdiag_backward G⟩
  · intro n G A hG hA
    exact zdiag_reflect G hG A hA
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [exampleA]
  · intro h
    have e := congrFun (congrFun h 0) 1
    simp [Matrix.transpose_apply, exampleA] at e
    norm_num at e
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [exampleA, Fin.rev]
  · refine ⟨!![0, 6, 2; 2, 0, 1; 2, 3, 0], ?_, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;> simp
    · intro h
      have e := congrFun (congrFun h 0) 1
      simp [Matrix.transpose_apply] at e
    · intro h
      have e := h 1 0
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three] at e
      norm_num at e
  · intro k i
    rw [zdiag_odd_pow k, Matrix.smul_apply, zdiag_example_diag i, smul_zero]
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · simp [dotProduct, mulVec, Fin.sum_univ_three, exampleA]
      norm_num
  · rintro ⟨x, hx, h⟩
    have hre := congrArg Complex.re h
    simp [dotProduct, mulVec, Fin.sum_univ_three, exampleA, Complex.mul_re, Complex.add_re,
      Complex.mul_im] at hre
    apply hx
    have hsum : ((x 0).re ^ 2 + (x 1).re ^ 2 + (x 2).re ^ 2 + (x 0).im ^ 2 + (x 1).im ^ 2 +
        (x 2).im ^ 2) + ((x 0).re + (x 1).re + (x 2).re) ^ 2 +
        ((x 0).im + (x 1).im + (x 2).im) ^ 2 = 0 := by
      nlinarith [hre]
    obtain ⟨a0, a1, a2, b0, b1, b2⟩ := zdiag_six _ _ _ _ _ _ _ _ hsum
    funext i
    fin_cases i <;> apply Complex.ext <;> simp_all
