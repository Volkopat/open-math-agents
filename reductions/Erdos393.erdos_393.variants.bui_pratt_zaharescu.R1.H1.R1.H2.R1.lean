import OMAReductions.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1_H1_R1
import Mathlib

/-!
BPZ, *Power savings for counting solutions to polynomial-factorial equations*, sections 4–7.
The analytic input constructs small Taylor rows on short intervals. The algebraic
input asserts the independence of the first three twisted derivatives of the seed.
A multiplicity count at distinct reciprocal points bounds the exceptional set.
No factorial equation is assumed at the evaluation point.
-/

namespace OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1_H1_R1_H2_R1

open Finset Polynomial Filter
open scoped Classical


/-- A multiplicity budget for distinct reciprocal points in any finite block. -/
theorem reciprocal_exceptions (P : ℚ[X]) (S : Finset ℕ) (L : ℕ) :
    ((S.filter fun (n : ℕ) => L ≤ rootMultiplicity (n : ℚ)⁻¹ P).card) * L ≤ P.natDegree := by
  classical
  let bad := S.filter fun (n : ℕ) => L ≤ rootMultiplicity (n : ℚ)⁻¹ P
  let f (n : ℕ) := (n : ℚ)⁻¹
  have hi : Function.Injective f := by
    intro n m h
    exact_mod_cast (inv_injective h : (n : ℚ) = m)
  calc
    _ = ∑ n ∈ bad, L := by simp [bad]
    _ ≤ ∑ n ∈ bad, P.roots.count (f n) := by
      apply sum_le_sum
      intro n hn
      rw [Polynomial.count_roots]
      exact (mem_filter.mp hn).2
    _ = ∑ x ∈ bad.image f, P.roots.count x := by rw [sum_image hi.injOn]
    _ ≤ ∑ x ∈ bad.image f ∪ P.roots.toFinset, P.roots.count x :=
      sum_le_sum_of_subset (subset_union_left)
    _ = P.roots.card := Multiset.sum_count_eq_card (fun x hx => mem_union_right _ (by simpa using hx))
    _ ≤ P.natDegree := P.card_roots'

/-- A nonzero determinant coefficient requires independent coefficient rows whose
total order is precisely that coefficient index. -/
theorem independent_jets {d k : ℕ} (a : Fin 3 → Fin d → Fin 3 → ℚ)
    (h : (Matrix.det (Matrix.of fun i j => ∑ l : Fin d,
      (X : ℚ[X])^(l : ℕ) * C (a i l j))).coeff k ≠ 0) :
    ∃ l : Fin 3 → Fin d, (∑ i, (l i : ℕ)) = k ∧
      Matrix.det (Matrix.of fun i j => a i (l i) j) ≠ 0 := by
  classical
  let g (i : Fin 3) (l : Fin d) : Fin 3 → ℚ[X] :=
    fun j => (X : ℚ[X])^(l:ℕ) * C (a i l j)
  have expand : Matrix.det (Matrix.of fun i j => ∑ l : Fin d, g i l j) =
      ∑ l : Fin 3 → Fin d, Matrix.det (Matrix.of fun i j => g i (l i) j) := by
    convert Matrix.detRowAlternating.toMultilinearMap.map_sum g using 1
    · congr 1
      ext i j
      simp [Matrix.of_apply, Finset.sum_apply]
    · rfl
  have one (l : Fin 3 → Fin d) : Matrix.det (Matrix.of fun i j => g i (l i) j) =
      C (Matrix.det (Matrix.of fun i j => a i (l i) j)) * X^(∑ i, (l i : ℕ)) := by
    let B := Matrix.of fun i j => a i (l i) j
    change (Matrix.of (fun i j => (X : ℚ[X])^(l i : ℕ) * B.map C i j)).det = C B.det * _
    rw [Matrix.det_mul_column (fun i => (X : ℚ[X])^(l i : ℕ)) (B.map C)]
    rw [Polynomial.C.map_det, Finset.prod_pow_eq_pow_sum, mul_comm]
    rfl
  change (Matrix.det (Matrix.of fun i j => ∑ l : Fin d, g i l j)).coeff k ≠ 0 at h
  rw [expand, finsetSum_coeff] at h
  by_contra! hn
  apply h
  apply sum_eq_zero
  intro l _
  rw [one, coeff_C_mul_X_pow]
  split <;> rename_i he
  · exact hn l (by omega)
  · rfl

/-- At every reciprocal point of low multiplicity, select independent rows
of Taylor coefficients of a polynomial matrix. -/
theorem reciprocal_independent (A : Matrix (Fin 3) (Fin 3) ℚ[X])
    (hA : A.det ≠ 0) (d : ℕ) (hd : ∀ i j, (A i j).natDegree < d) (n : ℕ) :
    let x := (n : ℚ)⁻¹
    ∃ l : Fin 3 → Fin d,
      (∑ i, (l i : ℕ)) = rootMultiplicity x A.det ∧
      Matrix.det (Matrix.of fun i j => (taylor x (A i j)).coeff (l i)) ≠ 0 := by
  intro x
  let B := A.map (taylor x)
  let a (i : Fin 3) (l : Fin d) (j : Fin 3) := (taylor x (A i j)).coeff l
  have hexp : B = Matrix.of (fun i j => ∑ l : Fin d, (X : ℚ[X])^(l:ℕ) * C (a i l j)) := by
    apply Matrix.ext; intro i j
    change taylor x (A i j) = _
    have hD : (taylor x (A i j)).natDegree < d := by simpa using hd i j
    change taylor x (A i j) = ∑ l : Fin d, (X : ℚ[X])^(l:ℕ) * C ((taylor x (A i j)).coeff l)
    rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => (X : ℚ[X])^m * C ((taylor x (A i j)).coeff m))]
    simpa only [mul_comm] using (taylor x (A i j)).as_sum_range_C_mul_X_pow' hD
  have hdet : taylor x A.det = B.det := (taylorAlgHom x).map_det A
  apply independent_jets a
  rw [← hexp, ← hdet]
  rw [Polynomial.rootMultiplicity_eq_natTrailingDegree, ← taylor_apply]
  exact coeff_natTrailingDegree_ne_zero.mpr ((taylor_eq_zero x A.det).not.mpr hA)

/-- Multiplication of each Taylor column by a rational polynomial unit at the
origin preserves the determinant's vanishing order, and hence the rank conclusion. -/
theorem weighted_jets (A : Matrix (Fin 3) (Fin 3) ℚ[X]) (hA : A.det ≠ 0)
    (n : ℕ) (W : Fin 3 → ℚ[X]) (hW : ∀ j, (W j).eval 0 = 1) :
    let x := (n : ℚ)⁻¹
    ∃ l : Fin 3 → ℕ, (∑ i, l i) = rootMultiplicity x A.det ∧
      Matrix.det (Matrix.of fun i j => (W j * taylor x (A i j)).coeff (l i)) ≠ 0 := by
  classical
  intro x
  let B := Matrix.of (fun i j => W j * taylor x (A i j))
  let U := ∏ j, W j
  have hu : U.eval 0 = 1 := by simp [U, Polynomial.eval_prod, hW]
  have hU : U ≠ 0 := by intro e; simp [e] at hu
  have hT := (taylor_eq_zero x A.det).not.mpr hA
  have heq : B.det = U * taylor x A.det := by
    have h := Matrix.det_mul_row W (A.map (taylor x))
    exact h.trans (congrArg (U * ·) ((taylorAlgHom x).map_det A).symm)
  have hB : B.det ≠ 0 := heq ▸ mul_ne_zero hU hT
  have horder : rootMultiplicity 0 B.det = rootMultiplicity x A.det := by
    rw [heq, rootMultiplicity_mul (mul_ne_zero hU hT),
        rootMultiplicity_eq_zero (show ¬U.IsRoot 0 from by simpa [Polynomial.IsRoot, hu]), zero_add]
    exact Polynomial.rootMultiplicity_eq_rootMultiplicity.symm
  let d := (∑ i, ∑ j, (B i j).natDegree) + 1
  have hd (i j) : (B i j).natDegree < d := by
    have h₁ := Finset.single_le_sum (f := fun j => (B i j).natDegree)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    have h₂ := Finset.single_le_sum (f := fun i => ∑ j, (B i j).natDegree)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ i)
    dsimp [d]; omega
  obtain ⟨l, hl, hh⟩ := reciprocal_independent B hB d hd 0
  refine ⟨fun i => (l i : ℕ), ?_, ?_⟩
  · simpa [horder] using hl
  · simpa [B] using hh

/-- The local small-form construction and height estimates. Each block has
its own seed. The column factors are Taylor units at the evaluation point.
The total degree budget combines the block lengths and the derivative cutoff. -/
def H1 : Prop := ∀ r : ℕ, 2 ≤ r → ∃ η : ℝ, 0 < η ∧ ∃ K : ℝ, 0 < K ∧
  ∀ᶠ N : ℕ in atTop, let M := ⌊(N:ℝ)^(1/34:ℝ)⌋₊
    ∀ u v : ℕ, 0 < u → u < v → v ≤ M → r ∣ u → r ∣ v →
    let T := C (r : ℚ) * ∏ k ∈ Icc 1 M, (1 - C (k:ℚ)*X)
    let β : Fin 3 → ℕ := ![0, u, v]
    let step := fun (j : Fin 3) (p : ℚ[X]) =>
      T * derivative p + (∑ k ∈ Ico 1 (β j), C (k:ℚ) *
        ∏ h ∈ (Icc 1 M).erase k, (1 - C (h:ℚ)*X)) * p
    let table := fun (p : Fin 3 → ℚ[X]) =>
      Matrix.of (fun (i j : Fin 3) => (step j)^[i.val] (p j))
    let Y := fun n : ℕ => (r:ℝ)*(n.factorial:ℝ)^(1/(r:ℝ))
    let w := fun b n : ℕ => ∏ j ∈ Ico 1 b, (1-(j:ℝ)/n)^(-(1:ℝ)/r)
    ∃ B L : ℕ, ∃ block : ℕ → Fin B, ∃ seed : Fin B → Fin 3 → ℚ[X],
      (∀ b j, seed b j ≠ 0) ∧
      ((∑ b, (table (seed b)).det.natDegree : ℕ) : ℝ) * (M:ℝ)^3 ≤ K*N*(L+1:ℕ) ∧
      ∀ n ∈ Ico N (2*N), ∃ W : Fin 3 → ℚ[X], (∀ j, (W j).eval 0 = 1) ∧
        ∀ i : Fin 3, ∀ k ≤ L, ∃ c : ℚ, c ≠ 0 ∧ ∃ h : Fin 3 → ℤ,
          (∀ j, (h j : ℚ) = c * (W j * taylor (n:ℚ)⁻¹ (table (seed (block n)) i j)).coeff k) ∧
          (∀ j, |(h j:ℝ)| ≤ (Y n)^(1-η)/8) ∧
          |(h 0:ℝ)+(h 1:ℝ)*w u n+(h 2:ℝ)*w v n| ≤ 1/(8*Y n)

/-- Algebraic nonvanishing for the BPZ twisted Wronskian (Lemma 5.4).
All three seed components are nonzero and the algebraic weights have distinct
branch sets. This assertion is independent of coefficient sizes and factorials. -/
def H2 : Prop := ∀ r M u v : ℕ, 2 ≤ r → 0 < u → u < v → v ≤ M → r ∣ u → r ∣ v →
  let T := C (r : ℚ) * ∏ k ∈ Icc 1 M, (1 - C (k:ℚ)*X)
  let β : Fin 3 → ℕ := ![0, u, v]
  let step := fun (j : Fin 3) (p : ℚ[X]) =>
    T * derivative p + (∑ k ∈ Ico 1 (β j), C (k:ℚ) *
      ∏ h ∈ (Icc 1 M).erase k, (1 - C (h:ℚ)*X)) * p
  let table := fun (p : Fin 3 → ℚ[X]) =>
    Matrix.of (fun (i j : Fin 3) => (step j)^[i.val] (p j))
  ∀ p : Fin 3 → ℚ[X], (∀ j, p j ≠ 0) → (table p).det ≠ 0

theorem main : H1 → H2 → OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1_H1_R1.H2 := by
  intro analytic algebraic r hr
  obtain ⟨η, hη, K, hK, ha⟩ := analytic r hr
  let Y := fun n : ℕ => (r:ℝ)*(n.factorial:ℝ)^(1/(r:ℝ))
  let w := fun b n : ℕ => ∏ j ∈ Ico 1 b, (1-(j:ℝ)/n)^(-(1:ℝ)/r)
  refine ⟨η, hη, K, hK, ?_⟩
  filter_upwards [ha, eventually_ge_atTop 1] with N hN hN1
  intro M u v hu huv hv hru hrv cert
  let T := C (r : ℚ) * ∏ k ∈ Icc 1 M, (1 - C (k:ℚ)*X)
  let β : Fin 3 → ℕ := ![0, u, v]
  let step := fun (j : Fin 3) (p : ℚ[X]) =>
    T * derivative p + (∑ k ∈ Ico 1 (β j), C (k:ℚ) *
      ∏ h ∈ (Icc 1 M).erase k, (1 - C (h:ℚ)*X)) * p
  let table := fun (p : Fin 3 → ℚ[X]) =>
    Matrix.of (fun (i j : Fin 3) => (step j)^[i.val] (p j))
  obtain ⟨B,L,block,seed,hseed,hbudget,hrows⟩ := hN u v hu huv hv hru hrv
  let S := (Ico N (2*N)).filter (fun n => ¬cert n)
  let P := fun b => (table (seed b)).det
  have low (n : ℕ) (hn : n ∈ Ico N (2*N)) (hlo : rootMultiplicity (n:ℚ)⁻¹ (P (block n)) ≤ L) :
      cert n := by
    obtain ⟨W,hW,rows⟩ := hrows n hn
    have hnz : (table (seed (block n))).det ≠ 0 :=
      algebraic r M u v hr hu huv hv hru hrv _ (hseed _)
    obtain ⟨l,hl,hd⟩ := weighted_jets (table (seed (block n))) hnz n W hW
    have hle (i : Fin 3) : l i ≤ L :=
      (Finset.single_le_sum (f := l) (fun j _ => Nat.zero_le _) (mem_univ i)).trans (hl.le.trans hlo)
    choose c hc row he hh herr using fun i => rows i (l i) (hle i)
    refine ⟨Matrix.of row, ?_, hh, herr⟩
    intro hz
    let G := Matrix.of (fun i j => (W j * taylor (n:ℚ)⁻¹ (table (seed (block n)) i j)).coeff (l i))
    have e : (Matrix.of row).map (Int.castRingHom ℚ) = Matrix.of (fun i j => c i * G i j) := by
      apply Matrix.ext; intro i j; exact he i j
    have ed := congrArg Matrix.det e
    have hcast : ((Matrix.of row).map (Int.castRingHom ℚ)).det = 0 := by
      change ((Int.castRingHom ℚ).mapMatrix (Matrix.of row)).det = 0
      rw [← RingHom.map_det, hz, map_zero]
    rw [hcast, Matrix.det_mul_column c G] at ed
    exact (mul_ne_zero (prod_ne_zero_iff.mpr fun i _ => hc i) hd) ed.symm
  have fiber (b : Fin B) : ((S.filter (fun n => block n = b)).card) * (L+1) ≤ (P b).natDegree := by
    let F := (Ico N (2*N)).filter (fun (n : ℕ) => L+1 ≤ rootMultiplicity (n:ℚ)⁻¹ (P b))
    have sub : S.filter (fun n => block n = b) ⊆ F := by
      intro n hn
      obtain ⟨hm, hb⟩ := mem_filter.mp hn
      obtain ⟨hin,hbad⟩ := mem_filter.mp hm
      apply mem_filter.mpr
      refine ⟨hin, ?_⟩
      by_contra! h
      exact hbad (low n hin (by rw [hb]; omega))
    exact (Nat.mul_le_mul_right _ (card_le_card sub)).trans (reciprocal_exceptions (P b) _ _)
  have hcard : S.card * (L+1) ≤ ∑ b, (P b).natDegree := by
    conv_lhs => rw [card_eq_sum_card_fiberwise (f := block) (t := univ) (fun _ _ => mem_univ _)]
    rw [sum_mul]
    exact sum_le_sum fun b _ => fiber b
  have hpos : 0 < (M:ℝ) := by
    have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have hM : 1 ≤ M := Nat.one_le_floor_iff _ |>.mpr (Real.one_le_rpow hN' (by norm_num))
    exact_mod_cast (show 0 < M by omega)
  have hc' : (S.card:ℝ) * (L+1:ℕ) ≤ ((∑ b, (P b).natDegree : ℕ):ℝ) := by exact_mod_cast hcard
  have result := (mul_le_mul_of_nonneg_right hc' (pow_pos hpos 3).le).trans hbudget
  change (S.card:ℝ) ≤ K*N/(M:ℝ)^3
  apply (le_div_iff₀ (pow_pos hpos 3)).mpr
  apply le_of_mul_le_mul_right (a := ((L+1:ℕ):ℝ)) _ (by positivity)
  convert result using 1 <;> ring

end OMA.R_Erdos393_erdos_393_variants_bui_pratt_zaharescu_R1_H1_R1_H2_R1
