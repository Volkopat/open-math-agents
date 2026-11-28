import OMAStatements.S_mo_334885
import Mathlib

namespace OMA.S_mo_334885

open Polynomial
open scoped BigOperators

private theorem linear_product_bound {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (B : ℤ) (hB : 1 ≤ B) (ha : ∀ j ∈ s, |a j| + 1 ≤ B) (k : ℕ) :
    |(∏ j ∈ s, (X - C (a j))).coeff k| ≤ B ^ s.card := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k <;> simp [coeff_one]
  | @insert j s hj ih =>
    let P : ℤ[X] := ∏ l ∈ s, (X - C (a l))
    have hP (n : ℕ) : |P.coeff n| ≤ B ^ s.card :=
      ih (fun l hl => ha l (Finset.mem_insert_of_mem hl)) n
    have hAj : |a j| + 1 ≤ B := ha j (Finset.mem_insert_self ..)
    have hpow : 0 ≤ B ^ s.card := pow_nonneg (by omega) _
    have hmul (n : ℕ) : |a j| * |P.coeff n| ≤ |a j| * B ^ s.card :=
      mul_le_mul_of_nonneg_left (hP n) (abs_nonneg _)
    rw [Finset.prod_insert hj, Finset.card_insert_of_notMem hj, pow_succ]
    change |((X - C (a j)) * P).coeff k| ≤ B ^ s.card * B
    have hround := mul_le_mul_of_nonneg_left hAj hpow
    cases k with
    | zero =>
      rw [coeff_zero_eq_eval_zero, eval_mul]
      simp only [eval_sub, eval_X, eval_C, zero_sub, abs_mul, abs_neg]
      rw [← coeff_zero_eq_eval_zero]
      nlinarith [hmul 0, mul_nonneg (abs_nonneg (a j)) hpow]
    | succ k =>
      rw [coeff_X_sub_C_mul]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      nlinarith [hmul (k + 1), hP k]

private noncomputable def basis {t : ℕ} (a : Fin t → ℤ) (i : Fin t) : ℤ[X] :=
  ∏ j ∈ Finset.univ.erase i, (X - C (a j))

private noncomputable def denom {t : ℕ} (a : Fin t → ℤ) (i : Fin t) : ℤ :=
  (basis a i).eval (a i)

private theorem basis_off {t : ℕ} (a : Fin t → ℤ) {i j : Fin t} (h : j ≠ i) :
    (basis a i).eval (a j) = 0 := by
  rw [basis, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨h, Finset.mem_univ j⟩) (by simp)

private theorem denominator_ne {t : ℕ} (a : Fin t → ℤ) (ha : Function.Injective a)
    (i : Fin t) : denom a i ≠ 0 := by
  rw [denom, basis, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simpa using sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (ha h.symm))

private theorem denominator_bound {t : ℕ} (a : Fin t → ℤ) (M : ℤ) (hM : 1 ≤ M)
    (ha : ∀ i, 0 < a i ∧ a i < M) (i : Fin t) : |denom a i| ≤ (M + 1) ^ t := by
  have hB : 1 ≤ M + 1 := by omega
  rw [denom, basis, eval_prod, Finset.abs_prod]
  calc
    _ ≤ ∏ _j ∈ Finset.univ.erase i, (M + 1) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro j _
      simp only [eval_sub, eval_X, eval_C]
      exact abs_le.mpr ⟨by have := ha i; have := ha j; omega,
        by have := ha i; have := ha j; omega⟩
    _ ≤ _ := by
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      exact pow_le_pow_right₀ hB (Nat.sub_le ..)

/-- An integer interpolant with the same positive scale at every node. -/
private theorem integer_interpolant {t : ℕ} (a : Fin t → ℤ) (ha : StrictMono a)
    (M K : ℤ) (hM : 1 ≤ M) (hK : 0 ≤ K) (hdom : ∀ i, 0 < a i ∧ a i < M)
    (y : Fin t → ℤ) (hy : ∀ i, |y i| ≤ K) :
    ∃ D : ℤ, ∃ f : ℤ[X], 0 < D ∧ D ≤ (M + 1) ^ (2 * t * t) ∧
      (∀ i, f.eval (a i) = D * y i) ∧ f.natDegree ≤ t - 1 ∧
      ∀ k, |f.coeff k| ≤ (t : ℤ) * K * (M + 1) ^ (2 * t * t + t) := by
  classical
  let d := denom a
  let D := ∏ j : Fin t, d j ^ 2
  let w := fun i : Fin t => d i * ∏ j ∈ Finset.univ.erase i, d j ^ 2
  let f : ℤ[X] := ∑ i : Fin t, C (y i * w i) * basis a i
  have hB : 1 ≤ M + 1 := by omega
  have hD : 0 < D := Finset.prod_pos fun j _ =>
    sq_pos_of_ne_zero (denominator_ne a ha.injective j)
  have hfactor (i : Fin t) : w i * d i = D := by
    dsimp [w, D]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => d j ^ 2) (Finset.mem_univ i)]
    ring
  have hDb : D ≤ (M + 1) ^ (2 * t * t) := by
    calc
      D ≤ ∏ _j : Fin t, ((M + 1) ^ t) ^ 2 := by
        apply Finset.prod_le_prod (fun _ _ => sq_nonneg _)
        intro j _
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (denominator_bound a M hM hdom j) _
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, ← pow_mul]
        congr 1
        ring
  have hw (i : Fin t) : |w i| ≤ D := by
    have hd : 1 ≤ |d i| := by
      have hh := abs_pos.mpr (denominator_ne a ha.injective i)
      change 0 < |d i| at hh
      omega
    have h := mul_le_mul_of_nonneg_left hd (abs_nonneg (w i))
    rw [mul_one, ← abs_mul, hfactor, abs_of_pos hD] at h
    exact h
  refine ⟨D, f, hD, hDb, ?_, ?_, ?_⟩
  · intro i
    change (evalRingHom (a i)) f = _
    rw [show f = ∑ j : Fin t, C (y j * w j) * basis a j by rfl, map_sum]
    rw [Finset.sum_eq_single i]
    · change (C (y i * w i) * basis a i).eval (a i) = _
      rw [eval_mul, eval_C]
      change (y i * w i) * d i = D * y i
      rw [mul_assoc, hfactor, mul_comm]
    · intro j _ hj
      change (C (y j * w j) * basis a j).eval (a i) = 0
      rw [eval_mul, basis_off a (Ne.symm hj), mul_zero]
    · simp
  · apply natDegree_sum_le_of_forall_le
    intro i _
    refine (natDegree_mul_le.trans ?_)
    rw [natDegree_C, zero_add, basis]
    refine (natDegree_prod_le _ _).trans ?_
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, (1 : ℕ) :=
        Finset.sum_le_sum fun j _ => natDegree_X_sub_C_le (a j)
      _ = t - 1 := by simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  · intro k
    change |(∑ i : Fin t, C (y i * w i) * basis a i).coeff k| ≤ _
    rw [finsetSum_coeff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ _i : Fin t, K * ((M + 1) ^ (2 * t * t)) * ((M + 1) ^ t) := by
        apply Finset.sum_le_sum
        intro i _
        rw [coeff_C_mul, abs_mul, abs_mul]
        have hcoef : |(basis a i).coeff k| ≤ (M + 1) ^ t := by
          refine (linear_product_bound (Finset.univ.erase i) a (M + 1) hB ?_ k).trans ?_
          · intro j _
            rw [abs_of_pos (hdom j).1]
            have := (hdom j).2
            omega
          · rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
            exact pow_le_pow_right₀ hB (Nat.sub_le ..)
        exact mul_le_mul (mul_le_mul (hy i) ((hw i).trans hDb) (abs_nonneg _) hK)
          hcoef (abs_nonneg _) (by positivity)
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_add]
        ring

private theorem upper_bound (t : ℕ) (M : ℤ) (hM : 1 ≤ M) (a b : Fin t → ℤ)
    (ha : StrictMono a) (hb : StrictMono b)
    (hdomA : ∀ i, 0 < a i ∧ a i < M) (hdomB : ∀ i, 0 < b i ∧ b i < M) :
    ∃ f g : ℤ[X], interlaces a b f g ∧ max f.natDegree g.natDegree ≤ t-1 ∧
      ∀ k, max |f.coeff k| |g.coeff k| ≤ heightBound t M := by
  let K : ℤ := 2 * t + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let ya (i : Fin t) : ℤ := 2 * (i.val : ℤ)
  let yb (i : Fin t) : ℤ := 2 * (i.val : ℤ) + 1
  have hya (i : Fin t) : |ya i| ≤ K := by
    have hi := i.isLt
    dsimp [ya, K]
    rw [abs_of_nonneg (by positivity)]
    omega
  have hyb (i : Fin t) : |yb i| ≤ K := by
    have hi := i.isLt
    dsimp [yb, K]
    rw [abs_of_nonneg (by positivity)]
    omega
  obtain ⟨da, f, hda, hdab, hfa, hfdeg, hfcoef⟩ :=
    integer_interpolant a ha M K hM hK hdomA ya hya
  obtain ⟨db, g, hdb, hdbb, hgb, hgdeg, hgcoef⟩ :=
    integer_interpolant b hb M K hM hK hdomB yb hyb
  refine ⟨C db * f, C da * g, ?_, max_le ?_ ?_, ?_⟩
  · have hprod : 0 < da * db := mul_pos hda hdb
    have hleft (i : Fin t) : (C db * f).eval (a i) = (da * db) * ya i := by
      rw [eval_mul, eval_C, hfa]
      ring
    have hright (i : Fin t) : (C da * g).eval (b i) = (da * db) * yb i := by
      rw [eval_mul, eval_C, hgb, mul_assoc]
    constructor
    · intro i
      rw [hleft, hright]
      have hy : ya i < yb i := by dsimp [ya, yb]; omega
      exact mul_lt_mul_of_pos_left hy hprod
    · intro i j hij
      rw [hright, hleft]
      have hval : i.val < j.val := hij
      have hy : yb i < ya j := by dsimp [ya, yb]; omega
      exact mul_lt_mul_of_pos_left hy hprod
  · exact (natDegree_C_mul_le ..).trans hfdeg
  · exact (natDegree_C_mul_le ..).trans hgdeg
  · intro k
    apply max_le
    · rw [coeff_C_mul, abs_mul, abs_of_pos hdb]
      refine (mul_le_mul hdbb (hfcoef k) (abs_nonneg _) (by positivity)).trans ?_
      dsimp [heightBound, K]
      rw [show 4 * t * t + t = (2 * t * t) + (2 * t * t + t) by ring, pow_add]
      ring_nf
      exact le_rfl
    · rw [coeff_C_mul, abs_mul, abs_of_pos hda]
      refine (mul_le_mul hdab (hgcoef k) (abs_nonneg _) (by positivity)).trans ?_
      dsimp [heightBound, K]
      rw [show 4 * t * t + t = (2 * t * t) + (2 * t * t + t) by ring, pow_add]
      ring_nf
      exact le_rfl

/-- Two shared nodes per block impose opposite signs on the difference. -/
private def leftNode (i : ℕ) : ℕ :=
  6 * (i / 4) + if i % 4 = 0 then 1 else if i % 4 = 1 then 2 else if i % 4 = 2 then 4 else 5

private def rightNode (i : ℕ) : ℕ :=
  6 * (i / 4) + if i % 4 = 0 then 2 else if i % 4 = 1 then 3 else if i % 4 = 2 then 4 else 6

private def testNode (j : ℕ) : ℕ := 6 * (j / 2) + 2 + 2 * (j % 2)

private theorem left_strict : StrictMono leftNode := by
  apply strictMono_nat_of_lt_succ
  intro i
  unfold leftNode
  split_ifs <;> omega

private theorem right_strict : StrictMono rightNode := by
  apply strictMono_nat_of_lt_succ
  intro i
  unfold rightNode
  split_ifs <;> omega

private theorem test_strict : StrictMono testNode := by
  apply strictMono_nat_of_lt_succ
  intro j
  unfold testNode
  omega

private theorem degree_of_signs (P : ℝ[X]) (m : ℕ) (hm : 0 < m)
    (x : ℕ → ℝ) (hx : StrictMono x)
    (hpos : ∀ j < m, j % 2 = 0 → 0 < P.eval (x j))
    (hneg : ∀ j < m, j % 2 ≠ 0 → P.eval (x j) < 0) : m - 1 ≤ P.natDegree := by
  classical
  have hP : P ≠ 0 := by
    intro he
    have := hpos 0 hm rfl
    simp [he] at this
  have rootBetween (j : Fin (m - 1)) :
      ∃ z, z ∈ Set.Ioo (x j.val) (x (j.val + 1)) ∧ P.IsRoot z := by
    have hfirst : j.val < m := lt_of_lt_of_le j.isLt (Nat.sub_le ..)
    have hnext : j.val + 1 < m := by have := j.isLt; omega
    have hle := hx.monotone (Nat.le_succ j.val)
    have hc := P.continuous.continuousOn (s := Set.Icc (x j.val) (x (j.val + 1)))
    have hr :
        ∃ z ∈ Set.Icc (x j.val) (x (j.val + 1)), P.eval z = 0 := by
      by_cases hj : j.val % 2 = 0
      · exact intermediate_value_Icc' hle hc ⟨(hneg _ hnext (by omega)).le, (hpos _ hfirst hj).le⟩
      · exact intermediate_value_Icc hle hc ⟨(hneg _ hfirst hj).le, (hpos _ hnext (by omega)).le⟩
    obtain ⟨z, hz, hzero⟩ := hr
    have hnz (i : ℕ) (hi : i < m) : P.eval (x i) ≠ 0 := by
      by_cases h : i % 2 = 0
      · exact (hpos i hi h).ne'
      · exact (hneg i hi h).ne
    refine ⟨z, ⟨lt_of_le_of_ne hz.1 ?_, lt_of_le_of_ne hz.2 ?_⟩, hzero⟩
    · intro he
      exact hnz _ hfirst (he ▸ hzero)
    · intro he
      exact hnz _ hnext (he ▸ hzero)
  choose r hr using rootBetween
  have hrinj : Function.Injective r := by
    apply StrictMono.injective
    intro i j hij
    have hii : i.val + 1 ≤ j.val := hij
    exact ((hr i).1.2.trans_le (hx.monotone hii)).trans (hr j).1.1
  let S := Finset.univ.map ⟨r, hrinj⟩
  have hs : S.val ⊆ P.roots := by
    intro z hz
    have hz' : z ∈ S := hz
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hz'
    exact (mem_roots hP).mpr (hr j).2
  simpa [S] using card_le_degree_of_subset_roots hs

private theorem lower_bound (s : ℕ) (hs : 0 < s) :
    ∃ a b : Fin (4 * s) → ℤ, StrictMono a ∧ StrictMono b ∧
      (∀ i, 0 < a i ∧ a i < 6 * (s : ℤ) + 1) ∧
      (∀ i, 0 < b i ∧ b i < 6 * (s : ℤ) + 1) ∧
      ∀ f g : ℤ[X], interlaces a b f g → 2 * s - 1 ≤ max f.natDegree g.natDegree := by
  let a (i : Fin (4 * s)) : ℤ := leftNode i.val
  let b (i : Fin (4 * s)) : ℤ := rightNode i.val
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    change (leftNode i.val : ℤ) < (leftNode j.val : ℤ)
    exact_mod_cast left_strict (show i.val < j.val from hij)
  · intro i j hij
    change (rightNode i.val : ℤ) < (rightNode j.val : ℤ)
    exact_mod_cast right_strict (show i.val < j.val from hij)
  · intro i
    have hi := i.isLt
    have hb : 0 < leftNode i.val ∧ leftNode i.val < 6 * s + 1 := by
      unfold leftNode
      split_ifs <;> omega
    change 0 < (leftNode i.val : ℤ) ∧ (leftNode i.val : ℤ) < 6 * (s : ℤ) + 1
    exact_mod_cast hb
  · intro i
    have hi := i.isLt
    have hb : 0 < rightNode i.val ∧ rightNode i.val < 6 * s + 1 := by
      unfold rightNode
      split_ifs <;> omega
    change 0 < (rightNode i.val : ℤ) ∧ (rightNode i.val : ℤ) < 6 * (s : ℤ) + 1
    exact_mod_cast hb
  · intro f g h
    let P := (f - g).map (Int.castRingHom ℝ)
    have hEval (j : ℕ) :
        P.eval (testNode j : ℝ) = ((f.eval (testNode j : ℤ) - g.eval (testNode j : ℤ) : ℤ) : ℝ) := by
      change ((f - g).map (Int.castRingHom ℝ)).eval ((testNode j : ℤ) : ℝ) = _
      simpa only [Int.coe_castRingHom, eval_sub] using
        (eval_map_apply (p := f - g) (Int.castRingHom ℝ) (testNode j : ℤ))
    refine (degree_of_signs P (2 * s) (by omega) (fun j => testNode j) ?_ ?_ ?_).trans
      (natDegree_map_le.trans (natDegree_sub_le f g))
    · intro i j hij
      change (testNode i : ℝ) < (testNode j : ℝ)
      exact_mod_cast test_strict hij
    · intro j hj he
      let q := j / 2
      let i : Fin (4 * s) := ⟨4 * q, by dsimp [q]; omega⟩
      let k : Fin (4 * s) := ⟨4 * q + 1, by dsimp [q]; omega⟩
      have ht : b i = testNode j ∧ a k = testNode j := by
        have ht' : rightNode (4*q) = testNode j ∧ leftNode (4*q+1) = testNode j := by
          unfold rightNode leftNode testNode
          dsimp [q]
          split_ifs <;> omega
        change (rightNode (4*q) : ℤ) = (testNode j : ℤ) ∧
          (leftNode (4*q+1) : ℤ) = (testNode j : ℤ)
        exact_mod_cast ht'
      have hh := h.2 i k (show i.val < k.val by dsimp [i, k]; omega)
      rw [ht.1, ht.2] at hh
      rw [hEval]
      exact_mod_cast (sub_pos.mpr hh)
    · intro j hj ho
      let q := j / 2
      let i : Fin (4 * s) := ⟨4 * q + 2, by dsimp [q]; omega⟩
      have ht : a i = testNode j ∧ b i = testNode j := by
        have ht' : leftNode (4*q+2) = testNode j ∧ rightNode (4*q+2) = testNode j := by
          unfold leftNode rightNode testNode
          dsimp [q]
          split_ifs <;> omega
        change (leftNode (4*q+2) : ℤ) = (testNode j : ℤ) ∧
          (rightNode (4*q+2) : ℤ) = (testNode j : ℤ)
        exact_mod_cast ht'
      have hh := h.1 i
      rw [ht.1, ht.2] at hh
      rw [hEval]
      exact_mod_cast (sub_neg.mpr hh)

end OMA.S_mo_334885

open OMA.S_mo_334885 in
theorem OMA.solution : type_of% @OMA.S_mo_334885.main := by
  constructor
  · intro t M hM a b ha hb hdomA hdomB
    refine ⟨⟨?_, ?_⟩, fun hsa hsb => upper_bound t M hM a b hsa hsb hdomA hdomB⟩
    · rintro ⟨f, g, h⟩
      constructor
      · intro i j hij
        refine lt_of_le_of_ne (ha hij.le) ?_
        intro he
        exact ((h.1 i).trans (h.2 i j hij)).ne (congrArg (fun z => f.eval z) he)
      · intro i j hij
        refine lt_of_le_of_ne (hb hij.le) ?_
        intro he
        exact ((h.2 i j hij).trans (h.1 j)).ne (congrArg (fun z => g.eval z) he)
    · rintro ⟨hsa, hsb⟩
      obtain ⟨f, g, h, _, _⟩ := upper_bound t M hM a b hsa hsb hdomA hdomB
      exact ⟨f, g, h⟩
  · intro l
    exact lower_bound (2 ^ l) (by positivity)