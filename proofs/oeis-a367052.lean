import OMAStatements.S_oeis_a367052
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.LinearMap
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Relation
import Mathlib.Tactic

namespace OMA.P_oeis_a367052

open OMA.S_oeis_a367052
open scoped Classical

/-- Build the `{0, 1}`-matrix from a chosen loop vertex `v` and a DAG `R`. -/
private noncomputable def matOf {n : ℕ} (v : Fin n) (R : Fin n → Fin n → Prop) :
    Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => if (i = v ∧ j = v) ∨ R i j then 1 else 0

private lemma matOf_zero_one {n : ℕ} (v : Fin n) (R : Fin n → Fin n → Prop) (i j : Fin n) :
    matOf v R i j = 0 ∨ matOf v R i j = 1 := by
  dsimp [matOf]
  split_ifs <;> simp

private lemma matOf_charpoly {n : ℕ} (hn : 1 ≤ n) (v : Fin n)
    {R : Fin n → Fin n → Prop} (hR : isDAG R) :
    (matOf v R).charpoly = Polynomial.X ^ n - Polynomial.X ^ (n - 1) := by
  -- Define `depth u = |{x | TransGen R x u}|` and injective `b u = n * depth u + u.val`.
  let depth : Fin n → ℕ := fun u => (Finset.univ.filter (fun x => Relation.TransGen R x u)).card
  have hdepth_lt : ∀ u : Fin n, depth u < n := by
    intro u
    have hss : Finset.univ.filter (fun x => Relation.TransGen R x u) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, fun heq => ?_⟩
      have hmem : u ∈ Finset.univ.filter (fun x => Relation.TransGen R x u) := by
        rw [heq]; exact Finset.mem_univ u
      exact hR u (Finset.mem_filter.mp hmem).2
    have := Finset.card_lt_card hss
    simpa [depth] using this
  have hdepth_mono : ∀ {u w : Fin n}, R u w → depth u < depth w := by
    intro u w huw
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, Relation.TransGen.tail hx.2 huw⟩
    · intro heq
      have hmem : u ∈ Finset.univ.filter (fun x => Relation.TransGen R x w) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.TransGen.single huw⟩
      rw [← heq, Finset.mem_filter] at hmem
      exact hR u hmem.2
  let b : Fin n → ℕ := fun u => n * depth u + u.val
  have hb_inj : Function.Injective b := by
    intro u w h
    dsimp [b] at h
    have hu := u.isLt; have hw := w.isLt
    have hval : u.val = w.val := by
      have hmod := congr_arg (· % n) h
      simp only [Nat.mul_add_mod, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hw] at hmod
      exact hmod
    exact Fin.ext hval
  have hbt : (matOf v R).charmatrix.BlockTriangular b := by
    intro i j hji
    have hij : i ≠ j := fun h => by subst h; exact lt_irrefl _ hji
    have hnR : ¬ R i j := by
      intro hRij
      have hdl := hdepth_mono hRij
      have hi := i.isLt
      have hbi_lt : b i < b j := by dsimp [b]; nlinarith
      omega
    have hA0 : matOf v R i j = 0 := by
      dsimp [matOf]
      rw [if_neg]
      rintro (⟨rfl, rfl⟩ | h)
      · exact hij rfl
      · exact hnR h
    simp [Matrix.charmatrix, Matrix.diagonal, hij, hA0]
  rw [Matrix.charpoly, hbt.det]
  have hprod : ∏ k ∈ Finset.univ.image b,
      ((matOf v R).charmatrix.toSquareBlock b k).det =
      ∏ u : Fin n, (Polynomial.X - Polynomial.C (matOf v R u u)) := by
    rw [Finset.prod_image (fun x _ y _ h => hb_inj h)]
    refine Finset.prod_congr rfl (fun u _ => ?_)
    have : Unique {i : Fin n // b i = b u} :=
      { default := ⟨u, rfl⟩
        uniq := fun ⟨i, hi⟩ => Subtype.ext (hb_inj hi) }
    rw [Matrix.det_unique]
    have hdef : (default : {i : Fin n // b i = b u}).1 = u :=
      hb_inj (default : {i : Fin n // b i = b u}).2
    simp [Matrix.toSquareBlock, Matrix.toSquareBlockProp, Matrix.charmatrix, hdef]
  rw [hprod]
  have hdiag : ∀ u : Fin n, matOf v R u u = if u = v then 1 else 0 := by
    intro u
    dsimp [matOf]
    have hnr : ¬ R u u := fun h => hR u (Relation.TransGen.single h)
    by_cases huv : u = v <;> simp [huv, hnr]
  have hsplit := Finset.mul_prod_erase Finset.univ (fun u : Fin n => Polynomial.X - Polynomial.C (matOf v R u u)) (Finset.mem_univ v)
  rw [← hsplit, hdiag v, if_pos rfl, map_one]
  have herase : ∏ u ∈ Finset.univ.erase v, (Polynomial.X - Polynomial.C (matOf v R u u)) =
      Polynomial.X ^ (n - 1) := by
    have hcongr : ∏ u ∈ Finset.univ.erase v, (Polynomial.X - Polynomial.C (matOf v R u u)) =
        ∏ _u ∈ Finset.univ.erase v, (Polynomial.X : Polynomial ℚ) := by
      refine Finset.prod_congr rfl (fun u hu => ?_)
      have huv : u ≠ v := (Finset.mem_erase.mp hu).1
      rw [hdiag u, if_neg huv, map_zero, sub_zero]
    rw [hcongr, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_fin]
  rw [herase, sub_mul, one_mul, ← pow_succ', Nat.sub_add_cancel hn]

private lemma trace_pow_eq_one {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hcp : A.charpoly = Polynomial.X ^ n - Polynomial.X ^ (n - 1)) :
    ∀ k : ℕ, 1 ≤ k → (A ^ k).trace = 1 := by
  have hch : A ^ n = A ^ (n - 1) := by
    have h0 := Matrix.aeval_self_charpoly A
    rw [hcp, map_sub, map_pow, map_pow, Polynomial.aeval_X] at h0
    exact sub_eq_zero.mp h0
  have htrA : A.trace = 1 := by
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have h := Matrix.trace_eq_neg_charpoly_coeff A
    rw [hcp, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X_pow] at h
    have hne : n - 1 ≠ n := by omega
    simp [hne] at h
    linarith
  rcases eq_or_lt_of_le hn with rfl | hn2
  · intro k hk
    have hA1 : A = 1 := by simpa using hch
    rw [hA1, one_pow]
    simp [Matrix.trace]
  · set P : Matrix (Fin n) (Fin n) ℚ := A ^ (n - 1)
    set Q : Matrix (Fin n) (Fin n) ℚ := A - P
    have hAP : A * P = P := by
      dsimp [P]; rw [← pow_succ', Nat.sub_add_cancel hn]; exact hch
    have hPA : P * A = P := by
      dsimp [P]; rw [← pow_succ, Nat.sub_add_cancel hn]; exact hch
    have hApow_P : ∀ m : ℕ, A ^ m * P = P := by
      intro m; induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, mul_assoc, hAP, ih]
    have hPP : P * P = P := hApow_P (n - 1)
    have hPQ : P * Q = 0 := by dsimp [Q]; rw [mul_sub, hPA, hPP, sub_self]
    have hQP : Q * P = 0 := by dsimp [Q]; rw [sub_mul, hAP, hPP, sub_self]
    have hQkp : ∀ k : ℕ, 1 ≤ k → Q ^ k * P = 0 := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simpa using hQP
        · rw [pow_succ, mul_assoc, hQP, mul_zero]
    have hQk : ∀ k : ℕ, 1 ≤ k → A ^ k = P + Q ^ k := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · dsimp [Q]; simp
        · rw [pow_succ, ih hkpos, pow_succ, show A = P + Q by dsimp [Q]; abel]
          rw [add_mul, mul_add, mul_add, hPP, hPQ, hQkp k hkpos]
          simp
    have hQnil : IsNilpotent Q := by
      refine ⟨n - 1, ?_⟩
      have h : P + Q ^ (n - 1) = P + 0 := by rw [add_zero]; exact (hQk (n - 1) (by omega)).symm
      exact add_left_cancel h
    have hnil_tr : ∀ N : Matrix (Fin n) (Fin n) ℚ, IsNilpotent N → N.trace = 0 := by
      intro N ⟨m, hm⟩
      have hlin : IsNilpotent (Matrix.toLin' N) := by
        refine ⟨m, ?_⟩
        have hpow : ∀ r, (Matrix.toLin' N) ^ r = Matrix.toLin' (N ^ r) := by
          intro r; induction r with
          | zero => simp [Module.End.one_eq_id]
          | succ r ihr =>
            rw [pow_succ, pow_succ, ihr]
            exact (Matrix.toLin'_mul (N ^ r) N).symm
        rw [hpow m, hm, map_zero]
      have htr_nil := LinearMap.isNilpotent_trace_of_isNilpotent hlin
      have htr_eq : LinearMap.trace ℚ (Fin n → ℚ) (Matrix.toLin' N) = N.trace := by
        rw [LinearMap.trace_eq_matrix_trace ℚ (Pi.basisFun ℚ (Fin n)) (Matrix.toLin' N)]
        congr 1
        ext i j
        simp [Matrix.toLin'_apply]
      rw [htr_eq] at htr_nil
      exact htr_nil.eq_zero
    have htrQ : Q.trace = 0 := hnil_tr Q hQnil
    have htrP : P.trace = 1 := by
      have h := hQk 1 le_rfl
      rw [pow_one, pow_one] at h
      have htr := congr_arg Matrix.trace h
      rw [Matrix.trace_add, htrA, htrQ, add_zero] at htr
      exact htr.symm
    intro k hk
    rw [hQk k hk, Matrix.trace_add, htrP, hnil_tr (Q ^ k) (hQnil.pow_of_pos (by omega)), add_zero]

private lemma pow_nonneg_of_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hnn : ∀ i j, 0 ≤ A i j) : ∀ k i j, 0 ≤ (A ^ k) i j := by
  intro k
  induction k with
  | zero =>
    intro i j
    by_cases h : i = j <;> simp [h]
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg (fun u _ => mul_nonneg (ih i u) (hnn u j))

private lemma pow_diag_ge {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hnn : ∀ i j, 0 ≤ A i j) (v : Fin n) (hv : A v v = 1) :
    ∀ k, 1 ≤ (A ^ k) v v := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    calc (1 : ℚ) = (1 : ℚ) * 1 := by norm_num
      _ ≤ (A ^ k) v v * A v v := by rw [hv]; linarith
      _ ≤ ∑ u : Fin n, (A ^ k) v u * A u v :=
          Finset.single_le_sum (fun u _ => mul_nonneg (pow_nonneg_of_nonneg hnn k v u) (hnn u v)) (Finset.mem_univ v)

private lemma path_gives_pow_ge_one {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    (hnn : ∀ i j, 0 ≤ A i j) {R : Fin n → Fin n → Prop}
    (hRA : ∀ i j, R i j → A i j = 1) {u w : Fin n} (h : Relation.TransGen R u w) :
    ∃ k ≥ 1, 1 ≤ (A ^ k) u w := by
  induction h with
  | single hr =>
    exact ⟨1, le_rfl, by rw [pow_one, hRA _ _ hr]⟩
  | tail _ hr ih =>
    obtain ⟨k, hk, hge⟩ := ih
    refine ⟨k + 1, by omega, ?_⟩
    rw [pow_succ, Matrix.mul_apply]
    calc (1 : ℚ) = 1 * 1 := by norm_num
      _ ≤ (A ^ k) u _ * A _ _ := by rw [hRA _ _ hr]; linarith
      _ ≤ ∑ x : Fin n, (A ^ k) u x * A x _ :=
          Finset.single_le_sum (fun x _ => mul_nonneg (pow_nonneg_of_nonneg hnn k u x) (hnn x _)) (Finset.mem_univ _)

private lemma target_unique_diag {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : isTargetMatrix A) : ∃! v : Fin n, A v v = 1 := by
  have htr1 : A.trace = 1 := by
    have := trace_pow_eq_one hn hA.2 1 le_rfl
    simpa using this
  have hnn : ∀ i j, 0 ≤ A i j := fun i j => by rcases hA.1 i j with h | h <;> linarith
  have hex : ∃ v : Fin n, A v v = 1 := by
    by_contra hall
    push Not at hall
    have h0 : ∀ i : Fin n, A i i = 0 := fun i => (hA.1 i i).resolve_right (hall i)
    have : A.trace = 0 := by simp [Matrix.trace, h0]
    linarith
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, hv, fun u hu => ?_⟩
  by_contra huv
  have hge2 : 2 ≤ A.trace := by
    have hsum := Finset.add_sum_erase Finset.univ (fun i : Fin n => A i i) (Finset.mem_univ v)
    have hmem : u ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨huv, Finset.mem_univ u⟩
    have hle := Finset.single_le_sum (fun i _ => hnn i i) hmem
    change (2 : ℚ) ≤ ∑ i : Fin n, A i i
    linarith
  linarith

private lemma target_isDAG {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : isTargetMatrix A) : isDAG (fun i j => i ≠ j ∧ A i j = 1) := by
  intro u hcyc
  have hnn : ∀ i j, 0 ≤ A i j := fun i j => by rcases hA.1 i j with h | h <;> linarith
  obtain ⟨v, hv, _⟩ := target_unique_diag hn hA
  -- Find a vertex `w ≠ v` on the cycle `hcyc : TransGen R u u`!
  set R : Fin n → Fin n → Prop := fun i j => i ≠ j ∧ A i j = 1
  have hw_cyc : ∃ w : Fin n, w ≠ v ∧ Relation.TransGen R w w := by
    have hrt_t : ∀ {a b c : Fin n}, Relation.ReflTransGen R a b → R b c → Relation.TransGen R a c := by
      intro a b c hab hbc
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp hab with rfl | htr
      · exact Relation.TransGen.single hbc
      · exact Relation.TransGen.tail htr hbc
    by_cases huv : u = v
    · subst huv
      rcases Relation.TransGen.head'_iff.mp hcyc with ⟨w, huw, hwu⟩
      exact ⟨w, huw.1.symm, hrt_t hwu huw⟩
    · exact ⟨u, huv, hcyc⟩
  obtain ⟨w, hwv, hww⟩ := hw_cyc
  obtain ⟨k, hk, hkw⟩ := path_gives_pow_ge_one hnn (fun _ _ h => h.2) hww
  have hkv : 1 ≤ (A ^ k) v v := pow_diag_ge hnn v hv k
  have htr1 : (A ^ k).trace = 1 := trace_pow_eq_one hn hA.2 k hk
  have hge2 : 2 ≤ (A ^ k).trace := by
    have hsum := Finset.add_sum_erase Finset.univ (fun i : Fin n => (A ^ k) i i) (Finset.mem_univ v)
    have hmem : w ∈ Finset.univ.erase v := Finset.mem_erase.mpr ⟨hwv, Finset.mem_univ w⟩
    have hle := Finset.single_le_sum (fun i _ => pow_nonneg_of_nonneg hnn k i i) hmem
    change (2 : ℚ) ≤ ∑ i : Fin n, (A ^ k) i i
    linarith
  linarith

private lemma prove_a367052 (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {A : Matrix (Fin n) (Fin n) ℚ // isTargetMatrix A} =
      n * Nat.card {R : Fin n → Fin n → Prop // isDAG R} := by
  have heq : {A : Matrix (Fin n) (Fin n) ℚ // isTargetMatrix A} ≃
      Fin n × {R : Fin n → Fin n → Prop // isDAG R} :=
    { toFun := fun ⟨A, hA⟩ =>
        ⟨(target_unique_diag hn hA).choose, ⟨fun i j => i ≠ j ∧ A i j = 1, target_isDAG hn hA⟩⟩
      invFun := fun ⟨v, ⟨R, hR⟩⟩ =>
        ⟨matOf v R, ⟨matOf_zero_one v R, matOf_charpoly hn v hR⟩⟩
      left_inv := by
        rintro ⟨A, hA⟩
        apply Subtype.ext
        ext i j
        have hv := (target_unique_diag hn hA).choose_spec
        dsimp [matOf]
        by_cases hij : i = j
        · subst hij
          by_cases hiv : i = (target_unique_diag hn hA).choose
          · subst hiv; simp [hv.1]
          · have h0 : A i i = 0 := (hA.1 i i).resolve_right (fun h1 => hiv (hv.2 i h1))
            simp [hiv, h0]
        · rcases hA.1 i j with h0 | h1
          · rw [if_neg]; · exact h0.symm
            rintro (⟨rfl, rfl⟩ | ⟨_, h1'⟩)
            · exact hij rfl
            · linarith
          · rw [if_pos (Or.inr ⟨hij, h1⟩)]; exact h1.symm
      right_inv := by
        rintro ⟨v, ⟨R, hR⟩⟩
        have hmat : isTargetMatrix (matOf v R) := ⟨matOf_zero_one v R, matOf_charpoly hn v hR⟩
        have hv_eq : (target_unique_diag hn hmat).choose = v := by
          have hv1 : matOf v R v v = 1 := by dsimp [matOf]; simp
          exact ((target_unique_diag hn hmat).choose_spec.2 v hv1).symm
        refine Prod.ext hv_eq ?_
        apply Subtype.ext
        ext i j
        dsimp [matOf]
        have hnr : ∀ x, ¬ R x x := fun x h => hR x (Relation.TransGen.single h)
        by_cases hij : i = j
        · subst hij; simp [hnr i]
        · by_cases hrij : R i j
          · simp [hij, hrij]
          · have hnot : ¬ ((i = v ∧ j = v) ∨ R i j) := by
              rintro (⟨rfl, rfl⟩ | h)
              · exact hij rfl
              · exact hrij h
            rw [if_neg hnot]
            simp [hij, hrij] }
  rw [Nat.card_congr heq, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]

end OMA.P_oeis_a367052

theorem OMA.solution : type_of% @OMA.S_oeis_a367052.main :=
  OMA.P_oeis_a367052.prove_a367052
