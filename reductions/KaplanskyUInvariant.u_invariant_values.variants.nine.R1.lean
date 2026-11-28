import FormalConjectures.Paper.KaplanskyUInvariant
import Mathlib

/-!
Reduction of `KaplanskyUInvariant.u_invariant_values.variants.nine` (Izhboldin's theorem,
Annals of Mathematics 154 (2001), 529-587: existence of a field of u-invariant 9) to the two
core algebraic-geometric theorems of Izhboldin (2001, Definition 0.2, Proposition 0.4, Theorem 7.3):
1. `H1`: Existence of a countable field `K` of characteristic not 2 carrying an essential
   9-dimensional diagonal quadratic form `a` (anisotropic, not a 4-fold Pfister neighbor,
   with even Clifford algebra index `>= 4`, i.e., not isomorphic to `M_8(Q)` for any quaternion
   algebra `Q = (p, q)_K` — realized by `<t_0, ..., t_8>` over `ℚ(t_0, ..., t_8)`).
2. `H2`: Izhboldin's preservation theorem (Proposition 0.4 / Theorem 7.3) for a single
   non-degenerate diagonal 10-dimensional quadratic form `b` over a countable field `K` of
   characteristic not 2: there exists a countable field extension `K'/K` (the function field
   `K(b)` of the quadric `b = 0`) making `b` isotropic while keeping `a` an essential 9-form.

In `main`, we prove completely from scratch:
- `exists_direct_limit_field`: the colimit field `F` (in `Type 0`) of a countable directed
  sequence of fields `K n` with transition homomorphisms `K n →+* K (n + 1)`, together with
  compatible embeddings and finite-tuple lifting to a common stage;
- `exists_u_invariant_nine_field_of_H1_H2`: a Cantor-dovetailing countable Merkurjev tower
  built purely from `H1` and single-form extensions `H2`, whose direct limit `F` has
  characteristic not 2, keeps `a` anisotropic, and makes every diagonal 10-form isotropic;
- `isGreatest_anisotropicDims_nine_of_forms`: full reduction from `IsGreatest (anisotropicDims F) 9`
  to an anisotropic diagonal 9-form and isotropy of all diagonal 10-forms, using orthogonal
  diagonalization (`equivalent_weightedSumSquares`) and coordinate-subspace restriction.
-/

namespace OMA.R_KaplanskyUInvariant_u_invariant_values_variants_nine_R1

/- Existence of an essential 9-dimensional diagonal quadratic form over a countable field of
characteristic not 2 (Izhboldin 2001, Definition 0.2; e.g. <t_0, ..., t_8> over ℚ(t_0, ..., t_8)). -/
def H1 : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NeZero (2 : K)) (_ : Countable K) (a : Fin 9 → K),
    (∀ i : Fin 9, a i ≠ 0) ∧
    (∀ x : Fin 9 → K, (∑ i : Fin 9, a i * x i ^ 2) = 0 → x = 0) ∧
    (∀ (c : K), c ≠ 0 → ∀ (u : Fin 4 → K), (∀ j : Fin 4, u j ≠ 0) →
      ∀ (T : (Fin 9 → K) →ₗ[K] ((Fin 4 → Bool) → K)),
        ¬ ∀ x : Fin 9 → K,
          (∑ s : Fin 4 → Bool, (∏ j : Fin 4, if s j then u j else 1) * (T x s) ^ 2) =
            c * ∑ i : Fin 9, a i * x i ^ 2) ∧
    (∀ p q : K, p ≠ 0 → q ≠ 0 →
      IsEmpty (CliffordAlgebra.even (QuadraticMap.weightedSumSquares K a) ≃ₐ[K]
        Matrix (Fin 8) (Fin 8) (QuaternionAlgebra K p 0 q)))

/- Izhboldin (2001, Proposition 0.4 / Theorem 7.3): for any essential 9-form a and any
non-degenerate diagonal 10-form b over a countable field K of characteristic not 2, there is
a countable field extension K'/K making b isotropic while preserving essentiality of a. -/
def H2 : Prop :=
  ∀ (K : Type) [Field K] [NeZero (2 : K)] [Countable K] (a : Fin 9 → K),
    (∀ i : Fin 9, a i ≠ 0) →
    (∀ x : Fin 9 → K, (∑ i : Fin 9, a i * x i ^ 2) = 0 → x = 0) →
    (∀ (c : K), c ≠ 0 → ∀ (u : Fin 4 → K), (∀ j : Fin 4, u j ≠ 0) →
      ∀ (T : (Fin 9 → K) →ₗ[K] ((Fin 4 → Bool) → K)),
        ¬ ∀ x : Fin 9 → K,
          (∑ s : Fin 4 → Bool, (∏ j : Fin 4, if s j then u j else 1) * (T x s) ^ 2) =
            c * ∑ i : Fin 9, a i * x i ^ 2) →
    (∀ p q : K, p ≠ 0 → q ≠ 0 →
      IsEmpty (CliffordAlgebra.even (QuadraticMap.weightedSumSquares K a) ≃ₐ[K]
        Matrix (Fin 8) (Fin 8) (QuaternionAlgebra K p 0 q))) →
    ∀ (b : Fin 10 → K), (∀ j : Fin 10, b j ≠ 0) →
      ∃ (K' : Type) (_ : Field K') (_ : Countable K') (f : K →+* K'),
        (∃ y : Fin 10 → K', y ≠ 0 ∧ (∑ j : Fin 10, f (b j) * y j ^ 2) = 0) ∧
        (∀ x : Fin 9 → K', (∑ i : Fin 9, f (a i) * x i ^ 2) = 0 → x = 0) ∧
        (∀ (c : K'), c ≠ 0 → ∀ (u : Fin 4 → K'), (∀ j : Fin 4, u j ≠ 0) →
          ∀ (T : (Fin 9 → K') →ₗ[K'] ((Fin 4 → Bool) → K')),
            ¬ ∀ x : Fin 9 → K',
              (∑ s : Fin 4 → Bool, (∏ j : Fin 4, if s j then u j else 1) * (T x s) ^ 2) =
                c * ∑ i : Fin 9, f (a i) * x i ^ 2) ∧
        (∀ p q : K', p ≠ 0 → q ≠ 0 →
          IsEmpty (CliffordAlgebra.even (QuadraticMap.weightedSumSquares K' (fun i => f (a i))) ≃ₐ[K']
            Matrix (Fin 8) (Fin 8) (QuaternionAlgebra K' p 0 q)))

/- Transition homomorphism family for a countable directed sequence of fields. -/
lemma exists_trans_maps (K : ℕ → Type) [∀ n, Field (K n)]
    (step : ∀ n, K n →+* K (n + 1)) :
    ∃ trans : ∀ (m n : ℕ), m ≤ n → K m →+* K n,
      (∀ (m : ℕ) (x : K m), trans m m le_rfl x = x) ∧
      (∀ {m n : ℕ} (h : m ≤ n) (x : K m),
        trans m (n + 1) (Nat.le_succ_of_le h) x = step n (trans m n h x)) ∧
      (∀ {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) (x : K l),
        trans m n h₂ (trans l m h₁ x) = trans l n (le_trans h₁ h₂) x) := by
  let trans : ∀ (m n : ℕ), m ≤ n → K m →+* K n := fun m =>
    Nat.rec
      (fun h => by
        have hm : m = 0 := Nat.eq_zero_of_le_zero h
        subst hm
        exact RingHom.id (K 0))
      (fun n ih h =>
        if hlt : m ≤ n then (step n).comp (ih hlt)
        else by
          have hm : m = n + 1 := by omega
          subst hm
          exact RingHom.id (K (n + 1)))
  have trans_self : ∀ (m : ℕ) (x : K m), trans m m le_rfl x = x := by
    intro m x
    cases m with
    | zero => rfl
    | succ n =>
      dsimp only [trans]
      split_ifs with hlt
      · exact absurd hlt (Nat.not_succ_le_self n)
      · rfl
  have trans_succ : ∀ {m n : ℕ} (h : m ≤ n) (x : K m),
      trans m (n + 1) (Nat.le_succ_of_le h) x = step n (trans m n h x) := by
    intro m n h x
    dsimp only [trans]
    split_ifs
    rfl
  have trans_comp : ∀ {l m n : ℕ} (h₁ : l ≤ m) (h₂ : m ≤ n) (x : K l),
      trans m n h₂ (trans l m h₁ x) = trans l n (le_trans h₁ h₂) x := by
    intro l m n
    induction n with
    | zero =>
      intro h₁ h₂ x
      obtain rfl : m = 0 := Nat.eq_zero_of_le_zero h₂
      obtain rfl : l = 0 := Nat.eq_zero_of_le_zero h₁
      rfl
    | succ n ih =>
      intro h₁ h₂ x
      by_cases hmn : m ≤ n
      · have hln : l ≤ n := le_trans h₁ hmn
        rw [trans_succ hmn, trans_succ hln, ih h₁ hmn x]
      · have hm : m = n + 1 := by omega
        subst hm
        exact trans_self (n + 1) (trans l (n + 1) h₁ x)
  exact ⟨trans, trans_self, trans_succ, trans_comp⟩

/- Direct limit (colimit) field of a countable directed sequence of fields in Type 0,
with compatible stage embeddings and finite-tuple lifting to a common stage. -/
lemma exists_direct_limit_field (K : ℕ → Type) [∀ n, Field (K n)]
    (step : ∀ n, K n →+* K (n + 1)) :
    ∃ (F : Type) (_ : Field F) (emb : ∀ n, K n →+* F),
      (∀ n (x : K n), emb (n + 1) (step n x) = emb n x) ∧
      (∀ (d : ℕ) (v : Fin d → F), ∃ (N : ℕ) (w : Fin d → K N), ∀ i : Fin d, v i = emb N (w i)) := by
  obtain ⟨trans, trans_self, trans_succ, trans_comp⟩ := exists_trans_maps K step
  let Rel : (Σ n : ℕ, K n) → (Σ n : ℕ, K n) → Prop := fun p q =>
    ∃ (k : ℕ) (hp : p.1 ≤ k) (hq : q.1 ≤ k), trans p.1 k hp p.2 = trans q.1 k hq q.2
  have hRel_equiv : Equivalence Rel := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨p.1, le_rfl, le_rfl, rfl⟩
    · intro p q ⟨k, hp, hq, heq⟩
      exact ⟨k, hq, hp, heq.symm⟩
    · intro p q r ⟨k₁, hp₁, hq₁, h₁⟩ ⟨k₂, hq₂, hr₂, h₂⟩
      let M := max k₁ k₂
      refine ⟨M, le_trans hp₁ (le_max_left _ _), le_trans hr₂ (le_max_right _ _), ?_⟩
      have e₁ : trans p.1 M (le_trans hp₁ (le_max_left _ _)) p.2 =
          trans q.1 M (le_trans hq₁ (le_max_left _ _)) q.2 := by
        rw [← trans_comp hp₁ (le_max_left k₁ k₂), ← trans_comp hq₁ (le_max_left k₁ k₂), h₁]
      have e₂ : trans q.1 M (le_trans hq₂ (le_max_right _ _)) q.2 =
          trans r.1 M (le_trans hr₂ (le_max_right _ _)) r.2 := by
        rw [← trans_comp hq₂ (le_max_right k₁ k₂), ← trans_comp hr₂ (le_max_right k₁ k₂), h₂]
      exact e₁.trans e₂
  let s : Setoid (Σ n : ℕ, K n) := ⟨Rel, hRel_equiv⟩
  let F : Type := Quotient s
  have hRel_trans : ∀ {m n : ℕ} (h : m ≤ n) (x : K m), Rel ⟨m, x⟩ ⟨n, trans m n h x⟩ :=
    fun h x => ⟨_, h, le_rfl, (trans_self _ _).symm⟩
  let fZero : F := Quotient.mk s ⟨0, 0⟩
  let fOne : F := Quotient.mk s ⟨0, 1⟩
  let fAdd : F → F → F := Quotient.lift₂
    (fun p q => Quotient.mk s ⟨max p.1 q.1,
      trans p.1 (max p.1 q.1) (le_max_left _ _) p.2 +
      trans q.1 (max p.1 q.1) (le_max_right _ _) q.2⟩)
    (by
      intro p₁ q₁ p₂ q₂ hp hq
      apply Quotient.sound
      rcases hp with ⟨k₁, hp₁, hp₂, hep⟩
      rcases hq with ⟨k₂, hq₁, hq₂, heq⟩
      let M := max (max (max p₁.1 q₁.1) (max p₂.1 q₂.1)) (max k₁ k₂)
      have h1 : max p₁.1 q₁.1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
      have h2 : max p₂.1 q₂.1 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
      have hk1 : k₁ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
      have hk2 : k₂ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
      refine ⟨M, h1, h2, ?_⟩
      rw [map_add, map_add, trans_comp, trans_comp, trans_comp, trans_comp]
      have ep : trans p₁.1 M (le_trans (le_max_left _ _) h1) p₁.2 =
          trans p₂.1 M (le_trans (le_max_left _ _) h2) p₂.2 := by
        rw [← trans_comp hp₁ hk1, ← trans_comp hp₂ hk1, hep]
      have eq : trans q₁.1 M (le_trans (le_max_right _ _) h1) q₁.2 =
          trans q₂.1 M (le_trans (le_max_right _ _) h2) q₂.2 := by
        rw [← trans_comp hq₁ hk2, ← trans_comp hq₂ hk2, heq]
      rw [ep, eq])
  let fMul : F → F → F := Quotient.lift₂
    (fun p q => Quotient.mk s ⟨max p.1 q.1,
      trans p.1 (max p.1 q.1) (le_max_left _ _) p.2 *
      trans q.1 (max p.1 q.1) (le_max_right _ _) q.2⟩)
    (by
      intro p₁ q₁ p₂ q₂ hp hq
      apply Quotient.sound
      rcases hp with ⟨k₁, hp₁, hp₂, hep⟩
      rcases hq with ⟨k₂, hq₁, hq₂, heq⟩
      let M := max (max (max p₁.1 q₁.1) (max p₂.1 q₂.1)) (max k₁ k₂)
      have h1 : max p₁.1 q₁.1 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
      have h2 : max p₂.1 q₂.1 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
      have hk1 : k₁ ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
      have hk2 : k₂ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
      refine ⟨M, h1, h2, ?_⟩
      rw [map_mul, map_mul, trans_comp, trans_comp, trans_comp, trans_comp]
      have ep : trans p₁.1 M (le_trans (le_max_left _ _) h1) p₁.2 =
          trans p₂.1 M (le_trans (le_max_left _ _) h2) p₂.2 := by
        rw [← trans_comp hp₁ hk1, ← trans_comp hp₂ hk1, hep]
      have eq : trans q₁.1 M (le_trans (le_max_right _ _) h1) q₁.2 =
          trans q₂.1 M (le_trans (le_max_right _ _) h2) q₂.2 := by
        rw [← trans_comp hq₁ hk2, ← trans_comp hq₂ hk2, heq]
      rw [ep, eq])
  let fNeg : F → F := Quotient.lift (fun p => Quotient.mk s ⟨p.1, -p.2⟩) (by
    intro p₁ p₂ ⟨k, h1, h2, heq⟩
    apply Quotient.sound
    exact ⟨k, h1, h2, by rw [map_neg, map_neg, heq]⟩)
  let fInv : F → F := Quotient.lift (fun p => Quotient.mk s ⟨p.1, p.2⁻¹⟩) (by
    intro p₁ p₂ ⟨k, h1, h2, heq⟩
    apply Quotient.sound
    exact ⟨k, h1, h2, by rw [map_inv₀, map_inv₀, heq]⟩)
  have mk_eq_trans : ∀ {m n : ℕ} (h : m ≤ n) (x : K m),
      Quotient.mk s ⟨m, x⟩ = Quotient.mk s ⟨n, trans m n h x⟩ :=
    fun h x => Quotient.sound (hRel_trans h x)
  have fAdd_same : ∀ (n : ℕ) (x y : K n),
      fAdd (Quotient.mk s ⟨n, x⟩) (Quotient.mk s ⟨n, y⟩) = Quotient.mk s ⟨n, x + y⟩ := by
    intro n x y
    apply Quotient.sound
    refine ⟨n, max_le le_rfl le_rfl, le_rfl, ?_⟩
    rw [map_add, trans_comp, trans_comp, trans_self, trans_self, trans_self]
  have fMul_same : ∀ (n : ℕ) (x y : K n),
      fMul (Quotient.mk s ⟨n, x⟩) (Quotient.mk s ⟨n, y⟩) = Quotient.mk s ⟨n, x * y⟩ := by
    intro n x y
    apply Quotient.sound
    refine ⟨n, max_le le_rfl le_rfl, le_rfl, ?_⟩
    rw [map_mul, trans_comp, trans_comp, trans_self, trans_self, trans_self]
  have hf_add_assoc : ∀ a b c : F, fAdd (fAdd a b) c = fAdd a (fAdd b c) := by
    intro a b c
    refine Quotient.inductionOn₃ a b c fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ => ?_
    let M := max (max i j) k
    have hi : i ≤ M := le_trans (le_max_left i j) (le_max_left _ k)
    have hj : j ≤ M := le_trans (le_max_right i j) (le_max_left _ k)
    have hk : k ≤ M := le_max_right _ k
    rw [mk_eq_trans hi x, mk_eq_trans hj y, mk_eq_trans hk z,
      fAdd_same, fAdd_same, fAdd_same, fAdd_same, add_assoc]
  have hf_zero_add : ∀ a : F, fAdd fZero a = a := by
    intro a
    refine Quotient.inductionOn a fun ⟨i, x⟩ => ?_
    change fAdd (Quotient.mk s ⟨0, 0⟩) (Quotient.mk s ⟨i, x⟩) = Quotient.mk s ⟨i, x⟩
    rw [mk_eq_trans (Nat.zero_le i) 0, map_zero, fAdd_same, zero_add]
  have hf_add_zero : ∀ a : F, fAdd a fZero = a := by
    intro a
    refine Quotient.inductionOn a fun ⟨i, x⟩ => ?_
    change fAdd (Quotient.mk s ⟨i, x⟩) (Quotient.mk s ⟨0, 0⟩) = Quotient.mk s ⟨i, x⟩
    rw [mk_eq_trans (Nat.zero_le i) 0, map_zero, fAdd_same, add_zero]
  have hf_neg_add_cancel : ∀ a : F, fAdd (fNeg a) a = fZero := by
    intro a
    refine Quotient.inductionOn a fun ⟨i, x⟩ => ?_
    change fAdd (Quotient.mk s ⟨i, -x⟩) (Quotient.mk s ⟨i, x⟩) = Quotient.mk s ⟨0, 0⟩
    rw [fAdd_same, neg_add_cancel, mk_eq_trans (Nat.zero_le i) 0, map_zero]
  have hf_add_comm : ∀ a b : F, fAdd a b = fAdd b a := by
    intro a b
    refine Quotient.inductionOn₂ a b fun ⟨i, x⟩ ⟨j, y⟩ => ?_
    rw [mk_eq_trans (le_max_left i j) x, mk_eq_trans (le_max_right i j) y,
      fAdd_same, fAdd_same, add_comm]
  have hf_mul_assoc : ∀ a b c : F, fMul (fMul a b) c = fMul a (fMul b c) := by
    intro a b c
    refine Quotient.inductionOn₃ a b c fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ => ?_
    let M := max (max i j) k
    have hi : i ≤ M := le_trans (le_max_left i j) (le_max_left _ k)
    have hj : j ≤ M := le_trans (le_max_right i j) (le_max_left _ k)
    have hk : k ≤ M := le_max_right _ k
    rw [mk_eq_trans hi x, mk_eq_trans hj y, mk_eq_trans hk z,
      fMul_same, fMul_same, fMul_same, fMul_same, mul_assoc]
  have hf_one_mul : ∀ a : F, fMul fOne a = a := by
    intro a
    refine Quotient.inductionOn a fun ⟨i, x⟩ => ?_
    change fMul (Quotient.mk s ⟨0, 1⟩) (Quotient.mk s ⟨i, x⟩) = Quotient.mk s ⟨i, x⟩
    rw [mk_eq_trans (Nat.zero_le i) 1, map_one, fMul_same, one_mul]
  have hf_mul_one : ∀ a : F, fMul a fOne = a := by
    intro a
    refine Quotient.inductionOn a fun ⟨i, x⟩ => ?_
    change fMul (Quotient.mk s ⟨i, x⟩) (Quotient.mk s ⟨0, 1⟩) = Quotient.mk s ⟨i, x⟩
    rw [mk_eq_trans (Nat.zero_le i) 1, map_one, fMul_same, mul_one]
  have hf_zero_mul : ∀ a : F, fMul fZero a = fZero := by
    intro a
    refine Quotient.inductionOn a fun ⟨i, x⟩ => ?_
    change fMul (Quotient.mk s ⟨0, 0⟩) (Quotient.mk s ⟨i, x⟩) = Quotient.mk s ⟨0, 0⟩
    rw [mk_eq_trans (Nat.zero_le i) 0, map_zero, fMul_same, zero_mul]
  have hf_mul_zero : ∀ a : F, fMul a fZero = fZero := by
    intro a
    refine Quotient.inductionOn a fun ⟨i, x⟩ => ?_
    change fMul (Quotient.mk s ⟨i, x⟩) (Quotient.mk s ⟨0, 0⟩) = Quotient.mk s ⟨0, 0⟩
    rw [mk_eq_trans (Nat.zero_le i) 0, map_zero, fMul_same, mul_zero]
  have hf_left_distrib : ∀ a b c : F, fMul a (fAdd b c) = fAdd (fMul a b) (fMul a c) := by
    intro a b c
    refine Quotient.inductionOn₃ a b c fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ => ?_
    let M := max (max i j) k
    have hi : i ≤ M := le_trans (le_max_left i j) (le_max_left _ k)
    have hj : j ≤ M := le_trans (le_max_right i j) (le_max_left _ k)
    have hk : k ≤ M := le_max_right _ k
    rw [mk_eq_trans hi x, mk_eq_trans hj y, mk_eq_trans hk z,
      fAdd_same, fMul_same, fMul_same, fMul_same, fAdd_same, left_distrib]
  have hf_right_distrib : ∀ a b c : F, fMul (fAdd a b) c = fAdd (fMul a c) (fMul b c) := by
    intro a b c
    refine Quotient.inductionOn₃ a b c fun ⟨i, x⟩ ⟨j, y⟩ ⟨k, z⟩ => ?_
    let M := max (max i j) k
    have hi : i ≤ M := le_trans (le_max_left i j) (le_max_left _ k)
    have hj : j ≤ M := le_trans (le_max_right i j) (le_max_left _ k)
    have hk : k ≤ M := le_max_right _ k
    rw [mk_eq_trans hi x, mk_eq_trans hj y, mk_eq_trans hk z,
      fAdd_same, fMul_same, fMul_same, fMul_same, fAdd_same, right_distrib]
  have hf_mul_comm : ∀ a b : F, fMul a b = fMul b a := by
    intro a b
    refine Quotient.inductionOn₂ a b fun ⟨i, x⟩ ⟨j, y⟩ => ?_
    rw [mk_eq_trans (le_max_left i j) x, mk_eq_trans (le_max_right i j) y,
      fMul_same, fMul_same, mul_comm]
  let fNsmul : ℕ → F → F := fun n x => Nat.rec fZero (fun _ acc => fAdd acc x) n
  let fZsmul : ℤ → F → F := fun z x =>
    match z with
    | Int.ofNat n => fNsmul n x
    | Int.negSucc n => fNeg (fNsmul (n + 1) x)
  let hCR : CommRing F :=
    { add := fAdd
      zero := fZero
      neg := fNeg
      mul := fMul
      one := fOne
      add_assoc := hf_add_assoc
      zero_add := hf_zero_add
      add_zero := hf_add_zero
      neg_add_cancel := hf_neg_add_cancel
      add_comm := hf_add_comm
      mul_assoc := hf_mul_assoc
      one_mul := hf_one_mul
      mul_one := hf_mul_one
      zero_mul := hf_zero_mul
      mul_zero := hf_mul_zero
      left_distrib := hf_left_distrib
      right_distrib := hf_right_distrib
      mul_comm := hf_mul_comm
      nsmul := fNsmul
      nsmul_zero := fun _ => rfl
      nsmul_succ := fun _ _ => rfl
      zsmul := fZsmul
      zsmul_zero' := fun _ => rfl
      zsmul_succ' := fun _ _ => rfl
      zsmul_neg' := fun _ _ => rfl }
  have hf_nontriv : ∃ a b : F, a ≠ b := by
    refine ⟨fZero, fOne, fun h => ?_⟩
    have hrel : Rel ⟨0, 0⟩ ⟨0, 1⟩ := Quotient.exact (s := s) h
    rcases hrel with ⟨k, h0, _, heq⟩
    rw [map_zero, map_one] at heq
    exact zero_ne_one heq
  have hf_mul_inv_cancel : ∀ a : F, a ≠ fZero → fMul a (fInv a) = fOne := by
    intro a
    refine Quotient.inductionOn a fun ⟨i, x⟩ hne => ?_
    have hx0 : x ≠ 0 := by
      intro h0
      apply hne
      subst h0
      change Quotient.mk s ⟨i, 0⟩ = Quotient.mk s ⟨0, 0⟩
      rw [mk_eq_trans (Nat.zero_le i) 0, map_zero]
    change fMul (Quotient.mk s ⟨i, x⟩) (Quotient.mk s ⟨i, x⁻¹⟩) = Quotient.mk s ⟨0, 1⟩
    rw [fMul_same, mul_inv_cancel₀ hx0, mk_eq_trans (Nat.zero_le i) 1, map_one]
  have hf_inv_zero : fInv fZero = fZero := by
    apply Quotient.sound
    exact ⟨0, le_rfl, le_rfl, by simp⟩
  let hFieldF : Field F :=
    { toCommRing := hCR
      inv := fInv
      exists_pair_ne := hf_nontriv
      mul_inv_cancel := hf_mul_inv_cancel
      inv_zero := hf_inv_zero
      nnqsmul := _
      qsmul := _ }
  let emb : ∀ n, K n →+* F := fun n =>
    { toFun := fun x => Quotient.mk s ⟨n, x⟩
      map_one' := by
        change Quotient.mk s ⟨n, 1⟩ = Quotient.mk s ⟨0, 1⟩
        rw [mk_eq_trans (Nat.zero_le n) 1, map_one]
      map_mul' := fun x y => (fMul_same n x y).symm
      map_zero' := by
        change Quotient.mk s ⟨n, 0⟩ = Quotient.mk s ⟨0, 0⟩
        rw [mk_eq_trans (Nat.zero_le n) 0, map_zero]
      map_add' := fun x y => (fAdd_same n x y).symm }
  refine ⟨F, hFieldF, emb, ?_, ?_⟩
  · intro n x
    apply Quotient.sound
    exact ⟨n + 1, le_rfl, Nat.le_succ n, by rw [trans_self, trans_succ le_rfl, trans_self]⟩
  · intro d v
    have hex : ∀ i : Fin d, ∃ p : Σ n : ℕ, K n, Quotient.mk s p = v i :=
      fun i => Quotient.exists_rep (v i)
    choose p hp using hex
    let N : ℕ := Finset.univ.sup fun i : Fin d => (p i).1
    let w : Fin d → K N := fun i =>
      trans (p i).1 N (Finset.le_sup (f := fun i : Fin d => (p i).1) (Finset.mem_univ i)) (p i).2
    refine ⟨N, w, fun i => ?_⟩
    rw [← hp i]
    apply Quotient.sound
    exact hRel_trans _ (p i).2

/- Cantor-dovetailing Merkurjev tower built from H1 (countable essential 9-form base) and H2
(single 10-form quadric extension), yielding a Type 0 field of characteristic not 2 where a
fixed diagonal 9-form remains anisotropic and every diagonal 10-form is isotropic. -/
lemma exists_u_invariant_nine_field_of_H1_H2 (hH1 : H1) (hH2 : H2) :
    ∃ (F : Type) (_ : Field F) (_ : NeZero (2 : F)) (a : Fin 9 → F),
      (∀ x : Fin 9 → F, (∑ i : Fin 9, a i * x i ^ 2) = 0 → x = 0) ∧
      (∀ b : Fin 10 → F, ∃ y : Fin 10 → F, y ≠ 0 ∧ (∑ j : Fin 10, b j * y j ^ 2) = 0) := by
  classical
  let IsEss : ∀ (K : Type), Field K → (Fin 9 → K) → Prop :=
    fun K hF a =>
      let _ : Field K := hF
      (∀ i : Fin 9, a i ≠ 0) ∧
      (∀ x : Fin 9 → K, (∑ i : Fin 9, a i * x i ^ 2) = 0 → x = 0) ∧
      (∀ (c : K), c ≠ 0 → ∀ (u : Fin 4 → K), (∀ j : Fin 4, u j ≠ 0) →
        ∀ (T : (Fin 9 → K) →ₗ[K] ((Fin 4 → Bool) → K)),
          ¬ ∀ x : Fin 9 → K,
            (∑ s : Fin 4 → Bool, (∏ j : Fin 4, if s j then u j else 1) * (T x s) ^ 2) =
              c * ∑ i : Fin 9, a i * x i ^ 2) ∧
      (∀ p q : K, p ≠ 0 → q ≠ 0 →
        IsEmpty (CliffordAlgebra.even (QuadraticMap.weightedSumSquares K a) ≃ₐ[K]
          Matrix (Fin 8) (Fin 8) (QuaternionAlgebra K p 0 q)))
  let Stage : Type 1 :=
    Σ (K : Type) (hF : Field K),
      let _ : Field K := hF
      Σ (a : Fin 9 → K),
        PLift (NeZero (2 : K) ∧ Countable K ∧ IsEss K hF a) × (ℕ → ℕ → (Fin 10 → K))
  have hex_enum : ∀ (K : Type) [Field K] [Countable K],
      ∃ e : ℕ → (Fin 10 → K), Function.Surjective e := by
    intro K _ _
    have : Nonempty (Fin 10 → K) := ⟨0⟩
    exact exists_surjective_nat (Fin 10 → K)
  obtain ⟨K₀, hF₀, h2₀, hC₀, a₀, ha0_nz, ha0_an, ha0_np, ha0_cl⟩ := hH1
  let enum₀ : ℕ → (Fin 10 → K₀) := Classical.choose (hex_enum K₀)
  have henum₀ : Function.Surjective enum₀ := Classical.choose_spec (hex_enum K₀)
  let base : Stage :=
    ⟨K₀, hF₀, a₀, ⟨⟨h2₀, hC₀, ha0_nz, ha0_an, ha0_np, ha0_cl⟩⟩, fun _ m => enum₀ m⟩
  have hadv : ∀ (n : ℕ) (st : Stage),
      let _ : Field st.1 := st.2.1
      ∃ (st' : Stage),
        let _ : Field st'.1 := st'.2.1
        ∃ (f : st.1 →+* st'.1),
          (∀ i : Fin 9, st'.2.2.1 i = f (st.2.2.1 i)) ∧
          (∃ y : Fin 10 → st'.1, y ≠ 0 ∧
            (∑ j : Fin 10, f (st.2.2.2.2 (Nat.unpair n).1 (Nat.unpair n).2 j) * y j ^ 2) = 0) ∧
          (Function.Surjective (st'.2.2.2.2 (n + 1))) ∧
          (∀ r m j, r ≠ n + 1 → st'.2.2.2.2 r m j = f (st.2.2.2.2 r m j)) := by
    intro n st
    rcases st with ⟨K, hF, a, ⟨⟨h2, hC, ha_ess⟩⟩, S⟩
    let _ : Field K := hF
    have : NeZero (2 : K) := h2
    have : Countable K := hC
    let b : Fin 10 → K := S (Nat.unpair n).1 (Nat.unpair n).2
    by_cases hb : ∀ j : Fin 10, b j ≠ 0
    · obtain ⟨K', hF', hC', f, ⟨y, hy0, hy_eq⟩, ha'_an, ha'_np, ha'_cl⟩ :=
        hH2 K a ha_ess.1 ha_ess.2.1 ha_ess.2.2.1 ha_ess.2.2.2 b hb
      let _ : Field K' := hF'
      have : Countable K' := hC'
      have h2' : NeZero (2 : K') := by
        refine ⟨fun h => ?_⟩
        have hmap : f (2 : K) = (0 : K') := by
          rw [map_ofNat]
          exact h
        exact NeZero.ne (2 : K) (f.injective (by rw [hmap, map_zero]))
      have ha'_nz : ∀ i : Fin 9, f (a i) ≠ 0 :=
        fun i h => ha_ess.1 i (f.injective (by rw [h, map_zero]))
      obtain ⟨e', he'⟩ := hex_enum K'
      let S' : ℕ → ℕ → (Fin 10 → K') := fun r m =>
        if r = n + 1 then e' m else fun j => f (S r m j)
      let st' : Stage :=
        ⟨K', hF', fun i => f (a i), ⟨⟨h2', hC', ha'_nz, ha'_an, ha'_np, ha'_cl⟩⟩, S'⟩
      refine ⟨st', f, fun _ => rfl, ⟨y, hy0, hy_eq⟩, ?_, ?_⟩
      · intro w
        obtain ⟨m, hm⟩ := he' w
        refine ⟨m, ?_⟩
        change S' (n + 1) m = w
        simp [S', hm]
      · intro r m j hr
        change S' r m j = f (S r m j)
        simp [S', hr]
    · push Not at hb
      obtain ⟨j₀, hj₀⟩ := hb
      obtain ⟨e', he'⟩ := hex_enum K
      let S' : ℕ → ℕ → (Fin 10 → K) := fun r m =>
        if r = n + 1 then e' m else S r m
      let st' : Stage := ⟨K, hF, a, ⟨⟨h2, hC, ha_ess⟩⟩, S'⟩
      refine ⟨st', RingHom.id K, fun _ => rfl, ?_, ?_, ?_⟩
      · refine ⟨Pi.single j₀ (1 : K), ?_, ?_⟩
        · intro h
          have h0 : (Pi.single j₀ (1 : K) : Fin 10 → K) j₀ = 0 := congrFun h j₀
          simp only [Pi.single_eq_same] at h0
          exact one_ne_zero h0
        · rw [Finset.sum_eq_single j₀]
          · change b j₀ * ((Pi.single j₀ (1 : K) : Fin 10 → K) j₀) ^ 2 = 0
            rw [hj₀, zero_mul]
          · intro j _ hj
            simp only [RingHom.id_apply, Pi.single_eq_of_ne hj]
            ring
          · intro h
            exact absurd (Finset.mem_univ j₀) h
      · intro w
        obtain ⟨m, hm⟩ := he' w
        refine ⟨m, ?_⟩
        change S' (n + 1) m = w
        simp [S', hm]
      · intro r m j hr
        change S' r m j = S r m j
        simp [S', hr]
  have htower_ex : ∃ (tower : ℕ → Stage),
      Function.Surjective ((tower 0).2.2.2.2 0) ∧
      ∀ n : ℕ,
        let _ : Field (tower n).1 := (tower n).2.1
        let _ : Field (tower (n + 1)).1 := (tower (n + 1)).2.1
        ∃ f : (tower n).1 →+* (tower (n + 1)).1,
          (∀ i : Fin 9, (tower (n + 1)).2.2.1 i = f ((tower n).2.2.1 i)) ∧
          (∃ y : Fin 10 → (tower (n + 1)).1, y ≠ 0 ∧
            (∑ j : Fin 10, f ((tower n).2.2.2.2 (Nat.unpair n).1 (Nat.unpair n).2 j) * y j ^ 2) = 0) ∧
          (Function.Surjective ((tower (n + 1)).2.2.2.2 (n + 1))) ∧
          (∀ r m j, r ≠ n + 1 → (tower (n + 1)).2.2.2.2 r m j = f ((tower n).2.2.2.2 r m j)) :=
    ⟨Nat.rec base fun n st => Classical.choose (hadv n st), henum₀,
      fun n => Classical.choose_spec (hadv n _)⟩
  obtain ⟨tower, hsurj0, hstep_ex⟩ := htower_ex
  let K : ℕ → Type := fun n => (tower n).1
  let _ : ∀ n, Field (K n) := fun n => (tower n).2.1
  let step : ∀ n, K n →+* K (n + 1) := fun n => Classical.choose (hstep_ex n)
  have hstep_a : ∀ n (i : Fin 9), (tower (n + 1)).2.2.1 i = step n ((tower n).2.2.1 i) :=
    fun n => (Classical.choose_spec (hstep_ex n)).1
  have hstep_kill : ∀ n, ∃ y : Fin 10 → K (n + 1), y ≠ 0 ∧
      (∑ j : Fin 10, step n ((tower n).2.2.2.2 (Nat.unpair n).1 (Nat.unpair n).2 j) * y j ^ 2) = 0 :=
    fun n => (Classical.choose_spec (hstep_ex n)).2.1
  have hstep_surj : ∀ r : ℕ, Function.Surjective ((tower r).2.2.2.2 r) := by
    intro r
    cases r with
    | zero => exact hsurj0
    | succ n => exact (Classical.choose_spec (hstep_ex n)).2.2.1
  have hstep_S : ∀ n r m j, r ≠ n + 1 →
      (tower (n + 1)).2.2.2.2 r m j = step n ((tower n).2.2.2.2 r m j) :=
    fun n => (Classical.choose_spec (hstep_ex n)).2.2.2
  obtain ⟨F, hFieldF, emb, hemb_step, hlift⟩ := exists_direct_limit_field K step
  let _ : Field F := hFieldF
  have h2F : NeZero (2 : F) := by
    refine ⟨fun h => ?_⟩
    have hmap : emb 0 (2 : K 0) = (0 : F) := by
      rw [map_ofNat]
      exact h
    have h20 : (2 : K 0) ≠ 0 := (tower 0).2.2.2.1.down.1.out
    exact h20 ((emb 0).injective (by rw [hmap, map_zero]))
  have hemb_a : ∀ n (i : Fin 9), emb n ((tower n).2.2.1 i) = emb 0 ((tower 0).2.2.1 i) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro i
      rw [hstep_a n i, hemb_step n, ih i]
  have hemb_S : ∀ {r n : ℕ} (h : r ≤ n) (m : ℕ) (j : Fin 10),
      emb n ((tower n).2.2.2.2 r m j) = emb r ((tower r).2.2.2.2 r m j) := by
    intro r n
    induction n with
    | zero =>
      intro h m j
      obtain rfl : r = 0 := Nat.eq_zero_of_le_zero h
      rfl
    | succ n ih =>
      intro h m j
      by_cases hrn : r ≤ n
      · have hne : r ≠ n + 1 := by omega
        rw [hstep_S n r m j hne, hemb_step n, ih hrn m j]
      · have hr : r = n + 1 := by omega
        subst hr
        rfl
  let aF : Fin 9 → F := fun i => emb 0 ((tower 0).2.2.1 i)
  refine ⟨F, hFieldF, h2F, aF, ?_, ?_⟩
  · intro x hx
    obtain ⟨N, w, hw⟩ := hlift 9 x
    have hsum_emb : emb N (∑ i : Fin 9, (tower N).2.2.1 i * w i ^ 2) = 0 := by
      rw [map_sum]
      have hterm : ∀ i : Fin 9,
          emb N ((tower N).2.2.1 i * w i ^ 2) = aF i * x i ^ 2 := by
        intro i
        rw [map_mul, map_pow, hemb_a N i, hw i]
      simp only [hterm]
      exact hx
    have hsum_N : (∑ i : Fin 9, (tower N).2.2.1 i * w i ^ 2) = 0 :=
      (emb N).injective (by rw [hsum_emb, map_zero])
    have hw0 : w = 0 := (tower N).2.2.2.1.down.2.2.2.1 w hsum_N
    funext i
    rw [hw i, hw0]
    exact map_zero (emb N)
  · intro b
    obtain ⟨r, b₀, hb₀⟩ := hlift 10 b
    obtain ⟨m, hm⟩ := hstep_surj r b₀
    let n : ℕ := Nat.pair r m
    have hrn : r ≤ n := Nat.left_le_pair r m
    have hunp : Nat.unpair n = (r, m) := Nat.unpair_pair r m
    obtain ⟨y, hy0, hy_eq⟩ := hstep_kill n
    refine ⟨fun j => emb (n + 1) (y j), ?_, ?_⟩
    · intro h
      apply hy0
      funext j
      have hj : emb (n + 1) (y j) = 0 := congrFun h j
      exact (emb (n + 1)).injective (by rw [hj, Pi.zero_apply, map_zero])
    · have hpush : emb (n + 1) (∑ j : Fin 10,
          step n ((tower n).2.2.2.2 (Nat.unpair n).1 (Nat.unpair n).2 j) * y j ^ 2) = 0 := by
        rw [hy_eq, map_zero]
      rw [map_sum] at hpush
      have hterm : ∀ j : Fin 10,
          emb (n + 1) (step n ((tower n).2.2.2.2 (Nat.unpair n).1 (Nat.unpair n).2 j) * y j ^ 2) =
            b j * (emb (n + 1) (y j)) ^ 2 := by
        intro j
        rw [map_mul, map_pow, hemb_step n, hunp, hemb_S hrn m j]
        have hbj : (tower r).2.2.2.2 r m j = b₀ j := congrFun hm j
        rw [hbj, ← hb₀ j]
      simp only [hterm] at hpush
      exact hpush

/- Reduction of IsGreatest (anisotropicDims F) 9 to an anisotropic diagonal 9-form and
isotropy of all diagonal 10-forms, via orthogonal diagonalization and coordinate restriction. -/
lemma isGreatest_anisotropicDims_nine_of_forms (F : Type) [Field F] [NeZero (2 : F)]
    (a : Fin 9 → F)
    (ha : ∀ x : Fin 9 → F, (∑ i : Fin 9, a i * x i ^ 2) = 0 → x = 0)
    (hb : ∀ b : Fin 10 → F, ∃ y : Fin 10 → F, y ≠ 0 ∧ (∑ j : Fin 10, b j * y j ^ 2) = 0) :
    IsGreatest (QuadraticForm.anisotropicDims F) 9 := by
  refine ⟨?_, ?_⟩
  · rw [QuadraticForm.mem_anisotropicDims_iff]
    refine ⟨QuadraticMap.weightedSumSquares F a, fun x hx => ha x ?_⟩
    simpa only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul, sq] using hx
  · intro n hn
    rcases QuadraticForm.mem_anisotropicDims_iff.mp hn with ⟨Q, hQ⟩
    by_contra hlt
    have hn10 : 10 ≤ n := by omega
    let _ : Invertible (2 : F) := invertibleOfNonzero (NeZero.ne (2 : F))
    obtain ⟨w, ⟨e⟩⟩ := Q.equivalent_weightedSumSquares
    have hfr : Module.finrank F (Fin n → F) = n := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    let emb10 : Fin 10 ↪ Fin (Module.finrank F (Fin n → F)) :=
      ⟨fun j => ⟨j.val, by omega⟩, fun j₁ j₂ h =>
        Fin.ext (congrArg (Fin.val (n := Module.finrank F (Fin n → F))) h)⟩
    let b : Fin 10 → F := fun j => w (emb10 j)
    obtain ⟨y, hy0, hy_eq⟩ := hb b
    let z : Fin (Module.finrank F (Fin n → F)) → F := fun i =>
      if hi : i.val < 10 then y ⟨i.val, hi⟩ else 0
    have hz_emb : ∀ j : Fin 10, z (emb10 j) = y j := by
      intro j
      change (if hi : j.val < 10 then y ⟨j.val, hi⟩ else 0) = y j
      split_ifs with hi
      · rfl
      · exact absurd j.isLt hi
    have hz_ne : z ≠ 0 := by
      intro hz0
      apply hy0
      funext j
      have h0 : z (emb10 j) = 0 := congrFun hz0 (emb10 j)
      rwa [hz_emb j] at h0
    have hz_val : QuadraticMap.weightedSumSquares F w z = 0 := by
      rw [QuadraticMap.weightedSumSquares_apply]
      have hsub : (Finset.univ.map emb10) ⊆ Finset.univ := Finset.subset_univ _
      rw [← Finset.sum_subset hsub]
      · rw [Finset.sum_map]
        have hterm : ∀ j : Fin 10, w (emb10 j) • (z (emb10 j) * z (emb10 j)) = b j * y j ^ 2 := by
          intro j
          rw [hz_emb j, smul_eq_mul, sq]
        simp only [hterm]
        exact hy_eq
      · intro i _ hi
        have hge : ¬ i.val < 10 := by
          intro hlt10
          apply hi
          rw [Finset.mem_map]
          exact ⟨⟨i.val, hlt10⟩, Finset.mem_univ _, Fin.ext rfl⟩
        change w i • ((if h : i.val < 10 then y ⟨i.val, h⟩ else 0) *
          (if h : i.val < 10 then y ⟨i.val, h⟩ else 0)) = 0
        simp [hge]
    have hv0 : e.symm z = 0 := hQ (e.symm z) (by rw [e.symm.map_app, hz_val])
    have hz0 : z = 0 := by
      have h1 : e (e.symm z) = e 0 := congrArg e hv0
      simpa using h1
    exact hz_ne hz0

theorem main : H1 → H2 → type_of% @KaplanskyUInvariant.u_invariant_values.variants.nine := by
  intro hH1 hH2
  obtain ⟨F, hFieldF, h2F, a, ha, hb⟩ := exists_u_invariant_nine_field_of_H1_H2 hH1 hH2
  exact ⟨F, hFieldF, h2F, isGreatest_anisotropicDims_nine_of_forms F a ha hb⟩

end OMA.R_KaplanskyUInvariant_u_invariant_values_variants_nine_R1
