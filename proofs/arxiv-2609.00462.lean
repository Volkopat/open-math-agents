import OMAStatements.S_arxiv_2609_00462

namespace OMA.P_arxiv_2609_00462

open OMA.S_arxiv_2609_00462

/-! ### Part 1: Tensor powers of magic unitaries and the intertwiner relation -/

/-- Entry `u^{⊗k}_{a, b} = u_{a 0, b 0} * u_{a 1, b 1} * ... * u_{a (k-1), b (k-1)}` in a
(possibly noncommutative) ring `R`. -/
private def uPow {V : Type*} {R : Type*} [Ring R] (u : Matrix V V R) :
    ∀ k : ℕ, (Fin k → V) → (Fin k → V) → R
  | 0, _, _ => 1
  | k + 1, a, b => u (a 0) (b 0) * uPow u k (fun i => a i.succ) (fun i => b i.succ)

private lemma uPow_cast {V : Type*} {R : Type*} [Ring R] (u : Matrix V V R)
    {m n : ℕ} (h : m = n) (a b : Fin m → V) :
    uPow u m a b = uPow u n (a ∘ Fin.cast h.symm) (b ∘ Fin.cast h.symm) := by
  subst h; rfl

private lemma uPow_add {V : Type*} {R : Type*} [Ring R] (u : Matrix V V R)
    (k₁ k₂ : ℕ) (a b : Fin (k₁ + k₂) → V) :
    uPow u (k₁ + k₂) a b =
      uPow u k₁ (fun i => a (Fin.castAdd k₂ i)) (fun i => b (Fin.castAdd k₂ i)) *
      uPow u k₂ (fun j => a (Fin.natAdd k₁ j)) (fun j => b (Fin.natAdd k₁ j)) := by
  induction k₁ with
  | zero =>
    rw [uPow_cast u (Nat.zero_add k₂)]
    simp only [uPow, one_mul]
    congr 1
    · ext j; exact congrArg a (Fin.ext (by simp [Fin.natAdd]))
    · ext j; exact congrArg b (Fin.ext (by simp [Fin.natAdd]))
  | succ k₁ ih =>
    have hstep : uPow u (k₁ + 1 + k₂) a b =
        u (a ⟨0, by omega⟩) (b ⟨0, by omega⟩) *
        uPow u (k₁ + k₂) (fun i => a ⟨i.val + 1, by omega⟩) (fun i => b ⟨i.val + 1, by omega⟩) := by
      rw [uPow_cast u (by omega : k₁ + 1 + k₂ = (k₁ + k₂) + 1)]
      rfl
    rw [hstep, ih]
    simp only [uPow, mul_assoc]
    refine congrArg (_ * ·) (congrArg (_ * ·) ?_)
    congr 1 <;> ext j <;> (congr 1; exact Fin.ext (by simp [Fin.natAdd]; omega))

/-- Matrix `T : Matrix (Fin l → V) (Fin k → V) ℂ` intertwines the magic unitary `u` over `R`:
`T · u^{⊗k} = u^{⊗l} · T`. -/
private def Intertwines {V : Type*} [Fintype V] {R : Type} [Ring R] [Algebra ℂ R]
    (u : Matrix V V R) (k l : ℕ) (T : Matrix (Fin l → V) (Fin k → V) ℂ) : Prop :=
  ∀ (i : Fin l → V) (j : Fin k → V),
    ∑ a : Fin k → V, algebraMap ℂ R (T i a) * uPow u k a j =
    ∑ b : Fin l → V, uPow u l i b * algebraMap ℂ R (T b j)

private def matTensor {V : Type*} {k₁ l₁ k₂ l₂ : ℕ}
    (T₁ : Matrix (Fin l₁ → V) (Fin k₁ → V) ℂ)
    (T₂ : Matrix (Fin l₂ → V) (Fin k₂ → V) ℂ) :
    Matrix (Fin (l₁ + l₂) → V) (Fin (k₁ + k₂) → V) ℂ :=
  Matrix.of fun i j =>
    T₁ (fun r => i (Fin.castAdd l₂ r)) (fun r => j (Fin.castAdd k₂ r)) *
    T₂ (fun r => i (Fin.natAdd l₁ r)) (fun r => j (Fin.natAdd k₁ r))

private def matU (V : Type*) : Matrix (Fin 1 → V) (Fin 0 → V) ℂ :=
  Matrix.of fun _ _ => 1

private def matUstar (V : Type*) : Matrix (Fin 0 → V) (Fin 1 → V) ℂ :=
  Matrix.of fun _ _ => 1

private def matM (V : Type*) [DecidableEq V] : Matrix (Fin 1 → V) (Fin 2 → V) ℂ :=
  Matrix.of fun i j => if j 0 = i 0 ∧ j 1 = i 0 then 1 else 0

private def matMstar (V : Type*) [DecidableEq V] : Matrix (Fin 2 → V) (Fin 1 → V) ℂ :=
  Matrix.of fun i j => if i 0 = j 0 ∧ i 1 = j 0 then 1 else 0

private def matSwap (V : Type*) [DecidableEq V] : Matrix (Fin 2 → V) (Fin 2 → V) ℂ :=
  Matrix.of fun i j => if i 0 = j 1 ∧ i 1 = j 0 then 1 else 0

private def matOf1 {V : Type*} (A : Matrix V V ℂ) : Matrix (Fin 1 → V) (Fin 1 → V) ℂ :=
  Matrix.of fun i j => A (i 0) (j 0)

private lemma intertwines_zero {V : Type*} [Fintype V] {R : Type} [Ring R] [Algebra ℂ R]
    (u : Matrix V V R) (k l : ℕ) : Intertwines u k l 0 := by
  intro i j; simp

private lemma intertwines_add {V : Type*} [Fintype V] {R : Type} [Ring R] [Algebra ℂ R]
    (u : Matrix V V R) {k l : ℕ} {T₁ T₂ : Matrix (Fin l → V) (Fin k → V) ℂ}
    (h1 : Intertwines u k l T₁) (h2 : Intertwines u k l T₂) :
    Intertwines u k l (T₁ + T₂) := by
  intro i j
  simp only [Matrix.add_apply, map_add, add_mul, mul_add, Finset.sum_add_distrib]
  rw [h1 i j, h2 i j]

private lemma intertwines_smul {V : Type*} [Fintype V] {R : Type} [Ring R] [Algebra ℂ R]
    (u : Matrix V V R) {k l : ℕ} (c : ℂ) {T : Matrix (Fin l → V) (Fin k → V) ℂ}
    (h : Intertwines u k l T) : Intertwines u k l (c • T) := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
  rw [h i j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_assoc, Algebra.commutes, mul_assoc]

private lemma intertwines_id {V : Type*} [Fintype V] [DecidableEq V]
    {R : Type} [Ring R] [Algebra ℂ R] (u : Matrix V V R) (k : ℕ) :
    Intertwines u k k 1 := by
  intro i j
  simp [Matrix.one_apply]

private lemma intertwines_comp {V : Type*} [Fintype V] {R : Type} [Ring R] [Algebra ℂ R]
    (u : Matrix V V R) {k l m : ℕ}
    {T₁ : Matrix (Fin l → V) (Fin k → V) ℂ} {T₂ : Matrix (Fin m → V) (Fin l → V) ℂ}
    (h1 : Intertwines u k l T₁) (h2 : Intertwines u l m T₂) :
    Intertwines u k m (T₂ * T₁) := by
  intro i j
  calc
    ∑ a : Fin k → V, algebraMap ℂ R ((T₂ * T₁) i a) * uPow u k a j
      = ∑ a : Fin k → V, ∑ c : Fin l → V,
          algebraMap ℂ R (T₂ i c) * (algebraMap ℂ R (T₁ c a) * uPow u k a j) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul, mul_assoc]
    _ = ∑ c : Fin l → V, algebraMap ℂ R (T₂ i c) *
          ∑ a : Fin k → V, algebraMap ℂ R (T₁ c a) * uPow u k a j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ c : Fin l → V, algebraMap ℂ R (T₂ i c) *
          ∑ b : Fin l → V, uPow u l c b * algebraMap ℂ R (T₁ b j) := by
        refine Finset.sum_congr rfl fun c _ => by rw [h1 c j]
    _ = ∑ b : Fin l → V,
          (∑ c : Fin l → V, algebraMap ℂ R (T₂ i c) * uPow u l c b) *
            algebraMap ℂ R (T₁ b j) := by
        simp_rw [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => (Finset.sum_mul _ _ _).symm
    _ = ∑ b : Fin l → V,
          (∑ d : Fin m → V, uPow u m i d * algebraMap ℂ R (T₂ d b)) *
            algebraMap ℂ R (T₁ b j) := by
        refine Finset.sum_congr rfl fun b _ => by rw [h2 i b]
    _ = ∑ d : Fin m → V, uPow u m i d * algebraMap ℂ R ((T₂ * T₁) d j) := by
        simp_rw [Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum]

private def piAddEquiv (V : Type*) (k₁ k₂ : ℕ) :
    ((Fin k₁ → V) × (Fin k₂ → V)) ≃ (Fin (k₁ + k₂) → V) where
  toFun p := Fin.addCases p.1 p.2
  invFun f := (fun i => f (Fin.castAdd k₂ i), fun j => f (Fin.natAdd k₁ j))
  left_inv p := by
    ext i <;> simp [Fin.addCases_left, Fin.addCases_right]
  right_inv f := by
    ext r
    refine Fin.addCases (fun i => ?_) (fun j => ?_) r
    · simp [Fin.addCases_left]
    · simp [Fin.addCases_right]

private lemma intertwines_tensor {V : Type*} [Fintype V] {R : Type} [Ring R] [Algebra ℂ R]
    (u : Matrix V V R) {k₁ l₁ k₂ l₂ : ℕ}
    {T₁ : Matrix (Fin l₁ → V) (Fin k₁ → V) ℂ} {T₂ : Matrix (Fin l₂ → V) (Fin k₂ → V) ℂ}
    (h1 : Intertwines u k₁ l₁ T₁) (h2 : Intertwines u k₂ l₂ T₂) :
    Intertwines u (k₁ + k₂) (l₁ + l₂) (matTensor T₁ T₂) := by
  intro i j
  let i₁ : Fin l₁ → V := fun r => i (Fin.castAdd l₂ r)
  let i₂ : Fin l₂ → V := fun r => i (Fin.natAdd l₁ r)
  let j₁ : Fin k₁ → V := fun r => j (Fin.castAdd k₂ r)
  let j₂ : Fin k₂ → V := fun r => j (Fin.natAdd k₁ r)
  have hL : ∑ a : Fin (k₁ + k₂) → V, algebraMap ℂ R (matTensor T₁ T₂ i a) * uPow u (k₁ + k₂) a j =
      (∑ a₁ : Fin k₁ → V, algebraMap ℂ R (T₁ i₁ a₁) * uPow u k₁ a₁ j₁) *
      (∑ a₂ : Fin k₂ → V, algebraMap ℂ R (T₂ i₂ a₂) * uPow u k₂ a₂ j₂) := by
    rw [← (piAddEquiv V k₁ k₂).sum_comp, Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a₂ _ => ?_
    simp only [piAddEquiv, Equiv.coe_fn_mk, matTensor, Matrix.of_apply, uPow_add,
      Fin.addCases_left, Fin.addCases_right, map_mul, i₁, i₂, j₁, j₂]
    calc
      algebraMap ℂ R (T₁ i₁ a₁) * algebraMap ℂ R (T₂ i₂ a₂) *
          (uPow u k₁ a₁ j₁ * uPow u k₂ a₂ j₂)
        = algebraMap ℂ R (T₁ i₁ a₁) * (algebraMap ℂ R (T₂ i₂ a₂) * uPow u k₁ a₁ j₁) *
            uPow u k₂ a₂ j₂ := by simp only [mul_assoc]
      _ = algebraMap ℂ R (T₁ i₁ a₁) * (uPow u k₁ a₁ j₁ * algebraMap ℂ R (T₂ i₂ a₂)) *
            uPow u k₂ a₂ j₂ := by rw [Algebra.commutes (T₂ i₂ a₂) (uPow u k₁ a₁ j₁)]
      _ = (algebraMap ℂ R (T₁ i₁ a₁) * uPow u k₁ a₁ j₁) *
            (algebraMap ℂ R (T₂ i₂ a₂) * uPow u k₂ a₂ j₂) := by simp only [mul_assoc]
  have hR : ∑ b : Fin (l₁ + l₂) → V, uPow u (l₁ + l₂) i b * algebraMap ℂ R (matTensor T₁ T₂ b j) =
      (∑ b₁ : Fin l₁ → V, uPow u l₁ i₁ b₁ * algebraMap ℂ R (T₁ b₁ j₁)) *
      (∑ b₂ : Fin l₂ → V, uPow u l₂ i₂ b₂ * algebraMap ℂ R (T₂ b₂ j₂)) := by
    rw [← (piAddEquiv V l₁ l₂).sum_comp, Fintype.sum_prod_type]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b₂ _ => ?_
    simp only [piAddEquiv, Equiv.coe_fn_mk, matTensor, Matrix.of_apply, uPow_add,
      Fin.addCases_left, Fin.addCases_right, map_mul, i₁, i₂, j₁, j₂]
    calc
      uPow u l₁ i₁ b₁ * uPow u l₂ i₂ b₂ *
          (algebraMap ℂ R (T₁ b₁ j₁) * algebraMap ℂ R (T₂ b₂ j₂))
        = uPow u l₁ i₁ b₁ * (uPow u l₂ i₂ b₂ * algebraMap ℂ R (T₁ b₁ j₁)) *
            algebraMap ℂ R (T₂ b₂ j₂) := by simp only [mul_assoc]
      _ = uPow u l₁ i₁ b₁ * (algebraMap ℂ R (T₁ b₁ j₁) * uPow u l₂ i₂ b₂) *
            algebraMap ℂ R (T₂ b₂ j₂) := by rw [← Algebra.commutes (T₁ b₁ j₁) (uPow u l₂ i₂ b₂)]
      _ = (uPow u l₁ i₁ b₁ * algebraMap ℂ R (T₁ b₁ j₁)) *
            (uPow u l₂ i₂ b₂ * algebraMap ℂ R (T₂ b₂ j₂)) := by simp only [mul_assoc]
  rw [hL, hR, h1 i₁ j₁, h2 i₂ j₂]

private lemma intertwines_U {V : Type*} [Fintype V] [DecidableEq V]
    {R : Type} [Ring R] [Algebra ℂ R] {u : Matrix V V R} (hu : IsMagicUnitary u) :
    Intertwines u 0 1 (matU V) := by
  intro i j
  have h1 : ∑ a : Fin 0 → V, algebraMap ℂ R (matU V i a) * uPow u 0 a j = 1 := by
    simp [matU, uPow]
  have h2 : ∑ b : Fin 1 → V, uPow u 1 i b * algebraMap ℂ R (matU V b j) = 1 := by
    rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
    simp [matU, uPow, hu.2.2.2.1 (i 0)]
  rw [h1, h2]

private lemma intertwines_Ustar {V : Type*} [Fintype V] [DecidableEq V]
    {R : Type} [Ring R] [Algebra ℂ R] {u : Matrix V V R} (hu : IsMagicUnitary u) :
    Intertwines u 1 0 (matUstar V) := by
  intro i j
  have h1 : ∑ a : Fin 1 → V, algebraMap ℂ R (matUstar V i a) * uPow u 1 a j = 1 := by
    rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
    simp [matUstar, uPow, hu.2.2.2.2 (j 0)]
  have h2 : ∑ b : Fin 0 → V, uPow u 0 i b * algebraMap ℂ R (matUstar V b j) = 1 := by
    simp [matUstar, uPow]
  rw [h1, h2]

private lemma intertwines_M {V : Type*} [Fintype V] [DecidableEq V]
    {R : Type} [Ring R] [Algebra ℂ R] {u : Matrix V V R} (hu : IsMagicUnitary u) :
    Intertwines u 2 1 (matM V) := by
  intro i j
  have hL : ∑ a : Fin 2 → V, algebraMap ℂ R (matM V i a) * uPow u 2 a j =
      u (i 0) (j 0) * u (i 0) (j 1) := by
    rw [Finset.sum_eq_single (fun _ : Fin 2 => i 0)]
    · simp [matM, uPow]
    · intro a _ ha
      have hnot : ¬ (a 0 = i 0 ∧ a 1 = i 0) := by
        rintro ⟨h0, h1⟩; apply ha; ext r; fin_cases r <;> assumption
      simp [matM, hnot]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : ∑ b : Fin 1 → V, uPow u 1 i b * algebraMap ℂ R (matM V b j) =
      if j 0 = j 1 then u (i 0) (j 0) else 0 := by
    rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
    by_cases hjj : j 0 = j 1
    · rw [if_pos hjj, Finset.sum_eq_single (j 0)]
      · simp [matM, uPow, hjj]
      · intro b _ hb; simp [matM, Ne.symm hb]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hjj]
      refine Finset.sum_eq_zero fun b _ => ?_
      have hnot : ¬ (j 0 = b ∧ j 1 = b) := fun ⟨h0, h1⟩ => hjj (h0.trans h1.symm)
      simp [matM, hnot]
  rw [hL, hR]
  by_cases hjj : j 0 = j 1
  · rw [if_pos hjj, ← hjj, hu.1]
  · rw [if_neg hjj, hu.2.1 _ _ _ hjj]

private lemma intertwines_Mstar {V : Type*} [Fintype V] [DecidableEq V]
    {R : Type} [Ring R] [Algebra ℂ R] {u : Matrix V V R} (hu : IsMagicUnitary u) :
    Intertwines u 1 2 (matMstar V) := by
  intro i j
  have hL : ∑ a : Fin 1 → V, algebraMap ℂ R (matMstar V i a) * uPow u 1 a j =
      if i 0 = i 1 then u (i 0) (j 0) else 0 := by
    rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
    by_cases hii : i 0 = i 1
    · rw [if_pos hii, Finset.sum_eq_single (i 0)]
      · simp [matMstar, uPow, hii]
      · intro a _ ha; simp [matMstar, Ne.symm ha]
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [if_neg hii]
      refine Finset.sum_eq_zero fun a _ => ?_
      have hnot : ¬ (i 0 = a ∧ i 1 = a) := fun ⟨h0, h1⟩ => hii (h0.trans h1.symm)
      simp [matMstar, hnot]
  have hR : ∑ b : Fin 2 → V, uPow u 2 i b * algebraMap ℂ R (matMstar V b j) =
      u (i 0) (j 0) * u (i 1) (j 0) := by
    rw [Finset.sum_eq_single (fun _ : Fin 2 => j 0)]
    · simp [matMstar, uPow]
    · intro b _ hb
      have hnot : ¬ (b 0 = j 0 ∧ b 1 = j 0) := by
        rintro ⟨h0, h1⟩; apply hb; ext r; fin_cases r <;> assumption
      simp [matMstar, hnot]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL, hR]
  by_cases hii : i 0 = i 1
  · rw [if_pos hii, ← hii, hu.1]
  · rw [if_neg hii, hu.2.2.1 _ _ _ hii]

private lemma intertwines_matOf1 {V : Type*} [Fintype V]
    {R : Type} [Ring R] [Algebra ℂ R] {u : Matrix V V R} {A : Matrix V V ℂ}
    (hcomm : u * A.map (algebraMap ℂ R) = A.map (algebraMap ℂ R) * u) :
    Intertwines u 1 1 (matOf1 A) := by
  intro i j
  rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp, ← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
  have h := congrFun (congrFun hcomm.symm (i 0)) (j 0)
  simpa [matOf1, uPow, Matrix.mul_apply] using h

private lemma comm_of_intertwines_swap {V : Type*} [Fintype V] [DecidableEq V]
    {R : Type} [Ring R] [Algebra ℂ R] {u : Matrix V V R}
    (hswap : Intertwines u 2 2 (matSwap V)) :
    ∀ a b c d : V, u a b * u c d = u c d * u a b := by
  intro a b c d
  have h := hswap ![c, a] ![b, d]
  have hL : ∑ x : Fin 2 → V, algebraMap ℂ R (matSwap V ![c, a] x) * uPow u 2 x ![b, d] =
      u a b * u c d := by
    rw [Finset.sum_eq_single ![a, c]]
    · simp [matSwap, uPow]
    · intro x _ hx
      have hnot : ¬ (c = x 1 ∧ a = x 0) := by
        rintro ⟨h1, h0⟩; apply hx; ext r; fin_cases r <;> simp [h0, h1]
      simp [matSwap, hnot]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hR : ∑ y : Fin 2 → V, uPow u 2 ![c, a] y * algebraMap ℂ R (matSwap V y ![b, d]) =
      u c d * u a b := by
    rw [Finset.sum_eq_single ![d, b]]
    · simp [matSwap, uPow]
    · intro y _ hy
      have hnot : ¬ (y 0 = d ∧ y 1 = b) := by
        rintro ⟨h0, h1⟩; apply hy; ext r; fin_cases r <;> simp [h0, h1]
      simp [matSwap, hnot]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [hL, hR] at h
  exact h

private lemma comm_aeval {V : Type*} [Fintype V] [DecidableEq V]
    {R : Type} [Ring R] [Algebra ℂ R] {u : Matrix V V R} {A : Matrix V V ℂ}
    (hcomm : u * A.map (algebraMap ℂ R) = A.map (algebraMap ℂ R) * u) (P : Polynomial ℂ) :
    u * (Polynomial.aeval A P).map (algebraMap ℂ R) =
      (Polynomial.aeval A P).map (algebraMap ℂ R) * u := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    have hmap_add : ∀ M₁ M₂ : Matrix V V ℂ,
        (M₁ + M₂).map (algebraMap ℂ R) = M₁.map (algebraMap ℂ R) + M₂.map (algebraMap ℂ R) := by
      intro M₁ M₂; ext x y; simp
    simp only [map_add, hmap_add, mul_add, add_mul, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul]
    have hmap_smul : ∀ (M : Matrix V V ℂ),
        (c • M).map (algebraMap ℂ R) = algebraMap ℂ R c • M.map (algebraMap ℂ R) := by
      intro M; ext x y; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    have hmap_pow : ∀ k : ℕ, (A ^ k).map (algebraMap ℂ R) = (A.map (algebraMap ℂ R)) ^ k := by
      intro k
      induction k with
      | zero => ext x y; simp [Matrix.one_apply]
      | succ k ih =>
        rw [pow_succ, pow_succ, ← ih]
        ext x y; simp [Matrix.mul_apply, map_sum, map_mul]
    rw [one_mul, hmap_smul, hmap_pow]
    have hpow_comm : u * (A.map (algebraMap ℂ R)) ^ n = (A.map (algebraMap ℂ R)) ^ n * u := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ← mul_assoc, ih, mul_assoc, hcomm, ← mul_assoc]
    ext x y
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    have := congrFun (congrFun hpow_comm x) y
    simp only [Matrix.mul_apply] at this
    calc
      ∑ z, u x z * (algebraMap ℂ R c * (A.map (algebraMap ℂ R) ^ n) z y)
        = algebraMap ℂ R c * ∑ z, u x z * (A.map (algebraMap ℂ R) ^ n) z y := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => ?_
          rw [← mul_assoc, ← Algebra.commutes c (u x z), mul_assoc]
      _ = algebraMap ℂ R c * ∑ z, (A.map (algebraMap ℂ R) ^ n) x z * u z y := by rw [this]
      _ = ∑ z, algebraMap ℂ R c * (A.map (algebraMap ℂ R) ^ n) x z * u z y := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => (mul_assoc _ _ _).symm

/-! ### Part 2: Cyclotomic cosets, Fourier diagonalization, and spectral separation -/

open Classical in
private noncomputable def cosetOf {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ) (y : ZMod p) :
    Finset (ZMod p) :=
  Finset.univ.filter fun x => ∃ e : E, x = (e.val : ZMod p) * y

private lemma cosetOf_zero {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ) :
    cosetOf E 0 = {0} := by
  ext x; simp [cosetOf]

private lemma mem_cosetOf_self {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ) (y : ZMod p) :
    y ∈ cosetOf E y := by
  simp only [cosetOf, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨1, by simp⟩

private lemma cosetOf_neg {p : ℕ} [Fact (Nat.Prime p)] {E : Subgroup (ZMod p)ˣ}
    (hneg : (-1 : (ZMod p)ˣ) ∈ E) (y x : ZMod p) :
    -x ∈ cosetOf E y ↔ x ∈ cosetOf E y := by
  have h1 : ∀ z, z ∈ cosetOf E y → -z ∈ cosetOf E y := by
    intro z hz
    simp only [cosetOf, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    obtain ⟨e, rfl⟩ := hz
    refine ⟨⟨-1 * e.val, E.mul_mem hneg e.prop⟩, ?_⟩
    simp
  exact ⟨fun h => by simpa using h1 (-x) h, h1 x⟩

private lemma cosetOf_mul {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (y x : ZMod p) :
    (a : ZMod p) * x ∈ cosetOf E ((a : ZMod p) * y) ↔ x ∈ cosetOf E y := by
  simp only [cosetOf, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e, h⟩
    refine ⟨e, ?_⟩
    have ha : (a : ZMod p) ≠ 0 := Units.ne_zero a
    apply mul_left_cancel₀ ha
    rw [h]; ring
  · rintro ⟨e, rfl⟩
    exact ⟨e, by ring⟩

private lemma cosetOf_mul_in_E {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (e : E) (y : ZMod p) : cosetOf E ((e.val : ZMod p) * y) = cosetOf E y := by
  ext x
  simp only [cosetOf, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e', rfl⟩
    exact ⟨⟨e'.val * e.val, E.mul_mem e'.prop e.prop⟩, by simp [mul_assoc]⟩
  · rintro ⟨e', rfl⟩
    refine ⟨⟨e'.val * e.val⁻¹, E.mul_mem e'.prop (E.inv_mem e.prop)⟩, ?_⟩
    show (e'.val : ZMod p) * y = ((e'.val * e.val⁻¹ : (ZMod p)ˣ) : ZMod p) * ((e.val : ZMod p) * y)
    rw [← mul_assoc, ← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]

private lemma cosetOf_eq_of_mem {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    {y z : ZMod p} (hz : z ∈ cosetOf E y) : cosetOf E z = cosetOf E y := by
  simp only [cosetOf, Finset.mem_filter, Finset.mem_univ, true_and] at hz
  obtain ⟨e, rfl⟩ := hz
  exact cosetOf_mul_in_E E e y

private lemma sum_q_omega_const {p : ℕ} [hp : Fact (Nat.Prime p)] (c : Fin p → ℚ)
    (hsum : ∑ j : Fin p, (c j : ℂ) * (Complex.exp (2 * Real.pi * Complex.I / p)) ^ j.val = 0) :
    ∀ j : Fin p, c j = c 0 := by
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hω : IsPrimitiveRoot ω p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  have hirr : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat hp.out.pos
  have hmin : minpoly ℚ ω = ∑ i ∈ Finset.range p, (Polynomial.X : Polynomial ℚ) ^ i := by
    have h1 := hω.minpoly_eq_cyclotomic_of_irreducible hirr
    rw [← h1, Polynomial.cyclotomic_prime ℚ p]
  let f : Polynomial ℚ := ∑ j : Fin p, Polynomial.C (c j) * Polynomial.X ^ j.val
  have hf0 : Polynomial.aeval ω f = 0 := by
    simp only [f, map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
      eq_ratCast, ω]
    exact hsum
  have hdvd : minpoly ℚ ω ∣ f := minpoly.dvd ℚ ω hf0
  obtain ⟨q, hq⟩ := hdvd
  have hdeg_min : (minpoly ℚ ω).natDegree = p - 1 := by
    rw [hmin]
    have h1 := Polynomial.cyclotomic_prime ℚ p
    rw [← h1, Polynomial.natDegree_cyclotomic, Nat.totient_prime hp.out]
  have hf_coeff : ∀ k : ℕ, f.coeff k = if hk : k < p then c ⟨k, hk⟩ else 0 := by
    intro k
    simp only [f, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hk : k < p
    · rw [dif_pos hk, Finset.sum_eq_single ⟨k, hk⟩]
      · simp
      · intro j _ hj; have : k ≠ j.val := fun h => hj (Fin.ext h.symm); simp [this]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    · rw [dif_neg hk]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : k ≠ j.val := fun h => hk (h ▸ j.isLt)
      simp [this]
  have hf_deg : f.natDegree ≤ p - 1 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [hf_coeff]
    have : ¬ k < p := by have := hp.out.two_le; omega
    simp [this]
  have hq_deg : q.natDegree = 0 := by
    by_cases hq0 : q = 0
    · simp [hq0]
    · have hmin_ne : minpoly ℚ ω ≠ 0 := by
        rw [hmin]
        intro h0
        have h1 := congrArg (fun g : Polynomial ℚ => g.coeff 0) h0
        simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Polynomial.coeff_zero] at h1
        rw [Finset.sum_eq_single 0] at h1
        · norm_num at h1
        · intro i _ hi; simp [Ne.symm hi]
        · intro hm; exact absurd (Finset.mem_range.mpr hp.out.pos) hm
      have hmul := Polynomial.natDegree_mul hmin_ne hq0
      rw [← hq, hdeg_min] at hmul
      omega
  have hq_eq : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hq_deg
  have hc_eq : ∀ j : Fin p, c j = q.coeff 0 := by
    intro j
    have h1 := congrArg (fun g : Polynomial ℚ => g.coeff j.val) hq
    rw [hf_coeff, dif_pos j.isLt, hq_eq, hmin] at h1
    simp only [Polynomial.coeff_mul_C, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow] at h1
    have hsum1 : (∑ i ∈ Finset.range p, if j.val = i then (1 : ℚ) else 0) = 1 := by
      rw [Finset.sum_eq_single j.val]
      · simp
      · intro i _ hi; simp [Ne.symm hi]
      · intro hm; exact absurd (Finset.mem_range.mpr j.isLt) hm
    rw [hsum1, one_mul] at h1
    exact h1
  intro j
  rw [hc_eq j, hc_eq 0]

private noncomputable def eigVal {p : ℕ} [Fact (Nat.Prime p)] (S : Finset (ZMod p)) (x : ZMod p) : ℂ :=
  ∑ s ∈ S, (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x * s).val

private lemma eigVal_eq_iff {p : ℕ} [hp : Fact (Nat.Prime p)] {S : Finset (ZMod p)}
    (hSne : S.Nonempty) (hS0 : (0 : ZMod p) ∉ S)
    (x y : ZMod p) :
    eigVal S x = eigVal S y ↔
      (x = 0 ∧ y = 0) ∨ (x ≠ 0 ∧ y ≠ 0 ∧ S.image (fun s => x * s) = S.image (fun s => y * s)) := by
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hω : IsPrimitiveRoot ω p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  have hω_pow : ∀ a : ZMod p, ω ^ a.val = ω ^ a.val := fun _ => rfl
  have heig_ind : ∀ z : ZMod p, z ≠ 0 →
      eigVal S z = ∑ j : Fin p,
        (if ((j.val : ZMod p) ∈ S.image (fun s => z * s)) then (1 : ℂ) else 0) * ω ^ j.val := by
    intro z hz
    unfold eigVal
    have hinj : Function.Injective (fun s : ZMod p => z * s) := mul_right_injective₀ hz
    have h1 : ∑ s ∈ S, ω ^ (z * s).val = ∑ t ∈ S.image (fun s => z * s), ω ^ t.val := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    rw [h1]
    have h2 : ∑ j : Fin p, (if ((j.val : ZMod p) ∈ S.image (fun s => z * s)) then (1 : ℂ) else 0) * ω ^ j.val =
        ∑ t : ZMod p, (if t ∈ S.image (fun s => z * s) then (1 : ℂ) else 0) * ω ^ t.val := by
      refine Finset.sum_bij (fun (j : Fin p) _ => (j.val : ZMod p)) (fun _ _ => Finset.mem_univ _)
        (fun j1 _ j2 _ h => Fin.ext (by
          have h1 := congrArg ZMod.val h
          rwa [ZMod.val_natCast_of_lt j1.isLt, ZMod.val_natCast_of_lt j2.isLt] at h1))
        (fun t _ => ⟨⟨t.val, ZMod.val_lt t⟩, Finset.mem_univ _, ZMod.natCast_zmod_val t⟩)
        (fun j _ => by rw [ZMod.val_natCast_of_lt j.isLt])
    rw [h2]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      Finset.filter_mem_eq_inter, Finset.univ_inter]
  constructor
  · intro heq
    by_cases hx : x = 0 <;> by_cases hy : y = 0
    · exact Or.inl ⟨hx, hy⟩
    · exfalso
      have hL : eigVal S x = (S.card : ℂ) := by simp [eigVal, hx]
      rw [hL, heig_ind y hy] at heq
      let c : Fin p → ℚ := fun j =>
        (if ((j.val : ZMod p) ∈ S.image (fun s => y * s)) then (1 : ℚ) else 0) -
        (if j.val = 0 then (S.card : ℚ) else 0)
      have hsum : ∑ j : Fin p, (c j : ℂ) * ω ^ j.val = 0 := by
        have hsplit : ∑ j : Fin p, (c j : ℂ) * ω ^ j.val =
            (∑ j : Fin p, (if ((j.val : ZMod p) ∈ S.image (fun s => y * s)) then (1 : ℂ) else 0) * ω ^ j.val) -
            (∑ j : Fin p, (if j.val = 0 then (S.card : ℂ) else 0) * ω ^ j.val) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [c, Rat.cast_sub, sub_mul]; split_ifs <;> simp
        rw [hsplit]
        have h0 : ∑ j : Fin p, (if j.val = 0 then (S.card : ℂ) else 0) * ω ^ j.val = (S.card : ℂ) := by
          rw [Finset.sum_eq_single (⟨0, hp.out.pos⟩ : Fin p)]
          · simp
          · intro j _ hj; have : j.val ≠ 0 := fun h => hj (Fin.ext h); simp [this]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        rw [h0, ← heq, sub_self]
      have hconst := sum_q_omega_const c hsum
      have h0mem : (0 : ZMod p) ∉ S.image (fun s => y * s) := by
        simp only [Finset.mem_image, not_exists, not_and]
        intro s hs h0; exact hS0 (by rwa [mul_eq_zero.mp h0 |>.resolve_left hy] at hs)
      have hc0 : c 0 = -(S.card : ℚ) := by
        simp only [c, Fin.val_zero, Nat.cast_zero, h0mem, ↓reduceIte, zero_sub]
      obtain ⟨s, hs⟩ := hSne
      have hys_ne : y * s ≠ 0 := mul_ne_zero hy (fun h => hS0 (h ▸ hs))
      let j1 : Fin p := ⟨(y * s).val, ZMod.val_lt _⟩
      have hj1_ne : j1.val ≠ 0 := by
        intro h; apply hys_ne
        have hval : (y * s).val = 0 := h
        have := ZMod.natCast_zmod_val (y * s); rw [hval] at this; simpa using this.symm
      have hj1_mem : (j1.val : ZMod p) ∈ S.image (fun s => y * s) := by
        rw [ZMod.natCast_zmod_val]; exact Finset.mem_image_of_mem _ hs
      have hcj1 : c j1 = 1 := by simp only [c, hj1_ne, hj1_mem, ↓reduceIte, sub_zero]
      have h1 := hconst j1
      rw [hc0, hcj1] at h1
      have : (S.card : ℚ) = -1 := by linarith
      have : 0 ≤ (S.card : ℚ) := Nat.cast_nonneg _
      linarith
    · exfalso
      have hR : eigVal S y = (S.card : ℂ) := by simp [eigVal, hy]
      rw [hR, heig_ind x hx] at heq
      let c : Fin p → ℚ := fun j =>
        (if ((j.val : ZMod p) ∈ S.image (fun s => x * s)) then (1 : ℚ) else 0) -
        (if j.val = 0 then (S.card : ℚ) else 0)
      have hsum : ∑ j : Fin p, (c j : ℂ) * ω ^ j.val = 0 := by
        have hsplit : ∑ j : Fin p, (c j : ℂ) * ω ^ j.val =
            (∑ j : Fin p, (if ((j.val : ZMod p) ∈ S.image (fun s => x * s)) then (1 : ℂ) else 0) * ω ^ j.val) -
            (∑ j : Fin p, (if j.val = 0 then (S.card : ℂ) else 0) * ω ^ j.val) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [c, Rat.cast_sub, sub_mul]; split_ifs <;> simp
        rw [hsplit]
        have h0 : ∑ j : Fin p, (if j.val = 0 then (S.card : ℂ) else 0) * ω ^ j.val = (S.card : ℂ) := by
          rw [Finset.sum_eq_single (⟨0, hp.out.pos⟩ : Fin p)]
          · simp
          · intro j _ hj; have : j.val ≠ 0 := fun h => hj (Fin.ext h); simp [this]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        rw [h0, heq, sub_self]
      have hconst := sum_q_omega_const c hsum
      have h0mem : (0 : ZMod p) ∉ S.image (fun s => x * s) := by
        simp only [Finset.mem_image, not_exists, not_and]
        intro s hs h0; exact hS0 (by rwa [mul_eq_zero.mp h0 |>.resolve_left hx] at hs)
      have hc0 : c 0 = -(S.card : ℚ) := by
        simp only [c, Fin.val_zero, Nat.cast_zero, h0mem, ↓reduceIte, zero_sub]
      obtain ⟨s, hs⟩ := hSne
      have hxs_ne : x * s ≠ 0 := mul_ne_zero hx (fun h => hS0 (h ▸ hs))
      let j1 : Fin p := ⟨(x * s).val, ZMod.val_lt _⟩
      have hj1_ne : j1.val ≠ 0 := by
        intro h; apply hxs_ne
        have hval : (x * s).val = 0 := h
        have := ZMod.natCast_zmod_val (x * s); rw [hval] at this; simpa using this.symm
      have hj1_mem : (j1.val : ZMod p) ∈ S.image (fun s => x * s) := by
        rw [ZMod.natCast_zmod_val]; exact Finset.mem_image_of_mem _ hs
      have hcj1 : c j1 = 1 := by simp only [c, hj1_ne, hj1_mem, ↓reduceIte, sub_zero]
      have h1 := hconst j1
      rw [hc0, hcj1] at h1
      have : 0 ≤ (S.card : ℚ) := Nat.cast_nonneg _
      linarith
    · refine Or.inr ⟨hx, hy, ?_⟩
      rw [heig_ind x hx, heig_ind y hy] at heq
      let c : Fin p → ℚ := fun j =>
        (if ((j.val : ZMod p) ∈ S.image (fun s => x * s)) then (1 : ℚ) else 0) -
        (if ((j.val : ZMod p) ∈ S.image (fun s => y * s)) then (1 : ℚ) else 0)
      have hsum : ∑ j : Fin p, (c j : ℂ) * ω ^ j.val = 0 := by
        have hsplit : ∑ j : Fin p, (c j : ℂ) * ω ^ j.val =
            (∑ j : Fin p, (if ((j.val : ZMod p) ∈ S.image (fun s => x * s)) then (1 : ℂ) else 0) * ω ^ j.val) -
            (∑ j : Fin p, (if ((j.val : ZMod p) ∈ S.image (fun s => y * s)) then (1 : ℂ) else 0) * ω ^ j.val) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [c, Rat.cast_sub, sub_mul]; split_ifs <;> simp
        rw [hsplit, heq, sub_self]
      have hconst := sum_q_omega_const c hsum
      have h0x : (0 : ZMod p) ∉ S.image (fun s => x * s) := by
        simp only [Finset.mem_image, not_exists, not_and]
        intro s hs h0; exact hS0 (by rwa [mul_eq_zero.mp h0 |>.resolve_left hx] at hs)
      have h0y : (0 : ZMod p) ∉ S.image (fun s => y * s) := by
        simp only [Finset.mem_image, not_exists, not_and]
        intro s hs h0; exact hS0 (by rwa [mul_eq_zero.mp h0 |>.resolve_left hy] at hs)
      have hc0 : c 0 = 0 := by
        simp only [c, Fin.val_zero, Nat.cast_zero, h0x, h0y, ↓reduceIte, sub_self]
      ext t
      let j : Fin p := ⟨t.val, ZMod.val_lt t⟩
      have hcj := hconst j
      rw [hc0] at hcj
      have htj : (j.val : ZMod p) = t := ZMod.natCast_zmod_val t
      simp only [c, htj] at hcj
      by_cases htx : t ∈ S.image (fun s => x * s) <;>
        by_cases hty : t ∈ S.image (fun s => y * s) <;>
        simp [htx, hty] at hcj ⊢
  · rintro (⟨rfl, rfl⟩ | ⟨hx, hy, himg⟩)
    · rfl
    · rw [heig_ind x hx, heig_ind y hy, himg]

private lemma circulantAdj_mulVec_fourier {p : ℕ} [hp : Fact (Nat.Prime p)]
    (C : Finset (ZMod p)) (hneg : ∀ c ∈ C, -c ∈ C) (x : ZMod p) :
    (circulantAdj p C).mulVec (fun t : ZMod p =>
      (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x * t).val) =
    eigVal C x • (fun t : ZMod p =>
      (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x * t).val) := by
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hω : IsPrimitiveRoot ω p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  have hω_add : ∀ a b : ZMod p, ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
    intro a b
    rw [← pow_add, ZMod.val_add]
    have hdiv := Nat.div_add_mod (a.val + b.val) p
    calc ω ^ ((a.val + b.val) % p)
        = ω ^ ((a.val + b.val) % p) * (ω ^ p) ^ ((a.val + b.val) / p) := by
            rw [hω.pow_eq_one, one_pow, mul_one]
      _ = ω ^ ((a.val + b.val) % p + p * ((a.val + b.val) / p)) := by
            rw [← pow_mul, ← pow_add]
      _ = ω ^ (a.val + b.val) := by rw [add_comm, hdiv]
  ext t
  simp only [Matrix.mulVec, dotProduct, circulantAdj, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    eigVal]
  have h1 : ∑ y : ZMod p, (if t - y ∈ C then (1 : ℂ) else 0) * ω ^ (x * y).val =
      ∑ c ∈ C, ω ^ (x * (t - c)).val := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero]
    refine Finset.sum_bij (fun y _ => t - y) (fun y hy => (Finset.mem_filter.mp hy).2)
      (fun y1 _ y2 _ h => by linear_combination -h)
      (fun c hc => ⟨t - c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hc⟩, by ring⟩)
      (fun y _ => by simp)
  rw [h1]
  have h2 : ∑ c ∈ C, ω ^ (x * (t - c)).val = ∑ c ∈ C, ω ^ (x * (t + c)).val := by
    refine Finset.sum_bij (fun c _ => -c) (fun c hc => hneg c hc)
      (fun c1 _ c2 _ h => neg_inj.mp h)
      (fun c hc => ⟨-c, hneg c hc, neg_neg c⟩)
      (fun c _ => by congr 2; ring)
  rw [h2, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  have : x * (t + c) = x * c + x * t := by ring
  rw [this, hω_add]

private lemma fourier_span_eq_of_mulVec {p : ℕ} [hp : Fact (Nat.Prime p)]
    (A B : Matrix (ZMod p) (ZMod p) ℂ)
    (h : ∀ x : ZMod p,
      A.mulVec (fun t : ZMod p => (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x * t).val) =
      B.mulVec (fun t : ZMod p => (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x * t).val)) :
    A = B := by
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)
  have hω : IsPrimitiveRoot ω p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  have hω_add : ∀ a b : ZMod p, ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
    intro a b
    rw [← pow_add, ZMod.val_add]
    have hdiv := Nat.div_add_mod (a.val + b.val) p
    calc ω ^ ((a.val + b.val) % p)
        = ω ^ ((a.val + b.val) % p) * (ω ^ p) ^ ((a.val + b.val) / p) := by
            rw [hω.pow_eq_one, one_pow, mul_one]
      _ = ω ^ ((a.val + b.val) % p + p * ((a.val + b.val) / p)) := by
            rw [← pow_mul, ← pow_add]
      _ = ω ^ (a.val + b.val) := by rw [add_comm, hdiv]
  have horth : ∀ d : ZMod p, ∑ x : ZMod p, ω ^ (x * d).val = if d = 0 then (p : ℂ) else 0 := by
    intro d
    by_cases hd : d = 0
    · simp [hd]
    · rw [if_neg hd]
      have hbij : ∑ x : ZMod p, ω ^ (x * d).val = ∑ y : ZMod p, ω ^ y.val :=
        Fintype.sum_equiv (Equiv.mulRight₀ d hd) _ _ (fun _ => rfl)
      rw [hbij]
      have hfin : ∑ y : ZMod p, ω ^ y.val = ∑ k ∈ Finset.range p, ω ^ k := by
        refine Finset.sum_bij (fun (y : ZMod p) _ => y.val)
          (fun y _ => Finset.mem_range.mpr (ZMod.val_lt y))
          (fun y1 _ y2 _ h => ZMod.val_injective p h)
          (fun k hk => ⟨(k : ZMod p), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)⟩)
          (fun _ _ => rfl)
      rw [hfin]
      exact hω.geom_sum_eq_zero hp.out.one_lt
  ext i j
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  suffices (p : ℂ) * A i j = (p : ℂ) * B i j from mul_left_cancel₀ hp0 this
  have hsum : ∀ M : Matrix (ZMod p) (ZMod p) ℂ,
      ∑ x : ZMod p, ω ^ (x * (-j)).val *
        (M.mulVec (fun t : ZMod p => ω ^ (x * t).val)) i = (p : ℂ) * M i j := by
    intro M
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      ∑ t : ZMod p, ∑ x : ZMod p, ω ^ (x * (-j)).val * (M i t * ω ^ (x * t).val)
        = ∑ t : ZMod p, M i t * ∑ x : ZMod p, ω ^ (x * (t - j)).val := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          have : x * (t - j) = x * (-j) + x * t := by ring
          rw [this, hω_add]; ring
      _ = ∑ t : ZMod p, M i t * (if t - j = 0 then (p : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun t _ => by rw [horth]
      _ = (p : ℂ) * M i j := by
          rw [Finset.sum_eq_single j]
          · simp [mul_comm]
          · intro t _ ht
            have : t - j ≠ 0 := sub_ne_zero.mpr ht
            simp [this]
          · intro hm; exact absurd (Finset.mem_univ _) hm
  rw [← hsum A, ← hsum B]
  refine Finset.sum_congr rfl fun x _ => by rw [h x]

private lemma spectral_poly {p : ℕ} [hp : Fact (Nat.Prime p)] {S : Finset (ZMod p)}
    (hSne : S.Nonempty) (hS0 : (0 : ZMod p) ∉ S)
    (hSneg : ∀ x ∈ S, -x ∈ S) (E : Subgroup (ZMod p)ˣ)
    (hE : ∀ a : (ZMod p)ˣ, a ∈ E ↔ S.image (fun s => (a : ZMod p) * s) = S)
    (hEneg : (-1 : (ZMod p)ˣ) ∈ E) (y : ZMod p) :
    ∃ P : Polynomial ℂ, Polynomial.aeval (circulantAdj p S) P = circulantAdj p (cosetOf E y) := by
  classical
  -- Show `eigVal (cosetOf E y)` factors through `eigVal S`!
  have hfactor : ∀ x₁ x₂ : ZMod p, eigVal S x₁ = eigVal S x₂ →
      eigVal (cosetOf E y) x₁ = eigVal (cosetOf E y) x₂ := by
    intro x₁ x₂ heq
    rcases (eigVal_eq_iff hSne hS0 x₁ x₂).mp heq with ⟨rfl, rfl⟩ | ⟨hx1, hx2, himg⟩
    · rfl
    · let a : (ZMod p)ˣ := Units.mk0 (x₂⁻¹ * x₁) (mul_ne_zero (inv_ne_zero hx2) hx1)
      have haE : a ∈ E := by
        rw [hE]
        ext t
        simp only [Finset.mem_image]
        have h1 : (a : ZMod p) = x₂⁻¹ * x₁ := rfl
        rw [h1]
        constructor
        · rintro ⟨s, hs, rfl⟩
          have hmem : x₁ * s ∈ S.image (fun u => x₂ * u) := by
            rw [← himg]; exact Finset.mem_image_of_mem _ hs
          obtain ⟨u, hu, hu_eq⟩ := Finset.mem_image.mp hmem
          have : x₂⁻¹ * x₁ * s = u := by
            apply mul_left_cancel₀ hx2
            calc x₂ * (x₂⁻¹ * x₁ * s) = (x₂ * x₂⁻¹) * (x₁ * s) := by ring
              _ = x₁ * s := by rw [mul_inv_cancel₀ hx2, one_mul]
              _ = x₂ * u := hu_eq.symm
          rwa [this]
        · intro ht
          have hmem : x₂ * t ∈ S.image (fun u => x₁ * u) := by
            rw [himg]; exact Finset.mem_image_of_mem _ ht
          obtain ⟨s, hs, hs_eq⟩ := Finset.mem_image.mp hmem
          refine ⟨s, hs, ?_⟩
          apply mul_left_cancel₀ hx2
          calc x₂ * (x₂⁻¹ * x₁ * s) = (x₂ * x₂⁻¹) * (x₁ * s) := by ring
            _ = x₁ * s := by rw [mul_inv_cancel₀ hx2, one_mul]
            _ = x₂ * t := hs_eq
      unfold eigVal
      have hperm : (cosetOf E y).image (fun c => (a : ZMod p) * c) = cosetOf E y := by
        ext c
        simp only [Finset.mem_image]
        constructor
        · rintro ⟨c', hc', rfl⟩
          have hc := cosetOf_mul E a y c'
          rw [cosetOf_mul_in_E E ⟨a, haE⟩ y] at hc
          exact hc.mpr hc'
        · intro hc
          refine ⟨(a⁻¹ : (ZMod p)ˣ) * c, ?_, by rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]⟩
          have h1 := cosetOf_mul E a⁻¹ y c
          rw [cosetOf_mul_in_E E ⟨a⁻¹, E.inv_mem haE⟩ y] at h1
          exact h1.mpr hc
      have hmul : ∀ c : ZMod p, x₁ * c = x₂ * ((a : ZMod p) * c) := by
        intro c
        have h1 : (a : ZMod p) = x₂⁻¹ * x₁ := rfl
        rw [h1]
        calc x₁ * c = (x₂ * x₂⁻¹) * (x₁ * c) := by rw [mul_inv_cancel₀ hx2, one_mul]
          _ = x₂ * (x₂⁻¹ * x₁ * c) := by ring
      calc
        ∑ c ∈ cosetOf E y, (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x₁ * c).val
          = ∑ c ∈ cosetOf E y, (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x₂ * ((a : ZMod p) * c)).val := by
            refine Finset.sum_congr rfl fun c _ => by rw [hmul]
        _ = ∑ c ∈ (cosetOf E y).image (fun c => (a : ZMod p) * c),
              (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x₂ * c).val := by
            rw [Finset.sum_image (fun c1 _ c2 _ h => mul_right_injective₀ (Units.ne_zero a) h)]
        _ = ∑ c ∈ cosetOf E y, (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x₂ * c).val := by
            rw [hperm]
  -- Lagrange interpolation polynomial `P` matching `eigVal (cosetOf E y)` on `vals = image (eigVal S) univ`!
  let vals : Finset ℂ := Finset.univ.image (eigVal S)
  let target : ℂ → ℂ := fun v =>
    if hv : ∃ x : ZMod p, eigVal S x = v then eigVal (cosetOf E y) (Classical.choose hv) else 0
  let P : Polynomial ℂ :=
    ∑ v ∈ vals, Polynomial.C (target v) *
      ∏ w ∈ vals.erase v, Polynomial.C ((v - w)⁻¹) * (Polynomial.X - Polynomial.C w)
  refine ⟨P, fourier_span_eq_of_mulVec _ _ fun x => ?_⟩
  have haeval_vec : ∀ Q : Polynomial ℂ,
      (Polynomial.aeval (circulantAdj p S) Q).mulVec
        (fun t : ZMod p => (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x * t).val) =
      Q.eval (eigVal S x) •
        (fun t : ZMod p => (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x * t).val) := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add p1 p2 hp1 hp2 =>
      simp only [map_add, Matrix.add_mulVec, Polynomial.eval_add, add_smul, hp1, hp2]
    | monomial k c =>
      simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
        one_mul, Matrix.smul_mulVec, Polynomial.eval_monomial]
      have hpow : ∀ m : ℕ,
          ((circulantAdj p S) ^ m).mulVec
            (fun t : ZMod p => (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x * t).val) =
          (eigVal S x) ^ m •
            (fun t : ZMod p => (Complex.exp (2 * Real.pi * Complex.I / p)) ^ (x * t).val) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
              circulantAdj_mulVec_fourier S hSneg x, smul_smul, mul_comm, pow_succ']
      rw [hpow, smul_smul]
  rw [haeval_vec P, circulantAdj_mulVec_fourier (cosetOf E y) (fun c hc => (cosetOf_neg hEneg y c).mpr hc) x]
  congr 1
  have hmem : eigVal S x ∈ vals := Finset.mem_image_of_mem _ (Finset.mem_univ x)
  simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
  rw [Finset.sum_eq_single (eigVal S x)]
  · have hprod : ∏ w ∈ vals.erase (eigVal S x), (eigVal S x - w)⁻¹ * (eigVal S x - w) = 1 := by
      refine Finset.prod_eq_one fun w hw => ?_
      have hne : eigVal S x - w ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hw).symm
      exact inv_mul_cancel₀ hne
    rw [hprod, mul_one]
    have hex : ∃ z : ZMod p, eigVal S z = eigVal S x := ⟨x, rfl⟩
    simp only [target, dif_pos hex]
    exact hfactor _ _ (Classical.choose_spec hex)
  · intro v hv hne
    have hmem_er : eigVal S x ∈ vals.erase v := Finset.mem_erase.mpr ⟨Ne.symm hne, hmem⟩
    have hprod : ∏ w ∈ vals.erase v, (v - w)⁻¹ * (eigVal S x - w) = 0 :=
      Finset.prod_eq_zero hmem_er (by simp)
    rw [hprod, mul_zero]
  · intro hm; exact absurd hmem hm

/-! ### Part 3: Generated intertwiner category `Cat E`, reachable module `Rmod E`, and capture dichotomy -/

/-- The tensor category generated by `U, U*, M, M*, id` and all cyclotomic class matrices
`T_y = circulantAdj p (cosetOf E y)`. -/
private inductive Cat {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ) :
    ∀ k l : ℕ, Matrix (Fin l → ZMod p) (Fin k → ZMod p) ℂ → Prop
  | zero (k l : ℕ) : Cat E k l 0
  | add {k l : ℕ} {T₁ T₂} : Cat E k l T₁ → Cat E k l T₂ → Cat E k l (T₁ + T₂)
  | smul {k l : ℕ} (c : ℂ) {T} : Cat E k l T → Cat E k l (c • T)
  | id (k : ℕ) : Cat E k k 1
  | comp {k l m : ℕ} {T₁ T₂} : Cat E k l T₁ → Cat E l m T₂ → Cat E k m (T₂ * T₁)
  | tensor {k₁ l₁ k₂ l₂ : ℕ} {T₁ T₂} :
      Cat E k₁ l₁ T₁ → Cat E k₂ l₂ T₂ → Cat E (k₁ + k₂) (l₁ + l₂) (matTensor T₁ T₂)
  | U : Cat E 0 1 (matU (ZMod p))
  | Ustar : Cat E 1 0 (matUstar (ZMod p))
  | M : Cat E 2 1 (matM (ZMod p))
  | Mstar : Cat E 1 2 (matMstar (ZMod p))
  | T (y : ZMod p) : Cat E 1 1 (matOf1 (circulantAdj p (cosetOf E y)))

private lemma cat_sound {p : ℕ} [Fact (Nat.Prime p)] {E : Subgroup (ZMod p)ˣ}
    {R : Type} [Ring R] [Algebra ℂ R] {u : Matrix (ZMod p) (ZMod p) R}
    (hu : IsMagicUnitary u)
    (hT : ∀ y : ZMod p,
      u * (circulantAdj p (cosetOf E y)).map (algebraMap ℂ R) =
      (circulantAdj p (cosetOf E y)).map (algebraMap ℂ R) * u)
    {k l : ℕ} {M : Matrix (Fin l → ZMod p) (Fin k → ZMod p) ℂ} (hM : Cat E k l M) :
    Intertwines u k l M := by
  induction hM with
  | zero k l => exact intertwines_zero u k l
  | add _ _ ih1 ih2 => exact intertwines_add u ih1 ih2
  | smul c _ ih => exact intertwines_smul u c ih
  | id k => exact intertwines_id u k
  | comp _ _ ih1 ih2 => exact intertwines_comp u ih1 ih2
  | tensor _ _ ih1 ih2 => exact intertwines_tensor u ih1 ih2
  | U => exact intertwines_U hu
  | Ustar => exact intertwines_Ustar hu
  | M => exact intertwines_M hu
  | Mstar => exact intertwines_Mstar hu
  | T y => exact intertwines_matOf1 (hT y)

/-- Conjugation of a `(k, l)`-matrix by a bijection `α : V ≃ V`. -/
private def conjPerm {V : Type*} {k l : ℕ} (α : V ≃ V)
    (M : Matrix (Fin l → V) (Fin k → V) ℂ) : Matrix (Fin l → V) (Fin k → V) ℂ :=
  Matrix.of fun i j => M (fun r => α.symm (i r)) (fun r => α.symm (j r))

/-- Affine bijection `x ↦ a * x + c` on `ZMod p`. -/
private def affEquiv {p : ℕ} [Fact (Nat.Prime p)] (a : (ZMod p)ˣ) (c : ZMod p) :
    ZMod p ≃ ZMod p where
  toFun x := (a : ZMod p) * x + c
  invFun y := (a : ZMod p)⁻¹ * (y - c)
  left_inv x := by
    dsimp only
    rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero a), one_mul]
  right_inv y := by
    dsimp only
    rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero a), one_mul, sub_add_cancel]

private lemma affEquiv_apply {p : ℕ} [Fact (Nat.Prime p)] (a : (ZMod p)ˣ) (c x : ZMod p) :
    affEquiv a c x = (a : ZMod p) * x + c := rfl

private lemma affEquiv_symm_apply {p : ℕ} [Fact (Nat.Prime p)] (a : (ZMod p)ˣ) (c y : ZMod p) :
    (affEquiv a c).symm y = (a : ZMod p)⁻¹ * (y - c) := rfl

private lemma conjPerm_T_eq {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (a : (ZMod p)ˣ) (c y : ZMod p) :
    conjPerm (affEquiv a c) (matOf1 (circulantAdj p (cosetOf E y))) =
      matOf1 (circulantAdj p (cosetOf E ((a : ZMod p) * y))) := by
  ext i j
  simp only [conjPerm, Matrix.of_apply, matOf1, circulantAdj]
  have hdiff : (affEquiv a c).symm (i 0) - (affEquiv a c).symm (j 0) =
      (a : ZMod p)⁻¹ * (i 0 - j 0) := by
    rw [affEquiv_symm_apply, affEquiv_symm_apply]; ring
  rw [hdiff]
  have hiff : (a : ZMod p)⁻¹ * (i 0 - j 0) ∈ cosetOf E y ↔
      i 0 - j 0 ∈ cosetOf E ((a : ZMod p) * y) := by
    have h1 := cosetOf_mul E a y ((a : ZMod p)⁻¹ * (i 0 - j 0))
    have h2 : (a : ZMod p) * ((a : ZMod p)⁻¹ * (i 0 - j 0)) = i 0 - j 0 := by
      rw [← mul_assoc, mul_inv_cancel₀ (Units.ne_zero a), one_mul]
    rw [h2] at h1
    exact h1.symm
  by_cases hm : (a : ZMod p)⁻¹ * (i 0 - j 0) ∈ cosetOf E y
  · rw [if_pos hm, if_pos (hiff.mp hm)]
  · rw [if_neg hm, if_neg (mt hiff.mpr hm)]

private lemma conjPerm_cat_aff {p : ℕ} [Fact (Nat.Prime p)] {E : Subgroup (ZMod p)ˣ}
    (a : (ZMod p)ˣ) (c : ZMod p) {k l : ℕ} {M : Matrix (Fin l → ZMod p) (Fin k → ZMod p) ℂ}
    (hM : Cat E k l M) : Cat E k l (conjPerm (affEquiv a c) M) := by
  let α := affEquiv a c
  induction hM with
  | zero k l =>
    have : conjPerm α (0 : Matrix (Fin l → ZMod p) (Fin k → ZMod p) ℂ) = 0 := by ext i j; simp [conjPerm]
    rw [this]; exact Cat.zero k l
  | add _ _ ih1 ih2 =>
    rename_i k l T₁ T₂ _ _
    have : conjPerm α (T₁ + T₂) = conjPerm α T₁ + conjPerm α T₂ := by ext i j; simp [conjPerm]
    rw [this]; exact Cat.add ih1 ih2
  | smul s _ ih =>
    rename_i k l T _
    have : conjPerm α (s • T) = s • conjPerm α T := by ext i j; simp [conjPerm]
    rw [this]; exact Cat.smul s ih
  | id k =>
    have : conjPerm α (1 : Matrix (Fin k → ZMod p) (Fin k → ZMod p) ℂ) = 1 := by
      ext i j; simp only [conjPerm, Matrix.of_apply, Matrix.one_apply]
      have hiff : (fun r => α.symm (i r)) = (fun r => α.symm (j r)) ↔ i = j := by
        constructor
        · intro h; ext r; exact α.symm.injective (congrFun h r)
        · intro h; rw [h]
      exact ite_congr (propext hiff) (fun _ => rfl) (fun _ => rfl)
    rw [this]; exact Cat.id k
  | comp _ _ ih1 ih2 =>
    rename_i k l m T₁ T₂ _ _
    have : conjPerm α (T₂ * T₁) = conjPerm α T₂ * conjPerm α T₁ := by
      ext i j
      simp only [conjPerm, Matrix.of_apply, Matrix.mul_apply]
      exact (Fintype.sum_equiv (Equiv.piCongrRight fun _ => α.symm) _ _ (fun _ => rfl)).symm
    rw [this]; exact Cat.comp ih1 ih2
  | tensor _ _ ih1 ih2 =>
    rename_i k₁ l₁ k₂ l₂ T₁ T₂ _ _
    have : conjPerm α (matTensor T₁ T₂) = matTensor (conjPerm α T₁) (conjPerm α T₂) := by
      ext i j; simp [conjPerm, matTensor]
    rw [this]; exact Cat.tensor ih1 ih2
  | U =>
    have : conjPerm α (matU (ZMod p)) = matU (ZMod p) := by ext i j; simp [conjPerm, matU]
    rw [this]; exact Cat.U
  | Ustar =>
    have : conjPerm α (matUstar (ZMod p)) = matUstar (ZMod p) := by ext i j; simp [conjPerm, matUstar]
    rw [this]; exact Cat.Ustar
  | M =>
    have : conjPerm α (matM (ZMod p)) = matM (ZMod p) := by
      ext i j; simp only [conjPerm, Matrix.of_apply, matM, α.symm.injective.eq_iff]
    rw [this]; exact Cat.M
  | Mstar =>
    have : conjPerm α (matMstar (ZMod p)) = matMstar (ZMod p) := by
      ext i j; simp only [conjPerm, Matrix.of_apply, matMstar, α.symm.injective.eq_iff]
    rw [this]; exact Cat.Mstar
  | T y =>
    rw [conjPerm_T_eq E a c y]
    exact Cat.T ((a : ZMod p) * y)

private lemma conjPerm_cat_G_eq {p : ℕ} [Fact (Nat.Prime p)] {E : Subgroup (ZMod p)ˣ}
    (a : E) (c : ZMod p) {k l : ℕ} {M : Matrix (Fin l → ZMod p) (Fin k → ZMod p) ℂ}
    (hM : Cat E k l M) : conjPerm (affEquiv a.val c) M = M := by
  let α := affEquiv a.val c
  induction hM with
  | zero k l => ext i j; simp [conjPerm]
  | add _ _ ih1 ih2 =>
    ext i j
    have h1 := congrFun (congrFun ih1 i) j
    have h2 := congrFun (congrFun ih2 i) j
    simp only [conjPerm, Matrix.of_apply, Matrix.add_apply] at h1 h2 ⊢
    rw [h1, h2]
  | smul s _ ih =>
    ext i j
    have h1 := congrFun (congrFun ih i) j
    simp only [conjPerm, Matrix.of_apply, Matrix.smul_apply] at h1 ⊢
    rw [h1]
  | id k =>
    ext i j; simp only [conjPerm, Matrix.of_apply, Matrix.one_apply]
    have hiff : (fun r => α.symm (i r)) = (fun r => α.symm (j r)) ↔ i = j := by
      constructor
      · intro h; ext r; exact α.symm.injective (congrFun h r)
      · intro h; rw [h]
    exact ite_congr (propext hiff) (fun _ => rfl) (fun _ => rfl)
  | comp _ _ ih1 ih2 =>
    rename_i k l m T₁ T₂ _ _
    have : conjPerm α (T₂ * T₁) = conjPerm α T₂ * conjPerm α T₁ := by
      ext i j
      simp only [conjPerm, Matrix.of_apply, Matrix.mul_apply]
      exact (Fintype.sum_equiv (Equiv.piCongrRight fun _ => α.symm) _ _ (fun _ => rfl)).symm
    rw [this, ih1, ih2]
  | tensor _ _ ih1 ih2 =>
    rename_i k₁ l₁ k₂ l₂ T₁ T₂ _ _
    have : conjPerm α (matTensor T₁ T₂) = matTensor (conjPerm α T₁) (conjPerm α T₂) := by
      ext i j; simp [conjPerm, matTensor]
    rw [this, ih1, ih2]
  | U => ext i j; simp [conjPerm, matU]
  | Ustar => ext i j; simp [conjPerm, matUstar]
  | M =>
    ext i j
    change (if α.symm (j 0) = α.symm (i 0) ∧ α.symm (j 1) = α.symm (i 0) then (1 : ℂ) else 0) =
      if j 0 = i 0 ∧ j 1 = i 0 then 1 else 0
    simp only [α.symm.injective.eq_iff]
  | Mstar =>
    ext i j
    change (if α.symm (i 0) = α.symm (j 0) ∧ α.symm (i 1) = α.symm (j 0) then (1 : ℂ) else 0) =
      if i 0 = j 0 ∧ i 1 = j 0 then 1 else 0
    simp only [α.symm.injective.eq_iff]
  | T y =>
    rw [conjPerm_T_eq E a.val c y, cosetOf_mul_in_E E a y]

/-- Apply a `(2, 1)`-morphism `A` to `e_a ⊗ e_b`, returning a vector `ZMod p → ℂ`. -/
private def eval21 {V : Type*} (A : Matrix (Fin 1 → V) (Fin 2 → V) ℂ) (a b : V) : V → ℂ :=
  fun x => A (fun _ => x) ![a, b]

/-- The reachable module `Rmod E a b ⊆ (ZMod p → ℂ)` of vectors `A(e_a ⊗ e_b)` for `A ∈ Cat E 2 1`. -/
private def Rmod {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ) (a b : ZMod p) :
    Submodule ℂ (ZMod p → ℂ) where
  carrier := {v | ∃ A, Cat E 2 1 A ∧ eval21 A a b = v}
  add_mem' := by
    rintro v₁ v₂ ⟨A₁, h1, rfl⟩ ⟨A₂, h2, rfl⟩
    exact ⟨A₁ + A₂, Cat.add h1 h2, by ext x; simp [eval21]⟩
  zero_mem' := ⟨0, Cat.zero 2 1, by ext x; simp [eval21]⟩
  smul_mem' := by
    rintro c v ⟨A, hA, rfl⟩
    exact ⟨c • A, Cat.smul c hA, by ext x; simp [eval21]⟩

private lemma cat_allOnes {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ) :
    Cat E 1 1 (matOf1 (Matrix.of fun _ _ => (1 : ℂ))) := by
  have hEq : matOf1 (Matrix.of fun _ _ : ZMod p => (1 : ℂ)) = matU (ZMod p) * matUstar (ZMod p) := by
    ext i j
    simp [matOf1, matU, matUstar, Matrix.mul_apply]
  rw [hEq]
  exact Cat.comp Cat.Ustar Cat.U

private lemma cat_M3 {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ) :
    Cat E 3 1 (Matrix.of fun i j => if j 0 = i 0 ∧ j 1 = i 0 ∧ j 2 = i 0 then 1 else 0) := by
  have h1 : Cat E 3 1 (matM (ZMod p) * matTensor (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ) (matM (ZMod p))) :=
    Cat.comp (Cat.tensor (Cat.id 1) Cat.M) Cat.M
  convert h1 using 1
  ext i j
  simp only [Matrix.of_apply, Matrix.mul_apply, matM, matTensor, Matrix.one_apply]
  rw [Finset.sum_eq_single (fun _ : Fin 2 => i 0)]
  · have h0 : (fun r : Fin 1 => (fun _ : Fin 2 => i 0) (Fin.castAdd 1 r)) =
        (fun r : Fin 1 => j (Fin.castAdd 2 r)) ↔ j 0 = i 0 := by
      constructor
      · intro h; exact (congrFun h 0).symm
      · intro h; ext r; fin_cases r; exact h.symm
    simp only [h0, Fin.natAdd]
    by_cases hj0 : j 0 = i 0 <;> by_cases hj1 : j 1 = i 0 <;> by_cases hj2 : j 2 = i 0 <;>
      simp [hj0, hj1, hj2]
  · intro b _ hb
    have hnot : ¬ (b 0 = i 0 ∧ b 1 = i 0) := by
      rintro ⟨h0, h1⟩; apply hb; ext r; fin_cases r <;> assumption
    simp [hnot]
  · intro hm; exact absurd (Finset.mem_univ _) hm

private lemma pi1_mem_Rmod {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ) (a b : ZMod p) :
    Pi.single a (1 : ℂ) ∈ Rmod E a b := by
  let J := matOf1 (Matrix.of fun _ _ : ZMod p => (1 : ℂ))
  refine ⟨matM (ZMod p) * matTensor (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ) J,
    Cat.comp (Cat.tensor (Cat.id 1) (cat_allOnes E)) Cat.M, ?_⟩
  ext x
  simp only [eval21, Matrix.mul_apply, matM, matTensor, Matrix.of_apply, Matrix.one_apply, J, matOf1]
  rw [Finset.sum_eq_single (fun _ : Fin 2 => x)]
  · by_cases hxa : x = a
    · subst hxa
      have heq : (fun r : Fin 1 => x) = (fun r : Fin 1 => ![x, b] (Fin.castAdd 1 r)) := by
        ext r; fin_cases r; rfl
      simp [heq]
    · have hne : (fun r : Fin 1 => x) ≠ (fun r : Fin 1 => ![a, b] (Fin.castAdd 1 r)) := by
        intro h; exact hxa (congrFun h 0)
      simp [hne, Pi.single_eq_of_ne hxa]
  · intro c _ hc
    have hnot : ¬ (c 0 = x ∧ c 1 = x) := by
      rintro ⟨h0, h1⟩; apply hc; ext r; fin_cases r <;> assumption
    simp [hnot]
  · intro hm; exact absurd (Finset.mem_univ _) hm

private lemma pi2_mem_Rmod {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ) (a b : ZMod p) :
    Pi.single b (1 : ℂ) ∈ Rmod E a b := by
  let J := matOf1 (Matrix.of fun _ _ : ZMod p => (1 : ℂ))
  refine ⟨matM (ZMod p) * matTensor J (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ),
    Cat.comp (Cat.tensor (cat_allOnes E) (Cat.id 1)) Cat.M, ?_⟩
  ext x
  simp only [eval21, Matrix.mul_apply, matM, matTensor, Matrix.of_apply, Matrix.one_apply, J, matOf1]
  rw [Finset.sum_eq_single (fun _ : Fin 2 => x)]
  · by_cases hxb : x = b
    · subst hxb
      have heq : (fun r : Fin 1 => x) = (fun r : Fin 1 => ![a, x] (Fin.natAdd 1 r)) := by
        ext r; fin_cases r; rfl
      simp [heq]
    · have hne : (fun _ : Fin 1 => x) ≠ (fun _ : Fin 1 => b) := fun h => hxb (congrFun h 0)
      simp [hne, Pi.single_eq_of_ne hxb]
  · intro c _ hc
    have hnot : ¬ (c 0 = x ∧ c 1 = x) := by
      rintro ⟨h0, h1⟩; apply hc; ext r; fin_cases r <;> assumption
    simp [hnot]
  · intro hm; exact absurd (Finset.mem_univ _) hm

private lemma const_one_mem_Rmod {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ) (a b : ZMod p) :
    (fun _ : ZMod p => (1 : ℂ)) ∈ Rmod E a b := by
  obtain ⟨A, hA, hAv⟩ := pi1_mem_Rmod E a b
  let J := matOf1 (Matrix.of fun _ _ : ZMod p => (1 : ℂ))
  refine ⟨J * A, Cat.comp hA (cat_allOnes E), ?_⟩
  ext x
  simp only [eval21, Matrix.mul_apply, J, matOf1, Matrix.of_apply, one_mul]
  rw [← (Equiv.funUnique (Fin 1) (ZMod p)).symm.sum_comp]
  have hfun : ∀ z : ZMod p, (uniqueElim z : Fin 1 → ZMod p) = (fun _ => z) :=
    fun z => by ext r; fin_cases r; rfl
  have hval : ∀ z : ZMod p, A (fun _ => z) ![a, b] = (Pi.single a (1 : ℂ) : ZMod p → ℂ) z :=
    fun z => congrFun hAv z
  rw [Finset.sum_eq_single a]
  · simp only [Equiv.funUnique_symm_apply, hfun, hval, Pi.single_eq_same]
  · intro z _ hz; simp only [Equiv.funUnique_symm_apply, hfun, hval, Pi.single_eq_of_ne hz]
  · intro hm; exact absurd (Finset.mem_univ _) hm

private lemma rmod_mulVec_T {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (a b y : ZMod p) {v : ZMod p → ℂ} (hv : v ∈ Rmod E a b) :
    (circulantAdj p (cosetOf E y)).mulVec v ∈ Rmod E a b := by
  obtain ⟨A, hA, rfl⟩ := hv
  refine ⟨matOf1 (circulantAdj p (cosetOf E y)) * A, Cat.comp hA (Cat.T y), ?_⟩
  ext x
  simp only [eval21, Matrix.mul_apply, matOf1, Matrix.of_apply, Matrix.mulVec, dotProduct]
  rw [← (Equiv.funUnique (Fin 1) (ZMod p)).symm.sum_comp]
  rfl

private lemma rmod_diag_left {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (a b y : ZMod p) {v : ZMod p → ℂ} (hv : v ∈ Rmod E a b) :
    (fun x => (if x - a ∈ cosetOf E y then (1 : ℂ) else 0) * v x) ∈ Rmod E a b := by
  obtain ⟨A, hA, rfl⟩ := hv
  let J := matOf1 (Matrix.of fun _ _ : ZMod p => (1 : ℂ))
  let Ty := matOf1 (circulantAdj p (cosetOf E y))
  let M3 : Matrix (Fin 1 → ZMod p) (Fin 3 → ZMod p) ℂ :=
    Matrix.of fun i j => if j 0 = i 0 ∧ j 1 = i 0 ∧ j 2 = i 0 then 1 else 0
  have hM3 : Cat E 3 1 M3 := cat_M3 E
  let step1 := matTensor (matMstar (ZMod p)) (matMstar (ZMod p))
  let step2 := matTensor (matTensor (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ) A)
    (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ)
  let step3 := matTensor (matTensor Ty (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ)) J
  have hstep1 : Cat E 2 4 step1 := Cat.tensor Cat.Mstar Cat.Mstar
  have hstep2 : Cat E 4 3 step2 := Cat.tensor (Cat.tensor (Cat.id 1) hA) (Cat.id 1)
  have hstep3 : Cat E 3 3 step3 := Cat.tensor (Cat.tensor (Cat.T y) (Cat.id 1)) (cat_allOnes E)
  refine ⟨M3 * (step3 * (step2 * step1)), Cat.comp (Cat.comp (Cat.comp hstep1 hstep2) hstep3) hM3, ?_⟩
  ext x
  simp only [eval21]
  have h1 : ∀ f : Fin 4 → ZMod p,
      step1 f ![a, b] = if f = ![a, a, b, b] then 1 else 0 := by
    intro f
    simp only [step1, matTensor, matMstar, Matrix.of_apply]
    by_cases hf : f = ![a, a, b, b]
    · subst hf; simp [Fin.castAdd, Fin.natAdd]
    · rw [if_neg hf]
      by_contra hne
      apply hf
      ext r; fin_cases r <;> simp [Fin.castAdd, Fin.natAdd] at hne ⊢ <;> tauto
  have h2 : ∀ g : Fin 3 → ZMod p,
      (step2 * step1) g ![a, b] =
        (if g 0 = a then 1 else 0) * A (fun _ => g 1) ![a, b] * (if g 2 = b then 1 else 0) := by
    intro g
    simp only [Matrix.mul_apply, h1]
    rw [Finset.sum_eq_single ![a, a, b, b]]
    · simp only [↓reduceIte, mul_one, step2, matTensor, Matrix.of_apply, Matrix.one_apply]
      have hg0 : (fun r : Fin 1 => g (Fin.castAdd 1 (Fin.castAdd 1 r))) =
          (fun r : Fin 1 => ![a, a, b, b] (Fin.castAdd 1 (Fin.castAdd 2 r))) ↔ g 0 = a := by
        constructor
        · intro h; exact congrFun h 0
        · intro h; ext r; fin_cases r; exact h
      have hg2 : (fun r : Fin 1 => g (Fin.natAdd 2 r)) =
          (fun r : Fin 1 => ![a, a, b, b] (Fin.natAdd 3 r)) ↔ g 2 = b := by
        constructor
        · intro h; exact congrFun h 0
        · intro h; ext r; fin_cases r; exact h
      have hab : (fun r : Fin 2 => ![a, a, b, b] (Fin.castAdd 1 (Fin.natAdd 1 r))) = ![a, b] := by
        ext r; fin_cases r <;> rfl
      have hg1 : (fun r : Fin 1 => g (Fin.castAdd 1 (Fin.natAdd 1 r))) = (fun _ => g 1) := by
        ext r; fin_cases r; rfl
      simp only [hg0, hg2, hab, hg1]
    · intro f _ hf; simp [hf]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have h3 : ∀ h : Fin 3 → ZMod p,
      (step3 * (step2 * step1)) h ![a, b] =
        (if h 0 - a ∈ cosetOf E y then 1 else 0) * A (fun _ => h 1) ![a, b] := by
    intro h
    simp only [Matrix.mul_apply, h2]
    rw [Finset.sum_eq_single ![a, h 1, b]]
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        ↓reduceIte, one_mul, mul_one, step3, matTensor, Matrix.of_apply, Ty, J, matOf1,
        circulantAdj, Matrix.one_apply]
      have hmid : (fun r : Fin 1 => h (Fin.castAdd 1 (Fin.natAdd 1 r))) =
          (fun r : Fin 1 => ![a, h 1, b] (Fin.castAdd 1 (Fin.natAdd 1 r))) := by
        ext r; fin_cases r; rfl
      rw [if_pos hmid, mul_one]
      change (if h 0 - a ∈ cosetOf E y then (1 : ℂ) else 0) *
          (A (fun _ => h 1) ![a, b] * if b = b then 1 else 0) =
        (if h 0 - a ∈ cosetOf E y then 1 else 0) * A (fun _ => h 1) ![a, b]
      simp only [↓reduceIte, mul_one]
    · intro g _ hg
      by_cases hg0 : g 0 = a
      · by_cases hg2 : g 2 = b
        · have hg1 : h 1 ≠ g 1 := by
            intro heq; apply hg; ext r; fin_cases r <;> simp [hg0, hg2, heq]
          have hne : (fun r : Fin 1 => h (Fin.castAdd 1 (Fin.natAdd 1 r))) ≠
              (fun r : Fin 1 => g (Fin.castAdd 1 (Fin.natAdd 1 r))) :=
            fun heq => hg1 (congrFun heq 0)
          simp only [step3, matTensor, Matrix.of_apply, Matrix.one_apply]
          rw [if_neg hne]; ring
        · simp [hg2]
      · simp [hg0]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  simp only [Matrix.mul_apply, h3, M3, Matrix.of_apply]
  rw [Finset.sum_eq_single (fun _ : Fin 3 => x)]
  · simp
  · intro h _ hh
    have hnot : ¬ (h 0 = x ∧ h 1 = x ∧ h 2 = x) := by
      rintro ⟨h0, h1, h2⟩; apply hh; ext r; fin_cases r <;> assumption
    simp [hnot]
  · intro hm; exact absurd (Finset.mem_univ _) hm

private lemma rmod_diag_right {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (a b y : ZMod p) {v : ZMod p → ℂ} (hv : v ∈ Rmod E a b) :
    (fun x => v x * (if x - b ∈ cosetOf E y then (1 : ℂ) else 0)) ∈ Rmod E a b := by
  obtain ⟨A, hA, rfl⟩ := hv
  let J := matOf1 (Matrix.of fun _ _ : ZMod p => (1 : ℂ))
  let Ty := matOf1 (circulantAdj p (cosetOf E y))
  let M3 : Matrix (Fin 1 → ZMod p) (Fin 3 → ZMod p) ℂ :=
    Matrix.of fun i j => if j 0 = i 0 ∧ j 1 = i 0 ∧ j 2 = i 0 then 1 else 0
  have hM3 : Cat E 3 1 M3 := cat_M3 E
  let step1 := matTensor (matMstar (ZMod p)) (matMstar (ZMod p))
  let step2 := matTensor (matTensor (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ) A)
    (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ)
  let step3 := matTensor (matTensor J (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ)) Ty
  have hstep1 : Cat E 2 4 step1 := Cat.tensor Cat.Mstar Cat.Mstar
  have hstep2 : Cat E 4 3 step2 := Cat.tensor (Cat.tensor (Cat.id 1) hA) (Cat.id 1)
  have hstep3 : Cat E 3 3 step3 := Cat.tensor (Cat.tensor (cat_allOnes E) (Cat.id 1)) (Cat.T y)
  refine ⟨M3 * (step3 * (step2 * step1)), Cat.comp (Cat.comp (Cat.comp hstep1 hstep2) hstep3) hM3, ?_⟩
  ext x
  simp only [eval21]
  have h1 : ∀ f : Fin 4 → ZMod p,
      step1 f ![a, b] = if f = ![a, a, b, b] then 1 else 0 := by
    intro f
    simp only [step1, matTensor, matMstar, Matrix.of_apply]
    by_cases hf : f = ![a, a, b, b]
    · subst hf; simp [Fin.castAdd, Fin.natAdd]
    · rw [if_neg hf]
      by_contra hne
      apply hf
      ext r; fin_cases r <;> simp [Fin.castAdd, Fin.natAdd] at hne ⊢ <;> tauto
  have h2 : ∀ g : Fin 3 → ZMod p,
      (step2 * step1) g ![a, b] =
        (if g 0 = a then 1 else 0) * A (fun _ => g 1) ![a, b] * (if g 2 = b then 1 else 0) := by
    intro g
    simp only [Matrix.mul_apply, h1]
    rw [Finset.sum_eq_single ![a, a, b, b]]
    · simp only [↓reduceIte, mul_one, step2, matTensor, Matrix.of_apply, Matrix.one_apply]
      have hg0 : (fun r : Fin 1 => g (Fin.castAdd 1 (Fin.castAdd 1 r))) =
          (fun r : Fin 1 => ![a, a, b, b] (Fin.castAdd 1 (Fin.castAdd 2 r))) ↔ g 0 = a := by
        constructor
        · intro h; exact congrFun h 0
        · intro h; ext r; fin_cases r; exact h
      have hg2 : (fun r : Fin 1 => g (Fin.natAdd 2 r)) =
          (fun r : Fin 1 => ![a, a, b, b] (Fin.natAdd 3 r)) ↔ g 2 = b := by
        constructor
        · intro h; exact congrFun h 0
        · intro h; ext r; fin_cases r; exact h
      have hab : (fun r : Fin 2 => ![a, a, b, b] (Fin.castAdd 1 (Fin.natAdd 1 r))) = ![a, b] := by
        ext r; fin_cases r <;> rfl
      have hg1 : (fun r : Fin 1 => g (Fin.castAdd 1 (Fin.natAdd 1 r))) = (fun _ => g 1) := by
        ext r; fin_cases r; rfl
      simp only [hg0, hg2, hab, hg1]
    · intro f _ hf; simp [hf]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have h3 : ∀ h : Fin 3 → ZMod p,
      (step3 * (step2 * step1)) h ![a, b] =
        A (fun _ => h 1) ![a, b] * (if h 2 - b ∈ cosetOf E y then 1 else 0) := by
    intro h
    simp only [Matrix.mul_apply, h2]
    rw [Finset.sum_eq_single ![a, h 1, b]]
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        ↓reduceIte, one_mul, step3, matTensor, Matrix.of_apply, Ty, J, matOf1,
        circulantAdj, Matrix.one_apply]
      have hmid : (fun r : Fin 1 => h (Fin.castAdd 1 (Fin.natAdd 1 r))) =
          (fun r : Fin 1 => ![a, h 1, b] (Fin.castAdd 1 (Fin.natAdd 1 r))) := by
        ext r; fin_cases r; rfl
      rw [if_pos hmid, one_mul]
      change (if h 2 - b ∈ cosetOf E y then (1 : ℂ) else 0) *
          (A (fun _ => h 1) ![a, b] * if b = b then 1 else 0) =
        A (fun _ => h 1) ![a, b] * (if h 2 - b ∈ cosetOf E y then 1 else 0)
      simp only [↓reduceIte, mul_one]
      exact mul_comm _ _
    · intro g _ hg
      by_cases hg0 : g 0 = a
      · by_cases hg2 : g 2 = b
        · have hg1 : h 1 ≠ g 1 := by
            intro heq; apply hg; ext r; fin_cases r <;> simp [hg0, hg2, heq]
          have hne : (fun r : Fin 1 => h (Fin.castAdd 1 (Fin.natAdd 1 r))) ≠
              (fun r : Fin 1 => g (Fin.castAdd 1 (Fin.natAdd 1 r))) :=
            fun heq => hg1 (congrFun heq 0)
          simp only [step3, matTensor, Matrix.of_apply, Matrix.one_apply]
          rw [if_neg hne]; ring
        · simp [hg2]
      · simp [hg0]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  simp only [Matrix.mul_apply, h3, M3, Matrix.of_apply]
  rw [Finset.sum_eq_single (fun _ : Fin 3 => x)]
  · simp
  · intro h _ hh
    have hnot : ¬ (h 0 = x ∧ h 1 = x ∧ h 2 = x) := by
      rintro ⟨h0, h1, h2⟩; apply hh; ext r; fin_cases r <;> assumption
    simp [hnot]
  · intro hm; exact absurd (Finset.mem_univ _) hm

private lemma block_ind_mem_Rmod {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (s t : ZMod p) :
    (fun x : ZMod p => if x ∈ cosetOf E s ∧ x - 1 ∈ cosetOf E t then (1 : ℂ) else 0) ∈ Rmod E 0 1 := by
  have h1 := rmod_diag_left E 0 1 s (const_one_mem_Rmod E 0 1)
  have h2 := rmod_diag_right E 0 1 t h1
  convert h2 using 1
  ext x; simp only [sub_zero]
  by_cases hs : x ∈ cosetOf E s <;> by_cases ht : x - 1 ∈ cosetOf E t <;> simp [hs, ht]

/-- Affine equivariance of `Rmod`: `v ∈ Rmod E a b ↔ (v ∘ α⁻¹) ∈ Rmod E (α a) (α b)`. -/
private lemma rmod_aff_equiv {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (u : (ZMod p)ˣ) (c a b : ZMod p) (v : ZMod p → ℂ) :
    v ∈ Rmod E a b ↔ (fun x => v ((affEquiv u c).symm x)) ∈ Rmod E (affEquiv u c a) (affEquiv u c b) := by
  let α := affEquiv u c
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨conjPerm α A, conjPerm_cat_aff u c hA, ?_⟩
    ext x
    simp only [eval21, conjPerm, Matrix.of_apply]
    congr 1; ext r; fin_cases r <;> exact Equiv.symm_apply_apply _ _
  · rintro ⟨A, hA, hv⟩
    have hα_inv : α.symm = affEquiv u⁻¹ (-(u : ZMod p)⁻¹ * c) := by
      ext x
      rw [affEquiv_symm_apply, affEquiv_apply, Units.val_inv_eq_inv_val]
      ring
    refine ⟨conjPerm (affEquiv u⁻¹ (-(u : ZMod p)⁻¹ * c)) A,
      conjPerm_cat_aff u⁻¹ _ hA, ?_⟩
    ext x
    have h1 := congrFun hv (α x)
    simp only [α, Equiv.symm_apply_apply] at h1
    rw [← h1]
    simp only [eval21, conjPerm, Matrix.of_apply]
    have hinv_symm : (affEquiv u⁻¹ (-(u : ZMod p)⁻¹ * c)).symm = α := by
      rw [← hα_inv, Equiv.symm_symm]
    rw [hinv_symm]
    congr 1; ext r; fin_cases r <;> rfl

private lemma rmod_finrank_eq {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    {a₁ b₁ a₂ b₂ : ZMod p} (h1 : a₁ ≠ b₁) (h2 : a₂ ≠ b₂) :
    Module.finrank ℂ (Rmod E a₁ b₁) = Module.finrank ℂ (Rmod E a₂ b₂) := by
  let u : (ZMod p)ˣ := Units.mk0 ((b₂ - a₂) * (b₁ - a₁)⁻¹)
    (mul_ne_zero (sub_ne_zero.mpr h2.symm) (inv_ne_zero (sub_ne_zero.mpr h1.symm)))
  let c : ZMod p := a₂ - (u : ZMod p) * a₁
  have ha : affEquiv u c a₁ = a₂ := by rw [affEquiv_apply]; simp only [c]; ring
  have hb : affEquiv u c b₁ = b₂ := by
    rw [affEquiv_apply]; simp only [c, u, Units.val_mk0]
    have hne : b₁ - a₁ ≠ 0 := sub_ne_zero.mpr h1.symm
    calc (b₂ - a₂) * (b₁ - a₁)⁻¹ * b₁ + (a₂ - (b₂ - a₂) * (b₁ - a₁)⁻¹ * a₁)
        = (b₂ - a₂) * ((b₁ - a₁)⁻¹ * (b₁ - a₁)) + a₂ := by ring
      _ = (b₂ - a₂) * 1 + a₂ := by rw [inv_mul_cancel₀ hne]
      _ = b₂ := by ring
  let e : (ZMod p → ℂ) ≃ₗ[ℂ] (ZMod p → ℂ) :=
    LinearEquiv.funCongrLeft ℂ ℂ (affEquiv u c).symm
  have hmap : Submodule.map (e : (ZMod p → ℂ) →ₗ[ℂ] (ZMod p → ℂ)) (Rmod E a₁ b₁) = Rmod E a₂ b₂ := by
    ext w
    simp only [Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [← ha, ← hb]
      exact (rmod_aff_equiv E u c a₁ b₁ v).mp hv
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      rw [rmod_aff_equiv E u c a₁ b₁ (e.symm w), ha, hb]
      convert hw using 1
      ext x; exact congrArg w ((affEquiv u c).apply_symm_apply x)
  rw [← hmap]
  exact (LinearEquiv.finrank_map_eq e (Rmod E a₁ b₁)).symm

/-- Cascade (Proposition 5.3): if `δ_z ∈ Rmod E a b`, then `w₁ ⊙ w₂ ∈ Rmod E a b` for all
`w₁ ∈ Rmod E a z` and `w₂ ∈ Rmod E z b`. -/
private lemma rmod_cascade {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    {a b z : ZMod p} (hz : Pi.single z (1 : ℂ) ∈ Rmod E a b)
    {w₁ w₂ : ZMod p → ℂ} (h1 : w₁ ∈ Rmod E a z) (h2 : w₂ ∈ Rmod E z b) :
    (fun x => w₁ x * w₂ x) ∈ Rmod E a b := by
  obtain ⟨Az, hAz, hAzv⟩ := hz
  obtain ⟨A₁, hA1, rfl⟩ := h1
  obtain ⟨A₂, hA2, rfl⟩ := h2
  let step1 := matTensor (matMstar (ZMod p)) (matMstar (ZMod p))
  let step2 := matTensor (matTensor (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ) (matMstar (ZMod p) * Az))
    (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ)
  let step3 := matTensor A₁ A₂
  have hstep1 : Cat E 2 4 step1 := Cat.tensor Cat.Mstar Cat.Mstar
  have hstep2 : Cat E 4 4 step2 := Cat.tensor (Cat.tensor (Cat.id 1) (Cat.comp hAz Cat.Mstar)) (Cat.id 1)
  have hstep3 : Cat E 4 2 step3 := Cat.tensor hA1 hA2
  refine ⟨matM (ZMod p) * (step3 * (step2 * step1)),
    Cat.comp (Cat.comp (Cat.comp hstep1 hstep2) hstep3) Cat.M, ?_⟩
  ext x
  simp only [eval21]
  have hs1 : ∀ f : Fin 4 → ZMod p, step1 f ![a, b] = if f = ![a, a, b, b] then 1 else 0 := by
    intro f
    simp only [step1, matTensor, matMstar, Matrix.of_apply]
    by_cases hf : f = ![a, a, b, b]
    · subst hf; simp [Fin.castAdd, Fin.natAdd]
    · rw [if_neg hf]
      by_contra hne; apply hf; ext r; fin_cases r <;> simp [Fin.castAdd, Fin.natAdd] at hne ⊢ <;> tauto
  have hMAz : ∀ g : Fin 2 → ZMod p, (matMstar (ZMod p) * Az) g ![a, b] =
      if g 0 = z ∧ g 1 = z then 1 else 0 := by
    intro g
    simp only [Matrix.mul_apply, matMstar, Matrix.of_apply]
    rw [← (Equiv.funUnique (Fin 1) (ZMod p)).symm.sum_comp]
    have hfun : ∀ y : ZMod p, (uniqueElim y : Fin 1 → ZMod p) = (fun _ => y) :=
      fun y => by ext r; fin_cases r; rfl
    have hval : ∀ y : ZMod p, Az (fun _ => y) ![a, b] = (Pi.single z (1 : ℂ) : ZMod p → ℂ) y :=
      fun y => congrFun hAzv y
    rw [Finset.sum_eq_single z]
    · simp only [Equiv.funUnique_symm_apply, hfun, hval, Pi.single_eq_same, mul_one]
    · intro y _ hy; simp only [Equiv.funUnique_symm_apply, hfun, hval, Pi.single_eq_of_ne hy, mul_zero]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hs2 : ∀ g : Fin 4 → ZMod p, (step2 * step1) g ![a, b] =
      if g = ![a, z, z, b] then 1 else 0 := by
    intro g
    simp only [Matrix.mul_apply, hs1]
    rw [Finset.sum_eq_single ![a, a, b, b]]
    · simp only [↓reduceIte, mul_one, step2, matTensor, Matrix.of_apply, Matrix.one_apply]
      have hab : (fun r : Fin 2 => ![a, a, b, b] (Fin.castAdd 1 (Fin.natAdd 1 r))) = ![a, b] := by
        ext r; fin_cases r <;> rfl
      rw [hab, hMAz]
      by_cases hg : g = ![a, z, z, b]
      · subst hg
        have h0 : (fun r : Fin 1 => ![a, z, z, b] (Fin.castAdd 1 (Fin.castAdd 2 r))) =
            (fun r : Fin 1 => ![a, a, b, b] (Fin.castAdd 1 (Fin.castAdd 2 r))) := by
          ext r; fin_cases r; rfl
        have h3 : (fun r : Fin 1 => ![a, z, z, b] (Fin.natAdd 3 r)) =
            (fun r : Fin 1 => ![a, a, b, b] (Fin.natAdd 3 r)) := by
          ext r; fin_cases r; rfl
        simp [h0, h3]
      · rw [if_neg hg]
        by_contra hne
        simp only [mul_eq_zero, ite_eq_right_iff, one_ne_zero, imp_false, not_or, not_not] at hne
        apply hg
        ext r; fin_cases r
        · exact congrFun hne.1.1 0
        · exact hne.1.2.1
        · exact hne.1.2.2
        · exact congrFun hne.2 0
    · intro f _ hf; simp [hf]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  have hs3 : ∀ h : Fin 2 → ZMod p, (step3 * (step2 * step1)) h ![a, b] =
      A₁ (fun _ => h 0) ![a, z] * A₂ (fun _ => h 1) ![z, b] := by
    intro h
    simp only [Matrix.mul_apply, hs2]
    rw [Finset.sum_eq_single ![a, z, z, b]]
    · simp only [↓reduceIte, mul_one, step3, matTensor, Matrix.of_apply]
      congr 1
      · congr 1 <;> (ext r; fin_cases r <;> rfl)
      · congr 1 <;> (ext r; fin_cases r <;> rfl)
    · intro g _ hg; simp [hg]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  simp only [Matrix.mul_apply, hs3, matM, Matrix.of_apply]
  rw [Finset.sum_eq_single (fun _ : Fin 2 => x)]
  · simp
  · intro h _ hh
    have hnot : ¬ (h 0 = x ∧ h 1 = x) := by rintro ⟨h0, h1⟩; apply hh; ext r; fin_cases r <;> assumption
    simp [hnot]
  · intro hm; exact absurd (Finset.mem_univ _) hm

private lemma rmod_splice {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    {a b z : ZMod p} (hab : a ≠ b) (haz : a ≠ z) (hzb : z ≠ b)
    (hz : Pi.single z (1 : ℂ) ∈ Rmod E a b) :
    Rmod E a z = Rmod E a b ∧ Rmod E z b = Rmod E a b := by
  have hle1 : Rmod E a z ≤ Rmod E a b := by
    intro w hw
    have := rmod_cascade E hz hw (const_one_mem_Rmod E z b)
    simpa using this
  have hle2 : Rmod E z b ≤ Rmod E a b := by
    intro w hw
    have := rmod_cascade E hz (const_one_mem_Rmod E a z) hw
    simpa using this
  exact ⟨Submodule.eq_of_le_of_finrank_eq hle1 (rmod_finrank_eq E haz hab),
         Submodule.eq_of_le_of_finrank_eq hle2 (rmod_finrank_eq E hzb hab)⟩

/-- In a field `F`, any subgroup `H ≤ Fˣ` of finite order `m` consists precisely of the `m`-th roots of unity. -/
private lemma subgroup_units_eq_roots {p : ℕ} [Fact (Nat.Prime p)] (H : Subgroup (ZMod p)ˣ) :
    ∀ x : (ZMod p)ˣ, x ∈ H ↔ x ^ Nat.card H = 1 := by
  classical
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hsub : ∀ x ∈ H, x ^ Nat.card H = 1 := by
    intro x hx
    have h1 : (⟨x, hx⟩ : H) ^ Nat.card H = 1 := by
      rw [Nat.card_eq_fintype_card]; exact pow_card_eq_one
    exact congrArg Subtype.val h1
  let S : Finset (ZMod p) := Finset.univ.filter fun y => y ^ Nat.card H = 1
  have hScard : S.card ≤ Nat.card H := by
    let poly : Polynomial (ZMod p) := Polynomial.X ^ Nat.card H - 1
    have hne : poly ≠ 0 := by
      intro h0
      have := congrArg (fun g : Polynomial (ZMod p) => g.coeff (Nat.card H)) h0
      simp [poly, Polynomial.coeff_one] at this
    have hroots : S.val ⊆ poly.roots := by
      intro y hy
      rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def]
      have hy' := (Finset.mem_filter.mp hy).2
      simp only [poly, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, hy', sub_self]
    calc S.card = S.val.card := rfl
      _ ≤ poly.roots.card := Multiset.card_le_card ((Multiset.le_iff_subset S.nodup).mpr hroots)
      _ ≤ poly.natDegree := Polynomial.card_roots' poly
      _ ≤ Nat.card H := by
        have h1 : (Polynomial.X ^ Nat.card H : Polynomial (ZMod p)).natDegree ≤ Nat.card H :=
          Polynomial.natDegree_X_pow_le _
        have h2 : (1 : Polynomial (ZMod p)).natDegree ≤ Nat.card H := by simp
        exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le h1 h2)
  let Hset : Finset (ZMod p) := Finset.univ.filter fun y => ∃ u : (ZMod p)ˣ, u ∈ H ∧ (u : ZMod p) = y
  have hHsub : Hset ⊆ S := by
    intro y hy
    obtain ⟨u, hu, rfl⟩ := (Finset.mem_filter.mp hy).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← Units.val_pow_eq_pow_val, hsub u hu, Units.val_one]
  have hHcard : Hset.card = Nat.card H := by
    rw [Nat.card_eq_fintype_card]
    have hEqImg : Hset = Finset.univ.image (fun u : H => (u.val : ZMod p)) := by
      ext y; simp [Hset]
    rw [hEqImg, Finset.card_image_of_injective _ (fun a b h => Subtype.ext (Units.ext h)), Finset.card_univ]
  have heq : Hset = S := Finset.eq_of_subset_of_card_le hHsub (by omega)
  intro x
  constructor
  · exact hsub x
  · intro hx
    have hmem : (x : ZMod p) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]⟩
    rw [← heq] at hmem
    obtain ⟨u, hu, hux⟩ := (Finset.mem_filter.mp hmem).2
    have : x = u := Units.ext hux.symm
    rwa [this]

/-- Capture Dichotomy (Theorem 5.8 / Corollary 5.9): a single captured point mass `δ_z ∈ Rmod E 0 1`
with `z ∉ {0, 1}` forces `δ_x ∈ Rmod E 0 1` for EVERY `x : ZMod p`! -/
private lemma capture_dichotomy {p : ℕ} [hp : Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    {z0 : ZMod p} (hz0 : z0 ≠ 0) (hz1 : z0 ≠ 1) (hcap : Pi.single z0 (1 : ℂ) ∈ Rmod E 0 1) :
    ∀ x : ZMod p, Pi.single x (1 : ℂ) ∈ Rmod E 0 1 := by
  let K : Set (ZMod p) := {z | Pi.single z (1 : ℂ) ∈ Rmod E 0 1}
  have h0K : (0 : ZMod p) ∈ K := pi1_mem_Rmod E 0 1
  have h1K : (1 : ZMod p) ∈ K := pi2_mem_Rmod E 0 1
  have hK_mul : ∀ z ∈ K, z ≠ 0 → ∀ w ∈ K, z * w ∈ K := by
    intro z hz hzne w hw
    by_cases hz1' : z = 1
    · simpa [hz1'] using hw
    · have hsp := (rmod_splice E zero_ne_one hzne.symm hz1' hz).1
      have h1 := (rmod_aff_equiv E (Units.mk0 z hzne) 0 0 1 (Pi.single w (1 : ℂ))).mp hw
      have hα0 : affEquiv (Units.mk0 z hzne) 0 0 = 0 := by rw [affEquiv_apply]; simp
      have hα1 : affEquiv (Units.mk0 z hzne) 0 1 = z := by rw [affEquiv_apply]; simp
      rw [hα0, hα1, hsp] at h1
      show Pi.single (z * w) (1 : ℂ) ∈ Rmod E 0 1
      convert h1 using 1
      ext x
      by_cases hx : x = z * w
      · subst hx
        have : (affEquiv (Units.mk0 z hzne) 0).symm (z * w) = w := by
          rw [affEquiv_symm_apply]; simp only [Units.val_mk0, sub_zero, ← mul_assoc, inv_mul_cancel₀ hzne, one_mul]
        simp [this]
      · have hne : (affEquiv (Units.mk0 z hzne) 0).symm x ≠ w := by
          intro heq; apply hx
          have := congrArg (affEquiv (Units.mk0 z hzne) 0) heq
          rw [Equiv.apply_symm_apply, affEquiv_apply] at this
          simpa using this
        simp [Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hne]
  have hK_aff : ∀ z ∈ K, z ≠ 0 → z ≠ 1 → ∀ w ∈ K, (1 - z) * w + z ∈ K := by
    intro z hz hzne hz1' w hw
    have hsp := (rmod_splice E zero_ne_one hzne.symm hz1' hz).2
    have h1z : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1')
    have h1 := (rmod_aff_equiv E (Units.mk0 (1 - z) h1z) z 0 1 (Pi.single w (1 : ℂ))).mp hw
    have hα0 : affEquiv (Units.mk0 (1 - z) h1z) z 0 = z := by rw [affEquiv_apply]; simp
    have hα1 : affEquiv (Units.mk0 (1 - z) h1z) z 1 = 1 := by rw [affEquiv_apply]; simp
    rw [hα0, hα1, hsp] at h1
    show Pi.single ((1 - z) * w + z) (1 : ℂ) ∈ Rmod E 0 1
    convert h1 using 1
    ext x
    by_cases hx : x = (1 - z) * w + z
    · subst hx
      have : (affEquiv (Units.mk0 (1 - z) h1z) z).symm ((1 - z) * w + z) = w := by
        rw [affEquiv_symm_apply]; simp only [Units.val_mk0, add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ h1z, one_mul]
      simp [this]
    · have hne : (affEquiv (Units.mk0 (1 - z) h1z) z).symm x ≠ w := by
        intro heq; apply hx
        have := congrArg (affEquiv (Units.mk0 (1 - z) h1z) z) heq
        rw [Equiv.apply_symm_apply, affEquiv_apply] at this
        simpa using this
      simp [Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hne]
  -- `H = {u : (ZMod p)ˣ | (u : ZMod p) ∈ K}` is a subgroup of `(ZMod p)ˣ`!
  let H : Subgroup (ZMod p)ˣ :=
    { carrier := {u | (u : ZMod p) ∈ K}
      one_mem' := h1K
      mul_mem' := fun {a b} ha hb => hK_mul a ha (Units.ne_zero a) b hb
      inv_mem' := fun {a} ha => by
        have hpos : 0 < orderOf a := orderOf_pos a
        have hpow : ∀ n : ℕ, (a ^ n : (ZMod p)ˣ).val ∈ K := by
          intro n; induction n with
          | zero => simpa using h1K
          | succ n ih =>
            rw [pow_succ]; exact hK_mul _ ih (Units.ne_zero _) a ha
        have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
          apply mul_left_cancel (a := a)
          rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        rw [hinv]; exact hpow (orderOf a - 1) }
  -- `L = {u : (ZMod p)ˣ | 1 - (u : ZMod p) ∈ K}` is ALSO a subgroup of `(ZMod p)ˣ` of the same size!
  let L : Subgroup (ZMod p)ˣ :=
    { carrier := {u | 1 - (u : ZMod p) ∈ K}
      one_mem' := by simpa using h0K
      mul_mem' := fun {a b} ha hb => by
        show 1 - ((a * b : (ZMod p)ˣ) : ZMod p) ∈ K
        have h1a : 1 - (a : ZMod p) ∈ K := ha
        have h1b : 1 - (b : ZMod p) ∈ K := hb
        by_cases ha1 : (a : ZMod p) = 1
        · simp [ha1, h1b]
        · have hz0' : 1 - (a : ZMod p) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
          have hz1' : 1 - (a : ZMod p) ≠ 1 := by intro h; exact Units.ne_zero a (by linear_combination -h)
          have haff := hK_aff (1 - (a : ZMod p)) h1a hz0' hz1' (1 - (b : ZMod p)) h1b
          have heq : (1 - (1 - (a : ZMod p))) * (1 - (b : ZMod p)) + (1 - (a : ZMod p)) =
              1 - ((a * b : (ZMod p)ˣ) : ZMod p) := by simp; ring
          rwa [heq] at haff
      inv_mem' := fun {a} ha => by
        have hpos : 0 < orderOf a := orderOf_pos a
        have hpow : ∀ n : ℕ, 1 - ((a ^ n : (ZMod p)ˣ) : ZMod p) ∈ K := by
          intro n; induction n with
          | zero => simpa using h0K
          | succ n ih =>
            have hstep : 1 - ((a ^ n * a : (ZMod p)ˣ) : ZMod p) ∈ K := by
              by_cases h1 : ((a ^ n : (ZMod p)ˣ) : ZMod p) = 1
              · simp only [Units.val_mul, h1, one_mul]; exact ha
              · have hz0' : 1 - ((a ^ n : (ZMod p)ˣ) : ZMod p) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
                have hz1' : 1 - ((a ^ n : (ZMod p)ˣ) : ZMod p) ≠ 1 := by
                  intro h; exact Units.ne_zero (a ^ n) (by linear_combination -h)
                have haff := hK_aff _ ih hz0' hz1' (1 - (a : ZMod p)) ha
                have heq : (1 - (1 - ((a ^ n : (ZMod p)ˣ) : ZMod p))) * (1 - (a : ZMod p)) +
                    (1 - ((a ^ n : (ZMod p)ˣ) : ZMod p)) = 1 - ((a ^ n * a : (ZMod p)ˣ) : ZMod p) := by
                  simp; ring
                rwa [heq] at haff
            rwa [pow_succ]
        have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
          apply mul_left_cancel (a := a)
          rw [mul_inv_cancel, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        rw [hinv]; exact hpow (orderOf a - 1) }
  have hHL_card : Nat.card H = Nat.card L := by
    classical
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    have hKfin : Fintype.card {x : ZMod p // x ∈ K ∧ x ≠ 0} = Fintype.card H := by
      refine Fintype.card_congr
        { toFun := fun ⟨x, hxK, hx0⟩ => ⟨Units.mk0 x hx0, hxK⟩
          invFun := fun ⟨u, hu⟩ => ⟨u, hu, Units.ne_zero u⟩
          left_inv := fun ⟨_, _, _⟩ => rfl
          right_inv := fun ⟨_, _⟩ => Subtype.ext (Units.ext rfl) }
    have hLfin : Fintype.card {x : ZMod p // x ∈ K ∧ x ≠ 1} = Fintype.card L := by
      refine Fintype.card_congr
        { toFun := fun ⟨x, hxK, hx1⟩ => ⟨Units.mk0 (1 - x) (sub_ne_zero.mpr (Ne.symm hx1)), by
            show 1 - (1 - x) ∈ K; simpa using hxK⟩
          invFun := fun ⟨u, hu⟩ => ⟨1 - u, hu, by intro h; exact Units.ne_zero u (by linear_combination -h)⟩
          left_inv := fun ⟨x, _, _⟩ => Subtype.ext (by simp only [Units.val_mk0]; ring)
          right_inv := fun ⟨u, _⟩ => Subtype.ext (Units.ext (by simp)) }
    rw [← hKfin, ← hLfin]
    have hK0 : Fintype.card {x : ZMod p // x ∈ K ∧ x ≠ 0} + 1 = Fintype.card {x : ZMod p // x ∈ K} := by
      have e : {x : ZMod p // x ∈ K} ≃ {x : ZMod p // x ∈ K ∧ x ≠ 0} ⊕ Unit :=
        { toFun := fun ⟨x, hx⟩ => if h : x = 0 then Sum.inr () else Sum.inl ⟨x, hx, h⟩
          invFun := fun s => match s with
            | Sum.inl ⟨x, hx, _⟩ => ⟨x, hx⟩
            | Sum.inr () => ⟨0, h0K⟩
          left_inv := fun ⟨x, hx⟩ => by by_cases h : x = 0 <;> simp [h]
          right_inv := fun s => match s with
            | Sum.inl ⟨x, hx, h⟩ => by simp [h]
            | Sum.inr () => by simp }
      rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_unit]
    have hK1 : Fintype.card {x : ZMod p // x ∈ K ∧ x ≠ 1} + 1 = Fintype.card {x : ZMod p // x ∈ K} := by
      have e : {x : ZMod p // x ∈ K} ≃ {x : ZMod p // x ∈ K ∧ x ≠ 1} ⊕ Unit :=
        { toFun := fun ⟨x, hx⟩ => if h : x = 1 then Sum.inr () else Sum.inl ⟨x, hx, h⟩
          invFun := fun s => match s with
            | Sum.inl ⟨x, hx, _⟩ => ⟨x, hx⟩
            | Sum.inr () => ⟨1, h1K⟩
          left_inv := fun ⟨x, hx⟩ => by by_cases h : x = 1 <;> simp [h]
          right_inv := fun s => match s with
            | Sum.inl ⟨x, hx, h⟩ => by simp [h]
            | Sum.inr () => by simp }
      rw [Fintype.card_congr e, Fintype.card_sum, Fintype.card_unit]
    omega
  have hHL : H = L := by
    ext u
    rw [subgroup_units_eq_roots H, subgroup_units_eq_roots L, hHL_card]
  have hsub1 : ∀ x : ZMod p, x ∈ K → 1 - x ∈ K := by
    intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using h1K
    · by_cases hx1 : x = 1
      · simpa [hx1] using h0K
      · have huH : Units.mk0 x hx0 ∈ H := hx
        rw [hHL] at huH
        exact huH
  -- Step 1: `-1 ∈ K`
  have hneg1 : (-1 : ZMod p) ∈ K := by
    have h1z : 1 - z0 ∈ K := hsub1 z0 hcap
    have hinv_u : (Units.mk0 z0 hz0)⁻¹ ∈ H := H.inv_mem hcap
    have hinv_mem : z0⁻¹ ∈ K := by
      have h1 : (((Units.mk0 z0 hz0)⁻¹ : (ZMod p)ˣ) : ZMod p) ∈ K := hinv_u
      simpa only [Units.val_inv_eq_inv_val, Units.val_mk0] using h1
    have h1inv : 1 - z0⁻¹ ∈ K := hsub1 z0⁻¹ hinv_mem
    have h1inv_ne : 1 - z0⁻¹ ≠ 0 := by
      intro h; apply hz1
      have : z0⁻¹ = 1 := by linear_combination -h
      simpa using congrArg Inv.inv this
    have h1z_ne : 1 - z0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    have hq_u : Units.mk0 (1 - z0) h1z_ne * (Units.mk0 (1 - z0⁻¹) h1inv_ne)⁻¹ ∈ H :=
      H.mul_mem h1z (H.inv_mem h1inv)
    have hneg_z : -z0 ∈ K := by
      have heq : ((Units.mk0 (1 - z0) h1z_ne * (Units.mk0 (1 - z0⁻¹) h1inv_ne)⁻¹ : (ZMod p)ˣ) : ZMod p) = -z0 := by
        simp only [Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
        apply mul_right_cancel₀ h1inv_ne
        rw [mul_assoc, inv_mul_cancel₀ h1inv_ne, mul_one, mul_sub, mul_one, neg_mul, mul_inv_cancel₀ hz0]
        ring
      have hqK : ((Units.mk0 (1 - z0) h1z_ne * (Units.mk0 (1 - z0⁻¹) h1inv_ne)⁻¹ : (ZMod p)ˣ) : ZMod p) ∈ K := hq_u
      rwa [heq] at hqK
    have hneg1_eq : (-z0) * z0⁻¹ = -1 := by rw [neg_mul, mul_inv_cancel₀ hz0]
    rw [← hneg1_eq]
    exact hK_mul (-z0) hneg_z (neg_ne_zero.mpr hz0) z0⁻¹ hinv_mem
  -- Step 2: `K` is closed under addition!
  have hK_add : ∀ a ∈ K, ∀ b ∈ K, a + b ∈ K := by
    intro a ha b hb
    by_cases ha0 : a = 0
    · simpa [ha0] using hb
    · by_cases hb0 : b = 0
      · simpa [hb0] using ha
      · have hne : -b * a⁻¹ ∈ K := by
          have hnb : -b ∈ K := by simpa using hK_mul (-1) hneg1 (neg_ne_zero.mpr one_ne_zero) b hb
          have hainv : a⁻¹ ∈ K := by
            have h1 : (((Units.mk0 a ha0)⁻¹ : (ZMod p)ˣ) : ZMod p) ∈ K :=
              H.inv_mem (show Units.mk0 a ha0 ∈ H from ha)
            simpa only [Units.val_inv_eq_inv_val, Units.val_mk0] using h1
          exact hK_mul (-b) hnb (neg_ne_zero.mpr hb0) a⁻¹ hainv
        have h1t : 1 - (-b * a⁻¹) ∈ K := hsub1 _ hne
        have heq : a * (1 - (-b * a⁻¹)) = a + b := by
          calc a * (1 - (-b * a⁻¹)) = a + b * (a * a⁻¹) := by ring
            _ = a + b := by rw [mul_inv_cancel₀ ha0, mul_one]
        rw [← heq]
        exact hK_mul a ha ha0 _ h1t
  -- Step 3: `K` contains every `(k : ZMod p)`, hence all of `ZMod p`!
  have hnat : ∀ k : ℕ, (k : ZMod p) ∈ K := by
    intro k; induction k with
    | zero => simpa using h0K
    | succ k ih => simpa [Nat.cast_succ] using hK_add (k : ZMod p) ih 1 h1K
  intro x
  rw [← ZMod.natCast_zmod_val x]
  exact hnat x.val

/-- Assembly Lemma (Lemma 4.5): if `Rmod E 0 y = ⊤` for every `y ≠ 0`, then `matSwap ∈ Cat E 2 2`. -/
private lemma assembly_swap {p : ℕ} [hp : Fact (Nat.Prime p)] (hp3 : 3 ≤ p)
    (E : Subgroup (ZMod p)ˣ)
    (hfull : ∀ y : ZMod p, y ≠ 0 → ∀ x : ZMod p, Pi.single x (1 : ℂ) ∈ Rmod E 0 y) :
    Cat E 2 2 (matSwap (ZMod p)) := by
  classical
  -- Step 1: Orbital projection `g y : (i, j) ↦ δ_{j - i ∈ cosetOf E y} (i, j)`
  let gMat (y : ZMod p) : Matrix (Fin 2 → ZMod p) (Fin 2 → ZMod p) ℂ :=
    Matrix.of fun i j => if i = j ∧ j 1 - j 0 ∈ cosetOf E y then 1 else 0
  have hgCat : ∀ y : ZMod p, Cat E 2 2 (gMat y) := by
    intro y
    let step1 := matTensor (matMstar (ZMod p)) (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ)
    let step2 := matTensor (matTensor (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ)
      (matOf1 (circulantAdj p (cosetOf E y)))) (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ)
    let step3 := matTensor (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ) (matM (ZMod p))
    have hcat : Cat E 2 2 (step3 * (step2 * step1)) :=
      Cat.comp (Cat.comp (Cat.tensor Cat.Mstar (Cat.id 1))
        (Cat.tensor (Cat.tensor (Cat.id 1) (Cat.T y)) (Cat.id 1)))
        (Cat.tensor (Cat.id 1) Cat.M)
    convert hcat using 1
    ext i j
    have hs1 : ∀ f : Fin 3 → ZMod p, step1 f j = if f = ![j 0, j 0, j 1] then 1 else 0 := by
      intro f
      simp only [step1, matTensor, matMstar, Matrix.of_apply, Matrix.one_apply]
      by_cases hf : f = ![j 0, j 0, j 1]
      · subst hf
        have h1 : (fun r : Fin 1 => ![j 0, j 0, j 1] (Fin.natAdd 2 r)) =
            (fun r : Fin 1 => j (Fin.natAdd 1 r)) := by ext r; fin_cases r; rfl
        simp [h1]
      · rw [if_neg hf]
        by_contra hne
        simp only [mul_eq_zero, ite_eq_right_iff, one_ne_zero, imp_false, not_or, not_not] at hne
        apply hf
        ext r; fin_cases r
        · exact hne.1.1
        · exact hne.1.2
        · exact congrFun hne.2 0
    have hs2 : ∀ h : Fin 3 → ZMod p, (step2 * step1) h j =
        (if h 0 = j 0 then 1 else 0) * (if h 1 - j 0 ∈ cosetOf E y then 1 else 0) * (if h 2 = j 1 then 1 else 0) := by
      intro h
      simp only [Matrix.mul_apply, hs1]
      rw [Finset.sum_eq_single ![j 0, j 0, j 1]]
      · simp only [↓reduceIte, mul_one, step2, matTensor, Matrix.of_apply, Matrix.one_apply, matOf1, circulantAdj]
        have h0 : (fun r : Fin 1 => h (Fin.castAdd 1 (Fin.castAdd 1 r))) =
            (fun r : Fin 1 => ![j 0, j 0, j 1] (Fin.castAdd 1 (Fin.castAdd 1 r))) ↔ h 0 = j 0 := by
          constructor
          · intro heq; exact congrFun heq 0
          · intro heq; ext r; fin_cases r; exact heq
        have h2 : (fun r : Fin 1 => h (Fin.natAdd 2 r)) =
            (fun r : Fin 1 => ![j 0, j 0, j 1] (Fin.natAdd 2 r)) ↔ h 2 = j 1 := by
          constructor
          · intro heq; exact congrFun heq 0
          · intro heq; ext r; fin_cases r; exact heq
        simp only [h0, h2]; rfl
      · intro f _ hf; simp [hf]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    simp only [gMat, Matrix.of_apply, Matrix.mul_apply, hs2]
    rw [Finset.sum_eq_single ![j 0, j 1, j 1]]
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        ↓reduceIte, one_mul, step3, matTensor, Matrix.of_apply, Matrix.one_apply, matM]
      have h0 : (fun r : Fin 1 => i (Fin.castAdd 1 r)) =
          (fun r : Fin 1 => ![j 0, j 1, j 1] (Fin.castAdd 2 r)) ↔ i 0 = j 0 := by
        constructor
        · intro heq; exact congrFun heq 0
        · intro heq; ext r; fin_cases r; exact heq
      simp only [h0]
      change (if i = j ∧ j 1 - j 0 ∈ cosetOf E y then (1 : ℂ) else 0) =
        ((if i 0 = j 0 then 1 else 0) * (if j 1 = i 1 ∧ j 1 = i 1 then 1 else 0)) *
          ((if j 1 - j 0 ∈ cosetOf E y then 1 else 0) * (if j 1 = j 1 then 1 else 0))
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg (fun h => hij h.1)]
        have : ¬ (i 0 = j 0 ∧ i 1 = j 1) := by
          rintro ⟨h0', h1'⟩; apply hij; ext r; fin_cases r <;> assumption
        by_cases h0' : i 0 = j 0 <;> by_cases h1' : i 1 = j 1 <;> simp_all [eq_comm]
    · intro h _ hh
      by_cases h0 : h 0 = j 0
      · by_cases h2 : h 2 = j 1
        · have h1 : h 1 ≠ j 1 := fun heq => hh (by ext r; fin_cases r <;> assumption)
          have hnot : ¬ (h 1 = i 1 ∧ h 2 = i 1) := fun ⟨a1, a2⟩ => h1 (a1.trans (a2.symm.trans h2))
          simp [step3, matTensor, matM, hnot]
        · simp [h2]
      · simp [h0]
    · intro hm; exact absurd (Finset.mem_univ _) hm
  -- Step 2: For each `y ≠ 0`, build `L_y ∈ Cat E 2 2` flipping `(i, j)` whenever `j - i ∈ cosetOf E y`!
  have hflip_orbit : ∀ y : ZMod p, y ≠ 0 →
      ∃ L : Matrix (Fin 2 → ZMod p) (Fin 2 → ZMod p) ℂ, Cat E 2 2 L ∧
        ∀ i j : Fin 2 → ZMod p, j 1 - j 0 ∈ cosetOf E y →
          L i j = if i 0 = j 1 ∧ i 1 = j 0 then 1 else 0 := by
    intro y hy
    -- Choose `w ∉ {0, y}` (exists since `p ≥ 3`)
    have hex_w : ∃ w : ZMod p, w ≠ 0 ∧ w ≠ y := by
      have hcard : ({0, y} : Finset (ZMod p)).card ≤ 2 := Finset.card_le_two
      have htot : (Finset.univ : Finset (ZMod p)).card = p := ZMod.card p
      have hne : (Finset.univ \ ({0, y} : Finset (ZMod p))).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hemp
        have hsub : (Finset.univ : Finset (ZMod p)) ⊆ {0, y} := Finset.sdiff_eq_empty_iff_subset.mp hemp
        have := Finset.card_le_card hsub
        omega
      obtain ⟨w, hw⟩ := hne
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and, not_or] at hw
      exact ⟨w, hw.1, hw.2⟩
    obtain ⟨w, hw0, hwy⟩ := hex_w
    have hyw : y - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwy)
    obtain ⟨Fw, hFw_cat, hFw_val⟩ := hfull y hy w
    obtain ⟨F1, hF1_cat, hF1_val⟩ := hfull w hw0 y
    obtain ⟨F2, hF2_cat, hF2_val⟩ := hfull (y - w) hyw (-w)
    let step1 := matTensor (matMstar (ZMod p)) (matMstar (ZMod p))
    let step2 := matTensor (matTensor (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ)
      (matMstar (ZMod p) * Fw)) (1 : Matrix (Fin 1 → ZMod p) (Fin 1 → ZMod p) ℂ)
    let step3 := matTensor F1 F2
    let L : Matrix (Fin 2 → ZMod p) (Fin 2 → ZMod p) ℂ := step3 * (step2 * step1)
    have hL_cat : Cat E 2 2 L :=
      Cat.comp (Cat.comp (Cat.tensor Cat.Mstar Cat.Mstar)
        (Cat.tensor (Cat.tensor (Cat.id 1) (Cat.comp hFw_cat Cat.Mstar)) (Cat.id 1)))
        (Cat.tensor hF1_cat hF2_cat)
    -- Evaluate `L i ![0, y]`!
    have hL_base : ∀ i : Fin 2 → ZMod p, L i ![0, y] = if i 0 = y ∧ i 1 = 0 then 1 else 0 := by
      intro i
      have hs1 : ∀ f : Fin 4 → ZMod p, step1 f ![0, y] = if f = ![0, 0, y, y] then 1 else 0 := by
        intro f
        simp only [step1, matTensor, matMstar, Matrix.of_apply]
        by_cases hf : f = ![0, 0, y, y]
        · subst hf; simp [Fin.castAdd, Fin.natAdd]
        · rw [if_neg hf]
          by_contra hne; apply hf; ext r; fin_cases r <;> simp [Fin.castAdd, Fin.natAdd] at hne ⊢ <;> tauto
      have hMFw : ∀ g : Fin 2 → ZMod p, (matMstar (ZMod p) * Fw) g ![0, y] =
          if g 0 = w ∧ g 1 = w then 1 else 0 := by
        intro g
        simp only [Matrix.mul_apply, matMstar, Matrix.of_apply]
        rw [← (Equiv.funUnique (Fin 1) (ZMod p)).symm.sum_comp]
        have hfun : ∀ z : ZMod p, (uniqueElim z : Fin 1 → ZMod p) = (fun _ => z) :=
          fun z => by ext r; fin_cases r; rfl
        have hval : ∀ z : ZMod p, Fw (fun _ => z) ![0, y] = (Pi.single w (1 : ℂ) : ZMod p → ℂ) z :=
          fun z => congrFun hFw_val z
        rw [Finset.sum_eq_single w]
        · simp only [Equiv.funUnique_symm_apply, hfun, hval, Pi.single_eq_same, mul_one]
        · intro z _ hz; simp only [Equiv.funUnique_symm_apply, hfun, hval, Pi.single_eq_of_ne hz, mul_zero]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      have hs2 : ∀ g : Fin 4 → ZMod p, (step2 * step1) g ![0, y] =
          if g = ![0, w, w, y] then 1 else 0 := by
        intro g
        simp only [Matrix.mul_apply, hs1]
        rw [Finset.sum_eq_single ![0, 0, y, y]]
        · simp only [↓reduceIte, mul_one, step2, matTensor, Matrix.of_apply, Matrix.one_apply]
          have hab : (fun r : Fin 2 => ![0, 0, y, y] (Fin.castAdd 1 (Fin.natAdd 1 r))) = ![0, y] := by
            ext r; fin_cases r <;> rfl
          rw [hab, hMFw]
          by_cases hg : g = ![0, w, w, y]
          · subst hg
            have h0 : (fun r : Fin 1 => ![0, w, w, y] (Fin.castAdd 1 (Fin.castAdd 2 r))) =
                (fun r : Fin 1 => ![0, 0, y, y] (Fin.castAdd 1 (Fin.castAdd 2 r))) := by
              ext r; fin_cases r; rfl
            have h3 : (fun r : Fin 1 => ![0, w, w, y] (Fin.natAdd 3 r)) =
                (fun r : Fin 1 => ![0, 0, y, y] (Fin.natAdd 3 r)) := by
              ext r; fin_cases r; rfl
            simp [h0, h3]
          · rw [if_neg hg]
            by_contra hne
            simp only [mul_eq_zero, ite_eq_right_iff, one_ne_zero, imp_false, not_or, not_not] at hne
            apply hg
            ext r; fin_cases r
            · exact congrFun hne.1.1 0
            · exact hne.1.2.1
            · exact hne.1.2.2
            · exact congrFun hne.2 0
        · intro f _ hf; simp [hf]
        · intro hm; exact absurd (Finset.mem_univ _) hm
      -- Evaluate `F2 (fun _ => i 1) ![w, y]` using translation by `w` (`G`-equivariance!)
      have hF2_shift : F2 (fun _ => i 1) ![w, y] = if i 1 = 0 then 1 else 0 := by
        have hG := conjPerm_cat_G_eq (1 : E) w hF2_cat
        have hpt := congrFun (congrFun hG (fun _ => i 1)) ![w, y]
        simp only [conjPerm, Matrix.of_apply, OneMemClass.coe_one] at hpt
        rw [← hpt]
        have hwy' : (fun r : Fin 2 => (affEquiv (1 : (ZMod p)ˣ) w).symm (![w, y] r)) = ![0, y - w] := by
          ext r; fin_cases r <;> simp [affEquiv_symm_apply]
        rw [hwy']
        have hval := congrFun hF2_val ((affEquiv (1 : (ZMod p)ˣ) w).symm (i 1))
        simp only [eval21] at hval
        rw [hval]
        have hiff : (affEquiv (1 : (ZMod p)ˣ) w).symm (i 1) = -w ↔ i 1 = 0 := by
          rw [affEquiv_symm_apply]; simp only [Units.val_one, inv_one, one_mul]
          constructor <;> intro h <;> linear_combination h
        by_cases hi1 : i 1 = 0
        · rw [if_pos hi1, hiff.mpr hi1]; simp
        · rw [if_neg hi1, Pi.single_eq_of_ne (mt hiff.mp hi1)]
      simp only [L, Matrix.mul_apply, hs2]
      rw [Finset.sum_eq_single ![0, w, w, y]]
      · simp only [↓reduceIte, mul_one, step3, matTensor, Matrix.of_apply]
        have h1a : (fun r : Fin 1 => i (Fin.castAdd 1 r)) = (fun _ => i 0) := by ext r; fin_cases r; rfl
        have h1b : (fun r : Fin 2 => ![0, w, w, y] (Fin.castAdd 2 r)) = ![0, w] := by ext r; fin_cases r <;> rfl
        have h2a : (fun r : Fin 1 => i (Fin.natAdd 1 r)) = (fun _ => i 1) := by ext r; fin_cases r; rfl
        have h2b : (fun r : Fin 2 => ![0, w, w, y] (Fin.natAdd 2 r)) = ![w, y] := by ext r; fin_cases r <;> rfl
        rw [h1a, h1b, h2a, h2b, hF2_shift]
        have hF1i : F1 (fun _ => i 0) ![0, w] = (Pi.single y (1 : ℂ) : ZMod p → ℂ) (i 0) := congrFun hF1_val (i 0)
        rw [hF1i]
        by_cases h0 : i 0 = y <;> by_cases h1 : i 1 = 0 <;> simp [h0, h1, Pi.single_eq_of_ne]
      · intro g _ hg; simp [hg]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    -- Now use `G`-equivariance of `L` to evaluate `L i j` for any `j 1 - j 0 ∈ cosetOf E y`!
    refine ⟨L, hL_cat, fun i j hj => ?_⟩
    simp only [cosetOf, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    obtain ⟨e, he⟩ := hj
    let α := affEquiv e.val (j 0)
    have hG := conjPerm_cat_G_eq e (j 0) hL_cat
    have hpt := congrFun (congrFun hG i) j
    simp only [conjPerm, Matrix.of_apply] at hpt
    rw [← hpt]
    have hj_pre : (fun r : Fin 2 => α.symm (j r)) = ![0, y] := by
      ext r; fin_cases r
      · show (e.val : ZMod p)⁻¹ * (j 0 - j 0) = 0
        simp only [sub_self, mul_zero]
      · show (e.val : ZMod p)⁻¹ * (j 1 - j 0) = y
        rw [he, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero e.val), one_mul]
    rw [hj_pre, hL_base]
    have h0 : α.symm (i 0) = y ↔ i 0 = j 1 := by
      constructor
      · intro h
        have := congrArg α h
        simp only [Equiv.apply_symm_apply, α, affEquiv_apply] at this
        linear_combination this - he
      · intro h
        rw [h]; show (e.val : ZMod p)⁻¹ * (j 1 - j 0) = y
        rw [he, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero e.val), one_mul]
    have h1 : α.symm (i 1) = 0 ↔ i 1 = j 0 := by
      constructor
      · intro h; have := congrArg α h; simp only [Equiv.apply_symm_apply, α, affEquiv_apply, mul_zero, zero_add] at this; exact this
      · intro h; rw [h]; show (e.val : ZMod p)⁻¹ * (j 0 - j 0) = 0; simp only [sub_self, mul_zero]
    exact ite_congr (propext (and_congr h0 h1)) (fun _ => rfl) (fun _ => rfl)
  -- Step 3: Sum `gMat 0 + ∑_{C ∈ orbits} L_C * gMat y_C` over the distinct nonzero cosets!
  let nonzeroCosets : Finset (Finset (ZMod p)) :=
    (Finset.univ.erase (0 : ZMod p)).image (cosetOf E)
  have hrep : ∀ C ∈ nonzeroCosets, ∃ y : ZMod p, y ≠ 0 ∧ cosetOf E y = C := by
    intro C hC
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hC
    exact ⟨y, (Finset.mem_erase.mp hy).1, rfl⟩
  let pickY (C : Finset (ZMod p)) : ZMod p :=
    if hC : C ∈ nonzeroCosets then Classical.choose (hrep C hC) else 1
  have hpick_ne : ∀ C (hC : C ∈ nonzeroCosets), pickY C ≠ 0 ∧ cosetOf E (pickY C) = C := by
    intro C hC; simp only [pickY, dif_pos hC]; exact Classical.choose_spec (hrep C hC)
  let pickL (C : Finset (ZMod p)) : Matrix (Fin 2 → ZMod p) (Fin 2 → ZMod p) ℂ :=
    if hC : C ∈ nonzeroCosets then
      Classical.choose (hflip_orbit (pickY C) (hpick_ne C hC).1)
    else 0
  have hpickL : ∀ C (hC : C ∈ nonzeroCosets),
      Cat E 2 2 (pickL C) ∧
      ∀ i j : Fin 2 → ZMod p, j 1 - j 0 ∈ C →
        pickL C i j = if i 0 = j 1 ∧ i 1 = j 0 then 1 else 0 := by
    intro C hC
    simp only [pickL, dif_pos hC]
    have hspec := Classical.choose_spec (hflip_orbit (pickY C) (hpick_ne C hC).1)
    exact ⟨hspec.1, fun i j hij => hspec.2 i j (by rwa [(hpick_ne C hC).2])⟩
  let Ξ : Matrix (Fin 2 → ZMod p) (Fin 2 → ZMod p) ℂ :=
    gMat 0 + ∑ C ∈ nonzeroCosets, pickL C * gMat (pickY C)
  have hΞ_cat : Cat E 2 2 Ξ := by
    refine Cat.add (hgCat 0) ?_
    suffices ∀ s : Finset (Finset (ZMod p)), s ⊆ nonzeroCosets →
        Cat E 2 2 (∑ C ∈ s, pickL C * gMat (pickY C)) from this nonzeroCosets (Finset.Subset.refl _)
    intro s
    induction s using Finset.induction with
    | empty => intro _; simp; exact Cat.zero 2 2
    | @insert C s hC ih =>
      intro hsub
      rw [Finset.sum_insert hC]
      have hCmem : C ∈ nonzeroCosets := hsub (Finset.mem_insert_self C s)
      have hs_sub : s ⊆ nonzeroCosets := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      exact Cat.add (Cat.comp (hgCat (pickY C)) (hpickL C hCmem).1) (ih hs_sub)
  have hΞ_eq : Ξ = matSwap (ZMod p) := by
    ext i j
    simp only [Ξ, Matrix.add_apply, Matrix.sum_apply, matSwap, Matrix.of_apply]
    have hterm : ∀ C ∈ nonzeroCosets,
        (pickL C * gMat (pickY C)) i j =
          if j 1 - j 0 ∈ C then (if i 0 = j 1 ∧ i 1 = j 0 then 1 else 0) else 0 := by
      intro C hC
      simp only [Matrix.mul_apply, gMat, Matrix.of_apply]
      rw [Finset.sum_eq_single j]
      · simp only [true_and, (hpick_ne C hC).2]
        by_cases hmem : j 1 - j 0 ∈ C
        · simp [hmem, (hpickL C hC).2 i j hmem]
        · simp [hmem]
      · intro k _ hk; simp [hk]
      · intro hm; exact absurd (Finset.mem_univ _) hm
    by_cases hd : j 1 - j 0 = 0
    · have hj01 : j 0 = j 1 := (sub_eq_zero.mp hd).symm
      have hg0 : gMat 0 i j = if i 0 = j 1 ∧ i 1 = j 0 then 1 else 0 := by
        simp only [gMat, Matrix.of_apply, cosetOf_zero, Finset.mem_singleton, hd, and_true]
        by_cases hij : i = j
        · subst hij; simp [hj01]
        · rw [if_neg hij]
          have : ¬ (i 0 = j 1 ∧ i 1 = j 0) := by
            rintro ⟨h0, h1⟩; apply hij; ext r; fin_cases r <;> simp [h0, h1, hj01]
          simp [this]
      have hsum0 : ∑ C ∈ nonzeroCosets, (pickL C * gMat (pickY C)) i j = 0 := by
        refine Finset.sum_eq_zero fun C hC => ?_
        rw [hterm C hC]
        have h0not : (0 : ZMod p) ∉ C := by
          rw [← (hpick_ne C hC).2]
          simp only [cosetOf, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
          intro e he
          exact (hpick_ne C hC).1 (mul_eq_zero.mp he.symm |>.resolve_left (Units.ne_zero e.val))
        rw [hd, if_neg h0not]
      rw [hg0, hsum0, add_zero]
    · have hg0 : gMat 0 i j = 0 := by
        simp [gMat, cosetOf_zero, hd]
      let C0 := cosetOf E (j 1 - j 0)
      have hC0_mem : C0 ∈ nonzeroCosets :=
        Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hd, Finset.mem_univ _⟩)
      have hsum : ∑ C ∈ nonzeroCosets, (pickL C * gMat (pickY C)) i j =
          if i 0 = j 1 ∧ i 1 = j 0 then 1 else 0 := by
        rw [Finset.sum_eq_single C0]
        · rw [hterm C0 hC0_mem, if_pos (mem_cosetOf_self E (j 1 - j 0))]
        · intro C hC hne
          rw [hterm C hC]
          have hnot : j 1 - j 0 ∉ C := by
            intro hmem
            apply hne
            rw [← (hpick_ne C hC).2] at hmem ⊢
            exact (cosetOf_eq_of_mem E hmem).symm
          rw [if_neg hnot]
        · intro hm; exact absurd hC0_mem hm
      rw [hg0, zero_add, hsum]
  rwa [← hΞ_eq]

/-! ### Part 4: Quadratic threshold (Confinement) and the 8 finite pairs up to type 10 -/

/-- Master criterion: if a single point mass `δ_z` (`z ∉ {0, 1}`) lies in `Rmod E 0 1`,
then `circulantAdj p S` has no quantum symmetry! -/
private lemma rigid_of_capture {p : ℕ} [hp : Fact (Nat.Prime p)] (hp5 : 5 ≤ p)
    {S : Finset (ZMod p)}
    (hSne : S.Nonempty) (hS0 : (0 : ZMod p) ∉ S)
    (hSneg : ∀ x ∈ S, -x ∈ S) (E : Subgroup (ZMod p)ˣ)
    (hE : ∀ a : (ZMod p)ˣ, a ∈ E ↔ S.image (fun s => (a : ZMod p) * s) = S)
    (hEneg : (-1 : (ZMod p)ˣ) ∈ E)
    {z0 : ZMod p} (hz0 : z0 ≠ 0) (hz1 : z0 ≠ 1)
    (hcap : Pi.single z0 (1 : ℂ) ∈ Rmod E 0 1) :
    HasNoQuantumSymmetry (circulantAdj p S) := by
  have hfull01 := capture_dichotomy E hz0 hz1 hcap
  have hfull : ∀ y : ZMod p, y ≠ 0 → ∀ x : ZMod p, Pi.single x (1 : ℂ) ∈ Rmod E 0 y := by
    intro y hy x
    have h1 := (rmod_aff_equiv E (Units.mk0 y hy) 0 0 1 (Pi.single (y⁻¹ * x) (1 : ℂ))).mp (hfull01 (y⁻¹ * x))
    have hα0 : affEquiv (Units.mk0 y hy) 0 0 = 0 := by rw [affEquiv_apply]; simp
    have hα1 : affEquiv (Units.mk0 y hy) 0 1 = y := by rw [affEquiv_apply]; simp
    rw [hα0, hα1] at h1
    convert h1 using 1
    ext t
    by_cases htx : t = x
    · subst htx
      have : (affEquiv (Units.mk0 y hy) 0).symm t = y⁻¹ * t := by
        rw [affEquiv_symm_apply]; simp
      simp [this]
    · have hne : (affEquiv (Units.mk0 y hy) 0).symm t ≠ y⁻¹ * x := by
        intro heq; apply htx
        have := congrArg (fun z => y * z) heq
        rw [affEquiv_symm_apply] at this
        simp only [Units.val_mk0, sub_zero, ← mul_assoc, mul_inv_cancel₀ hy, one_mul] at this
        exact this
      simp [Pi.single_eq_of_ne htx, Pi.single_eq_of_ne hne]
  have hswap : Cat E 2 2 (matSwap (ZMod p)) := assembly_swap (by omega) E hfull
  intro R _ _ u hu hcomm
  have hT : ∀ y : ZMod p,
      u * (circulantAdj p (cosetOf E y)).map (algebraMap ℂ R) =
      (circulantAdj p (cosetOf E y)).map (algebraMap ℂ R) * u := by
    intro y
    obtain ⟨P, hP⟩ := spectral_poly hSne hS0 hSneg E hE hEneg y
    rw [← hP]
    exact comm_aeval hcomm P
  exact comm_of_intertwines_swap (cat_sound hu hT hswap)

/-- Singleton block implies capture (`δ_z ∈ Rmod E 0 1`). -/
private lemma capture_of_singleton_block {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (s t z : ZMod p) (hblk : ∀ x : ZMod p, (x ∈ cosetOf E s ∧ x - 1 ∈ cosetOf E t) ↔ x = z) :
    Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  have h := block_ind_mem_Rmod E s t
  convert h using 1
  ext x
  by_cases hx : x = z
  · subst hx; simp [(hblk x).mpr rfl]
  · simp [hblk x, hx]

/-- Confinement Lemma (Lemma 6.1) + Quadratic Threshold (Theorem 6.2):
if `p > (k - 1) * (k - 2) + 2` where `k = |E|`, some basepoint block is a singleton! -/
private lemma exists_singleton_of_gt_quad {p : ℕ} [hp : Fact (Nat.Prime p)]
    (E : Subgroup (ZMod p)ˣ)
    (hgt : (Nat.card E - 1) * (Nat.card E - 2) + 2 < p) :
    ∃ s t z : ZMod p, z ≠ 0 ∧ z ≠ 1 ∧
      ∀ x : ZMod p, (x ∈ cosetOf E s ∧ x - 1 ∈ cosetOf E t) ↔ x = z := by
  classical
  let Efin : Finset (ZMod p)ˣ := Finset.univ.filter (· ∈ E)
  have hEcard : Efin.card = Nat.card E := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_subtype]
  let E1 : Finset (ZMod p)ˣ := Efin.erase 1
  have h1mem : (1 : (ZMod p)ˣ) ∈ Efin := Finset.mem_filter.mpr ⟨Finset.mem_univ _, E.one_mem⟩
  have hE1_card : E1.card = Nat.card E - 1 := by
    rw [Finset.card_erase_of_mem h1mem, hEcard]
  let pairs : Finset ((ZMod p)ˣ × (ZMod p)ˣ) := (E1 ×ˢ E1).filter fun q => q.1 ≠ q.2
  have hpairs_card : pairs.card = (Nat.card E - 1) * (Nat.card E - 2) := by
    have hdiag : (E1 ×ˢ E1).filter (fun q => q.1 = q.2) = E1.image (fun e => (e, e)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
      constructor
      · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl⟩
      · rintro ⟨e, he, h⟩; cases h; exact ⟨⟨he, he⟩, rfl⟩
    have hsum : pairs.card + ((E1 ×ˢ E1).filter fun q => q.1 = q.2).card = (E1 ×ˢ E1).card := by
      rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
      have : ∀ q ∈ E1 ×ˢ E1, (if q.1 ≠ q.2 then 1 else 0) + (if q.1 = q.2 then 1 else 0) = 1 := by
        intro q _; by_cases h : q.1 = q.2 <;> simp [h]
      rw [Finset.sum_congr rfl this]; simp
    rw [hdiag, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1),
        Finset.card_product, hE1_card] at hsum
    have hmul : (Nat.card E - 1) * (Nat.card E - 1) =
        (Nat.card E - 1) * (Nat.card E - 2) + (Nat.card E - 1) := by
      cases h : Nat.card E with
      | zero => simp
      | succ k =>
        cases k with
        | zero => simp
        | succ m =>
          simp only [Nat.add_sub_cancel, show m + 1 + 1 - 2 = m from by omega]; ring
    omega
  let bad : Finset (ZMod p) :=
    pairs.image fun q => (1 - (q.2 : ZMod p)) * ((q.1 : ZMod p) - (q.2 : ZMod p))⁻¹
  have hbad_card : bad.card ≤ (Nat.card E - 1) * (Nat.card E - 2) :=
    le_trans Finset.card_image_le (le_of_eq hpairs_card)
  let rest : Finset (ZMod p) := (Finset.univ.erase (0 : ZMod p)).erase 1
  have hrest_card : rest.card = p - 2 := by
    have h10 : (1 : ZMod p) ∈ Finset.univ.erase (0 : ZMod p) :=
      Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ _⟩
    rw [Finset.card_erase_of_mem h10, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, ZMod.card p]
    omega
  have hne : (rest \ bad).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    have hsub : rest ⊆ bad := Finset.sdiff_eq_empty_iff_subset.mp hemp
    have := Finset.card_le_card hsub
    omega
  obtain ⟨z, hz⟩ := hne
  simp only [Finset.mem_sdiff, rest, Finset.mem_erase, Finset.mem_univ, and_true] at hz
  obtain ⟨⟨hz1, hz0⟩, hz_notbad⟩ := hz
  refine ⟨z, z - 1, z, hz0, hz1, fun x => ?_⟩
  constructor
  · rintro ⟨hx1, hx2⟩
    by_contra hxz
    simp only [cosetOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    obtain ⟨e, he⟩ := hx1
    obtain ⟨e', he'⟩ := hx2
    have he_ne1 : e.val ≠ 1 := by
      intro h; apply hxz; rw [he, h]; simp
    have he'_ne1 : e'.val ≠ 1 := by
      intro h; apply hxz
      rw [h, Units.val_one, one_mul] at he'
      linear_combination he'
    have hdiff : ((e.val : ZMod p) - (e'.val : ZMod p)) * z = 1 - (e'.val : ZMod p) := by
      linear_combination -(he - he')
    have hee' : e.val ≠ e'.val := by
      intro h
      rw [h, sub_self, zero_mul] at hdiff
      apply he'_ne1; exact Units.ext (by rw [Units.val_one]; linear_combination hdiff)
    have hsub_ne : (e.val : ZMod p) - (e'.val : ZMod p) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hee' (Units.ext h))
    have hz_eq : z = (1 - (e'.val : ZMod p)) * ((e.val : ZMod p) - (e'.val : ZMod p))⁻¹ := by
      apply mul_right_cancel₀ hsub_ne
      rw [mul_assoc, inv_mul_cancel₀ hsub_ne, mul_one, mul_comm]
      exact hdiff
    apply hz_notbad
    refine Finset.mem_image.mpr ⟨(e.val, e'.val), ?_, hz_eq.symm⟩
    simp only [pairs, Finset.mem_filter, Finset.mem_product, E1, Efin, Finset.mem_erase,
      Finset.mem_univ, true_and]
    exact ⟨⟨⟨he_ne1, e.prop⟩, ⟨he'_ne1, e'.prop⟩⟩, hee'⟩
  · rintro rfl
    exact ⟨mem_cosetOf_self E x, mem_cosetOf_self E (x - 1)⟩

/-- Helper for finite certificates: identify `E` of order `k` as `{u : (ZMod p)ˣ | u ^ k = 1}`,
and express `x ∈ cosetOf E y` purely via `k`-th powers in `ZMod p`! -/
private lemma mem_cosetOf_iff_pow {p k : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (hk : Nat.card E = k) {y : ZMod p} (hy : y ≠ 0) (x : ZMod p) :
    x ∈ cosetOf E y ↔ x ≠ 0 ∧ x ^ k = y ^ k := by
  constructor
  · intro hx
    simp only [cosetOf, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨e, rfl⟩ := hx
    refine ⟨mul_ne_zero (Units.ne_zero e.val) hy, ?_⟩
    rw [mul_pow]
    have h1 := (subgroup_units_eq_roots E e.val).mp e.prop
    rw [hk] at h1
    have h2 : (e.val : ZMod p) ^ k = 1 := by
      rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    rw [h2, one_mul]
  · rintro ⟨hx0, hpow⟩
    let u : (ZMod p)ˣ := Units.mk0 (x * y⁻¹) (mul_ne_zero hx0 (inv_ne_zero hy))
    have huE : u ∈ E := by
      rw [subgroup_units_eq_roots E, hk]
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      show (x * y⁻¹) ^ k = 1
      rw [mul_pow, hpow, inv_pow, mul_inv_cancel₀ (pow_ne_zero k hy)]
    simp only [cosetOf, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨u, huE⟩, ?_⟩
    simp [u, mul_assoc, inv_mul_cancel₀ hy]

/-- Depth-2 certificate helper (C2): if `B = cosetOf E s ∩ (1 + cosetOf E t)` and
`D = cosetOf E s' ∩ (1 + cosetOf E t')`, and for every `x ∈ D`, the count
`v(x) = |{b ∈ B | x - b ∈ cosetOf E u}|` equals `m1` at `x = z` and `m2` (`m1 ≠ m2`) at all other `x ∈ D`,
then `Pi.single z 1 ∈ Rmod E 0 1`! -/
private lemma capture_cert_C2 {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (s t u s' t' z : ZMod p) (m1 m2 : ℤ) (hm : m1 ≠ m2)
    (hzD : z ∈ cosetOf E s' ∧ z - 1 ∈ cosetOf E t')
    (hcnt : ∀ x : ZMod p, x ∈ cosetOf E s' → x - 1 ∈ cosetOf E t' →
      ((Finset.univ.filter fun b : ZMod p =>
          b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t ∧ x - b ∈ cosetOf E u).card : ℤ) =
        if x = z then m1 else m2) :
    Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  let chiB : ZMod p → ℂ := fun x => if x ∈ cosetOf E s ∧ x - 1 ∈ cosetOf E t then 1 else 0
  let chiD : ZMod p → ℂ := fun x => if x ∈ cosetOf E s' ∧ x - 1 ∈ cosetOf E t' then 1 else 0
  have hchiB : chiB ∈ Rmod E 0 1 := block_ind_mem_Rmod E s t
  have hchiD : chiD ∈ Rmod E 0 1 := block_ind_mem_Rmod E s' t'
  have hv : (circulantAdj p (cosetOf E u)).mulVec chiB ∈ Rmod E 0 1 := rmod_mulVec_T E 0 1 u hchiB
  have hDv1 := rmod_diag_left E 0 1 s' hv
  have hDv := rmod_diag_right E 0 1 t' hDv1
  have hsub : (fun x => (if x - 0 ∈ cosetOf E s' then (1 : ℂ) else 0) *
      ((circulantAdj p (cosetOf E u)).mulVec chiB x) *
      (if x - 1 ∈ cosetOf E t' then 1 else 0)) - (m2 : ℂ) • chiD ∈ Rmod E 0 1 :=
    Submodule.sub_mem _ hDv (Submodule.smul_mem _ _ hchiD)
  have hscaled := Submodule.smul_mem (Rmod E 0 1) (((m1 : ℂ) - (m2 : ℂ))⁻¹) hsub
  convert hscaled using 1
  ext x
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_zero, chiD]
  have hval : (circulantAdj p (cosetOf E u)).mulVec chiB x =
      ((Finset.univ.filter fun b : ZMod p =>
        b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t ∧ x - b ∈ cosetOf E u).card : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, circulantAdj, Matrix.of_apply, chiB]
    have h1 : ∀ b : ZMod p,
        (if x - b ∈ cosetOf E u then (1 : ℂ) else 0) *
          (if b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t then 1 else 0) =
        if b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t ∧ x - b ∈ cosetOf E u then 1 else 0 := by
      intro b
      by_cases h1 : b ∈ cosetOf E s <;> by_cases h2 : b - 1 ∈ cosetOf E t <;>
        by_cases h3 : x - b ∈ cosetOf E u <;> simp [h1, h2, h3]
    simp_rw [h1, Finset.sum_boole]
  have hneC : (m1 : ℂ) - (m2 : ℂ) ≠ 0 := by
    intro h; apply hm; exact_mod_cast sub_eq_zero.mp h
  by_cases hxD : x ∈ cosetOf E s' ∧ x - 1 ∈ cosetOf E t'
  · have hc := hcnt x hxD.1 hxD.2
    have hcC : ((Finset.univ.filter fun b : ZMod p =>
        b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t ∧ x - b ∈ cosetOf E u).card : ℂ) =
        if x = z then (m1 : ℂ) else (m2 : ℂ) := by
      have : (((Finset.univ.filter fun b : ZMod p =>
          b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t ∧ x - b ∈ cosetOf E u).card : ℤ) : ℂ) =
        ((if x = z then m1 else m2 : ℤ) : ℂ) := congrArg Int.cast hc
      simpa [apply_ite] using this
    rw [hval, hcC]
    by_cases hxz : x = z
    · subst hxz; simp [hxD, inv_mul_cancel₀ hneC]
    · simp [hxD, hxz]
  · have hxz : x ≠ z := fun h => hxD (h ▸ hzD)
    rw [Pi.single_eq_of_ne hxz]
    by_cases hs' : x ∈ cosetOf E s' <;> by_cases ht' : x - 1 ∈ cosetOf E t' <;> simp_all

/-- Depth-3 certificate helper (C3) for `p = 17, k = 8`. -/
private lemma capture_cert_C3 {p : ℕ} [Fact (Nat.Prime p)] (E : Subgroup (ZMod p)ˣ)
    (s t u s' t' u' s'' t'' z : ZMod p) (m0 m1 m2 : ℤ) (hm : m1 ≠ m2)
    (hzD' : z ∈ cosetOf E s'' ∧ z - 1 ∈ cosetOf E t'')
    (hcnt : ∀ x : ZMod p, x ∈ cosetOf E s'' → x - 1 ∈ cosetOf E t'' →
      (∑ d ∈ Finset.univ.filter (fun d : ZMod p => d ∈ cosetOf E s' ∧ d - 1 ∈ cosetOf E t' ∧ x - d ∈ cosetOf E u'),
        (((Finset.univ.filter fun b : ZMod p =>
            b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t ∧ d - b ∈ cosetOf E u).card : ℤ) - m0)) =
        if x = z then m1 else m2) :
    Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  let chiB : ZMod p → ℂ := fun x => if x ∈ cosetOf E s ∧ x - 1 ∈ cosetOf E t then 1 else 0
  let chiD : ZMod p → ℂ := fun x => if x ∈ cosetOf E s' ∧ x - 1 ∈ cosetOf E t' then 1 else 0
  let chiD' : ZMod p → ℂ := fun x => if x ∈ cosetOf E s'' ∧ x - 1 ∈ cosetOf E t'' then 1 else 0
  have hv : (circulantAdj p (cosetOf E u)).mulVec chiB ∈ Rmod E 0 1 :=
    rmod_mulVec_T E 0 1 u (block_ind_mem_Rmod E s t)
  let v1 : ZMod p → ℂ := fun x =>
    (if x - 0 ∈ cosetOf E s' then (1 : ℂ) else 0) *
      ((circulantAdj p (cosetOf E u)).mulVec chiB x) *
      (if x - 1 ∈ cosetOf E t' then 1 else 0) - (m0 : ℂ) * chiD x
  have hv1 : v1 ∈ Rmod E 0 1 :=
    Submodule.sub_mem _ (rmod_diag_right E 0 1 t' (rmod_diag_left E 0 1 s' hv))
      (Submodule.smul_mem _ _ (block_ind_mem_Rmod E s' t'))
  have hv2 : (circulantAdj p (cosetOf E u')).mulVec v1 ∈ Rmod E 0 1 := rmod_mulVec_T E 0 1 u' hv1
  have hD'v2 := rmod_diag_right E 0 1 t'' (rmod_diag_left E 0 1 s'' hv2)
  have hsub := Submodule.sub_mem (Rmod E 0 1) hD'v2
    (Submodule.smul_mem _ (m2 : ℂ) (block_ind_mem_Rmod E s'' t''))
  have hscaled := Submodule.smul_mem (Rmod E 0 1) (((m1 : ℂ) - (m2 : ℂ))⁻¹) hsub
  convert hscaled using 1
  ext x
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, sub_zero]
  have hv1_eq : ∀ d : ZMod p, v1 d =
      if d ∈ cosetOf E s' ∧ d - 1 ∈ cosetOf E t' then
        (((Finset.univ.filter fun b : ZMod p =>
            b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t ∧ d - b ∈ cosetOf E u).card : ℤ) - m0 : ℤ)
      else 0 := by
    intro d
    simp only [v1, sub_zero, chiD]
    have hval : (circulantAdj p (cosetOf E u)).mulVec chiB d =
        ((Finset.univ.filter fun b : ZMod p =>
          b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t ∧ d - b ∈ cosetOf E u).card : ℂ) := by
      simp only [Matrix.mulVec, dotProduct, circulantAdj, Matrix.of_apply, chiB]
      have h1 : ∀ b : ZMod p,
          (if d - b ∈ cosetOf E u then (1 : ℂ) else 0) *
            (if b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t then 1 else 0) =
          if b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t ∧ d - b ∈ cosetOf E u then 1 else 0 := by
        intro b
        by_cases h1 : b ∈ cosetOf E s <;> by_cases h2 : b - 1 ∈ cosetOf E t <;>
          by_cases h3 : d - b ∈ cosetOf E u <;> simp [h1, h2, h3]
      simp_rw [h1, Finset.sum_boole]
    rw [hval]
    by_cases h1 : d ∈ cosetOf E s' <;> by_cases h2 : d - 1 ∈ cosetOf E t' <;> simp [h1, h2]
  have hv2_eq : (circulantAdj p (cosetOf E u')).mulVec v1 x =
      ((∑ d ∈ Finset.univ.filter (fun d : ZMod p =>
          d ∈ cosetOf E s' ∧ d - 1 ∈ cosetOf E t' ∧ x - d ∈ cosetOf E u'),
        (((Finset.univ.filter fun b : ZMod p =>
            b ∈ cosetOf E s ∧ b - 1 ∈ cosetOf E t ∧ d - b ∈ cosetOf E u).card : ℤ) - m0) : ℤ) : ℂ) := by
    simp only [Matrix.mulVec, dotProduct, circulantAdj, Matrix.of_apply, hv1_eq, Int.cast_sum]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases h1 : d ∈ cosetOf E s' <;> by_cases h2 : d - 1 ∈ cosetOf E t' <;>
      by_cases h3 : x - d ∈ cosetOf E u' <;> simp [h1, h2, h3]
  have hneC : (m1 : ℂ) - (m2 : ℂ) ≠ 0 := by
    intro h; apply hm; exact_mod_cast sub_eq_zero.mp h
  by_cases hxD' : x ∈ cosetOf E s'' ∧ x - 1 ∈ cosetOf E t''
  · have hc := hcnt x hxD'.1 hxD'.2
    rw [hv2_eq, hc]
    by_cases hxz : x = z
    · subst hxz; simp [hxD', inv_mul_cancel₀ hneC]
    · simp [hxD', hxz]
  · have hxz : x ≠ z := fun h => hxD' (h ▸ hzD')
    rw [Pi.single_eq_of_ne hxz]
    by_cases hs'' : x ∈ cosetOf E s'' <;> by_cases ht'' : x - 1 ∈ cosetOf E t'' <;> simp_all

-- Pure `ZMod p` decidable certificates for the 8 finite pairs (no `Fact`, no `⁻¹`!).
private lemma check_19_6 : ∀ x : ZMod 19,
    ((x ≠ 0 ∧ x ^ 6 = 2 ^ 6) ∧ (x - 1 ≠ 0 ∧ (x - 1) ^ 6 = 1 ^ 6)) ↔ x = 2 := by
  decide

private lemma check_41_8 : ∀ x : ZMod 41,
    ((x ≠ 0 ∧ x ^ 8 = 4 ^ 8) ∧ (x - 1 ≠ 0 ∧ (x - 1) ^ 8 = 8 ^ 8)) ↔ x = 12 := by
  decide

private lemma check_61_10 : ∀ x : ZMod 61,
    ((x ≠ 0 ∧ x ^ 10 = 8 ^ 10) ∧ (x - 1 ≠ 0 ∧ (x - 1) ^ 10 = 2 ^ 10)) ↔ x = 8 := by
  decide

private lemma check_71_10 : ∀ x : ZMod 71,
    ((x ≠ 0 ∧ x ^ 10 = 2 ^ 10) ∧ (x - 1 ≠ 0 ∧ (x - 1) ^ 10 = 1 ^ 10)) ↔ x = 2 := by
  decide

private lemma check_13_6 : ∀ x : ZMod 13,
    (x ≠ 0 ∧ x ^ 6 = 2 ^ 6) → (x - 1 ≠ 0 ∧ (x - 1) ^ 6 = 1 ^ 6) →
    ((Finset.univ.filter fun b : ZMod 13 =>
      (b ≠ 0 ∧ b ^ 6 = 1 ^ 6) ∧ (b - 1 ≠ 0 ∧ (b - 1) ^ 6 = 1 ^ 6) ∧
      (x - b ≠ 0 ∧ (x - b) ^ 6 = 1 ^ 6)).card : ℤ) = if x = 2 then 0 else 1 := by
  decide

private lemma check_31_10 : ∀ x : ZMod 31,
    (x ≠ 0 ∧ x ^ 10 = 3 ^ 10) → (x - 1 ≠ 0 ∧ (x - 1) ^ 10 = 5 ^ 10) →
    ((Finset.univ.filter fun b : ZMod 31 =>
      (b ≠ 0 ∧ b ^ 10 = 5 ^ 10) ∧ (b - 1 ≠ 0 ∧ (b - 1) ^ 10 = 1 ^ 10) ∧
      (x - b ≠ 0 ∧ (x - b) ^ 10 = 1 ^ 10)).card : ℤ) = if x = 6 then 1 else 0 := by
  decide

private lemma check_41_10 : ∀ x : ZMod 41,
    (x ≠ 0 ∧ x ^ 10 = 2 ^ 10) → (x - 1 ≠ 0 ∧ (x - 1) ^ 10 = 1 ^ 10) →
    ((Finset.univ.filter fun b : ZMod 41 =>
      (b ≠ 0 ∧ b ^ 10 = 3 ^ 10) ∧ (b - 1 ≠ 0 ∧ (b - 1) ^ 10 = 2 ^ 10) ∧
      (x - b ≠ 0 ∧ (x - b) ^ 10 = 1 ^ 10)).card : ℤ) = if x = 2 then 1 else 0 := by
  decide

private lemma check_17_8 : ∀ x : ZMod 17,
    (x ≠ 0 ∧ x ^ 8 = 1 ^ 8) → (x - 1 ≠ 0 ∧ (x - 1) ^ 8 = 1 ^ 8) →
    (∑ d ∈ Finset.univ.filter (fun d : ZMod 17 =>
        (d ≠ 0 ∧ d ^ 8 = 1 ^ 8) ∧ (d - 1 ≠ 0 ∧ (d - 1) ^ 8 = 3 ^ 8) ∧
        (x - d ≠ 0 ∧ (x - d) ^ 8 = 1 ^ 8)),
      (((Finset.univ.filter fun b : ZMod 17 =>
          (b ≠ 0 ∧ b ^ 8 = 1 ^ 8) ∧ (b - 1 ≠ 0 ∧ (b - 1) ^ 8 = 1 ^ 8) ∧
          (d - b ≠ 0 ∧ (d - b) ^ 8 = 1 ^ 8)).card : ℤ) - 1)) =
      if x = 16 then 2 else 1 := by
  decide

private lemma zmod_nat_ne {p : ℕ} [NeZero p] (a b : ℕ) (h : a % p ≠ b % p) :
    (a : ZMod p) ≠ (b : ZMod p) := fun he =>
  h (by have := congrArg ZMod.val he; simpa [ZMod.val_natCast] using this)

private lemma base_13_6 :
    ((2 : ZMod 13) ≠ 0 ∧ (2 : ZMod 13) ^ 6 = 2 ^ 6) ∧
    ((2 : ZMod 13) - 1 ≠ 0 ∧ ((2 : ZMod 13) - 1) ^ 6 = 1 ^ 6) := by decide

private lemma base_31_10 :
    ((6 : ZMod 31) ≠ 0 ∧ (6 : ZMod 31) ^ 10 = 3 ^ 10) ∧
    ((6 : ZMod 31) - 1 ≠ 0 ∧ ((6 : ZMod 31) - 1) ^ 10 = 5 ^ 10) := by decide

private lemma base_41_10 :
    ((2 : ZMod 41) ≠ 0 ∧ (2 : ZMod 41) ^ 10 = 2 ^ 10) ∧
    ((2 : ZMod 41) - 1 ≠ 0 ∧ ((2 : ZMod 41) - 1) ^ 10 = 1 ^ 10) := by decide

private lemma base_17_8 :
    ((16 : ZMod 17) ≠ 0 ∧ (16 : ZMod 17) ^ 8 = 1 ^ 8) ∧
    ((16 : ZMod 17) - 1 ≠ 0 ∧ ((16 : ZMod 17) - 1) ^ 8 = 1 ^ 8) := by decide

-- The 8 finite pairs!
private lemma cap_19_6 [Fact (Nat.Prime 19)] (E : Subgroup (ZMod 19)ˣ) (hk : Nat.card E = 6) :
    ∃ z : ZMod 19, z ≠ 0 ∧ z ≠ 1 ∧ Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  have h20 : (2 : ZMod 19) ≠ 0 := by simpa using zmod_nat_ne (p := 19) 2 0 (by decide)
  have h21 : (2 : ZMod 19) ≠ 1 := by simpa using zmod_nat_ne (p := 19) 2 1 (by decide)
  have h10 : (1 : ZMod 19) ≠ 0 := one_ne_zero
  refine ⟨2, h20, h21, capture_of_singleton_block E 2 1 2 fun x => ?_⟩
  rw [mem_cosetOf_iff_pow E hk h20, mem_cosetOf_iff_pow E hk h10]
  exact check_19_6 x

private lemma cap_41_8 [Fact (Nat.Prime 41)] (E : Subgroup (ZMod 41)ˣ) (hk : Nat.card E = 8) :
    ∃ z : ZMod 41, z ≠ 0 ∧ z ≠ 1 ∧ Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  have h120 : (12 : ZMod 41) ≠ 0 := by simpa using zmod_nat_ne (p := 41) 12 0 (by decide)
  have h121 : (12 : ZMod 41) ≠ 1 := by simpa using zmod_nat_ne (p := 41) 12 1 (by decide)
  have h40 : (4 : ZMod 41) ≠ 0 := by simpa using zmod_nat_ne (p := 41) 4 0 (by decide)
  have h80 : (8 : ZMod 41) ≠ 0 := by simpa using zmod_nat_ne (p := 41) 8 0 (by decide)
  refine ⟨12, h120, h121, capture_of_singleton_block E 4 8 12 fun x => ?_⟩
  rw [mem_cosetOf_iff_pow E hk h40, mem_cosetOf_iff_pow E hk h80]
  exact check_41_8 x

private lemma cap_61_10 [Fact (Nat.Prime 61)] (E : Subgroup (ZMod 61)ˣ) (hk : Nat.card E = 10) :
    ∃ z : ZMod 61, z ≠ 0 ∧ z ≠ 1 ∧ Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  have h80 : (8 : ZMod 61) ≠ 0 := by simpa using zmod_nat_ne (p := 61) 8 0 (by decide)
  have h81 : (8 : ZMod 61) ≠ 1 := by simpa using zmod_nat_ne (p := 61) 8 1 (by decide)
  have h20 : (2 : ZMod 61) ≠ 0 := by simpa using zmod_nat_ne (p := 61) 2 0 (by decide)
  refine ⟨8, h80, h81, capture_of_singleton_block E 8 2 8 fun x => ?_⟩
  rw [mem_cosetOf_iff_pow E hk h80, mem_cosetOf_iff_pow E hk h20]
  exact check_61_10 x

private lemma cap_71_10 [Fact (Nat.Prime 71)] (E : Subgroup (ZMod 71)ˣ) (hk : Nat.card E = 10) :
    ∃ z : ZMod 71, z ≠ 0 ∧ z ≠ 1 ∧ Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  have h20 : (2 : ZMod 71) ≠ 0 := by simpa using zmod_nat_ne (p := 71) 2 0 (by decide)
  have h21 : (2 : ZMod 71) ≠ 1 := by simpa using zmod_nat_ne (p := 71) 2 1 (by decide)
  have h10 : (1 : ZMod 71) ≠ 0 := one_ne_zero
  refine ⟨2, h20, h21, capture_of_singleton_block E 2 1 2 fun x => ?_⟩
  rw [mem_cosetOf_iff_pow E hk h20, mem_cosetOf_iff_pow E hk h10]
  exact check_71_10 x

private lemma cap_13_6 [Fact (Nat.Prime 13)] (E : Subgroup (ZMod 13)ˣ) (hk : Nat.card E = 6) :
    ∃ z : ZMod 13, z ≠ 0 ∧ z ≠ 1 ∧ Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  have h20 : (2 : ZMod 13) ≠ 0 := by simpa using zmod_nat_ne (p := 13) 2 0 (by decide)
  have h21 : (2 : ZMod 13) ≠ 1 := by simpa using zmod_nat_ne (p := 13) 2 1 (by decide)
  have h10 : (1 : ZMod 13) ≠ 0 := one_ne_zero
  refine ⟨2, h20, h21, capture_cert_C2 E 1 1 1 2 1 2 0 1 (by omega) ?_ ?_⟩
  · rw [mem_cosetOf_iff_pow E hk h20, mem_cosetOf_iff_pow E hk h10]; exact base_13_6
  · intro x hx1 hx2
    rw [mem_cosetOf_iff_pow E hk h20] at hx1
    rw [mem_cosetOf_iff_pow E hk h10] at hx2
    have hfilt : (Finset.univ.filter fun b : ZMod 13 =>
        b ∈ cosetOf E 1 ∧ b - 1 ∈ cosetOf E 1 ∧ x - b ∈ cosetOf E 1) =
      (Finset.univ.filter fun b : ZMod 13 =>
        (b ≠ 0 ∧ b ^ 6 = 1 ^ 6) ∧ (b - 1 ≠ 0 ∧ (b - 1) ^ 6 = 1 ^ 6) ∧
        (x - b ≠ 0 ∧ (x - b) ^ 6 = 1 ^ 6)) := by
      refine Finset.filter_congr fun b _ => ?_
      rw [mem_cosetOf_iff_pow E hk h10, mem_cosetOf_iff_pow E hk h10, mem_cosetOf_iff_pow E hk h10]
    rw [hfilt]
    exact check_13_6 x hx1 hx2

private lemma cap_31_10 [Fact (Nat.Prime 31)] (E : Subgroup (ZMod 31)ˣ) (hk : Nat.card E = 10) :
    ∃ z : ZMod 31, z ≠ 0 ∧ z ≠ 1 ∧ Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  have h60 : (6 : ZMod 31) ≠ 0 := by simpa using zmod_nat_ne (p := 31) 6 0 (by decide)
  have h61 : (6 : ZMod 31) ≠ 1 := by simpa using zmod_nat_ne (p := 31) 6 1 (by decide)
  have h10 : (1 : ZMod 31) ≠ 0 := one_ne_zero
  have h30 : (3 : ZMod 31) ≠ 0 := by simpa using zmod_nat_ne (p := 31) 3 0 (by decide)
  have h50 : (5 : ZMod 31) ≠ 0 := by simpa using zmod_nat_ne (p := 31) 5 0 (by decide)
  refine ⟨6, h60, h61, capture_cert_C2 E 5 1 1 3 5 6 1 0 (by omega) ?_ ?_⟩
  · rw [mem_cosetOf_iff_pow E hk h30, mem_cosetOf_iff_pow E hk h50]; exact base_31_10
  · intro x hx1 hx2
    rw [mem_cosetOf_iff_pow E hk h30] at hx1
    rw [mem_cosetOf_iff_pow E hk h50] at hx2
    have hfilt : (Finset.univ.filter fun b : ZMod 31 =>
        b ∈ cosetOf E 5 ∧ b - 1 ∈ cosetOf E 1 ∧ x - b ∈ cosetOf E 1) =
      (Finset.univ.filter fun b : ZMod 31 =>
        (b ≠ 0 ∧ b ^ 10 = 5 ^ 10) ∧ (b - 1 ≠ 0 ∧ (b - 1) ^ 10 = 1 ^ 10) ∧
        (x - b ≠ 0 ∧ (x - b) ^ 10 = 1 ^ 10)) := by
      refine Finset.filter_congr fun b _ => ?_
      rw [mem_cosetOf_iff_pow E hk h50, mem_cosetOf_iff_pow E hk h10, mem_cosetOf_iff_pow E hk h10]
    rw [hfilt]
    exact check_31_10 x hx1 hx2

private lemma cap_41_10 [Fact (Nat.Prime 41)] (E : Subgroup (ZMod 41)ˣ) (hk : Nat.card E = 10) :
    ∃ z : ZMod 41, z ≠ 0 ∧ z ≠ 1 ∧ Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  have h20 : (2 : ZMod 41) ≠ 0 := by simpa using zmod_nat_ne (p := 41) 2 0 (by decide)
  have h21 : (2 : ZMod 41) ≠ 1 := by simpa using zmod_nat_ne (p := 41) 2 1 (by decide)
  have h10 : (1 : ZMod 41) ≠ 0 := one_ne_zero
  have h30 : (3 : ZMod 41) ≠ 0 := by simpa using zmod_nat_ne (p := 41) 3 0 (by decide)
  refine ⟨2, h20, h21, capture_cert_C2 E 3 2 1 2 1 2 1 0 (by omega) ?_ ?_⟩
  · rw [mem_cosetOf_iff_pow E hk h20, mem_cosetOf_iff_pow E hk h10]; exact base_41_10
  · intro x hx1 hx2
    rw [mem_cosetOf_iff_pow E hk h20] at hx1
    rw [mem_cosetOf_iff_pow E hk h10] at hx2
    have hfilt : (Finset.univ.filter fun b : ZMod 41 =>
        b ∈ cosetOf E 3 ∧ b - 1 ∈ cosetOf E 2 ∧ x - b ∈ cosetOf E 1) =
      (Finset.univ.filter fun b : ZMod 41 =>
        (b ≠ 0 ∧ b ^ 10 = 3 ^ 10) ∧ (b - 1 ≠ 0 ∧ (b - 1) ^ 10 = 2 ^ 10) ∧
        (x - b ≠ 0 ∧ (x - b) ^ 10 = 1 ^ 10)) := by
      refine Finset.filter_congr fun b _ => ?_
      rw [mem_cosetOf_iff_pow E hk h30, mem_cosetOf_iff_pow E hk h20, mem_cosetOf_iff_pow E hk h10]
    rw [hfilt]
    exact check_41_10 x hx1 hx2

private lemma cap_17_8 [Fact (Nat.Prime 17)] (E : Subgroup (ZMod 17)ˣ) (hk : Nat.card E = 8) :
    ∃ z : ZMod 17, z ≠ 0 ∧ z ≠ 1 ∧ Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
  have h160 : (16 : ZMod 17) ≠ 0 := by simpa using zmod_nat_ne (p := 17) 16 0 (by decide)
  have h161 : (16 : ZMod 17) ≠ 1 := by simpa using zmod_nat_ne (p := 17) 16 1 (by decide)
  have h10 : (1 : ZMod 17) ≠ 0 := one_ne_zero
  have h30 : (3 : ZMod 17) ≠ 0 := by simpa using zmod_nat_ne (p := 17) 3 0 (by decide)
  refine ⟨16, h160, h161, capture_cert_C3 E 1 1 1 1 3 1 1 1 16 1 2 1 (by omega) ?_ ?_⟩
  · rw [mem_cosetOf_iff_pow E hk h10, mem_cosetOf_iff_pow E hk h10]; exact base_17_8
  · intro x hx1 hx2
    rw [mem_cosetOf_iff_pow E hk h10] at hx1 hx2
    have houter : (Finset.univ.filter fun d : ZMod 17 =>
        d ∈ cosetOf E 1 ∧ d - 1 ∈ cosetOf E 3 ∧ x - d ∈ cosetOf E 1) =
      (Finset.univ.filter fun d : ZMod 17 =>
        (d ≠ 0 ∧ d ^ 8 = 1 ^ 8) ∧ (d - 1 ≠ 0 ∧ (d - 1) ^ 8 = 3 ^ 8) ∧
        (x - d ≠ 0 ∧ (x - d) ^ 8 = 1 ^ 8)) := by
      refine Finset.filter_congr fun d _ => ?_
      rw [mem_cosetOf_iff_pow E hk h10, mem_cosetOf_iff_pow E hk h30, mem_cosetOf_iff_pow E hk h10]
    have hinner : ∀ d : ZMod 17, (Finset.univ.filter fun b : ZMod 17 =>
        b ∈ cosetOf E 1 ∧ b - 1 ∈ cosetOf E 1 ∧ d - b ∈ cosetOf E 1) =
      (Finset.univ.filter fun b : ZMod 17 =>
        (b ≠ 0 ∧ b ^ 8 = 1 ^ 8) ∧ (b - 1 ≠ 0 ∧ (b - 1) ^ 8 = 1 ^ 8) ∧
        (d - b ≠ 0 ∧ (d - b) ^ 8 = 1 ^ 8)) := fun d => by
      refine Finset.filter_congr fun b _ => ?_
      rw [mem_cosetOf_iff_pow E hk h10, mem_cosetOf_iff_pow E hk h10, mem_cosetOf_iff_pow E hk h10]
    rw [houter]
    simp_rw [hinner]
    exact check_17_8 x hx1 hx2

private lemma eight_pairs_enum (p k : ℕ) (hp : Nat.Prime p) (hp5 : 5 ≤ p)
    (heven : 2 ∣ k) (hk10 : k ≤ 10) (hk_pos : 0 < k) (hdvd : k ∣ p - 1) (hlt : k < p - 1)
    (hle : p ≤ (k - 1) * (k - 2) + 2) :
    (p = 13 ∧ k = 6) ∨ (p = 19 ∧ k = 6) ∨ (p = 17 ∧ k = 8) ∨ (p = 41 ∧ k = 8) ∨
    (p = 31 ∧ k = 10) ∨ (p = 41 ∧ k = 10) ∨ (p = 61 ∧ k = 10) ∨ (p = 71 ∧ k = 10) := by
  have hp74 : p ≤ 74 := by
    have : (k - 1) * (k - 2) ≤ 9 * 8 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hk_cases : k = 2 ∨ k = 4 ∨ k = 6 ∨ k = 8 ∨ k = 10 := by omega
  rcases hk_cases with rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · have : p ≤ 22 := by omega
    interval_cases p <;> simp_all
  · have : p ≤ 44 := by omega
    interval_cases p <;> simp_all <;> exact absurd hp (by decide)
  · interval_cases p <;> simp_all <;> exact absurd hp (by decide)

/-- Theorem 6.5 (classification for type ≤ 10): every nontrivial symmetric circulant graph of
prime order `p ≥ 5` and type `|E(S)| ≤ 10` has no quantum symmetry. -/
private lemma rigid_type_le_10 (p : ℕ) [hp : Fact (Nat.Prime p)] (hp5 : 5 ≤ p)
    (S : Finset (ZMod p)) (hSne : S.Nonempty) (hS0 : (0 : ZMod p) ∉ S)
    (hSprop : S ≠ Finset.univ.erase 0) (hSneg : ∀ x ∈ S, -x ∈ S)
    (hk10 : (multiplierGroup p S).card ≤ 10) :
    HasNoQuantumSymmetry (circulantAdj p S) := by
  classical
  let E : Subgroup (ZMod p)ˣ :=
    { carrier := {a | S.image (fun s => (a : ZMod p) * s) = S}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        show S.image (fun s => ((a * b : (ZMod p)ˣ) : ZMod p) * s) = S
        have : (fun s : ZMod p => ((a * b : (ZMod p)ˣ) : ZMod p) * s) =
            (fun s => (a : ZMod p) * s) ∘ (fun s => (b : ZMod p) * s) := by
          ext s; simp [mul_assoc]
        rw [this, ← Finset.image_image, hb, ha]
      inv_mem' := fun {a} ha => by
        show S.image (fun s => ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * s) = S
        have h1 : S.image (fun s => ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * s) =
            (S.image (fun s => (a : ZMod p) * s)).image (fun s => ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * s) := by
          rw [ha]
        rw [h1, Finset.image_image]
        have hid : ((fun s : ZMod p => ((a⁻¹ : (ZMod p)ˣ) : ZMod p) * s) ∘
            (fun s : ZMod p => (a : ZMod p) * s)) = id := by
          ext s; simp only [Function.comp_apply, id_eq]
          rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
        rw [hid, Finset.image_id] }
  have hE : ∀ a : (ZMod p)ˣ, a ∈ E ↔ S.image (fun s => (a : ZMod p) * s) = S := fun _ => Iff.rfl
  have hEneg : (-1 : (ZMod p)ˣ) ∈ E := by
    rw [hE]; ext x; simp only [Finset.mem_image, Units.val_neg, Units.val_one, neg_one_mul]
    exact ⟨fun ⟨s, hs, h⟩ => h ▸ hSneg s hs, fun hx => ⟨-x, hSneg x hx, neg_neg x⟩⟩
  have hEcard : Nat.card E = (multiplierGroup p S).card := by
    rw [Nat.card_eq_fintype_card]
    refine Fintype.card_congr
      { toFun := fun ⟨a, ha⟩ => ⟨(a : ZMod p), Finset.mem_filter.mpr ⟨Finset.mem_univ _, Units.ne_zero a, ha⟩⟩
        invFun := fun ⟨x, hx⟩ =>
          have hx' := (Finset.mem_filter.mp hx).2
          ⟨Units.mk0 x hx'.1, hx'.2⟩
        left_inv := fun ⟨_, _⟩ => Subtype.ext (Units.ext rfl)
        right_inv := fun ⟨_, _⟩ => rfl } |>.trans (Fintype.card_coe _)
  have hk_le : Nat.card E ≤ 10 := hEcard.symm ▸ hk10
  have hk_pos : 0 < Nat.card E := Nat.card_pos
  have heven : 2 ∣ Nat.card E := by
    let negSub : Subgroup E := Subgroup.zpowers (⟨-1, hEneg⟩ : E)
    have hord2 : orderOf (⟨-1, hEneg⟩ : E) = 2 := by
      have hne1 : (⟨-1, hEneg⟩ : E) ≠ 1 := by
        intro h
        have h1 : (-1 : ZMod p) = 1 := congrArg (fun u : E => (u.val : ZMod p)) h
        have h2 : (2 : ZMod p) = 0 := by linear_combination -h1
        have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
        have := Nat.le_of_dvd (by omega) hd
        omega
      have hsq : (⟨-1, hEneg⟩ : E) ^ 2 = 1 := by ext; simp
      exact orderOf_eq_prime hsq hne1
    have hdvd := orderOf_dvd_natCard (⟨-1, hEneg⟩ : E)
    rwa [hord2] at hdvd
  have hUcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdvd_pm1 : Nat.card E ∣ p - 1 := by
    rw [← hUcard]
    exact Subgroup.card_subgroup_dvd_card E
  have hlt_pm1 : Nat.card E < p - 1 := by
    have hle := Nat.le_of_dvd (by omega) hdvd_pm1
    rcases eq_or_lt_of_le hle with heq | hlt
    · exfalso
      -- If `|E| = p - 1`, then `E = ⊤`, so `S` is stable under all of `(ZMod p)ˣ`, forcing `S = univ.erase 0`!
      have htop : ∀ a : (ZMod p)ˣ, a ∈ E := by
        have hEq : E = ⊤ := Subgroup.eq_top_of_card_eq E (by rw [heq, hUcard])
        intro a; rw [hEq]; trivial
      apply hSprop
      ext x
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hx hx0; exact hS0 (hx0 ▸ hx)
      · intro hx0
        obtain ⟨s, hs⟩ := hSne
        have hs0 : s ≠ 0 := fun h => hS0 (h ▸ hs)
        let a : (ZMod p)ˣ := Units.mk0 (x * s⁻¹) (mul_ne_zero hx0 (inv_ne_zero hs0))
        have ha := (hE a).mp (htop a)
        rw [← ha]
        refine Finset.mem_image.mpr ⟨s, hs, ?_⟩
        simp [a, mul_assoc, inv_mul_cancel₀ hs0]
    · exact hlt
  by_cases hgt : (Nat.card E - 1) * (Nat.card E - 2) + 2 < p
  · obtain ⟨s, t, z, hz0, hz1, hblk⟩ := exists_singleton_of_gt_quad E hgt
    exact rigid_of_capture hp5 hSne hS0 hSneg E hE hEneg hz0 hz1
      (capture_of_singleton_block E s t z hblk)
  · push Not at hgt
    have h8 := eight_pairs_enum p (Nat.card E) hp.out hp5 heven hk_le hk_pos hdvd_pm1 hlt_pm1 hgt
    have hcap_exists : ∃ z : ZMod p, z ≠ 0 ∧ z ≠ 1 ∧ Pi.single z (1 : ℂ) ∈ Rmod E 0 1 := by
      rcases h8 with ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ |
        ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩ | ⟨rfl, hk⟩
      · exact cap_13_6 E hk
      · exact cap_19_6 E hk
      · exact cap_17_8 E hk
      · exact cap_41_8 E hk
      · exact cap_31_10 E hk
      · exact cap_41_10 E hk
      · exact cap_61_10 E hk
      · exact cap_71_10 E hk
    obtain ⟨z, hz0, hz1, hcap⟩ := hcap_exists
    exact rigid_of_capture hp5 hSne hS0 hSneg E hE hEneg hz0 hz1 hcap

theorem main_proof : type_of% @OMA.S_arxiv_2609_00462.main := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : connC31.Nonempty := by decide
    have h2 : (0 : ZMod 31) ∉ connC31 := by decide
    have h3 : connC31 ≠ Finset.univ.erase 0 := by decide
    have h4 : ∀ x ∈ connC31, -x ∈ connC31 := by decide
    have h5 : (multiplierGroup 31 connC31).card ≤ 10 := by decide
    have : Fact (Nat.Prime 31) := ⟨by decide⟩
    exact rigid_type_le_10 31 (by omega) connC31 h1 h2 h3 h4 h5
  · have h1 : connC41.Nonempty := by decide
    have h2 : (0 : ZMod 41) ∉ connC41 := by decide
    have h3 : connC41 ≠ Finset.univ.erase 0 := by decide
    have h4 : ∀ x ∈ connC41, -x ∈ connC41 := by decide
    have h5 : (multiplierGroup 41 connC41).card ≤ 10 := by decide
    have : Fact (Nat.Prime 41) := ⟨by decide⟩
    exact rigid_type_le_10 41 (by omega) connC41 h1 h2 h3 h4 h5
  · intro p _ hp5 S hSne hS0 hSprop hSneg hk10
    exact rigid_type_le_10 p hp5 S hSne hS0 hSprop hSneg hk10

end OMA.P_arxiv_2609_00462

theorem OMA.solution : type_of% @OMA.S_arxiv_2609_00462.main :=
  OMA.P_arxiv_2609_00462.main_proof
