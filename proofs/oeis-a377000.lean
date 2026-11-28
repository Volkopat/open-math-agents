import OMAStatements.S_oeis_a377000

open OMA.S_oeis_a377000

namespace A377000Proof

open Matrix

def adj {n : ℕ} (a b : Fin n) : Prop := (a : ℕ) + 1 = b ∨ (b : ℕ) + 1 = a

instance {n : ℕ} (a b : Fin n) : Decidable (adj a b) := by unfold adj; infer_instance

def Chain {n k : ℕ} (x : Fin (k + 1) → Fin n) : Prop := ∀ i : Fin k, adj (x i.castSucc) (x i.succ)

instance {n k : ℕ} (x : Fin (k + 1) → Fin n) : Decidable (Chain x) := by
  unfold Chain; infer_instance

theorem chain_cons {n k : ℕ} (a : Fin n) (y : Fin (k + 1) → Fin n) :
    Chain (Fin.cons a y : Fin (k + 2) → Fin n) ↔ adj a (y 0) ∧ Chain y := by
  unfold Chain
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]

theorem esth_iff {n k : ℕ} (x : Fin (k + 1) → Fin n) :
    IsEsthetic x ↔ (x 0 : ℕ) ≠ 0 ∧ Chain x := by
  unfold IsEsthetic Chain adj
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨?_, fun i => ?_⟩
    · have := h0 (Nat.succ_pos k)
      rwa [show (⟨0, Nat.succ_pos k⟩ : Fin (k + 1)) = 0 from Fin.ext (by simp)] at this
    · have hh : (i.castSucc : ℕ) + 1 < k + 1 := by simp
      have e : (⟨(i.castSucc : ℕ) + 1, hh⟩ : Fin (k + 1)) = i.succ := Fin.ext (by simp)
      have := h1 i.castSucc hh
      rw [e] at this
      exact this
  · rintro ⟨h0, h1⟩
    refine ⟨fun h => ?_, fun i h => ?_⟩
    · rwa [show (⟨0, h⟩ : Fin (k + 1)) = 0 from Fin.ext (by simp)]
    · have hi : (i : ℕ) < k := by omega
      have := h1 ⟨i, hi⟩
      have e1 : (⟨i, hi⟩ : Fin k).castSucc = i := Fin.ext (by simp)
      have e2 : (⟨i, hi⟩ : Fin k).succ = ⟨(i : ℕ) + 1, h⟩ := Fin.ext (by simp)
      rw [e1, e2] at this
      exact this

def P (n k : ℕ) (d : Fin n) : ℕ :=
  (Finset.univ.filter fun x : Fin (k + 1) → Fin n => x 0 = d ∧ Chain x).card

def s : (n : ℕ) → ℕ → Fin n → ℕ
  | _, 0, _ => 1
  | n, k + 1, d => ∑ e : Fin n, if adj d e then s n k e else 0

theorem fiber {n k : ℕ} (q : Fin n → Prop) [DecidablePred q] :
    (∑ y : Fin (k + 1) → Fin n, if q (y 0) ∧ Chain y then 1 else 0) =
      ∑ e : Fin n, if q e then P n k e else 0 := by
  have h1 : ∀ e : Fin n, (if q e then P n k e else 0) =
      ∑ y : Fin (k + 1) → Fin n, if y 0 = e ∧ q e ∧ Chain y then 1 else 0 := by
    intro e
    rw [P, Finset.card_filter]
    by_cases he : q e
    · simp [he]
    · simp [he]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (y 0)]
  · simp
  · intro e _ he
    rw [if_neg]
    rintro ⟨h, -⟩
    exact he h.symm
  · simp

theorem P_zero {n : ℕ} (d : Fin n) : P n 0 d = 1 := by
  rw [P, Finset.card_eq_one]
  refine ⟨fun _ => d, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    funext i
    rw [show i = 0 from Fin.ext (by have := i.isLt; simp), h]
  · rintro rfl
    exact ⟨rfl, fun i => i.elim0⟩

theorem P_succ (n k : ℕ) (d : Fin n) :
    P n (k + 1) d = ∑ e : Fin n, if adj d e then P n k e else 0 := by
  rw [← fiber, P, Finset.card_filter, ← (Fin.consEquiv fun _ => Fin n).sum_comp,
    Fintype.sum_prod_type]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, chain_cons]
  rw [Finset.sum_eq_single d]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun y _ => by rw [if_neg]; rintro ⟨h, -⟩; exact ha h
  · simp

theorem P_eq (n k : ℕ) : ∀ d, P n k d = s n k d := by
  induction k with
  | zero => intro d; rw [P_zero]; rfl
  | succ k ih =>
    intro d
    rw [P_succ, s]
    exact Finset.sum_congr rfl fun e _ => by rw [ih]

theorem T_s (n m : ℕ) : (T n (m + 1) : ℤ) = ∑ d : Fin n, if (d : ℕ) ≠ 0 then (s n m d : ℤ) else 0 := by
  have h : T n (m + 1) = ∑ d : Fin n, if (d : ℕ) ≠ 0 then P n m d else 0 := by
    rw [← fiber, T, Finset.card_filter]
    exact Finset.sum_congr rfl fun x _ => if_congr (esth_iff x) rfl rfl
  rw [h]
  push_cast [Nat.cast_sum, Nat.cast_ite]
  exact Finset.sum_congr rfl fun d _ => by rw [P_eq]

-- Rows with a listed recurrence: a per-digit identity spreads to all lengths.
def Wr (c : List ℤ) (n k : ℕ) (d : Fin n) : ℤ :=
  ∑ i ∈ Finset.range c.length, c.getD i 0 * (s n (k + i) d : ℤ)

theorem Wr_succ (c : List ℤ) (n k : ℕ) (d : Fin n) :
    Wr c n (k + 1) d = ∑ e : Fin n, if adj d e then Wr c n k e else 0 := by
  unfold Wr
  have h : ∀ i, (s n (k + 1 + i) d : ℤ) = ∑ e : Fin n, if adj d e then (s n (k + i) e : ℤ) else 0 := by
    intro i
    rw [show k + 1 + i = (k + i) + 1 by ring, s]
    push_cast [Nat.cast_sum, Nat.cast_ite]
    rfl
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs <;> simp

theorem Wr_zero (c : List ℤ) (n k0 : ℕ) (h : ∀ d, Wr c n k0 d = 0) :
    ∀ k d, Wr c n (k0 + k) d = 0 := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih =>
    intro d
    rw [show k0 + (k + 1) = (k0 + k) + 1 by ring, Wr_succ]
    exact Finset.sum_eq_zero fun e _ => by split_ifs <;> simp [ih]

theorem rowrec (c : List ℤ) (n k0 : ℕ) (h : ∀ d, Wr c n k0 d = 0) (k : ℕ) :
    ∑ i ∈ Finset.range c.length, c.getD i 0 * (T n (k0 + k + 1 + i) : ℤ) = 0 := by
  have e : ∀ i, (T n (k0 + k + 1 + i) : ℤ) =
      ∑ d : Fin n, if (d : ℕ) ≠ 0 then (s n (k0 + k + i) d : ℤ) else 0 := by
    intro i
    rw [show k0 + k + 1 + i = (k0 + k + i) + 1 by ring, T_s]
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun d _ => ?_
  have := Wr_zero c n k0 h k d
  unfold Wr at this
  split_ifs
  · exact this
  · simp

-- The general statement, from the Cayley-Hamilton theorem for the adjacency matrix.
def A (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j => if adj i j then 1 else 0

theorem s_mat (n k : ℕ) : ∀ d, (s n k d : ℤ) = ((A n ^ k) *ᵥ (fun _ => (1 : ℤ))) d := by
  induction k with
  | zero => intro d; simp [s]
  | succ k ih =>
    intro d
    rw [pow_succ', ← Matrix.mulVec_mulVec, s]
    simp only [Matrix.mulVec, dotProduct] at ih ⊢
    push_cast [Nat.cast_sum, Nat.cast_ite]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [ih e]
    simp only [A]
    split_ifs <;> simp

theorem general (n : ℕ) : ∃ d : ℕ, ∃ c : ℕ → ℤ, ∀ k : ℕ, 1 ≤ k →
    (T n (k + d) : ℤ) = ∑ i ∈ Finset.range d, c i * T n (k + i) := by
  refine ⟨n, fun i => -(A n).charpoly.coeff i, fun k hk => ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hp := Matrix.aeval_self_charpoly (A n)
  rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at hp
  have hlead : (A n).charpoly.coeff n = 1 := by
    have := Matrix.charpoly_monic (A n)
    rw [Polynomial.Monic, Polynomial.leadingCoeff, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin] at this
    exact this
  set u : Fin n → ℤ := fun d => if (d : ℕ) ≠ 0 then 1 else 0 with hu
  have hT : ∀ j, (T n (m + 1 + j) : ℤ) = ∑ d, u d * ((A n ^ (m + j)) *ᵥ fun _ => (1 : ℤ)) d := by
    intro j
    rw [show m + 1 + j = (m + j) + 1 by ring, T_s]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [s_mat, hu]
    by_cases hd : (d : ℕ) = 0 <;> simp [hd]
  have hv := congrArg (fun M => ∑ d, u d * ((A n ^ m * M) *ᵥ fun _ => (1 : ℤ)) d) hp
  simp only [Matrix.sum_mulVec, Finset.sum_apply, Finset.mul_sum,
    Matrix.zero_mulVec, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hv
  rw [Finset.sum_comm] at hv
  have hv' : ∑ i ∈ Finset.range (n + 1), (A n).charpoly.coeff i * (T n (m + 1 + i) : ℤ) = 0 := by
    rw [← hv]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mulVec, ← pow_add, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_range_succ, hlead] at hv'
  simp only [neg_mul, Finset.sum_neg_distrib]
  linarith

theorem T9_5 : (T 9 5 : ℤ) = 5 * T 9 3 - 5 * T 9 1 := by
  rw [T_s, T_s, T_s]
  decide +kernel

end A377000Proof

open A377000Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a377000.main := by
  refine ⟨fun n _ => general n, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 4 := ⟨k - 4, by omega⟩
    have h := rowrec [1, -2, -1, 1] 6 0 (by decide +kernel) m
    simp [Finset.sum_range_succ] at h
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega]
    ring_nf at h ⊢
    linarith
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
    have h := rowrec [2, 0, -4, 0, 1] 7 0 (by decide +kernel) m
    simp [Finset.sum_range_succ] at h
    rw [show m + 5 - 2 = m + 3 by omega, show m + 5 - 4 = m + 1 by omega]
    ring_nf at h ⊢
    linarith
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 5 := ⟨k - 5, by omega⟩
    have h := rowrec [1, 2, -3, -1, 1] 8 0 (by decide +kernel) m
    simp [Finset.sum_range_succ] at h
    rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
      show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega]
    ring_nf at h ⊢
    linarith
  · intro k hk
    rcases (by omega : k = 5 ∨ 6 ≤ k) with h5 | h6
    · subst h5
      exact T9_5
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
      have h := rowrec [5, 0, -5, 0, 1] 9 1 (by decide +kernel) m
      simp [Finset.sum_range_succ] at h
      rw [show m + 6 - 2 = m + 4 by omega, show m + 6 - 4 = m + 2 by omega]
      ring_nf at h ⊢
      linarith
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 6 := ⟨k - 6, by omega⟩
    have h := rowrec [-1, 3, 3, -4, -1, 1] 10 0 (by decide +kernel) m
    simp [Finset.sum_range_succ] at h
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega]
    ring_nf at h ⊢
    linarith
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
    have h := rowrec [-2, 0, 9, 0, -6, 0, 1] 11 0 (by decide +kernel) m
    simp [Finset.sum_range_succ] at h
    rw [show m + 7 - 2 = m + 5 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 6 = m + 1 by omega]
    ring_nf at h ⊢
    linarith
  · intro k hk
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 7 := ⟨k - 7, by omega⟩
    have h := rowrec [-1, -3, 6, 4, -5, -1, 1] 12 0 (by decide +kernel) m
    simp [Finset.sum_range_succ] at h
    rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
      show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
      show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega]
    ring_nf at h ⊢
    linarith

