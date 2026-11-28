import OMAStatements.S_oeis_a187772

open OMA.S_oeis_a187772
open scoped Matrix

private def Q (k : ℕ) : Matrix (Fin 2) (Fin 2) (ZMod k) := !![0, 1; 1, 1]

private theorem q_unit (k : ℕ) : IsUnit (Q k) := by
  let B : Matrix (Fin 2) (Fin 2) (ZMod k) := !![-1, 1; 1, 0]
  refine ⟨⟨Q k, B, ?_, ?_⟩, rfl⟩ <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Q, B, Matrix.mul_apply, Fin.sum_univ_two]

private theorem q_power (k n : ℕ) :
    Q k ^ (n+1) = !![(Nat.fib n : ZMod k), (Nat.fib (n+1) : ZMod k);
      (Nat.fib (n+1) : ZMod k), (Nat.fib (n+2) : ZMod k)] := by
  induction n with
  | zero => simp [Q, Nat.fib_add_two]
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Q, Matrix.mul_apply, Fin.sum_univ_two, Nat.fib_add_two]

private theorem q_period (k p : ℕ) (hp : 0 < p) :
    Q k ^ p = 1 ↔ ∀ r : ℕ, Nat.fib (r + p) % k = Nat.fib r % k := by
  have equiv (r : ℕ) : Nat.fib (r+p) % k = Nat.fib r % k ↔
      (Nat.fib (r+p) : ZMod k) = (Nat.fib r : ZMod k) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).symm
  simp_rw [equiv]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hp)
  rw [q_power]
  constructor
  · intro h r
    have h₀ := congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod k) => A 0 1) h
    have h₁ := congrArg (fun A : Matrix (Fin 2) (Fin 2) (ZMod k) => A 1 1) h
    simp at h₀ h₁
    induction r using Nat.twoStepInduction with
    | zero => simpa using h₀
    | one => simpa [Nat.add_comm 1] using h₁
    | more r ihr ihr₁ =>
      rw [show r+2+(n+1)=(r+(n+1))+2 by omega, Nat.fib_add_two, Nat.fib_add_two,
        Nat.cast_add, Nat.cast_add, show r+(n+1)+1 = r+1+(n+1) by omega, ihr, ihr₁]
  · intro h
    have h₀ : (Nat.fib (n+1) : ZMod k) = 0 := by simpa using h 0
    have h₁ : (Nat.fib (n+2) : ZMod k) = 1 := by simpa [Nat.add_comm 1] using h 1
    have h₂ : (Nat.fib n : ZMod k) = 1 := by
      rw [Nat.fib_add_two, Nat.cast_add, h₀, add_zero] at h₁
      exact h₁
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h₀, h₁, h₂]

private theorem danzer_order (k : ℕ) (hp : 0 < orderOf (Q k)) :
    a187772 2 k = orderOf (Q k) := by
  have h₀ : matMod k (danzerMatrix 2 0) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matMod, danzerMatrix, chebSMat]
  have h₁ : matMod k (danzerMatrix 2 1) = Q k := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matMod, danzerMatrix, chebSMat, danzerBase, Q]
  unfold a187772 a220555
  simp only [Nat.reduceSubDiff, one_mul]
  have hu : (Finset.univ : Finset (Fin 2)) = {0, 1} := by decide
  rw [hu, Finset.sup_insert, Finset.sup_singleton]
  change orderOf (matMod k (danzerMatrix 2 0)) ⊔ orderOf (matMod k (danzerMatrix 2 1)) = _
  rw [h₀, h₁, orderOf_one]
  exact sup_eq_right.mpr (Nat.succ_le_iff.mpr hp)

theorem OMA.solution : type_of% @OMA.S_oeis_a187772.main := by
  intro k hk
  let : NeZero k := ⟨by omega⟩
  have hp : 0 < orderOf (Q k) := (q_unit k).isOfFinOrder.orderOf_pos
  rw [danzer_order k hp]
  let S := {p : ℕ | 0 < p ∧ ∀ r : ℕ, Nat.fib (r+p) % k = Nat.fib r % k}
  have hm : orderOf (Q k) ∈ S := ⟨hp, (q_period k _ hp).mp (pow_orderOf_eq_one _)⟩
  have hs := Nat.sInf_mem (show S.Nonempty from ⟨_, hm⟩)
  change orderOf (Q k) = sInf S
  exact le_antisymm (orderOf_le_of_pow_eq_one hs.1 ((q_period k _ hs.1).mpr hs.2))
    (Nat.sInf_le hm)