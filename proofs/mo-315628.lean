import OMAStatements.S_mo_315628
import Mathlib

-- Problem: mo-315628, are exchangeable Bernoulli variables with at most m < n successes
-- always pairwise negatively correlated?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No. For n = 3 and m = 2 put mass 1/2 on (0,0,0) and mass 1/6 on each of the three vectors
-- with exactly two successes. Then E[X_i X_j] = 1/6 while E[X_i] E[X_j] = 1/9.

open OMA.S_mo_315628 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_315628.main) := by
  intro h
  have hsum : ∀ F : (Fin 3 → Bool) → ℝ, ∑ x, F x =
      F ![true, true, true] + F ![true, true, false] + F ![true, false, true] +
        F ![true, false, false] + F ![false, true, true] + F ![false, true, false] +
        F ![false, false, true] + F ![false, false, false] := by
    intro F
    rw [← Equiv.sum_comp
      (⟨fun p => ![p.1, p.2.1, p.2.2], fun x => (x 0, x 1, x 2),
        fun p => by rcases p with ⟨a, b, c⟩; rfl,
        fun x => by ext i; fin_cases i <;> rfl⟩ : (Bool × Bool × Bool) ≃ (Fin 3 → Bool)) F]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Equiv.coe_fn_mk]
    ring
  have hperm : ∀ (x : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)),
      successes (x ∘ σ) = successes x := by
    intro x σ
    unfold successes
    exact Equiv.sum_comp σ (fun i => if x i then 1 else 0)
  have hs : ∀ a b c : Bool, successes ![a, b, c] =
      (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) := by
    intro a b c
    unfold successes
    rw [Fin.sum_univ_three]
    rfl
  let w : (Fin 3 → Bool) → ℝ := fun x =>
    if successes x = 0 then 1 / 2 else if successes x = 2 then 1 / 6 else 0
  have hnonneg : ∀ x, 0 ≤ w x := by
    intro x
    simp only [w]
    split_ifs <;> norm_num
  have htotal : ∑ x, w x = 1 := by
    rw [hsum]
    norm_num [w, hs]
  have hsymm : ∀ (x : Fin 3 → Bool) (σ : Equiv.Perm (Fin 3)), w (x ∘ σ) = w x := by
    intro x σ
    simp only [w, hperm]
  have hsupp : ∀ x, 0 < w x → successes x ≤ 2 := by
    intro x hx
    by_contra hcon
    have h1 : successes x ≠ 0 := by omega
    have h2 : successes x ≠ 2 := by omega
    simp [w, h1, h2] at hx
  have hmain := h 3 2 (by norm_num) w hnonneg htotal hsymm hsupp 0 1 (by decide)
  unfold meanProduct meanBit at hmain
  simp only [hsum] at hmain
  norm_num [w, hs] at hmain
