import OMAStatements.S_oeis_a366362

-- Problem: A366362: Triangle read by rows: T(n,k) = Sum_{y=1..n} Sum_{x=1..n} [GCD(f(x,y), n) = k], where f(x,y) = x^3 - x^2 - y^2 - y.
-- Upstream: formal-conjectures statements/oeis-a366362.lean:0 (declaration OMA.S_oeis_a366362.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: Int.gcd (f x y) n = n iff n divides f x y = -(y^2 + y - (x^3 - x^2)). Then swap the
-- two sums and move each index from 1..n to 0..n-1: the summand has the same value at n and at 0,
-- because the polynomial changes by a multiple of n.

open OMA.S_oeis_a366362 in
theorem OMA.solution : type_of% @OMA.S_oeis_a366362.main := by
  have shift : ∀ (n : ℕ) (h : ℕ → ℕ), h n = h 0 →
      ∑ x ∈ Finset.Icc 1 n, h x = ∑ x ∈ Finset.range n, h x := by
    intro n h hp
    have bridge : ∀ m : ℕ, ∑ x ∈ Finset.Icc 1 m, h x = ∑ x ∈ Finset.range m, h (x + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih, Finset.sum_range_succ]
    rw [bridge n]
    have h3 := (Finset.sum_range_succ' h n).symm.trans (Finset.sum_range_succ h n)
    rw [hp] at h3
    exact Nat.add_right_cancel h3
  intro n _
  have hdiv : ∀ z : ℤ, Int.gcd z (n : ℤ) = n ↔ (n : ℤ) ∣ z := by
    intro z
    have h : Int.gcd z (n : ℤ) = (n : ℤ).natAbs ↔ (n : ℤ) ∣ z :=
      Int.gcd_eq_natAbs_right_iff_dvd
    rw [Int.natAbs_natCast] at h
    exact h
  have per : ∀ A B C : ℤ, A = B + (n : ℤ) * C → ((n : ℤ) ∣ A ↔ (n : ℤ) ∣ B) := by
    intro A B C h
    rw [h]
    exact dvd_add_left (dvd_mul_right _ _)
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℕ → ℕ, ∀ x y : ℕ, G x y =
      if (n : ℤ) ∣ ((y : ℤ) ^ 2 + (y : ℤ) - ((x : ℤ) ^ 3 - (x : ℤ) ^ 2)) then 1 else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have e1 : T n n = ∑ y ∈ Finset.Icc 1 n, ∑ x ∈ Finset.Icc 1 n, G x y := by
    unfold T
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    have hneg : f (x : ℤ) (y : ℤ) =
        -((y : ℤ) ^ 2 + (y : ℤ) - ((x : ℤ) ^ 3 - (x : ℤ) ^ 2)) := by
      unfold f
      ring
    rw [hG, hneg]
    refine if_congr ?_ rfl rfl
    rw [hdiv, dvd_neg]
  have e2 : ∑ y ∈ Finset.Icc 1 n, ∑ x ∈ Finset.Icc 1 n, G x y =
      ∑ x ∈ Finset.Icc 1 n, ∑ y ∈ Finset.Icc 1 n, G x y := Finset.sum_comm
  have e3 : ∀ x : ℕ, ∑ y ∈ Finset.Icc 1 n, G x y = ∑ y ∈ Finset.range n, G x y := by
    intro x
    apply shift n (fun y => G x y)
    show G x n = G x 0
    rw [hG, hG]
    refine if_congr ?_ rfl rfl
    exact per _ _ ((n : ℤ) + 1) (by push_cast; ring)
  have e3' : ∑ x ∈ Finset.Icc 1 n, ∑ y ∈ Finset.Icc 1 n, G x y =
      ∑ x ∈ Finset.Icc 1 n, ∑ y ∈ Finset.range n, G x y :=
    Finset.sum_congr rfl (fun x _ => e3 x)
  have e4 : ∑ x ∈ Finset.Icc 1 n, ∑ y ∈ Finset.range n, G x y =
      ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n, G x y := by
    apply shift n (fun x => ∑ y ∈ Finset.range n, G x y)
    show ∑ y ∈ Finset.range n, G n y = ∑ y ∈ Finset.range n, G 0 y
    apply Finset.sum_congr rfl
    intro y _
    rw [hG, hG]
    refine if_congr ?_ rfl rfl
    exact per _ _ ((n : ℤ) - (n : ℤ) ^ 2) (by push_cast; ring)
  rw [e1, e2, e3', e4]
  unfold a060457
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [hG]
