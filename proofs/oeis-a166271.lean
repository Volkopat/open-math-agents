import OMAStatements.S_oeis_a166271
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

namespace OMA.P_oeis_a166271

open OMA.S_oeis_a166271

private def Jsum (n k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k + 1), jacobiSym (i : ℤ) (12 * n + 7)

private lemma jacobi_neg_sub (n : ℕ) (x : ℤ) :
    jacobiSym ((12 * n + 7 : ℕ) - x) (12 * n + 7) = -jacobiSym x (12 * n + 7) := by
  have hodd : Odd (12 * n + 7) := ⟨6 * n + 3, by omega⟩
  have hneg : jacobiSym (-1) (12 * n + 7) = -1 := by
    rw [jacobiSym.at_neg_one hodd]
    have hc : ((12 * n + 7 : ℕ) : ZMod 4) = 3 := by
      have : 12 * n + 7 = 4 * (3 * n + 1) + 3 := by omega
      rw [this]; push_cast; rw [show (4 : ZMod 4) = 0 by decide]; simp
    rw [hc]; decide
  have h1 : (((12 * n + 7 : ℕ) : ℤ) - x) % ((12 * n + 7 : ℕ) : ℤ) = (-x) % ((12 * n + 7 : ℕ) : ℤ) := by
    rw [show ((12 * n + 7 : ℕ) : ℤ) - x = -x + ((12 * n + 7 : ℕ) : ℤ) by ring, Int.add_emod_right]
  rw [jacobiSym.mod_left' h1, show -x = (-1 : ℤ) * x by ring, jacobiSym.mul_left, hneg]
  ring

private lemma jacobi_sub_m (n : ℕ) (x : ℤ) :
    jacobiSym (x - (12 * n + 7 : ℕ)) (12 * n + 7) = jacobiSym x (12 * n + 7) := by
  exact jacobiSym.mod_left' (Int.sub_emod_right x ((12 * n + 7 : ℕ) : ℤ))

private lemma jacobi_three (n : ℕ) : jacobiSym 3 (12 * n + 7) = -1 := by
  have hqr := jacobiSym.quadratic_reciprocity_three_mod_four (by decide : 3 % 4 = 3)
    (by omega : (12 * n + 7) % 4 = 3)
  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, hqr]
  have hmod : ((12 * n + 7 : ℕ) : ℤ) % ((3 : ℕ) : ℤ) = (1 : ℤ) % ((3 : ℕ) : ℤ) := by omega
  rw [jacobiSym.mod_left' hmod, jacobiSym.one_left]

private lemma jacobi_two_even (k : ℕ) : jacobiSym 2 (12 * (2 * k) + 7) = 1 := by
  have hodd : Odd (12 * (2 * k) + 7) := ⟨12 * k + 3, by omega⟩
  rw [jacobiSym.at_two hodd]
  have hc : ((12 * (2 * k) + 7 : ℕ) : ZMod 8) = 7 := by
    have : 12 * (2 * k) + 7 = 8 * (3 * k) + 7 := by omega
    rw [this]; push_cast; rw [show (8 : ZMod 8) = 0 by decide]; simp
  rw [hc]; decide

private lemma jacobi_two_odd (k : ℕ) : jacobiSym 2 (12 * (2 * k + 1) + 7) = -1 := by
  have hodd : Odd (12 * (2 * k + 1) + 7) := ⟨12 * k + 9, by omega⟩
  rw [jacobiSym.at_two hodd]
  have hc : ((12 * (2 * k + 1) + 7 : ℕ) : ZMod 8) = 3 := by
    have : 12 * (2 * k + 1) + 7 = 8 * (3 * k + 2) + 3 := by omega
    rw [this]; push_cast; rw [show (8 : ZMod 8) = 0 by decide]; simp
  rw [hc]; decide

private lemma sum_range_eq_Icc (n k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), jacobiSym (i : ℤ) (12 * n + 7) =
      ∑ i ∈ Finset.Icc 1 k, jacobiSym (i : ℤ) (12 * n + 7) := by
  have hsplit : Finset.range (k + 1) = insert 0 (Finset.Icc 1 k) := by
    ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  have h0 : 0 ∉ Finset.Icc 1 k := by simp
  rw [hsplit, Finset.sum_insert h0, Nat.cast_zero, jacobiSym.zero_left (by omega : 1 < 12 * n + 7), zero_add]

private lemma jacobi_bridge_relations (n : ℕ) :
    let A := Jsum n (2 * n + 1)
    let S13 := Jsum n (4 * n + 2)
    let S12 := Jsum n (6 * n + 3)
    S13 = S12 + A ∧ S13 = jacobiSym 2 (12 * n + 7) * (2 * A) := by
  dsimp only [Jsum]
  rw [sum_range_eq_Icc, sum_range_eq_Icc, sum_range_eq_Icc]
  set m : ℕ := 12 * n + 7
  set A : ℤ := ∑ i ∈ Finset.Icc 1 (2 * n + 1), jacobiSym (i : ℤ) m
  set B : ℤ := ∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 2), jacobiSym (i : ℤ) m
  set C : ℤ := ∑ i ∈ Finset.Icc (4 * n + 3) (6 * n + 3), jacobiSym (i : ℤ) m
  have hAB : ∑ i ∈ Finset.Icc 1 (4 * n + 2), jacobiSym (i : ℤ) m = A + B := by
    have hu : Finset.Icc 1 (4 * n + 2) = Finset.Icc 1 (2 * n + 1) ∪ Finset.Icc (2 * n + 2) (4 * n + 2) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hd : Disjoint (Finset.Icc 1 (2 * n + 1)) (Finset.Icc (2 * n + 2) (4 * n + 2)) := by
      rw [Finset.disjoint_left]; intro x h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
    rw [hu, Finset.sum_union hd]
  have hABC : ∑ i ∈ Finset.Icc 1 (6 * n + 3), jacobiSym (i : ℤ) m = A + B + C := by
    have hu : Finset.Icc 1 (6 * n + 3) = Finset.Icc 1 (4 * n + 2) ∪ Finset.Icc (4 * n + 3) (6 * n + 3) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hd : Disjoint (Finset.Icc 1 (4 * n + 2)) (Finset.Icc (4 * n + 3) (6 * n + 3)) := by
      rw [Finset.disjoint_left]; intro x h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
    rw [hu, Finset.sum_union hd, hAB]
  rw [hAB, hABC]
  -- Mod 3 partition of Icc 1 (6*n+3)
  let I3 := Finset.Icc 1 (6 * n + 3)
  let M0 := I3.filter (fun k => k % 3 = 0)
  let M1 := I3.filter (fun k => k % 3 = 1)
  let M2 := I3.filter (fun k => k % 3 = 2)
  have hpart3 : ∑ k ∈ I3, jacobiSym (k : ℤ) m =
      (∑ k ∈ M0, jacobiSym (k : ℤ) m) + (∑ k ∈ M1, jacobiSym (k : ℤ) m) +
      (∑ k ∈ M2, jacobiSym (k : ℤ) m) := by
    have hu : I3 = M0 ∪ M1 ∪ M2 := by
      ext k; simp only [M0, M1, M2, Finset.mem_union, Finset.mem_filter]
      by_cases hk : k ∈ I3 <;> simp [hk]; omega
    have hd01 : Disjoint M0 M1 := Finset.disjoint_left.mpr (fun k h1 h2 => by
      simp only [M0, M1, Finset.mem_filter] at h1 h2; omega)
    have hd012 : Disjoint (M0 ∪ M1) M2 := Finset.disjoint_left.mpr (fun k h1 h2 => by
      simp only [M0, M1, M2, Finset.mem_union, Finset.mem_filter] at h1 h2; omega)
    rw [hu, Finset.sum_union hd012, Finset.sum_union hd01]
  have hM0 : ∑ k ∈ M0, jacobiSym (k : ℤ) m = -A := by
    have hbij : ∑ i ∈ Finset.Icc 1 (2 * n + 1), jacobiSym ((3 * i : ℕ) : ℤ) m =
        ∑ k ∈ M0, jacobiSym (k : ℤ) m := by
      apply Finset.sum_bij (fun i _ => 3 * i)
      · intro i hi; simp only [M0, I3, Finset.mem_filter, Finset.mem_Icc] at hi ⊢; omega
      · intro i1 _ i2 _ h; omega
      · intro k hk; simp only [M0, I3, Finset.mem_filter, Finset.mem_Icc] at hk
        exact ⟨k / 3, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro i _; rfl
    rw [← hbij]
    calc ∑ i ∈ Finset.Icc 1 (2 * n + 1), jacobiSym ((3 * i : ℕ) : ℤ) m
        = ∑ i ∈ Finset.Icc 1 (2 * n + 1), (jacobiSym 3 m * jacobiSym (i : ℤ) m) := by
          apply Finset.sum_congr rfl; intro i _; push_cast; exact jacobiSym.mul_left 3 (i : ℤ) m
      _ = jacobiSym 3 m * A := by rw [← Finset.mul_sum]
      _ = -A := by rw [jacobi_three n]; ring
  have hM1 : ∑ k ∈ M1, jacobiSym (k : ℤ) m = B := by
    have hbij : ∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 2), jacobiSym ((m - 3 * i : ℕ) : ℤ) m =
        ∑ k ∈ M1, jacobiSym (k : ℤ) m := by
      apply Finset.sum_bij (fun i _ => m - 3 * i)
      · intro i hi; simp only [M1, I3, Finset.mem_filter, Finset.mem_Icc] at hi ⊢; omega
      · intro i1 h1 i2 h2 h; rw [Finset.mem_Icc] at h1 h2; omega
      · intro k hk; simp only [M1, I3, Finset.mem_filter, Finset.mem_Icc] at hk
        exact ⟨(m - k) / 3, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro i _; rfl
    rw [← hbij]
    calc ∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 2), jacobiSym ((m - 3 * i : ℕ) : ℤ) m
        = ∑ i ∈ Finset.Icc (2 * n + 2) (4 * n + 2), (-jacobiSym 3 m * jacobiSym (i : ℤ) m) := by
          apply Finset.sum_congr rfl; intro i hi
          rw [Finset.mem_Icc] at hi
          have hsub : ((m - 3 * i : ℕ) : ℤ) = (m : ℤ) - (3 * (i : ℤ)) := by omega
          rw [hsub, jacobi_neg_sub n (3 * (i : ℤ)), jacobiSym.mul_left]; ring
      _ = (-jacobiSym 3 m) * B := by rw [← Finset.mul_sum]
      _ = B := by rw [jacobi_three n]; ring
  have hM2 : ∑ k ∈ M2, jacobiSym (k : ℤ) m = -C := by
    have hbij : ∑ i ∈ Finset.Icc (4 * n + 3) (6 * n + 3), jacobiSym ((3 * i - m : ℕ) : ℤ) m =
        ∑ k ∈ M2, jacobiSym (k : ℤ) m := by
      apply Finset.sum_bij (fun i _ => 3 * i - m)
      · intro i hi; simp only [M2, I3, Finset.mem_filter, Finset.mem_Icc] at hi ⊢; omega
      · intro i1 h1 i2 h2 h; rw [Finset.mem_Icc] at h1 h2; omega
      · intro k hk; simp only [M2, I3, Finset.mem_filter, Finset.mem_Icc] at hk
        exact ⟨(k + m) / 3, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro i _; rfl
    rw [← hbij]
    calc ∑ i ∈ Finset.Icc (4 * n + 3) (6 * n + 3), jacobiSym ((3 * i - m : ℕ) : ℤ) m
        = ∑ i ∈ Finset.Icc (4 * n + 3) (6 * n + 3), (jacobiSym 3 m * jacobiSym (i : ℤ) m) := by
          apply Finset.sum_congr rfl; intro i hi
          rw [Finset.mem_Icc] at hi
          have hsub : ((3 * i - m : ℕ) : ℤ) = (3 * (i : ℤ)) - (m : ℤ) := by omega
          rw [hsub, jacobi_sub_m n (3 * (i : ℤ)), jacobiSym.mul_left]
      _ = jacobiSym 3 m * C := by rw [← Finset.mul_sum]
      _ = -C := by rw [jacobi_three n]; ring
  have hC : C = -A := by
    have h := hABC.symm.trans hpart3
    rw [hM0, hM1, hM2] at h
    linarith
  -- Mod 2 partition of Icc 1 (4*n+2)
  let I2 := Finset.Icc 1 (4 * n + 2)
  let E0 := I2.filter (fun k => k % 2 = 0)
  let E1 := I2.filter (fun k => k % 2 = 1)
  have hpart2 : ∑ k ∈ I2, jacobiSym (k : ℤ) m =
      (∑ k ∈ E0, jacobiSym (k : ℤ) m) + (∑ k ∈ E1, jacobiSym (k : ℤ) m) := by
    have hu : I2 = E0 ∪ E1 := by
      ext k; simp only [E0, E1, Finset.mem_union, Finset.mem_filter]
      by_cases hk : k ∈ I2 <;> simp [hk]; omega
    have hd : Disjoint E0 E1 := Finset.disjoint_left.mpr (fun k h1 h2 => by
      simp only [E0, E1, Finset.mem_filter] at h1 h2; omega)
    rw [hu, Finset.sum_union hd]
  have hE0 : ∑ k ∈ E0, jacobiSym (k : ℤ) m = jacobiSym 2 m * A := by
    have hbij : ∑ i ∈ Finset.Icc 1 (2 * n + 1), jacobiSym ((2 * i : ℕ) : ℤ) m =
        ∑ k ∈ E0, jacobiSym (k : ℤ) m := by
      apply Finset.sum_bij (fun i _ => 2 * i)
      · intro i hi; simp only [E0, I2, Finset.mem_filter, Finset.mem_Icc] at hi ⊢; omega
      · intro i1 _ i2 _ h; omega
      · intro k hk; simp only [E0, I2, Finset.mem_filter, Finset.mem_Icc] at hk
        exact ⟨k / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro i _; rfl
    rw [← hbij]
    calc ∑ i ∈ Finset.Icc 1 (2 * n + 1), jacobiSym ((2 * i : ℕ) : ℤ) m
        = ∑ i ∈ Finset.Icc 1 (2 * n + 1), (jacobiSym 2 m * jacobiSym (i : ℤ) m) := by
          apply Finset.sum_congr rfl; intro i _; push_cast; exact jacobiSym.mul_left 2 (i : ℤ) m
      _ = jacobiSym 2 m * A := by rw [← Finset.mul_sum]
  have hE1 : ∑ k ∈ E1, jacobiSym (k : ℤ) m = -jacobiSym 2 m * C := by
    have hbij : ∑ i ∈ Finset.Icc (4 * n + 3) (6 * n + 3), jacobiSym ((m - 2 * i : ℕ) : ℤ) m =
        ∑ k ∈ E1, jacobiSym (k : ℤ) m := by
      apply Finset.sum_bij (fun i _ => m - 2 * i)
      · intro i hi; simp only [E1, I2, Finset.mem_filter, Finset.mem_Icc] at hi ⊢; omega
      · intro i1 h1 i2 h2 h; rw [Finset.mem_Icc] at h1 h2; omega
      · intro k hk; simp only [E1, I2, Finset.mem_filter, Finset.mem_Icc] at hk
        exact ⟨(m - k) / 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
      · intro i _; rfl
    rw [← hbij]
    calc ∑ i ∈ Finset.Icc (4 * n + 3) (6 * n + 3), jacobiSym ((m - 2 * i : ℕ) : ℤ) m
        = ∑ i ∈ Finset.Icc (4 * n + 3) (6 * n + 3), (-jacobiSym 2 m * jacobiSym (i : ℤ) m) := by
          apply Finset.sum_congr rfl; intro i hi
          rw [Finset.mem_Icc] at hi
          have hsub : ((m - 2 * i : ℕ) : ℤ) = (m : ℤ) - (2 * (i : ℤ)) := by omega
          rw [hsub, jacobi_neg_sub n (2 * (i : ℤ)), jacobiSym.mul_left]; ring
      _ = (-jacobiSym 2 m) * C := by rw [← Finset.mul_sum]
  have h2 := hAB.symm.trans hpart2
  rw [hE0, hE1, hC] at h2
  constructor <;> linarith

private lemma jacobi_even (k : ℕ) :
    Jsum (2 * k) (4 * (2 * k) + 2) = 2 * Jsum (2 * k) (2 * (2 * k) + 1) ∧
    Jsum (2 * k) (6 * (2 * k) + 3) = Jsum (2 * k) (2 * (2 * k) + 1) := by
  have h := jacobi_bridge_relations (2 * k)
  dsimp only at h
  rw [jacobi_two_even k] at h
  constructor <;> linarith

private lemma jacobi_odd (k : ℕ) :
    Jsum (2 * k + 1) (4 * (2 * k + 1) + 2) = -2 * Jsum (2 * k + 1) (2 * (2 * k + 1) + 1) ∧
    Jsum (2 * k + 1) (6 * (2 * k + 1) + 3) = -3 * Jsum (2 * k + 1) (2 * (2 * k + 1) + 1) := by
  have h := jacobi_bridge_relations (2 * k + 1)
  dsimp only at h
  rw [jacobi_two_odd k] at h
  constructor <;> linarith

private lemma prove_main :
    ∀ n : ℕ, a166271 n = -2 * a166269 n := by
  intro n
  have h1 : a166269 n = Jsum (2 * n + 1) (2 * (2 * n + 1) + 1) := rfl
  have h2 : a166271 n = Jsum (2 * n + 1) (4 * (2 * n + 1) + 2) := rfl
  rw [h1, h2]
  exact (jacobi_odd n).1

end OMA.P_oeis_a166271

theorem OMA.solution : type_of% @OMA.S_oeis_a166271.main :=
  OMA.P_oeis_a166271.prove_main
