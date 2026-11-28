import OMAStatements.S_oeis_a034387
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

open Finset OMA.S_oeis_a034387

namespace OMA.A034387

private lemma sum_reflect (i n : ℕ) (f : ℕ → ℕ) :
    (∑ j ∈ Icc i n, f (i + n - j)) = ∑ j ∈ Icc i n, f j := by
  refine sum_bij (fun j _ => i + n - j) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [mem_Icc] at hj ⊢
    omega
  · intro j hj k hk heq
    simp only [mem_Icc] at hj hk
    omega
  · intro j hj
    simp only [mem_Icc] at hj
    refine ⟨i + n - j, ?_, ?_⟩
    · simp only [mem_Icc]
      omega
    · omega
  · intros
    rfl

private lemma sum_triangle (n : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ Icc 1 n, ∑ k ∈ Icc i n, f k) = ∑ k ∈ Icc 1 n, k * f k := by
  calc
    _ = ∑ i ∈ Icc 1 n, ∑ k ∈ Icc 1 n, if i ≤ k then f k else 0 := by
      apply sum_congr rfl
      intro i hi
      rw [← sum_filter]
      have h : (Icc 1 n).filter (fun k => i ≤ k) = Icc i n := by
        ext k
        simp only [mem_filter, mem_Icc] at hi ⊢
        omega
      rw [h]
    _ = ∑ k ∈ Icc 1 n, ∑ i ∈ Icc 1 n, if i ≤ k then f k else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      rw [← sum_filter]
      have h : (Icc 1 n).filter (fun i => i ≤ k) = Icc 1 k := by
        ext i
        simp only [mem_filter, mem_Icc] at hk ⊢
        omega
      simp [h, Nat.card_Icc]

end OMA.A034387

theorem OMA.solution : type_of% @OMA.S_oeis_a034387.main := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_mk]
  symm
  calc
    tripleCoeff n = ∑ i ∈ Icc 1 n, ∑ k ∈ Icc i n, if k.Prime then 1 else 0 := by
      unfold tripleCoeff
      exact sum_congr rfl fun i _ => OMA.A034387.sum_reflect i n
        (fun k => if k.Prime then 1 else 0)
    _ = ∑ k ∈ Icc 1 n, k * (if k.Prime then 1 else 0) :=
      OMA.A034387.sum_triangle n (fun k => if k.Prime then 1 else 0)
    _ = primeSum n := by
      unfold primeSum
      apply sum_congr rfl
      intro k _
      by_cases hk : k.Prime <;> simp [hk]
