import OMAStatements.S_oeis_a001067
import Mathlib.Tactic
open OMA.S_oeis_a001067

/-!
The known counterexample recorded in OEIS A119766 is n=10 in A001067.
The p0 includes B'(1)=1/2 and is certified against Mathlib's recursion.
The unsigned reduced numerator at index 10 is 174611 = 283*617.
-/

namespace A001067

private def p0 (n : ℕ) : ℚ :=
  ([1,1/2,1/6,0,-1/30,0,1/42,0,-1/30,0,5/66,0,-691/2730,0,7/6,0,
    -3617/510,0,43867/798,0,-174611/330] : List ℚ).getD n 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem p1 : ∀ n : Fin 21,
    p0 n.val = 1 - ∑ k ∈ Finset.range n.val, n.val.choose k / (n.val-k+1) * p0 k := by
  decide +kernel

private lemma p2 (n : ℕ) (h : n<21) : bernoulli' n=p0 n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
      calc
        bernoulli' n = 1 - ∑ k ∈ Finset.range n, n.choose k / (n-k+1) * bernoulli' k := bernoulli'_def n
        _ = 1 - ∑ k ∈ Finset.range n, n.choose k / (n-k+1) * p0 k := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          rw [ih k (Finset.mem_range.mp hk) (by have lt := Finset.mem_range.mp hk; omega)]
        _ = p0 n := (p1 ⟨n,h⟩).symm

private lemma p3 : absNumerator 10=174611 := by
  have hb : bernoulli 20=-(174611:ℚ)/330 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by decide),p2 20 (by decide)]
    decide +kernel
  rw [absNumerator, show (2:ℕ)*10=20 by decide,hb]
  decide +kernel

end A001067

open OMA.S_oeis_a001067 A001067 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a001067.main) := by
  intro h
  have result := h 10 (by decide)
  rw [p3] at result
  rcases result with hOne | hp
  · omega
  · have factor : 283 ∣ (174611:ℕ) := ⟨617,rfl⟩
    have impossible := hp.eq_one_or_self_of_dvd 283 factor
    omega
