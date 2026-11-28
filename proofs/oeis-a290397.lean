import OMAStatements.S_oeis_a290397

-- Credit: @rleshner (agent: Codex, model: GPT-6)

/-!
# Gutkovskiy's bound for sums of nonprime squarefree numbers

For m > 36, consider the m odd numbers x between 1 and 2m. At most
(17/72)(2m) positive integers up to 2m are divisible by the square of an odd
integer greater than one. Exclude all such numbers and their reflections
2m - x, as well as 1 and 2m - 1. Some odd x remains. The two doubled
summands 2x and 2(2m - x) are composite and squarefree. An exact finite
check covers 3 ≤ m ≤ 36, and appending at most three ones provides the
remaining residues modulo four.

Gabriel Mincu and Laurențiu Panaitopol proved in 2006 that every integer
n ≥ 2 is a sum of two squarefree integers (Theorem 1 of “On some properties
of squarefree and squareful numbers”). Here the summands must be nonprime.
Source: https://oeis.org/A290397
-/

namespace SquarefreeSums

open Finset OMA.S_oeis_a290397

private theorem tail_term (x : ℚ) (hx : 0 ≤ x) :
    1 / (2*x+5)^2 ≤ 1/(4*(x+2)) - 1/(4*(x+3)) := by
  field_simp
  nlinarith

private theorem reciprocal_sum_aux (K : ℕ) :
    ∑ i ∈ range (K+1), (1:ℚ)/(2*(i:ℚ)+3)^2 ≤ 17/72 - 1/(4*((K:ℚ)+2)) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [sum_range_succ]
    push_cast
    have ht := tail_term (K:ℚ) (by positivity)
    rw [show 2*((K:ℚ)+1)+3 = 2*K+5 by ring, show (K:ℚ)+1+2 = K+3 by ring]
    linarith

private theorem reciprocal_sum (K : ℕ) :
    ∑ i ∈ range K, (1:ℚ)/(2*(i:ℚ)+3)^2 ≤ 17/72 := by
  cases K with
  | zero => norm_num
  | succ K =>
    have h := reciprocal_sum_aux K
    have : 0 ≤ 1/(4*((K:ℚ)+2)) := by positivity
    linarith

private def multiples (N d : ℕ) : Finset ℕ :=
  (range (N+1)).filter (fun k => k ≠ 0 ∧ d ∣ k)

private def bad (N : ℕ) : Finset ℕ :=
  (range N).biUnion (fun i => multiples N ((2*i+3)^2))

private theorem bound_bad (N : ℕ) : ((bad N).card : ℚ) ≤ (N:ℚ) * (17/72) := by
  have h : (bad N).card ≤ ∑ i ∈ range N, N/((2*i+3)^2) := by
    simpa [bad, multiples, Nat.card_multiples'] using
      (card_biUnion_le (s := range N) (t := fun i => multiples N ((2*i+3)^2)))
  calc ((bad N).card:ℚ) ≤ ∑ i ∈ range N, ((N/((2*i+3)^2):ℕ):ℚ) := by exact_mod_cast h
       _ ≤ ∑ i ∈ range N, (N:ℚ)*(1/(2*(i:ℚ)+3)^2) := by
         apply sum_le_sum
         intro i _
         have hdiv : ((N/((2*i+3)^2):ℕ):ℚ) ≤ (N:ℚ) / (((2*i+3)^2:ℕ):ℚ) :=
           Nat.cast_div_le
         push_cast at hdiv
         simpa [div_eq_mul_inv] using hdiv
       _ = (N:ℚ) * ∑ i ∈ range N, (1:ℚ)/(2*(i:ℚ)+3)^2 := (mul_sum ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_sum N) (by positivity)

private theorem sqfree_outside {x N : ℕ} (hx : 0 < x) (hxN : x ≤ N) (ho : x % 2 = 1)
    (hmiss : x ∉ bad N) : Squarefree x := by
  apply Nat.squarefree_iff_prime_squarefree.mpr
  intro p hp hd
  apply hmiss
  rcases hp.eq_two_or_odd with rfl | hodd
  · obtain ⟨t,ht⟩ := hd
    omega
  have hple : p ≤ x := Nat.le_of_dvd hx ((dvd_mul_right p p).trans hd)
  have hp2 := hp.two_le
  let i := (p - 3)/2
  have heq : 2*i+3 = p := by dsimp [i]; omega
  have hi : i < N := by dsimp [i]; omega
  apply mem_biUnion.mpr
  refine ⟨i, mem_range.mpr hi, ?_⟩
  simp [multiples, hx.ne', hxN, heq, pow_two, hd]

private theorem doubled {x : ℕ} (hx : 1 < x) (ho : x % 2 = 1) (hs : Squarefree x) :
    IsA000469 (2*x) := by
  have hcop : Nat.Coprime 2 x := Nat.coprime_two_left.mpr (by exact Nat.odd_iff.mpr ho)
  exact ⟨by omega, (Nat.squarefree_mul hcop).mpr ⟨Nat.prime_two.prime.squarefree, hs⟩,
    Nat.not_prime_mul (by decide) (by omega)⟩

private theorem large_pair (m : ℕ) (hm : 36 < m) :
    ∃ x y : ℕ, IsA000469 x ∧ IsA000469 y ∧ x + y = 4*m := by
  classical
  let N := 2*m
  let odds := (range m).image (fun i => 2*i+1)
  let excluded := (bad N ∪ (bad N).image (fun x => N-x)) ∪ {1, N-1}
  have ho_card : odds.card = m := by
    rw [Finset.card_image_of_injective _ (show Function.Injective (fun i : ℕ => 2*i+1) by
      intro a b h; dsimp at h; omega)]
    simp
  have he_card : excluded.card ≤ 2*(bad N).card + 2 := by
    have h₁ := card_union_le (bad N) ((bad N).image (fun x => N-x))
    have h₂ := card_union_le (bad N ∪ (bad N).image (fun x => N-x)) ({1,N-1}:Finset ℕ)
    have h₃ := card_image_le (s := bad N) (f := fun x => N-x)
    have h₄ : ({1,N-1}:Finset ℕ).card ≤ 2 := by
      simpa using card_insert_le 1 ({N-1}:Finset ℕ)
    dsimp [excluded]
    omega
  have hlt : excluded.card < odds.card := by
    rw [ho_card]
    have b := bound_bad (2*m)
    change ((bad N).card:ℚ) ≤ (↑(2*m):ℚ)*(17/72) at b
    push_cast at b
    have c : (36:ℚ) < (m:ℚ) := by exact_mod_cast hm
    have d : (excluded.card:ℚ) ≤ 2*((bad N).card:ℚ)+2 := by exact_mod_cast he_card
    exact_mod_cast (show (excluded.card:ℚ) < (m:ℚ) by linarith)
  obtain ⟨x,hx,hout⟩ := exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
  have him := mem_range.mp hi
  have hN : N = 2*m := rfl
  let x := 2*i+1
  have hxs : 0 < x ∧ x < N ∧ x%2 = 1 := by dsimp [x]; omega
  have hys : 0 < N-x ∧ N-x ≤ N ∧ (N-x)%2 = 1 := by omega
  change x ∉ excluded at hout
  simp only [excluded, mem_union, mem_insert, mem_singleton, not_or] at hout
  have hyout : N-x ∉ bad N := by
    intro h
    exact hout.1.2 (mem_image.mpr ⟨N-x,h,by omega⟩)
  have hX := sqfree_outside hxs.1 hxs.2.1.le hxs.2.2 hout.1.1
  have hY := sqfree_outside hys.1 hys.2.1 hys.2.2 hyout
  refine ⟨2*x, 2*(N-x), doubled (by obtain ⟨_, h⟩ := hout; omega) hxs.2.2 hX,
    doubled (by obtain ⟨_, h⟩ := hout; omega) hys.2.2 hY, by omega⟩

private theorem small_pair (m : ℕ) (h₀ : 3 ≤ m) (hm : m ≤ 36) :
    ∃ x y : ℕ, IsA000469 x ∧ IsA000469 y ∧ x + y = 4*m := by
  have cert : ∀ j : Fin 37, 3 ≤ j.val → ∃ p : Fin 8,
      2 < p.val ∧ p.val.Prime ∧ p.val ≤ 2*j.val ∧
      2 < 2*j.val-p.val ∧ (2*j.val-p.val).Prime := by decide
  obtain ⟨p,hp,hpp,hle,hq,hqp⟩ := cert ⟨m, by omega⟩ h₀
  dsimp only at hle hq hqp
  have hpodd := hpp.eq_two_or_odd.resolve_left (by omega)
  have hqodd := hqp.eq_two_or_odd.resolve_left (by omega)
  exact ⟨2*p.val, 2*(2*m-p.val), doubled (by omega) hpodd hpp.prime.squarefree,
    doubled (by omega) hqodd hqp.prime.squarefree, by omega⟩

private theorem one_ok : IsA000469 1 := ⟨by decide, squarefree_one, Nat.not_prime_one⟩

private theorem add_ones (l : List ℕ) (r : ℕ) (h : l.length+r ≤ 5)
    (hl : ∀ x ∈ l, IsA000469 x) (n : ℕ) (hn : l.sum+r = n) :
    ∃ s : List ℕ, s.length ≤ 5 ∧ (∀ x ∈ s, IsA000469 x) ∧ s.sum = n := by
  refine ⟨l ++ List.replicate r 1, by simpa using h, ?_, by simpa using hn⟩
  intro x hx
  rcases List.mem_append.mp hx with ht | ht
  · exact hl x ht
  · have := (List.mem_replicate.mp ht).2
    exact this ▸ one_ok

theorem solve (n : ℕ) (hn : 1 ≤ n) :
    ∃ l : List ℕ, l.length ≤ 5 ∧ (∀ x ∈ l, IsA000469 x) ∧ l.sum = n := by
  have h6 : IsA000469 6 := doubled (x := 3) (by decide) (by decide) Nat.prime_three.prime.squarefree
  have h10 : IsA000469 10 := doubled (x := 5) (by decide) (by decide) (show Nat.Prime 5 by decide).prime.squarefree
  by_cases hsmall : n < 12
  · by_cases ha : n ≤ 5
    · exact add_ones [] n (by simpa using ha) (by simp) n (by simp)
    by_cases hb : n ≤ 10
    · exact add_ones [6] (n-6) (by simp; omega) (by simpa using h6) n (by simp; omega)
    · exact add_ones [10] 1 (by decide) (by simpa using h10) n (by simp; omega)
  have hm : 3 ≤ n/4 := by omega
  obtain ⟨x,y,hx,hy,hxy⟩ := (show ∃ x y : ℕ, IsA000469 x ∧ IsA000469 y ∧ x+y=4*(n/4) by
    by_cases h : 36 < n/4
    · exact large_pair _ h
    · exact small_pair _ hm (by omega))
  exact add_ones [x,y] (n%4) (by simp; omega) (by simpa using And.intro hx hy) n (by simp; omega)

end SquarefreeSums

theorem OMA.solution : type_of% @OMA.S_oeis_a290397.main := SquarefreeSums.solve
