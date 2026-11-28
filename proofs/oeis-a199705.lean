import OMAStatements.S_oeis_a199705

-- Original proof and statement by @jleguina in #13565.
-- Count the zero-sum triples, then remove the two equal-neighbor classes.

namespace OMA.A199705

abbrev Triple := ℤ × ℤ × ℤ

noncomputable def zeroSumTriples (n : ℕ) : Finset Triple :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun p : Triple => p.1 + p.2.1 + p.2.2 = 0))

end OMA.A199705

namespace OMA.A199705

open Finset

private abbrev tuples (s : ℕ) := Finset.Nat.antidiagonalTuple 3 s

private theorem all_card (s : ℕ) : (tuples s).card = (s + 2).choose 2 := by
  change (List.Nat.antidiagonalTuple 3 s).length = _
  rw [List.Nat.antidiagonalTuple, List.length_flatMap]
  simp only [List.length_map, List.Nat.antidiagonalTuple_two, List.Nat.length_antidiagonal]
  induction s with
  | zero => decide
  | succ s ih =>
    rw [List.Nat.antidiagonal_succ, List.map_cons, List.sum_cons, List.map_map]
    change s + 2 + ((List.Nat.antidiagonal s).map (fun p => p.2 + 1)).sum = _
    rw [ih, Nat.choose_succ_succ (s + 2), Nat.choose_one_right]

private theorem bounded_card (n : ℕ) :
    (zeroSumTriples n).card = ((tuples (3 * n)).filter (fun f => ∀ i, f i ≤ 2 * n)).card := by
  unfold zeroSumTriples
  refine card_nbij' (fun t => ![(t.1 + n).toNat, (t.2.1 + n).toNat, (t.2.2 + n).toNat])
    (fun f => ((f 0 : ℤ) - n, (f 1 : ℤ) - n, (f 2 : ℤ) - n)) ?_ ?_ ?_ ?_
  · rintro ⟨x,y,z⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Icc] at h
    rcases h with ⟨⟨⟨hx, hx'⟩, ⟨hy, hy'⟩, ⟨hz, hz'⟩⟩, hs⟩
    simp only [mem_coe, mem_filter, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three]
    refine ⟨?_, fun i => ?_⟩
    · change (x + n).toNat + (y + n).toNat + (z + n).toNat = _
      omega
    · fin_cases i <;> simp <;> omega
  · intro f h
    simp only [mem_coe, mem_filter, Finset.Nat.mem_antidiagonalTuple, Fin.sum_univ_three] at h
    simp only [mem_coe, mem_filter, mem_product, mem_Icc]
    have h0 := h.2 0
    have h1 := h.2 1
    have h2 := h.2 2
    omega
  · rintro ⟨x,y,z⟩ h
    simp only [mem_coe, mem_filter, mem_product, mem_Icc] at h
    rcases h with ⟨⟨⟨hx, _⟩, ⟨hy, _⟩, ⟨hz, _⟩⟩, _⟩
    change (((x + n).toNat : ℤ) - n, ((y + n).toNat : ℤ) - n,
      ((z + n).toNat : ℤ) - n) = (x, y, z)
    simp only [Prod.mk.injEq]
    omega
  · intro f _
    funext i
    fin_cases i <;> simp

private def overflow (n : ℕ) (i : Fin 3) := (tuples (3 * n)).filter (fun f => 2 * n < f i)

-- Removing 2n+1 stars from the overflowing coordinate leaves a tuple of sum n-1.
private theorem overflow_card (n : ℕ) (hn : 0 < n) (i : Fin 3) :
    (overflow n i).card = (n + 1).choose 2 := by
  rw [show n + 1 = n - 1 + 2 by omega, ← all_card]
  have hsplit (f : Fin 3 → ℕ) : (∑ k, f k) = f i + ∑ k ∈ univ \ {i}, f k := by
    simpa using sum_update_of_mem (mem_univ i) f (f i)
  refine card_nbij' (fun f => Function.update f i (f i - (2 * n + 1)))
    (fun f => Function.update f i (f i + (2 * n + 1))) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [mem_coe, overflow, mem_filter, Finset.Nat.mem_antidiagonalTuple] at hf ⊢
    rw [hsplit f] at hf
    rw [sum_update_of_mem (mem_univ i)]
    omega
  · intro f hf
    simp only [mem_coe, overflow, mem_filter, Finset.Nat.mem_antidiagonalTuple] at hf ⊢
    rw [hsplit f] at hf
    rw [sum_update_of_mem (mem_univ i)]
    simp only [Function.update_self]
    omega
  · intro f hf
    have hf := (mem_filter.mp hf).2
    funext j
    by_cases h : j = i
    · simp [h]
      omega
    · simp [h]
  · intro f _
    funext j
    by_cases h : j = i <;> simp [h]

private theorem count_add (n : ℕ) (hn : 0 < n) :
    (zeroSumTriples n).card + 3 * (n + 1).choose 2 = (3 * n + 2).choose 2 := by
  have hbad : ((tuples (3 * n)).filter (fun f => ¬ ∀ i, f i ≤ 2 * n)) =
      univ.biUnion (overflow n) := by
    ext f
    simp [overflow, not_le]
  have hd : ((univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint (overflow n) := by
    intro i _ j _ hij
    refine disjoint_left.mpr ?_
    intro f hi hj
    rw [overflow, mem_filter, Finset.Nat.mem_antidiagonalTuple] at hi hj
    have h := sum_le_sum_of_subset_of_nonneg (f := f)
      (subset_univ ({i, j} : Finset (Fin 3))) (fun k _ _ => Nat.zero_le (f k))
    simp [hij, hi.1] at h
    omega
  have h := card_filter_add_card_filter_not (s := tuples (3 * n)) (fun f => ∀ i, f i ≤ 2 * n)
  rw [← bounded_card n, hbad, card_biUnion hd, all_card] at h
  simpa [overflow_card n hn, Nat.mul_comm] using h

theorem count_all (n : ℕ) : (zeroSumTriples n).card = 3 * n ^ 2 + 3 * n + 1 := by
  by_cases hn : 0 < n
  · have h := congrArg (fun x : ℕ => (x : ℚ)) (count_add n hn)
    have hp := congrArg (fun x : ℕ => (x : ℚ)) (Nat.descFactorial_eq_factorial_mul_choose (3*n+2) 2)
    have hm := congrArg (fun x : ℕ => (x : ℚ)) (Nat.descFactorial_eq_factorial_mul_choose (n+1) 2)
    norm_num [Nat.descFactorial_succ, Nat.factorial_succ,
      show 3 * n + 2 - 1 = 3 * n + 1 by omega] at h hp hm
    have he : ((zeroSumTriples n).card : ℚ) = 3 * (n : ℚ) ^ 2 + 3 * (n : ℚ) + 1 := by
      linear_combination (2 * h - hp + 3 * hm) / 2
    exact_mod_cast he
  · obtain rfl : n = 0 := by omega
    decide

end OMA.A199705

namespace OMA.A199705

open Finset

private lemma mem_zeroSumTriples {n : ℕ} {x y z : ℤ} :
    (x, y, z) ∈ zeroSumTriples n ↔
      -(n : ℤ) ≤ x ∧ x ≤ n ∧ -(n : ℤ) ≤ y ∧ y ≤ n ∧
        -(n : ℤ) ≤ z ∧ z ≤ n ∧ x + y + z = 0 := by
  simp only [zeroSumTriples, mem_filter, mem_product, mem_Icc, and_assoc]

private lemma card_equal_neighbor (n : ℕ) (left : Bool) :
    ((zeroSumTriples n).filter fun p => if left then p.1 = p.2.1 else p.2.1 = p.2.2).card =
      2 * (n / 2) + 1 := by
  let I := Icc (-((n : ℤ) / 2)) ((n : ℤ) / 2)
  let trip (t : ℤ) : Triple := if left then (t, t, -2 * t) else (-2 * t, t, t)
  have h := card_nbij' trip (fun p : Triple => p.2.1)
    (s := I) (t := (zeroSumTriples n).filter fun p =>
      if left then p.1 = p.2.1 else p.2.1 = p.2.2) ?_ ?_ ?_ ?_
  · rw [← h]
    change (Icc _ _).card = _
    rw [Int.card_Icc]
    omega
  · intro t ht
    change t ∈ I at ht
    rw [show I = Icc (-((n : ℤ) / 2)) ((n : ℤ) / 2) by rfl, mem_Icc] at ht
    cases left <;> simp [trip, mem_zeroSumTriples] <;> omega
  · rintro ⟨x, y, z⟩ hp
    change (x, y, z) ∈ (zeroSumTriples n).filter _ at hp
    change y ∈ I
    cases left <;> simp [I, mem_zeroSumTriples] at hp ⊢ <;> omega
  · intro t _
    cases left <;> rfl
  · rintro ⟨x, y, z⟩ hp
    change (x, y, z) ∈ (zeroSumTriples n).filter _ at hp
    change trip y = (x, y, z)
    cases left <;> simp [trip, mem_zeroSumTriples] at hp ⊢ <;> omega

theorem a_formula (h : ∀ n : ℕ, (zeroSumTriples n).card = 3 * n ^ 2 + 3 * n + 1) (n : ℕ) :
    (OMA.S_oeis_a199705.a n : ℤ) = (n : ℤ) + 3 * (n : ℤ) ^ 2 + 2 * (↑(n % 2) : ℤ) := by
  let L := (zeroSumTriples n).filter fun p => p.1 = p.2.1
  let R := (zeroSumTriples n).filter fun p => p.2.1 = p.2.2
  let bad (p : Triple) := p.1 = p.2.1 ∨ p.2.1 = p.2.2
  have hL : L.card = 2 * (n / 2) + 1 := card_equal_neighbor n true
  have hR : R.card = 2 * (n / 2) + 1 := card_equal_neighbor n false
  have hmeet : L ∩ R = {(0, 0, 0)} := by
    ext p
    rcases p with ⟨x, y, z⟩
    simp only [L, R, mem_inter, mem_filter, mem_singleton, mem_zeroSumTriples, Prod.mk.injEq]
    omega
  have hgood : OMA.S_oeis_a199705.a n = ((zeroSumTriples n) \ (zeroSumTriples n).filter bad).card := by
    unfold OMA.S_oeis_a199705.a
    congr 1
    ext p
    simp only [mem_sdiff, mem_filter, zeroSumTriples, bad]
    tauto
  have hadd := card_sdiff_add_card_eq_card (filter_subset bad (zeroSumTriples n))
  rw [← hgood, show (zeroSumTriples n).filter bad = L ∪ R from filter_or _ _ _] at hadd
  have hunion := card_union_add_card_inter L R
  rw [hmeet, card_singleton, hL, hR] at hunion
  have hc : OMA.S_oeis_a199705.a n + 2 * (2 * (n / 2) + 1) = 3 * n ^ 2 + 3 * n + 2 := by
    have := h n
    omega
  have hz := congrArg (fun x : ℕ => (x : ℤ)) hc
  push_cast at hz
  omega

end OMA.A199705

namespace OMA.A199705

open PowerSeries OMA.S_oeis_a199705

theorem main_of_formula (h : ∀ n : ℕ,
    (a n : ℤ) = (n : ℤ) + 3 * (n : ℤ) ^ 2 + 2 * (↑(n % 2) : ℤ)) :
    type_of% @OMA.S_oeis_a199705.main := by
  have hc (n : ℕ) : (a n : ℚ) = (n : ℚ) + 3 * (n : ℚ) ^ 2 + 2 * (↑(n % 2) : ℚ) := by
    exact_mod_cast h n
  refine ⟨?_, ?_, ?_⟩
  · rw [eq_mul_inv_iff_mul_eq (by simp)]
    let A := mk (fun n => (a n : ℚ))
    have hd : A * ((1 - X) ^ 3 * (1 + X)) =
        A - C 2 * (X ^ 1 * A) + C 2 * (X ^ 3 * A) - X ^ 4 * A := by
      rw [map_ofNat C 2]
      ring
    have hn : (2 * X * (3 + X + 2 * X ^ 2) : ℚ⟦X⟧) =
        C 6 * X ^ 1 + C 2 * X ^ 2 + C 4 * X ^ 3 := by
      simp only [map_ofNat]
      ring
    change A * _ = _
    rw [hd, hn]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, A, coeff_mk]
    by_cases hs : n < 4
    · interval_cases n <;> norm_num [hc]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
      simp (disch := omega) [Nat.add_sub_assoc, Nat.cast_add, hc,
        show (k + 4) % 2 = k % 2 by omega,
        show (k + 3) % 2 = (k + 1) % 2 by omega]
      ring
  · intro n _ hn
    simpa [hn] using h n
  · intro n _ hn
    have hh := h n
    rw [hn] at hh
    omega

end OMA.A199705

open OMA.A199705 in
theorem OMA.solution : type_of% @OMA.S_oeis_a199705.main :=
  main_of_formula (a_formula count_all)
