import OMAStatements.S_oeis_a087304

namespace OMA.S_oeis_a087304

private def repunit (k : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate k 1)

private theorem positive_binary_multiple (n : ℕ) (hn : 0 < n) :
    ∃ r : ℕ, 0 < r ∧ n ∣ r ∧
      ((Nat.digits 10 r).map fun d => if d = 0 then 1 else d).prod = 1 := by
  -- Two decimal repunits have the same residue. Their difference has
  -- a nonempty run of ones followed by zeros.
  obtain ⟨i, j, hij, hmod⟩ : ∃ i j : ℕ, i < j ∧ repunit i ≡ repunit j [MOD n] := by
    obtain ⟨i, _, j, _, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to
        (s := Finset.range (n + 1)) (t := Finset.range n)
        (f := fun k => repunit k % n) (by simp)
        (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hn))
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, heq⟩
    · exact ⟨j, i, h, heq.symm⟩
  let k := j - i
  have hk : 0 < k := by dsimp [k]; omega
  have hdecomp : repunit j = repunit i + 10 ^ i * repunit k := by
    have hl : List.replicate j (1 : ℕ) = List.replicate i 1 ++ List.replicate k 1 := by
      rw [← List.replicate_add, show i + k = j by dsimp [k]; omega]
    unfold repunit
    rw [hl, Nat.ofDigits_append, List.length_replicate]
  have hpos : 0 < repunit k := by
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [hl]
    simp [repunit, List.replicate_succ, Nat.ofDigits_cons]
  have hdigits : Nat.digits 10 (repunit k) = List.replicate k 1 := by
    apply Nat.digits_ofDigits 10 (by decide)
    · intro d hd
      have he := (List.eq_of_mem_replicate hd : d = 1)
      omega
    · intro h
      simp
  refine ⟨10 ^ i * repunit k, Nat.mul_pos (by positivity) hpos, ?_, ?_⟩
  · simpa [hdecomp] using hmod.dvd'
  · rw [Nat.digits_base_pow_mul (by decide) hpos, hdigits, List.map_append, List.prod_append]
    simp

end OMA.S_oeis_a087304

open OMA.S_oeis_a087304 in
theorem OMA.solution : type_of% @OMA.S_oeis_a087304.main := by
  intro n hn
  obtain ⟨r, hrPos, hrDvd, hrProd⟩ := positive_binary_multiple n hn
  let l := (Nat.digits 10 r).length
  let m := r + 10 ^ l * n
  have hrBound : r < 10 ^ l := Nat.lt_base_pow_length_digits (by decide)
  have hbase : 10 ^ l ≤ 10 ^ l * n := Nat.le_mul_of_pos_right _ hn
  have hlo : 10 ^ l * n < m := by dsimp [m]; omega
  have hhi : m < 10 ^ (l + 1) * n := by
    rw [pow_succ, show 10 ^ l * 10 * n = 10 * (10 ^ l * n) by ac_rfl]
    dsimp [m]
    omega
  refine ⟨m, lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (by positivity)) hlo,
    Nat.dvd_add hrDvd (dvd_mul_left n _), ?_, ?_⟩
  · intro k
    by_cases hk : k ≤ l
    · exact ne_of_gt (lt_of_le_of_lt
        (Nat.mul_le_mul_right n (Nat.pow_le_pow_right (by decide) hk)) hlo)
    · exact ne_of_lt (lt_of_lt_of_le hhi
        (Nat.mul_le_mul_right n (Nat.pow_le_pow_right (by decide) (by omega))))
  · unfold digitProduct
    change ((Nat.digits 10 (r + 10 ^ l * n)).map fun d => if d = 0 then 1 else d).prod = _
    rw [← Nat.digits_append_digits (by decide : 0 < 10), List.map_append,
      List.prod_append, hrProd, one_mul]
