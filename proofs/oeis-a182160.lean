import OMAStatements.S_oeis_a182160
import Mathlib

/-!
# A182160: every decimal digit-power orbit eventually repeats

Write `f` for the map "sum of the `e`-th powers of the decimal digits", `C = 9 ^ e`, and `L`
for the number of digits of `v`.  Every digit is at most `9`, so `f v ≤ C * L`.

* If `L < 10 C` this gives `f v ≤ 10 C²`.
* If `L ≥ 10 C` then `10 C ≤ 5 ^ L` and `L ≤ 2 ^ L`, so `10 C L ≤ 10 ^ L ≤ 10 v`, i.e. `f v ≤ v`.

Hence `f v ≤ max v (10 C²)` always, the whole orbit of `s` stays below `M = max s (10 C²)`,
and among the first `M + 2` iterates two must coincide by the pigeonhole principle.
-/

namespace OMA.S_oeis_a182160

/-- Each digit contributes at most `9 ^ e`. -/
lemma digitPowerSum_le (e v : ℕ) :
    digitPowerSum e v ≤ 9 ^ e * (Nat.digits 10 v).length := by
  unfold digitPowerSum
  have h : ∀ x ∈ (Nat.digits 10 v).map (fun d => d ^ e), x ≤ 9 ^ e := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    exact Nat.pow_le_pow_left (Nat.le_of_lt_succ (Nat.digits_lt_base (by norm_num) hd)) e
  have := List.sum_le_card_nsmul _ _ h
  simpa [mul_comm] using this

/-- The map never exceeds `max v (10 C²)`. -/
lemma bound (e v : ℕ) : digitPowerSum e v ≤ max v (9 ^ e * (10 * 9 ^ e)) := by
  have hf := digitPowerSum_le e v
  have hCpos : 0 < 9 ^ e := by positivity
  rcases lt_or_ge (Nat.digits 10 v).length (10 * 9 ^ e) with h | h
  · exact le_max_of_le_right (hf.trans (Nat.mul_le_mul_left _ h.le))
  · have hv : v ≠ 0 := by
      rintro rfl
      simp at h
    have h10 : 10 ^ (Nat.digits 10 v).length ≤ 10 * v :=
      Nat.base_pow_length_digits_le 10 v (by norm_num) hv
    have h5 : 10 * 9 ^ e ≤ 5 ^ (Nat.digits 10 v).length :=
      h.trans (Nat.lt_pow_self (by norm_num)).le
    have h2 : (Nat.digits 10 v).length ≤ 2 ^ (Nat.digits 10 v).length :=
      Nat.lt_two_pow_self.le
    have hmul : 10 * (9 ^ e * (Nat.digits 10 v).length) ≤ 10 * v := by
      calc 10 * (9 ^ e * (Nat.digits 10 v).length)
          = (10 * 9 ^ e) * (Nat.digits 10 v).length := by ring
        _ ≤ 5 ^ (Nat.digits 10 v).length * 2 ^ (Nat.digits 10 v).length :=
            Nat.mul_le_mul h5 h2
        _ = 10 ^ (Nat.digits 10 v).length := by rw [← Nat.mul_pow]
        _ ≤ 10 * v := h10
    exact le_max_of_le_left (hf.trans (by omega))

/-- The whole orbit of `s` stays below `max s (10 C²)`. -/
lemma orbit_le (e s : ℕ) (i : ℕ) :
    (digitPowerSum e)^[i] s ≤ max s (9 ^ e * (10 * 9 ^ e)) := by
  induction i with
  | zero => exact le_max_left _ _
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact (bound e _).trans (max_le ih (le_max_right _ _))

end OMA.S_oeis_a182160

open OMA.S_oeis_a182160 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182160.main := by
  intro e _ s
  set M := max s (9 ^ e * (10 * 9 ^ e)) with hM
  -- pigeonhole: `M + 2` iterates, all in `{0, …, M}`
  obtain ⟨i, -, j, -, hij, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (M + 2)) (t := Finset.range (M + 1))
      (f := fun i => (digitPowerSum e)^[i] s) (by simp)
      (fun i _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (orbit_le e s i)))
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact ⟨i, j, h, heq⟩
  · exact ⟨j, i, h, heq.symm⟩
