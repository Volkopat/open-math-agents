import OMAStatements.S_oeis_a113573
import Mathlib

/-!
# A113573: the digit-pattern multiple of `n` exists

Write the `n`-digit number with leading digit 1, and at each later position `r`
the digit 2 or 3 when `r` is prime, 8 or 9 otherwise. Choosing the larger digit at
exponent `e` adds `10 ^ e`, so it suffices to hit every residue modulo `n` with
sums of distinct powers `10 ^ e`, `e < n - 1`.

For `n = 2 ^ a * c` with `c` odd and prime to 5: the low exponents `e < a` fix the
residue modulo `2 ^ a` (parity induction), and the exponents `a ≤ e < n - 1`, which
are multiples of `2 ^ a` and units modulo `c`, fix the residue modulo `c`: adding a
unit to a proper subset of `ZMod c` always produces a new element, so `c - 1` of them
reach everything. The case `n = 5` is the explicit witness 12245.
-/

namespace OMA.P_oeis_a113573

open Finset

/-- Low digits: the last `a` digits can fix the residue modulo `2 ^ a`. -/
theorem low (a X : ℕ) : ∃ T ⊆ range a, 2 ^ a ∣ X + ∑ e ∈ T, 10 ^ e := by
  induction a with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ a ih =>
    obtain ⟨T, hT, q, hq⟩ := ih
    rcases Nat.even_or_odd q with hq2 | hq2
    · obtain ⟨r, hr⟩ := hq2
      refine ⟨T, hT.trans (range_subset_range.2 (Nat.le_succ a)), ⟨r, ?_⟩⟩
      rw [hq, hr, pow_succ]; ring
    · have ha : a ∉ T := fun h => by simpa using hT h
      refine ⟨insert a T, ?_, ?_⟩
      · intro e he
        rcases mem_insert.1 he with rfl | he
        · simp
        · have := hT he; simp at this ⊢; omega
      · rw [sum_insert ha]
        obtain ⟨r, hr⟩ : Even (q + 5 ^ a) := Odd.add_odd hq2 (Odd.pow (by decide))
        refine ⟨r, ?_⟩
        have h10 : (10 : ℕ) ^ a = 2 ^ a * 5 ^ a := by rw [← mul_pow]; norm_num
        calc X + (10 ^ a + ∑ e ∈ T, 10 ^ e) = (X + ∑ e ∈ T, 10 ^ e) + 10 ^ a := by ring
          _ = 2 ^ a * (q + 5 ^ a) := by rw [hq, h10]; ring
          _ = 2 ^ (a + 1) * r := by rw [hr, pow_succ]; ring

/-- A set closed under adding a unit is everything. -/
theorem closed_univ {c : ℕ} [NeZero c] (A : Finset (ZMod c)) (y0 : ZMod c) (hy0 : y0 ∈ A)
    (u : ZMod c) (hu : IsUnit u) (hA : ∀ y ∈ A, y + u ∈ A) : A = univ := by
  obtain ⟨U, rfl⟩ := hu
  have hk : ∀ k : ℕ, y0 + (k : ZMod c) * U ∈ A := by
    intro k
    induction k with
    | zero => simpa using hy0
    | succ k ih =>
      have := hA _ ih
      push_cast
      convert this using 1; ring
  apply eq_univ_of_forall
  intro z
  have := hk ((z - y0) * (U⁻¹ : (ZMod c)ˣ) : ZMod c).val
  rw [ZMod.natCast_zmod_val] at this
  convert this using 1
  rw [mul_assoc, Units.inv_mul, mul_one]; ring

/-- The residues mod `c` of the sums `∑ e ∈ T, 10 ^ e` for `T ⊆ E`. -/
noncomputable def sums (c : ℕ) (E : Finset ℕ) : Finset (ZMod c) :=
  E.powerset.image (fun T => ((∑ e ∈ T, 10 ^ e : ℕ) : ZMod c))

theorem sums_card (c : ℕ) [NeZero c] (hc : Nat.Coprime 10 c) (E : Finset ℕ) :
    min c (E.card + 1) ≤ (sums c E).card := by
  induction E using Finset.induction_on with
  | empty => simp [sums]
  | insert x E hx ih =>
    have hsub : sums c E ⊆ sums c (insert x E) := by
      intro y hy
      simp only [sums, mem_image, mem_powerset] at hy ⊢
      obtain ⟨T, hT, rfl⟩ := hy
      exact ⟨T, hT.trans (subset_insert x E), rfl⟩
    have hshift : ∀ y ∈ sums c E, y + ((10 : ZMod c) ^ x) ∈ sums c (insert x E) := by
      intro y hy
      simp only [sums, mem_image, mem_powerset] at hy ⊢
      obtain ⟨T, hT, rfl⟩ := hy
      have hxT : x ∉ T := fun h => hx (hT h)
      refine ⟨insert x T, insert_subset_insert x hT, ?_⟩
      rw [sum_insert hxT]; push_cast; ring
    rw [card_insert_of_notMem hx]
    by_cases hall : sums c E = univ
    · have h1 : (sums c (insert x E)) = univ := eq_univ_of_forall fun z => hsub (hall ▸ mem_univ z)
      rw [h1, card_univ, ZMod.card]; exact min_le_left _ _
    · have hne : ∃ y ∈ sums c E, y + (10 : ZMod c) ^ x ∉ sums c E := by
        by_contra hcon
        push_neg at hcon
        apply hall
        refine closed_univ _ 0 ?_ _ ?_ hcon
        · simp only [sums, mem_image, mem_powerset]
          exact ⟨∅, empty_subset _, by simp⟩
        · have : IsUnit (((10 ^ x : ℕ) : ZMod c)) :=
            (ZMod.isUnit_iff_coprime _ _).2 (Nat.Coprime.pow_left x hc)
          simpa using this
      obtain ⟨y, hy, hy'⟩ := hne
      have hlt : (sums c E).card < (sums c (insert x E)).card := by
        apply card_lt_card
        rw [ssubset_iff_of_subset hsub]
        exact ⟨_, hshift y hy, hy'⟩
      omega

/-- High digits: enough exponents fix any residue modulo `c` coprime to `10`. -/
theorem high (c : ℕ) (hc0 : c ≠ 0) (hc : Nat.Coprime 10 c) (E : Finset ℕ) (hE : c ≤ E.card + 1)
    (X : ℕ) : ∃ T ⊆ E, c ∣ X + ∑ e ∈ T, 10 ^ e := by
  have : NeZero c := ⟨hc0⟩
  have hcard := sums_card c hc E
  have hu : sums c E = univ := by
    apply eq_univ_of_card
    rw [ZMod.card]
    exact le_antisymm (by simpa [ZMod.card] using card_le_univ (sums c E))
      (by omega)
  have hmem : (-(X : ZMod c)) ∈ sums c E := hu ▸ mem_univ _
  simp only [sums, mem_image, mem_powerset] at hmem
  obtain ⟨T, hT, hTX⟩ := hmem
  refine ⟨T, hT, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast at hTX ⊢
  rw [hTX]; ring


/-- The digit at exponent `e` (position `n - e` from the left). -/
def dig (n : ℕ) (T : Finset ℕ) (e : ℕ) : ℕ :=
  if e = n - 1 then 1 else (if (n - e).Prime then 2 else 8) + (if e ∈ T then 1 else 0)

theorem ofDigits_map_range (f : ℕ → ℕ) (n : ℕ) :
    Nat.ofDigits 10 ((List.range n).map f) = ∑ e ∈ range n, f e * 10 ^ e := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, ih, sum_range_succ]
    simp [Nat.ofDigits_singleton]; ring

theorem dig_lt (n : ℕ) (T : Finset ℕ) (e : ℕ) : dig n T e < 10 := by
  unfold dig; split_ifs <;> norm_num

theorem digits_eq (n : ℕ) (hn : 1 ≤ n) (T : Finset ℕ) :
    Nat.digits 10 (Nat.ofDigits 10 ((List.range n).map (dig n T))) =
      (List.range n).map (dig n T) := by
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨e, _, rfl⟩ := hl
    exact dig_lt n T e
  · intro h
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp [List.range_succ, dig]

theorem rev_getD (f : ℕ → ℕ) (n i : ℕ) (hi : i < n) :
    ((List.range n).map f).reverse.getD i 0 = f (n - 1 - i) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [List.getElem_reverse]

theorem good (n : ℕ) (hn : 1 ≤ n) (T : Finset ℕ) :
    OMA.S_oeis_a113573.GoodDigits n (Nat.ofDigits 10 ((List.range n).map (dig n T))) := by
  unfold OMA.S_oeis_a113573.GoodDigits
  rw [digits_eq n hn T]
  refine ⟨by simp, ?_⟩
  intro r hr1 hrn
  dsimp only
  rw [rev_getD _ _ _ (by omega)]
  have e1 : n - 1 - (r - 1) = n - r := by omega
  rw [e1]
  rcases Nat.lt_or_ge r 2 with h | h
  · have hr : r = 1 := by omega
    subst hr
    simp [dig]
  · have hne : n - r ≠ n - 1 := by omega
    have hr : n - (n - r) = r := by omega
    simp only [dig, hne, hr, ↓reduceIte]
    refine ⟨fun h1 => by omega, fun hp => ?_, fun _ hp => ?_⟩
    · simp only [hp, ↓reduceIte]; split_ifs <;> norm_num
    · simp only [hp, ↓reduceIte]; split_ifs <;> norm_num

theorem value (n : ℕ) (T : Finset ℕ) (hT : T ⊆ range (n - 1)) :
    Nat.ofDigits 10 ((List.range n).map (dig n T)) =
      Nat.ofDigits 10 ((List.range n).map (dig n ∅)) + ∑ e ∈ T, 10 ^ e := by
  rw [ofDigits_map_range, ofDigits_map_range]
  have hT' : T ⊆ range n := hT.trans (range_subset_range.2 (Nat.sub_le n 1))
  have hs : ∑ e ∈ T, 10 ^ e = ∑ e ∈ range n, (if e ∈ T then 10 ^ e else 0) := by
    rw [sum_ite_mem, inter_eq_right.2 hT']
  rw [hs, ← sum_add_distrib]
  apply sum_congr rfl
  intro e he
  by_cases h1 : e = n - 1
  · subst h1
    have hnT : n - 1 ∉ T := fun h => by have := hT h; simp at this
    simp [dig, hnT]
  · by_cases h2 : e ∈ T <;> simp [dig, h1, h2] <;> split_ifs <;> ring

theorem key (n : ℕ) (hn : 1 ≤ n) (h5 : ¬ 5 ∣ n) (X : ℕ) :
    ∃ T ⊆ range (n - 1), n ∣ X + ∑ e ∈ T, 10 ^ e := by
  obtain ⟨a, c, hc, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (n := n) (by omega)
  have hc2 : c % 2 = 1 := Nat.odd_iff.1 hc
  have hc0 : c ≠ 0 := by omega
  have h2c : Nat.Coprime 2 c :=
    (Nat.prime_two.coprime_iff_not_dvd).2 (by omega)
  have h5c : Nat.Coprime 5 c :=
    (Nat.prime_five.coprime_iff_not_dvd).2 (fun h => h5 (Dvd.dvd.mul_left h _))
  have hcop : Nat.Coprime 10 c := by
    have := Nat.coprime_mul_iff_left.2 ⟨h2c, h5c⟩
    simpa using this
  have ha : a < 2 ^ a := Nat.lt_two_pow_self
  have hn' : a + c ≤ 2 ^ a * c := by
    have h3 : (a + 1) * c ≤ 2 ^ a * c := Nat.mul_le_mul_right c ha
    have h4 : a ≤ a * c := Nat.le_mul_of_pos_right a (by omega)
    rw [add_mul, one_mul] at h3
    linarith
  obtain ⟨T1, hT1, h1⟩ := low a X
  obtain ⟨T2, hT2, h2⟩ := high c hc0 hcop (Ico a (2 ^ a * c - 1)) (by simp; omega)
    (X + ∑ e ∈ T1, 10 ^ e)
  have hdisj : Disjoint T1 T2 := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    have i1 := hT1 he1
    have i2 := hT2 he2
    simp at i1 i2
    omega
  refine ⟨T1 ∪ T2, ?_, ?_⟩
  · intro e he
    rcases mem_union.1 he with he | he
    · have := hT1 he; simp at this ⊢; omega
    · have := hT2 he; simp at this ⊢; omega
  · rw [sum_union hdisj, ← add_assoc]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (Nat.Coprime.pow_left a h2c)
    · apply dvd_add h1
      apply dvd_sum
      intro e he
      have := hT2 he
      simp at this
      have h10 : (10 : ℕ) ^ e = 2 ^ e * 5 ^ e := by rw [← mul_pow]; norm_num
      rw [h10]
      exact (pow_dvd_pow 2 this.1).trans (dvd_mul_right _ _)
    · exact h2

theorem solution_aux : ∀ n : ℕ, 1 ≤ n → (¬ ∃ t, 1 < t ∧ n = 5 * t) →
    ∃ m, n ∣ m ∧ OMA.S_oeis_a113573.GoodDigits n m := by
  intro n hn h
  by_cases h5n : n = 5
  · subst h5n
    refine ⟨12245, by norm_num, ?_⟩
    have hd : Nat.digits 10 12245 = [5, 4, 2, 2, 1] := by norm_num
    unfold OMA.S_oeis_a113573.GoodDigits
    rw [hd]
    refine ⟨rfl, ?_⟩
    intro r hr1 hr5
    interval_cases r <;> norm_num
  · have h5 : ¬ 5 ∣ n := by
      rintro ⟨t, rfl⟩
      apply h
      refine ⟨t, ?_, rfl⟩
      omega
    obtain ⟨T, hT, hdvd⟩ := key n hn h5 (Nat.ofDigits 10 ((List.range n).map (dig n ∅)))
    exact ⟨_, (value n T hT) ▸ hdvd, good n hn T⟩

end OMA.P_oeis_a113573

theorem OMA.solution : type_of% @OMA.S_oeis_a113573.main := OMA.P_oeis_a113573.solution_aux
