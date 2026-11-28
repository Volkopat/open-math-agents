import OMAStatements.S_oeis_a385970

namespace OMA.S_oeis_a385970

open Finset

private def selfSum (s : Finset ℕ) := ∑ i ∈ s, (i+2)^(i+2)

private theorem selfBound {s : Finset ℕ} {m : ℕ} (hs : s ⊆ range m) :
    selfSum s ≤ m*(m+1)^(m+1) := by
  calc
    _ ≤ ∑ _i ∈ s, (m+1)^(m+1) := by
      apply sum_le_sum
      intro i hi
      have h : i < m := mem_range.mp (hs hi)
      exact (Nat.pow_le_pow_left (by omega : i+2 ≤ m+1) _).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    _ = s.card*(m+1)^(m+1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by simpa using card_le_card hs)

/-- Each self-power exceeds the sum of all smaller self-powers, so all
their finite subset sums are distinct. -/
private theorem selfInj : Function.Injective selfSum := by
  have hmono : StrictMono (fun s : Colex (Finset ℕ) => selfSum (ofColex s)) := by
    intro s t hst
    obtain ⟨i, hit, his, hmax⟩ := Finset.Colex.lt_iff_exists_forall_lt.mp hst
    unfold selfSum
    rw [← sum_sdiff_lt_sum_sdiff]
    have hsub : ofColex s \ ofColex t ⊆ range i := by
      intro j hj
      obtain ⟨hjs, hjt⟩ := mem_sdiff.mp hj
      exact mem_range.mpr (hmax j hjs hjt)
    calc
      _ ≤ i*(i+1)^(i+1) := selfBound hsub
      _ < (i+2)*(i+2)^(i+1) := by
        have hp : 0 < (i+1)^(i+1) := by positivity
        exact (Nat.mul_lt_mul_of_pos_right (by omega : i < i+2) hp).trans_le
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
      _ = (i+2)^(i+2) := (pow_succ' (i+2) (i+1)).symm
      _ ≤ _ := single_le_sum (f := fun j : ℕ => (j+2)^(j+2))
        (fun _ _ => Nat.zero_le _) (mem_sdiff.mpr ⟨hit,his⟩)
  intro s t he
  exact toColex.injective (hmono.injective (a₁ := toColex s) (a₂ := toColex t) he)

private theorem selfRep {s : Finset ℕ} (hs : s.Nonempty) : ∃ xs, Represents (selfSum s) xs := by
  classical
  let xs := s.toList.map (fun i => (i+2,i+2))
  refine ⟨xs, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [xs] using hs.ne_empty
  · simp only [xs, List.map_map]
    exact s.nodup_toList.map (by intro a b h; change a+2=b+2 at h; omega)
  · intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    simp
  · simp [xs, List.map_map, Function.comp_def]
  · simp [xs, powerSum, List.map_map, Function.comp_def, selfSum]

private def letters (B : ℕ) : Finset ℕ :=
  insert 0 (((range B) ×ˢ (range B)).image (fun p => p.1 ^ p.2))

private def shortSums (B : ℕ) : ℕ → Finset ℕ
  | 0 => {0}
  | k+1 => (letters B ×ˢ shortSums B k).image (fun p => p.1 + p.2)

private theorem lettersBound (B : ℕ) : (letters B).card ≤ B^2+1 := by
  calc
    _ ≤ _ := card_insert_le _ _
    _ ≤ ((range B) ×ˢ (range B)).card+1 := Nat.add_le_add_right card_image_le _
    _ = _ := by simp [sq]

private theorem shortBound (B k : ℕ) : (shortSums B k).card ≤ (B^2+1)^k := by
  induction k with
  | zero => simp [shortSums]
  | succ k ih =>
    change (Finset.image _ _).card ≤ _
    apply card_image_le.trans
    rw [card_product, pow_succ']
    exact Nat.mul_le_mul (lettersBound B) ih

private theorem zeroShort (B k : ℕ) : 0 ∈ shortSums B k := by
  induction k with
  | zero => simp [shortSums]
  | succ k ih =>
    exact mem_image.mpr ⟨(0,0), mem_product.mpr ⟨mem_insert_self .., ih⟩, rfl⟩

private theorem listShort {B k : ℕ} {xs : List (ℕ × ℕ)} (hk : xs.length ≤ k)
    (hb : ∀ p ∈ xs, p.1 < B ∧ p.2 < B) : powerSum xs ∈ shortSums B k := by
  induction k generalizing xs with
  | zero => have : xs = [] := List.length_eq_zero_iff.mp (by omega); subst xs; exact zeroShort B 0
  | succ k ih =>
    cases xs with
    | nil => exact zeroShort B _
    | cons p xs =>
      have hp := hb p (by simp)
      have hlet : p.1^p.2 ∈ letters B := mem_insert_of_mem (mem_image.mpr
        ⟨p, mem_product.mpr ⟨mem_range.mpr hp.1, mem_range.mpr hp.2⟩,rfl⟩)
      have hxs := ih (xs := xs) (by simpa using hk) (fun d hd => hb d (List.mem_cons_of_mem _ hd))
      exact mem_image.mpr ⟨(p.1^p.2, powerSum xs), mem_product.mpr ⟨hlet,hxs⟩,rfl⟩

/-- Every base occurs somewhere as an exponent. A representation of a
number below `2^B` therefore uses only pairs of numbers below `B`. -/
private theorem repShort {N B k : ℕ} {xs : List (ℕ × ℕ)} (hN : N < 2^B)
    (hr : Represents N xs) (hk : xs.length ≤ k) : N ∈ shortSums B k := by
  have he (p : ℕ × ℕ) (hp : p ∈ xs) : p.2 < B := by
    have hterm : p.1^p.2 ≤ powerSum xs := List.le_sum_of_mem (List.mem_map_of_mem hp)
    rw [hr.total] at hterm
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      ((Nat.pow_le_pow_left (hr.bases p hp) _).trans_lt (hterm.trans_lt hN))
  rw [← hr.total]
  apply listShort hk
  intro p hp
  have hm : p.1 ∈ xs.map Prod.snd := hr.exponents.mem_iff.mp (List.mem_map_of_mem hp)
  obtain ⟨q,hq,hqp⟩ := List.mem_map.mp hm
  exact ⟨hqp ▸ he q hq, he p hp⟩

private theorem selfSize {m : ℕ} {s : Finset ℕ} (hs : s ⊆ range m) : selfSum s < 2^((m+3)^2) := by
  calc
    _ ≤ m*(m+1)^(m+1) := selfBound hs
    _ ≤ 2^m*(2^(m+1))^(m+1) := Nat.mul_le_mul (Nat.lt_pow_self (by decide)).le
      (Nat.pow_le_pow_left (Nat.lt_pow_self (by decide)).le _)
    _ = 2^(m+(m+1)*(m+1)) := by rw [← pow_mul, ← pow_add]
    _ < _ := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr (by nlinarith)

private theorem enoughSubsets (k : ℕ) : ∃ m : ℕ, (((m+3)^2)^2+1)^k < 2^m := by
  have hlim := tendsto_pow_const_div_const_pow_of_one_lt (4*k) (by norm_num : (1:ℝ) < 2)
  have hev : ∀ᶠ m : ℕ in Filter.atTop, (m:ℝ)^(4*k)/2^m < 1/(17:ℝ)^k :=
    hlim.eventually (gt_mem_nhds (by positivity))
  obtain ⟨m, h, hm⟩ := (hev.and (Filter.eventually_ge_atTop 3)).exists
  have hR : (17:ℝ)^k*(m:ℝ)^(4*k) < 2^m := by
    have h' := (div_lt_div_iff₀ (by positivity : (0:ℝ) < 2^m) (by positivity : (0:ℝ) < 17^k)).mp h
    linarith
  have hnat : (17:ℕ)^k*m^(4*k) < 2^m := by exact_mod_cast hR
  have hb : (((m+3)^2)^2+1) ≤ 17*m^4 := by
    have h1 : m+3 ≤ 2*m := by omega
    have hp := Nat.pow_le_pow_left h1 4
    have hpos : 0 < m^4 := by positivity
    calc
      _ = (m+3)^4+1 := by ring
      _ ≤ (2*m)^4+1 := by omega
      _ ≤ _ := by rw [mul_pow]; omega
  refine ⟨m, (Nat.pow_le_pow_left hb k).trans_lt ?_⟩
  simpa [mul_pow, pow_mul] using hnat

end OMA.S_oeis_a385970

open OMA.S_oeis_a385970 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a385970.main := by
  classical
  intro k
  by_contra! h
  obtain ⟨m, hm⟩ := enoughSubsets k
  let B := (m+3)^2
  have cover : (range m).powerset.image selfSum ⊆ shortSums B k := by
    intro N hN
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hN
    by_cases hse : s.Nonempty
    · obtain ⟨xs,hr,hk⟩ := h (selfSum s) (selfRep hse)
      exact repShort (selfSize (mem_powerset.mp hs)) hr hk
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hse
      subst s
      simpa [selfSum] using zeroShort B k
  have hc := card_le_card cover
  rw [card_image_of_injective _ selfInj, card_powerset, card_range] at hc
  exact hm.not_ge (hc.trans (shortBound B k))
