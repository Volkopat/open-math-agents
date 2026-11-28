import OMAStatements.S_oeis_a113572
import Mathlib

open Finset OMA.S_oeis_a113572

/- Choose a base digit that may be increased by one at every nonleading position. -/
private def digitBaseAt (n i : ℕ) : ℕ :=
  if i+1=n then 1 else if (n-i).Prime then 2 else 8

private def digitBase (n : ℕ) : ℕ := ∑ i ∈ range n, digitBaseAt n i * 10^i

private lemma oma_of_digits_range (f : ℕ → ℕ) (n : ℕ) :
    Nat.ofDigits 10 ((List.range n).map f) = ∑ i ∈ range n, f i * 10^i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, Nat.ofDigits_append, sum_range_succ, ih]
    simp [mul_comm]

private lemma oma_digits_realization {n : ℕ} (hn : 1 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ range (n-1)) : GoodDigits n (digitBase n + ∑ i ∈ S, 10^i) := by
  let f (i : ℕ) := digitBaseAt n i + if i ∈ S then 1 else 0
  let L := (List.range n).map f
  have hf (i : ℕ) : 0 < f i ∧ f i < 10 := by
    simp only [f, digitBaseAt]
    split_ifs <;> decide
  have hmem {x : ℕ} (hx : x ∈ L) : 0 < x ∧ x < 10 := by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hf i
  have hfilter : (range n).filter (· ∈ S) = S := by
    ext i
    simp only [mem_filter, mem_range]
    exact ⟨And.right, fun hi => ⟨by have := mem_range.mp (hS hi); omega, hi⟩⟩
  have hval : Nat.ofDigits 10 L = digitBase n + ∑ i ∈ S, 10^i := by
    rw [oma_of_digits_range]
    simp only [f, add_mul, sum_add_distrib, digitBase]
    congr 1
    simp_rw [ite_mul, one_mul, zero_mul]
    rw [← sum_filter, hfilter]
  have digits : Nat.digits 10 (digitBase n + ∑ i ∈ S, 10^i) = L := by
    rw [← hval]
    exact Nat.digits_ofDigits 10 (by decide) _ (fun _ h => (hmem h).2)
      (fun h => (hmem (List.getLast_mem h)).1.ne')
  unfold GoodDigits
  rw [digits]
  have hlen : L.length = n := by simp [L]
  refine ⟨hlen, ?_⟩
  intro r hr hrn
  have hget : L.reverse.getD (r-1) 0 = f (n-r) := by
    rw [List.getD_eq_getElem _ _ (by simp [hlen]; omega), List.getElem_reverse]
    simp [L, List.getElem_map, show n-1-(r-1) = n-r by omega]
  rw [hget]
  rcases eq_or_lt_of_le hr with rfl | hr₂
  · have hs : n-1 ∉ S := fun h => (lt_irrefl _ (mem_range.mp (hS h)))
    simp [f, digitBaseAt, show n-1+1=n by omega, hs]
  · have hl : n-r+1 ≠ n := by omega
    have hr' : n-(n-r) = r := by omega
    simp only [f, digitBaseAt, if_neg hl, hr']
    have hr₂' : 2 ≤ r := by omega
    by_cases hp : r.Prime <;> by_cases hs : n-r ∈ S <;>
      simp [hp, hs, hr₂.ne', hr₂', Nat.prime_two, Nat.prime_three] <;> decide

private lemma oma_good_digits_five : ∃ m : ℕ, 5 ∣ m ∧ GoodDigits 5 m := by
  refine ⟨12285, by decide, by decide, ?_⟩
  intro r hr hr'
  interval_cases r <;> decide

/- The v lowest positions give divisibility by the full 2-part of n, one bit at a time. -/
private lemma digit_two_lift (v B : ℕ) :
    ∃ S ⊆ range v, 2 ^ v ∣ B + ∑ i ∈ S, 10 ^ i := by
  induction v with
  | zero => exact ⟨∅, by simp, by simp⟩
  | succ v ih =>
    obtain ⟨S, hS, t, ht⟩ := ih
    have hS' : S ⊆ range (v+1) := hS.trans (range_mono (by omega))
    by_cases he : 2 ∣ t
    · refine ⟨S, hS', ?_⟩
      rw [ht, pow_succ]
      exact Nat.mul_dvd_mul_left _ he
    · have hv : v ∉ S := fun h => (Nat.lt_irrefl v) (mem_range.mp (hS h))
      have h5 : 5 ^ v % 2 = 1 := by
        simpa [Nat.ModEq] using (show Nat.ModEq 2 5 1 by decide).pow v
      have even_sum : 2 ∣ 5^v + t := by omega
      refine ⟨insert v S, insert_subset (by simp) hS', ?_⟩
      rw [sum_insert hv, Nat.add_left_comm B, ht, show (10:ℕ)^v = 2^v * 5^v by rw [← mul_pow]; rfl,
        ← Nat.mul_add, pow_succ]
      exact Nat.mul_dvd_mul_left _ even_sum

private lemma digit_position_bound {v q n : ℕ} (hq : 0 < q) (hn : n = 2^v*q) :
    v + (q-1) ≤ n-1 := by
  have hpow := Nat.lt_two_pow_self (n := v)
  have hmul : (v+1)*q ≤ 2^v*q := Nat.mul_le_mul_right q hpow
  have hvq : v ≤ v*q := by simpa using Nat.mul_le_mul_left v hq
  rw [Nat.add_mul, one_mul] at hmul
  omega

/- The optional increments are additive generators modulo every q coprime to ten. Each new position increases the number of reachable residues until all are reached. -/
private theorem oma_decimal_odd_cover {q v L : ℕ} (hc : q.Coprime 10)
    (hL : q - 1 ≤ L) (hq : 0 < q) (r : ZMod q) :
    ∃ S ⊆ range L, (∑ i ∈ S, (10 : ZMod q) ^ (v + i)) = r := by
  classical
  let _ : NeZero q := ⟨hq.ne'⟩
  let w (i : ℕ) : ZMod q := 10 ^ (v + i)
  let R (l : ℕ) : Finset (ZMod q) := (range l).powerset.image (fun S => ∑ i ∈ S, w i)
  have memR {l : ℕ} {a : ZMod q} : a ∈ R l ↔ ∃ S ⊆ range l, (∑ i ∈ S, w i) = a := by
    simp [R]
  have zeroR (l : ℕ) : 0 ∈ R l := memR.mpr ⟨∅, empty_subset _, by simp⟩
  have monoR (l : ℕ) : R l ⊆ R (l + 1) := by
    intro a ha
    obtain ⟨S, hS, hs⟩ := memR.mp ha
    exact memR.mpr ⟨S, hS.trans (range_mono (by omega)), hs⟩
  have stepR (l : ℕ) {a : ZMod q} (ha : a ∈ R l) : a + w l ∈ R (l + 1) := by
    obtain ⟨S, hS, rfl⟩ := memR.mp ha
    have hl : l ∉ S := fun h => (Nat.lt_irrefl l) (mem_range.mp (hS h))
    refine memR.mpr ⟨insert l S, insert_subset (mem_range.mpr (by omega))
      (hS.trans (range_mono (by omega))), ?_⟩
    rw [sum_insert hl, add_comm]
  -- If no new residue appears, the old residues contain every multiple of the new weight.
  have full (l : ℕ) (he : R (l + 1) = R l) : R l = univ := by
    apply eq_univ_of_forall
    intro y
    obtain ⟨u, hu⟩ : IsUnit (w l) := ((ZMod.isUnit_iff_coprime 10 q).mpr hc.symm).pow _
    have hmul (k : ℕ) : (k : ZMod q) * w l ∈ R l := by
      induction k with
      | zero => simpa using zeroR l
      | succ k ih => simpa [he, Nat.cast_succ, add_mul] using stepR l ih
    have h := hmul (y * (↑u⁻¹ : ZMod q)).val
    simpa [hu.symm, mul_assoc] using h
  have lower (l : ℕ) : min (l + 1) q ≤ (R l).card := by
    induction l with
    | zero =>
      exact (min_le_left _ _).trans (card_pos.mpr ⟨0, zeroR 0⟩)
    | succ l ih =>
      by_cases he : R (l + 1) = R l
      · simp [he, full l he, ZMod.card]
      · have hlt := card_lt_card (ssubset_of_subset_of_ne (monoR l) (Ne.symm he))
        omega
  have hcard : Fintype.card (ZMod q) ≤ (R L).card := by
    simpa [ZMod.card, min_eq_right (show q ≤ L + 1 by omega)] using lower L
  have hall : R L = univ := eq_of_subset_of_card_le (subset_univ _) (by simpa using hcard)
  exact memR.mp (hall ▸ mem_univ r)

/- The positions correcting the odd part are disjoint from the low positions and preserve divisibility by the 2-part. -/
private lemma digit_choose_adjustments
    (low : ∀ v B : ℕ, ∃ S ⊆ range v, 2^v ∣ B + ∑ i ∈ S, 10^i)
    (cover : ∀ {q v L : ℕ}, q.Coprime 10 → q-1 ≤ L → 0<q → ∀ r : ZMod q,
      ∃ S ⊆ range L, (∑ i ∈ S, (10 : ZMod q)^(v+i)) = r)
    (bound : ∀ {v q n : ℕ}, 0 < q → n=2^v*q → v+(q-1) ≤ n-1)
    (n B : ℕ) (hn : 0<n) (hn5 : ¬ 5 ∣ n) :
    ∃ S ⊆ range (n-1), n ∣ B + ∑ i ∈ S, 10^i := by
  let v := n.factorization 2
  let q := n/2^v
  have hq : 0 < q := Nat.ordCompl_pos 2 hn.ne'
  have hnq : 2^v*q = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have h2q : Nat.Coprime 2 q := Nat.coprime_ordCompl Nat.prime_two hn.ne'
  have h5q : ¬ 5 ∣ q := fun h => hn5 (h.trans (Nat.ordCompl_dvd n 2))
  have hq10 : q.Coprime 10 := h2q.symm.mul_right ((Nat.prime_five.coprime_iff_not_dvd.mpr h5q).symm)
  have cap := bound hq hnq.symm
  obtain ⟨S,hS,hS2⟩ := low v B
  let C := B + ∑ i ∈ S, 10^i
  obtain ⟨A,hA,hAq⟩ := cover (v := v) hq10 (le_refl (q-1)) hq (-(C : ZMod q))
  let addv : ℕ ↪ ℕ := ⟨fun i => v+i,fun _ _ h => Nat.add_left_cancel h⟩
  let T := A.map addv
  have hTq : ((∑ i ∈ T, 10^i : ℕ) : ZMod q) = -(C : ZMod q) := by
    push_cast
    rw [show T = A.map addv from rfl, Finset.sum_map]
    exact hAq
  have hT2 : 2^v ∣ ∑ i ∈ T, 10^i := by
    apply Finset.dvd_sum
    intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_map.mp hi
    change 2^v ∣ 10^(v+j)
    rw [pow_add]
    exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (by decide : 2 ∣ 10) _) _
  have hdis : Disjoint S T := by
    apply disjoint_left.mpr
    intro i hi ht
    have hilt := mem_range.mp (hS hi)
    obtain ⟨j,hj,rfl⟩ := mem_map.mp ht
    change v+j<v at hilt
    omega
  refine ⟨S ∪ T, ?_, ?_⟩
  · intro i hi
    apply mem_range.mpr
    rcases mem_union.mp hi with h | h
    · have := mem_range.mp (hS h); omega
    · obtain ⟨j,hj,rfl⟩ := mem_map.mp h
      have := mem_range.mp (hA hj)
      change v+j<n-1
      omega
  · rw [sum_union hdis, ←add_assoc, ←hnq]
    apply (h2q.pow_left v).mul_dvd_of_dvd_of_dvd (dvd_add hS2 hT2)
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    change ((C + ∑ i ∈ T, 10^i : ℕ) : ZMod q) = _
    rw [Nat.cast_add, hTq, add_neg_cancel]

theorem OMA.solution : type_of% @OMA.S_oeis_a113572.main := by
  intro n hn h5
  by_cases hd : 5 ∣ n
  · obtain ⟨t, rfl⟩ := hd
    have ht : t ≤ 1 := by
      by_contra! h
      exact h5 ⟨t,h,rfl⟩
    have : t = 1 := by omega
    subst t
    exact oma_good_digits_five
  · obtain ⟨S,hS,hdiv⟩ := digit_choose_adjustments digit_two_lift oma_decimal_odd_cover
      digit_position_bound n (digitBase n) hn hd
    exact ⟨_,hdiv,oma_digits_realization hn S hS⟩
