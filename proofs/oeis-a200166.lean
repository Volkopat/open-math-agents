import OMAStatements.S_oeis_a200166
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Ordered triples for OEIS A200166

We count the triples for each middle entry, then subtract the triples whose
total is zero. Reflection pairs the contributions of positive and negative
middle entries. The resulting parity polynomial gives the coefficients of
the conjectured generating function after multiplying by its denominator.

Source: https://oeis.org/A200166
Credit: @ali-hamdan-007
-/

namespace OMA.S_oeis_a200166

/-- Partition the triples by whether their total is zero. -/
theorem card_split (n : ℕ) : a n + (zeroSet n).card = (baseSet n).card := by
  classical
  unfold a goodSet zeroSet
  simpa using (Finset.card_filter_add_card_filter_not
    (p := fun t : ℤ × ℤ × ℤ => t.1 + t.2.1 + t.2.2 ≠ 0) (s := baseSet n))

/-- With the middle entry fixed, a triple is uniquely specified by its
ordered endpoint pair. Its one remaining restriction rules out a midpoint. -/
private theorem card_at_centre (n : ℕ) (y : ℤ) (hy : y ∈ alphabet n) :
    ((baseSet n).filter fun t => t.2.1 = y).card =
    (((alphabet n).erase y ×ˢ (alphabet n).erase y).filter
      fun p => p.1 + p.2 ≠ 2*y).card := by
  refine Finset.card_bij' (fun t _ => (t.1, t.2.2)) (fun p _ => (p.1, y, p.2)) ?_ ?_ ?_ ?_
  · rintro ⟨x, w, z⟩ h
    simp only [baseSet, Finset.mem_filter, Finset.mem_product, Finset.mem_erase] at h ⊢
    grind
  · rintro ⟨x,z⟩ h
    simp only [baseSet, Finset.mem_filter, Finset.mem_product, Finset.mem_erase] at h ⊢
    grind
  · rintro ⟨x,w,z⟩ h
    have hw : w=y := (Finset.mem_filter.mp h).2
    rw [hw]
  · rintro ⟨x,z⟩ _
    rfl

/-- Each forbidden pair has the unique partner z = 2y − x. -/
private theorem card_midpoint (E : Finset ℤ) (y : ℤ) :
    ((E ×ˢ E).filter fun p => p.1 + p.2 = 2*y).card =
    (E.filter fun x => 2*y-x ∈ E).card := by
  refine Finset.card_bij' (fun p _ => p.1) (fun x _ => (x,2*y-x)) ?_ ?_ ?_ ?_
  · rintro ⟨x,z⟩ h
    obtain ⟨hmem, heq⟩ := Finset.mem_filter.mp h
    obtain ⟨hx,hz⟩ := Finset.mem_product.mp hmem
    have h : 2*y-x=z := by change x+z=2*y at heq; omega
    exact Finset.mem_filter.mpr ⟨hx, h.symm ▸ hz⟩
  · intro x hx
    obtain ⟨hx, hz⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hz⟩, by change x+(2*y-x)=2*y; omega⟩
  · rintro ⟨x,z⟩ h
    have h : x+z=2*y := (Finset.mem_filter.mp h).2
    exact Prod.ext rfl (by change 2*y-x=z; omega)
  · intros
    rfl

theorem base_by_centre (n : ℕ) :
    (baseSet n).card = ∑ y ∈ alphabet n,
      (((alphabet n).erase y).card^2 -
          (((alphabet n).erase y).filter fun x => 2*y-x ∈ (alphabet n).erase y).card) := by
  classical
  have hsub : (baseSet n : Set (ℤ × ℤ × ℤ)).MapsTo (fun t => t.2.1) (alphabet n) := by
    rintro ⟨x,y,z⟩ ht
    exact (Finset.mem_product.mp (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).2).1
  rw [Finset.card_eq_sum_card_fiberwise hsub]
  apply Finset.sum_congr rfl
  intro y hy
  rw [card_at_centre n y hy]
  let E := (alphabet n).erase y
  have h := Finset.card_filter_add_card_filter_not
    (s := E ×ˢ E) (fun p : ℤ × ℤ => p.1+p.2 ≠ 2*y)
  simp only [not_not, Finset.card_product] at h
  rw [card_midpoint E y] at h
  change _ = E.card^2 - (E.filter fun x => 2*y-x ∈ E).card
  rw [pow_two]
  exact Nat.eq_sub_of_add_eq h

/-- Pair the positive and negative letters of Hardin's alphabet. -/
theorem sum_alphabet_even (f : ℤ → ℤ) (hf : ∀ y : ℤ, f (-y) = f y) (n : ℕ) :
    (∑ y ∈ alphabet n, f y) = 2 * ∑ i ∈ Finset.range n, f ((i:ℤ)+1) := by
  induction n with
  | zero => simp [alphabet]
  | succ n ih =>
    have hset : alphabet (n+1) =
        insert (-((n:ℤ)+1)) (insert ((n:ℤ)+1) (alphabet n)) := by
      ext v
      simp only [alphabet, Finset.mem_erase, Finset.mem_Icc, Finset.mem_insert, Nat.cast_succ]
      omega
    have hn₁ : (n:ℤ)+1 ∉ alphabet n := by
      simp only [alphabet, Finset.mem_erase, Finset.mem_Icc]
      omega
    have hn₂ : -((n:ℤ)+1) ∉ insert ((n:ℤ)+1) (alphabet n) := by
      simp only [alphabet, Finset.mem_insert, Finset.mem_erase, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert hn₂, Finset.sum_insert hn₁, hf, ih, Finset.sum_range_succ]
    ring

private def endChoices (n : ℕ) (y : ℤ) := (alphabet n).erase y
private def apStarts (n : ℕ) (y : ℤ) :=
  (endChoices n y).filter fun x => 2*y-x ∈ endChoices n y

/-- Allowed ordered endpoint pairs, after removing the pairs in arithmetic progression. -/
private def centreScore (n : ℕ) (y : ℤ) : ℤ :=
  ((endChoices n y).card ^ 2 - (apStarts n y).card : ℕ)

private theorem ends_neg_iff (n : ℕ) (x y : ℤ) :
    -x ∈ endChoices n (-y) ↔ x ∈ endChoices n y := by
  simp only [endChoices, alphabet, Finset.mem_erase, Finset.mem_Icc]
  omega

private theorem ap_neg_iff (n : ℕ) (x y : ℤ) :
    -x ∈ apStarts n (-y) ↔ x ∈ apStarts n y := by
  simp only [apStarts, Finset.mem_filter, ends_neg_iff]
  rw [show 2 * -y - -x = -(2*y-x) by ring, ends_neg_iff]

private theorem neg_card (S : ℤ → Finset ℤ) (h : ∀ x y, -x ∈ S (-y) ↔ x ∈ S y) (y : ℤ) :
    (S (-y)).card = (S y).card := by
  refine Finset.card_bij' (fun x _ => -x) (fun x _ => -x) ?_ ?_ ?_ ?_
  · intro x hx
    exact (h (-x) y).mp (by simpa using hx)
  · intro x hx
    exact (h x y).mpr hx
  · intro x _; simp
  · intro x _; simp

private theorem score_even (n : ℕ) (y : ℤ) : centreScore n (-y) = centreScore n y := by
  simp only [centreScore, neg_card _ (ends_neg_iff n), neg_card _ (ap_neg_iff n)]

/-- An AP with positive center y starts in [2y−n,n]. Remove y, and also remove
0 and 2y when the interval contains them. -/
private theorem ap_pos_card (n : ℕ) (y : ℤ) (hy : 0 < y) (hyn : y ≤ n) :
    ((apStarts n y).card : ℤ) =
      2*((n:ℤ)-y) - 2*(if 2*y ≤ n then 1 else 0) := by
  let I := Finset.Icc (2*y-n) (n:ℤ)
  have hcard := Int.card_Icc_of_le (2*y-n) (n:ℤ) (by omega)
  have hmy : y ∈ I := Finset.mem_Icc.mpr (by omega)
  have herase := Finset.card_erase_add_one hmy
  change (I.card : ℤ) = _ at hcard
  by_cases h : 2*y ≤ n
  · have heq : apStarts n y = ((I.erase y).erase 0).erase (2*y) := by
      ext x
      simp only [apStarts, endChoices, alphabet, I, Finset.mem_filter,
        Finset.mem_erase, Finset.mem_Icc]
      omega
    have hz : (0:ℤ) ∈ I.erase y := by
      simp only [I, Finset.mem_erase, Finset.mem_Icc]; omega
    have ht : 2*y ∈ (I.erase y).erase 0 := by
      simp only [I, Finset.mem_erase, Finset.mem_Icc]; omega
    have h₂ := Finset.card_erase_add_one hz
    have h₃ := Finset.card_erase_add_one ht
    rw [heq, if_pos h]
    omega
  · have heq : apStarts n y = I.erase y := by
      ext x
      simp only [apStarts, endChoices, alphabet, I, Finset.mem_filter,
        Finset.mem_erase, Finset.mem_Icc]
      omega
    rw [heq, if_neg h]
    omega

private theorem score_pos (n : ℕ) (y : ℤ) (hy : 0 < y) (hyn : y ≤ n) :
    centreScore n y =
      (2*(n:ℤ)-1)^2 - 2*((n:ℤ)-y) + 2*(if 2*y ≤ n then 1 else 0) := by
  have hcard := Int.card_Icc_of_le (-(n:ℤ)) (n:ℤ) (by omega)
  have hc₁ := Finset.card_erase_add_one (show (0:ℤ) ∈ Finset.Icc (-(n:ℤ)) n by
    rw [Finset.mem_Icc]; omega)
  have hc₂ := Finset.card_erase_add_one (show y ∈ alphabet n by
    simp only [alphabet, Finset.mem_erase, Finset.mem_Icc]; omega)
  have he : ((endChoices n y).card : ℤ) = 2*(n:ℤ)-1 := by
    unfold endChoices
    unfold alphabet at hc₂ ⊢
    omega
  have hsub : (apStarts n y).card ≤ (endChoices n y).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hsq : (apStarts n y).card ≤ (endChoices n y).card^2 := by
    exact le_trans hsub (by
      rcases Nat.eq_zero_or_pos (endChoices n y).card with h | h
      · simp [h]
      · nlinarith)
  rw [centreScore, Nat.cast_sub hsq, Nat.cast_pow, he, ap_pos_card n y hy hyn]
  ring

private theorem half_indicator (n : ℕ) :
    (∑ i ∈ Finset.range n, if 2*((i:ℤ)+1) ≤ (n:ℤ) then (1:ℤ) else 0) = (↑(n/2) : ℤ) := by
  rw [Finset.sum_boole]
  have he : (Finset.range n).filter (fun i : ℕ => 2*((i:ℤ)+1) ≤ (n:ℤ)) =
      Finset.range (n/2) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [he, Finset.card_range]

private theorem twice_sum_indices (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, (i:ℤ)) = (n:ℤ)*((n:ℤ)-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linarith only [ih, show ((n:ℤ)+1)*((n:ℤ)+1-1) = (n:ℤ)*((n:ℤ)-1)+2*n by ring]

/-- The unrestricted three-entry count (A199944), using the literal middle-entry split. -/
theorem base_closed_of_centres (n : ℕ)
    (hb : (baseSet n).card = ∑ y ∈ alphabet n,
      (((alphabet n).erase y).card^2 -
        (((alphabet n).erase y).filter fun x => 2*y-x ∈ (alphabet n).erase y).card)) :
    ((baseSet n).card : ℤ) = 8*(n:ℤ)^3 - 10*(n:ℤ)^2 + 6*n - 2*↑(n%2) := by
  rw [hb, Nat.cast_sum]
  change (∑ y ∈ alphabet n, centreScore n y) = _
  rw [sum_alphabet_even _ (score_even n)]
  have hsum : (∑ i ∈ Finset.range n, centreScore n ((i:ℤ)+1)) =
      ∑ i ∈ Finset.range n,
        ((2*(n:ℤ)-1)^2 - 2*(n:ℤ) + 2 + 2*(i:ℤ) +
          2*(if 2*((i:ℤ)+1) ≤ (n:ℤ) then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [score_pos n ((i:ℤ)+1) (by omega) (by omega)]
    ring
  rw [hsum]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, half_indicator,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, twice_sum_indices]
  have hdiv : 2*(↑(n/2) : ℤ) + ↑(n%2) = (n:ℤ) := by omega
  linarith only [hdiv, show (n:ℤ)*((2*(n:ℤ)-1)^2-2*n+2) =
    4*(n:ℤ)^3-6*(n:ℤ)^2+3*n by ring, show (n:ℤ)*((n:ℤ)-1) = (n:ℤ)^2-n by ring]

/-- Zero-sum triples with prescribed middle entry. -/
private def zeroFiber (n : ℕ) (y : ℤ) :=
  (zeroSet n).filter fun t => t.2.1 = y

private theorem mem_zeroFiber {n : ℕ} {x y z c : ℤ} :
    (x,y,z) ∈ zeroFiber n c ↔
    x ≠ 0 ∧ -(n:ℤ) ≤ x ∧ x ≤ n ∧ y ≠ 0 ∧ -(n:ℤ) ≤ y ∧ y ≤ n ∧
    z ≠ 0 ∧ -(n:ℤ) ≤ z ∧ z ≤ n ∧ x ≠ y ∧ y ≠ z ∧
    x+z ≠ 2*y ∧ x+y+z = 0 ∧ y = c := by
  simp only [zeroFiber, zeroSet, baseSet, alphabet, Finset.mem_filter,
    Finset.mem_product, Finset.mem_erase, Finset.mem_Icc]
  tauto

private theorem zeroFiber_neg (n : ℕ) (y : ℤ) :
    (zeroFiber n (-y)).card = (zeroFiber n y).card := by
  let neg (t : ℤ × ℤ × ℤ) := (-t.1, -t.2.1, -t.2.2)
  refine Finset.card_bij' (fun t _ => neg t) (fun t _ => neg t) ?_ ?_ ?_ ?_
  · rintro ⟨x,c,z⟩ ht
    change (-x,-c,-z) ∈ zeroFiber n y
    rw [mem_zeroFiber] at *
    omega
  · rintro ⟨x,c,z⟩ ht
    change (-x,-c,-z) ∈ zeroFiber n (-y)
    rw [mem_zeroFiber] at *
    omega
  · rintro ⟨x,c,z⟩ _
    simp [neg]
  · rintro ⟨x,c,z⟩ _
    simp [neg]

/-- The free first coordinate in a zero-sum triple with positive middle entry. -/
private def zeroFirst (n : ℕ) (y : ℤ) : Finset ℤ :=
  let s := Finset.Icc (-(n:ℤ)) ((n:ℤ)-y)
  (((s.erase 0).erase (-y)).erase y).erase (-2*y)

private theorem zeroFiber_to_first {n : ℕ} {y : ℤ} (hy : 0 < y) (hn : y ≤ n) :
    (zeroFiber n y).card = (zeroFirst n y).card := by
  refine Finset.card_bij' (fun t _ => t.1) (fun x _ => (x,y,-y-x)) ?_ ?_ ?_ ?_
  · rintro ⟨x,c,z⟩ ht
    rw [mem_zeroFiber] at ht
    simp only [zeroFirst, Finset.mem_erase, Finset.mem_Icc]
    omega
  · intro x hx
    simp only [zeroFirst, Finset.mem_erase, Finset.mem_Icc] at hx
    rw [mem_zeroFiber]
    omega
  · rintro ⟨x,c,z⟩ ht
    rw [mem_zeroFiber] at ht
    have hc : c = y := by omega
    have he : -y-x = z := by omega
    simp [hc, he]
  · intro x _
    rfl

private theorem zeroFirst_card {n : ℕ} {y : ℤ} (hy : 0 < y) (hn : y ≤ n) :
    ((zeroFirst n y).card : ℤ) = 2*n-y-1 - (if 2*y ≤ n then 2 else 0) := by
  let s := Finset.Icc (-(n:ℤ)) ((n:ℤ)-y)
  let t := (s.erase 0).erase (-y)
  have h0 : (0:ℤ) ∈ s := by simp only [s, Finset.mem_Icc]; omega
  have h1 : -y ∈ s.erase 0 := by
    simp only [s, Finset.mem_erase, Finset.mem_Icc]
    omega
  have c0 := Finset.card_erase_add_one h0
  have c1 := Finset.card_erase_add_one h1
  have cs := Int.card_Icc_of_le (-(n:ℤ)) ((n:ℤ)-y) (by omega)
  change (s.card : ℤ) = _ at cs
  change t.card + 1 = _ at c1
  change (((t.erase y).erase (-2*y)).card : ℤ) = _
  split
  next h =>
    have h2 : y ∈ t := by
      simp only [t, s, Finset.mem_erase, Finset.mem_Icc]
      omega
    have h3 : -2*y ∈ t.erase y := by
      simp only [t, s, Finset.mem_erase, Finset.mem_Icc]
      omega
    have c2 := Finset.card_erase_add_one h2
    have c3 := Finset.card_erase_add_one h3
    omega
  next h =>
    have h2 : y ∉ t := by
      simp only [t, s, Finset.mem_erase, Finset.mem_Icc]
      omega
    have h3 : -2*y ∉ t := by
      simp only [t, s, Finset.mem_erase, Finset.mem_Icc]
      omega
    rw [Finset.erase_eq_of_notMem h2, Finset.erase_eq_of_notMem h3]
    omega

private theorem zeroDescending (a : ℤ) (m : ℕ) :
    2 * (∑ i ∈ Finset.range m, (a-((i:ℤ)+1)-1)) =
      (m:ℤ) * (2*a-m-3) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    linear_combination ih

private theorem zeroPenalty (n : ℕ) :
    (∑ i ∈ Finset.range n, if 2*((i:ℤ)+1) ≤ n then (2:ℤ) else 0) =
      2*(↑(n/2):ℤ) := by
  have hset : (Finset.range n).filter (fun i : ℕ => 2*((i:ℤ)+1) ≤ n) =
      Finset.range (n/2) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hset]
  simp [mul_comm]

/-- The zero-sum triples among the arrays satisfying all difference constraints. -/
theorem zero_card (n : ℕ) :
    ((zeroSet n).card : ℤ) = 3*(n:ℤ)*((n:ℤ)-1)-4*(↑(n/2):ℤ) := by
  have hmap : ((zeroSet n : Finset _) : Set (ℤ × ℤ × ℤ)).MapsTo
      (fun t => t.2.1) (alphabet n) := by
    rintro ⟨x,y,z⟩ ht
    simp only [zeroSet, baseSet, Finset.mem_filter, Finset.mem_product,
      Finset.mem_coe] at ht
    exact ht.1.1.2.1
  have hcard := Finset.card_eq_sum_card_fiberwise hmap
  change (zeroSet n).card = ∑ y ∈ alphabet n, (zeroFiber n y).card at hcard
  rw [hcard, Nat.cast_sum, sum_alphabet_even (fun y => ((zeroFiber n y).card:ℤ))
    (fun y => congrArg Nat.cast (zeroFiber_neg n y))]
  have hsum : (∑ i ∈ Finset.range n, ((zeroFiber n ((i:ℤ)+1)).card : ℤ)) =
      ∑ i ∈ Finset.range n,
        (2*(n:ℤ)-((i:ℤ)+1)-1 - (if 2*((i:ℤ)+1) ≤ n then 2 else 0)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [zeroFiber_to_first (by omega) (by omega), zeroFirst_card (by omega) (by omega)]
  rw [hsum, Finset.sum_sub_distrib, zeroPenalty, mul_sub, zeroDescending]
  ring

private theorem formulas_of_count (hc : ∀ n : ℕ, (a n : ℤ) =
    8*(n : ℤ)^3 - 13*(n : ℤ)^2 + 11*(n : ℤ) - 4*((n%2 : ℕ) : ℤ)) :
    (∀ n : ℕ, seriesCoeff n - 3*seriesCoeff ((n : ℤ)-1)
      + 2*seriesCoeff ((n : ℤ)-2) + 2*seriesCoeff ((n : ℤ)-3)
      - 3*seriesCoeff ((n : ℤ)-4) + seriesCoeff ((n : ℤ)-5) = numeratorCoeff n) ∧
    (∀ n : ℕ, 1 ≤ n → Even n → (a n : ℤ) = 11*(n : ℤ) - 13*n^2 + 8*n^3) ∧
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n : ℤ) = -4 + 11*(n : ℤ) - 13*n^2 + 8*n^3) := by
  have recurrence (k : ℕ) : (a (k+5) : ℤ) - 3*(a (k+4) : ℤ)
      + 2*(a (k+3) : ℤ) + 2*(a (k+2) : ℤ) - 3*(a (k+1) : ℤ) + a k = 0 := by
    rw [hc (k+5), hc (k+4), hc (k+3), hc (k+2), hc (k+1), hc k]
    rw [show (k+5)%2 = (k+1)%2 by omega, show (k+4)%2 = k%2 by omega,
        show (k+3)%2 = (k+1)%2 by omega, show (k+2)%2 = k%2 by omega]
    push_cast
    ring
  have idx (j : ℕ) : seriesCoeff (j : ℤ) = (a j : ℤ) := by
    cases j with
    | zero => norm_num [seriesCoeff, hc]
    | succ j => simp [seriesCoeff]
  constructor
  · intro n
    match n with
    | 0 | 1 | 2 | 3 | 4 => norm_num [seriesCoeff, numeratorCoeff, hc]
    | k+5 =>
      rw [show (↑(k+5 : ℕ) : ℤ)-1 = ↑(k+4 : ℕ) by omega,
          show (↑(k+5 : ℕ) : ℤ)-2 = ↑(k+3 : ℕ) by omega,
          show (↑(k+5 : ℕ) : ℤ)-3 = ↑(k+2 : ℕ) by omega,
          show (↑(k+5 : ℕ) : ℤ)-4 = ↑(k+1 : ℕ) by omega,
          show (↑(k+5 : ℕ) : ℤ)-5 = ↑k by omega]
      simp only [idx]
      exact recurrence k
  · constructor
    · intro n _ h
      obtain ⟨k, hk⟩ := h
      rw [hc n, show n%2 = 0 by omega]
      push_cast
      ring
    · intro n _ h
      obtain ⟨k, hk⟩ := h
      rw [hc n, show n%2 = 1 by omega]
      push_cast
      ring

end OMA.S_oeis_a200166

open OMA.S_oeis_a200166

theorem OMA.solution : type_of% @OMA.S_oeis_a200166.main := by
  apply formulas_of_count
  intro n
  have hb := base_closed_of_centres n (base_by_centre n)
  have hz := zero_card n
  have hs : (a n : ℤ) + ((zeroSet n).card : ℤ) = ((baseSet n).card : ℤ) := by
    exact_mod_cast card_split n
  have hp : 2*(↑(n/2) : ℤ) + ↑(n%2) = (n : ℤ) := by omega
  linarith only [hs, hb, hz, hp]
