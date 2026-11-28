import OMAStatements.S_oeis_a059804
import Mathlib

/-! Geometry and prime-counting estimates for the stated A059804 conjecture. -/

namespace OMA.S_oeis_a059804
private noncomputable abbrev brP (i : ℕ) : ℝ := Nat.nth Nat.Prime i
private noncomputable abbrev brS (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, brP i ^ 2

private theorem brDist {n : ℕ} (z : ℕ → ℤ) (t : ℝ) :
    dist (pt fun i : Fin n => z i) (t • v n) ^ 2 =
      ∑ i ∈ Finset.range n, ((z i : ℝ) - t * brP i)^2 := by
  rw [EuclideanSpace.dist_sq_eq, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  change dist (z i : ℝ) (t * brP i) ^ 2 = _
  rw [Real.dist_eq, sq_abs]

private theorem brSeg (n : ℕ) : segment ℝ 0 (v n) =
    (fun t : ℝ => t • v n) '' Set.Icc (0:ℝ) 1 := by simp [segment_eq_image]

private theorem brLower {n : ℕ} (A : ℝ)
    (half : ∀ (z : ℕ → ℤ), (∃ i < n, z i ≠ 0) → ∀ t : ℝ, 0 ≤ t → t ≤ 1/2 →
      A ≤ ∑ i ∈ Finset.range n, ((z i : ℝ) - t * brP i)^2)
    (x : Fin n → ℤ) (hx : pt x ≠ 0) (hv : pt x ≠ v n) :
    A ≤ Metric.infDist (pt x) (segment ℝ 0 (v n)) ^ 2 := by
  classical
  let z : ℕ → ℤ := fun i => if hi : i < n then x ⟨i, hi⟩ else 0
  have hz (i : Fin n) : z i = x i := dif_pos i.isLt
  have hcomp : IsCompact (segment ℝ 0 (v n)) := by
    rw [brSeg]; exact isCompact_Icc.image (by fun_prop)
  obtain ⟨y, hy, he⟩ := hcomp.exists_infDist_eq_dist ⟨0, left_mem_segment ..⟩ (pt x)
  rw [brSeg] at hy
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hy
  rw [he, show x = (fun i : Fin n => z i) from funext (fun i => (hz i).symm), brDist]
  by_cases h : t ≤ 1/2
  · apply half z _ t ht0 h
    by_contra! ha
    apply hx
    ext i
    change (x i : ℝ) = 0
    rw [← hz i, ha i i.isLt, Int.cast_zero]
  · let w : ℕ → ℤ := fun i => (Nat.nth Nat.Prime i : ℤ) - z i
    have hw : ∃ i < n, w i ≠ 0 := by
      by_contra! ha
      apply hv
      ext i
      change (x i : ℝ) = brP i
      have e := ha i i.isLt
      change (Nat.nth Nat.Prime i : ℤ) - z i = 0 at e
      rw [← hz i]
      unfold brP
      exact_mod_cast (sub_eq_zero.mp e).symm
    refine (half w hw (1-t) (by linarith) (by linarith)).trans_eq ?_
    apply Finset.sum_congr rfl
    intro i _
    simp only [w, Int.cast_sub, Int.cast_natCast, brP]
    ring

theorem bridge059804 (n : ℕ) (hn : 19 ≤ n)
    (half : ∀ (z : ℕ → ℤ), (∃ i < n, z i ≠ 0) → ∀ t : ℝ, 0 ≤ t → t ≤ 1/2 →
      1 - brP (n-1)^2 / brS n ≤ ∑ i ∈ Finset.range n, ((z i : ℝ) - t * brP i)^2) :
    d n * ‖v n‖^2 = ∑ i ∈ Finset.range (n-1), (Nat.nth Nat.Prime i : ℝ)^2 := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  let S := brS (k+1)
  let P := brP k
  have hS : S = brS k + P^2 := Finset.sum_range_succ _ _
  have hPs : (2:ℝ) ≤ P := by
    change 2 ≤ (Nat.nth Nat.Prime k : ℝ)
    exact_mod_cast (Nat.prime_nth_prime k).two_le
  have hk : 0 ≤ brS k := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hs : 0 < S := by nlinarith
  let t := P/S
  have ht : t ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (by linarith) hs.le
    · exact (div_le_one hs).mpr (by nlinarith)
  let z (i : ℕ) : ℤ := if i = k then 1 else 0
  let x : Fin (k+1) → ℤ := fun i => z i
  have hx : pt x ≠ 0 := by
    intro e
    have h := congrArg (fun a : EuclideanSpace ℝ (Fin (k+1)) => a (Fin.last k)) e
    change (z k : ℝ) = 0 at h
    simp [z] at h
  have hv : pt x ≠ v (k+1) := by
    intro e
    have h := congrArg (fun a : EuclideanSpace ℝ (Fin (k+1)) => a (Fin.last k)) e
    change (z k : ℝ) = P at h
    simp only [z, if_pos rfl, Int.cast_one] at h
    linarith
  let r := Metric.infDist (pt x) (segment ℝ 0 (v (k+1))) ^ 2
  have hmin : d (k+1) = 1 - P^2/S := by
    apply le_antisymm
    · calc
        d (k+1) ≤ r := by
          unfold d
          refine csInf_le ?_ ?_
          swap
          · exact ⟨x, hx, hv, rfl⟩
          exact ⟨0, by rintro _ ⟨u, _, _, rfl⟩; exact sq_nonneg _⟩
        _ ≤ dist (pt x) (t • v (k+1)) ^ 2 := by
          apply pow_le_pow_left₀ Metric.infDist_nonneg _
          apply Metric.infDist_le_dist_of_mem
          rw [brSeg]
          exact ⟨t, ht, rfl⟩
        _ = (∑ i ∈ Finset.range k, ((z i : ℝ) - t * brP i)^2) + (1-t*P)^2 := by
          change dist (pt fun i : Fin (k+1) => z i) _ ^ 2 = _
          rw [brDist, Finset.sum_range_succ]; simp [z, P]
        _ = t^2 * brS k + (1-t*P)^2 := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          simp [z, ne_of_lt (Finset.mem_range.mp hi), mul_pow]
        _ = 1 - P^2/S := by
          dsimp only [t]
          rw [show brS k = S - P^2 by linarith]
          field_simp; ring
    · unfold d
      refine le_csInf ?_ ?_
      · exact ⟨r, x, hx, hv, rfl⟩
      rintro _ ⟨u, h0, h1, rfl⟩
      exact brLower _ half u h0 h1
  have hnrm : ‖v (k+1)‖ ^ 2 = S := by
    rw [EuclideanSpace.real_norm_sq_eq]
    dsimp only [S, brS]
    rw [← Fin.sum_univ_eq_sum_range]
    rfl
  rw [hmin, hnrm]
  change (1 - P^2/S)*S = brS k
  field_simp
  linarith

end OMA.S_oeis_a059804

namespace A059804
open Finset
noncomputable abbrev p (i : ℕ) : ℝ := Nat.nth Nat.Prime i
noncomputable abbrev total (n : ℕ) : ℝ := ∑ i ∈ range n, p i ^ 2
noncomputable abbrev err (n : ℕ) (x : ℕ → ℤ) (t : ℝ) : ℝ := ∑ i ∈ range n, ((x i : ℝ) - t * p i)^2
noncomputable abbrev threshold (n : ℕ) : ℝ := 1 - p (n-1)^2 / total n

private lemma closestZero (k : ℤ) (u : ℝ) (h0 : 0 ≤ u) (hu : u ≤ 1/2) : u^2 ≤ ((k : ℝ)-u)^2 := by
  by_cases hk : k ≤ 0
  · have h : (k : ℝ) ≤ 0 := by exact_mod_cast hk
    nlinarith [mul_nonpos_of_nonpos_of_nonneg h h0, sq_nonneg (k : ℝ)]
  · have h : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ k by linarith) (show 0 ≤ (k : ℝ)-2*u by linarith)]

private lemma closestNonzero (k : ℤ) (hk : k ≠ 0) (u : ℝ) (h0 : 0 ≤ u) (hu : u ≤ 1/2) :
    (1-u)^2 ≤ ((k : ℝ)-u)^2 := by
  by_cases h : k < 0
  · have h' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ (-1 : ℤ) by omega)
    nlinarith [mul_nonneg (show 0 ≤ -(k : ℝ)-1 by linarith) (show 0 ≤ -(k : ℝ)+1+2*u by linarith)]
  · have h' : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
    nlinarith [mul_nonneg (show 0 ≤ (k : ℝ)-1 by linarith) (show 0 ≤ (k : ℝ)+1-2*u by linarith)]

lemma p_monotone : Monotone p := by
  intro i j hij
  exact_mod_cast (Nat.nth_strictMono (Nat.infinite_setOfPred_prime)).monotone hij

lemma p_pos (i : ℕ) : 0 < p i := by
  exact_mod_cast (Nat.prime_nth_prime i).pos

lemma total_pos {n : ℕ} (hn : 0 < n) : 0 < total n := by
  apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
  exact ⟨0, mem_range.mpr hn, sq_pos_of_pos (p_pos 0)⟩

lemma endpoint {n : ℕ} (hn : 0 < n) (x : ℕ → ℤ) (hx : ∃ j < n, x j ≠ 0)
    (t : ℝ) (ht : 0 ≤ t) (hnear : t * p (n-1) ≤ 1/2) : threshold n ≤ err n x t := by
  obtain ⟨j,hj,hx⟩ := hx
  have hS := total_pos hn
  have hp (i : ℕ) (hi : i < n) : t * p i ≤ t * p (n-1) :=
    mul_le_mul_of_nonneg_left (p_monotone (by omega)) ht
  have hsum := Finset.sum_le_sum (s := range n) (f := fun i => (t*p i)^2 + if i=j then (1 - 2*t*p (n-1)) else 0)
    (g := fun i => ((x i : ℝ) - t*p i)^2) (by
      intro i hi
      have h1 := hp i (mem_range.mp hi)
      have h2 := mul_nonneg ht (p_pos i).le
      by_cases h : i=j
      · subst i
        simp only [if_true]
        nlinarith [closestNonzero (x j) hx _ h2 (h1.trans hnear)]
      · simp only [if_neg h, add_zero]
        exact closestZero _ _ h2 (h1.trans hnear))
  simp only [Finset.sum_add_distrib, mul_pow, ← Finset.mul_sum,
    Finset.sum_ite_eq', mem_range.mpr hj, if_true] at hsum
  change 1 - _ / total n ≤ _
  apply le_trans _ hsum
  change 1 - _ / total n ≤ t^2 * total n + (1 - 2*t*p (n-1))
  field_simp [hS.ne']
  nlinarith [sq_nonneg (t*total n-p (n-1))]

lemma density_to_error {n : ℕ} (hn : 0 < n) (x : ℕ → ℤ) (t y : ℝ) (ht : 0 < t)
    (hty : t * y = 1/2) (hy : y ≤ p (n-1))
    (A : Finset ℕ) (hA : 16 ≤ A.card)
    (hb : ∀ q ∈ A, q.Prime ∧ y/2 < (q : ℝ) ∧ (q : ℝ) ≤ y) : 1 ≤ err n x t := by
  let f := Nat.primeCounting'
  have hf (q : ℕ) (hq : q ∈ A) : p (f q) = q := by
    exact_mod_cast Nat.nth_count (hb q hq).1
  have hmono : StrictMono p := by
    intro a b hab
    exact_mod_cast Nat.nth_strictMono Nat.infinite_setOfPred_prime hab
  have hA' : (A.image f).card = A.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hbb hab
    have e : (a : ℝ) = b := (hf a ha).symm.trans ((congrArg p hab).trans (hf b hbb))
    exact_mod_cast e
  have hsub : A.image f ⊆ range n := by
    intro i hi
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hi
    have : f q ≤ n-1 := hmono.le_iff_le.mp (by rw [hf q hq]; exact (hb q hq).2.2.trans hy)
    exact mem_range.mpr (by omega)
  have hsum := Finset.sum_le_sum (s := A.image f) (f := fun _ => (1:ℝ)/16)
    (g := fun i => ((x i : ℝ) - t*p i)^2) (by
      intro i hi
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hi
      obtain ⟨_,l,r⟩ := hb q hq
      have lo := mul_le_mul_of_nonneg_left l.le ht.le
      have up := mul_le_mul_of_nonneg_left r ht.le
      rw [hf q hq]
      have h0 : 1/4 ≤ t*(q:ℝ) := by nlinarith
      calc (1:ℝ)/16 ≤ (t * (q:ℝ))^2 := by nlinarith [sq_nonneg (t*(q:ℝ)-1/4)]
           _ ≤ _ := closestZero _ _ (by linarith) (by linarith))
  simp only [sum_const, nsmul_eq_mul, hA'] at hsum
  have hAr : (16:ℝ) ≤ A.card := by exact_mod_cast hA
  have hbig := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => ((x i : ℝ)-t*p i)^2) hsub
    (fun _ _ _ => sq_nonneg _)
  change 1 ≤ ∑ i ∈ range n, _
  exact le_trans (by linarith : 1 ≤ ∑ i ∈ A.image f, ((x i : ℝ)-t*p i)^2) hbig


lemma halfBound
    (compact : ∀ n, 19 ≤ n → n < 39 → ∀ x t, 1 / (2*p (n-1)) ≤ t → t ≤ 1/2 → threshold n ≤ err n x t)
    (compact39 : ∀ x t, 1/334 ≤ t → t ≤ 1/2 → 1 ≤ err 39 x t)
    (window : ∀ y : ℝ, 167 ≤ y → ∃ A : Finset ℕ, 16 ≤ A.card ∧ ∀ q ∈ A, q.Prime ∧ y/2 < (q : ℝ) ∧ (q : ℝ) ≤ y)
    {n : ℕ} (hn : 19 ≤ n) (x : ℕ → ℤ) (hx : ∃ j < n, x j ≠ 0) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1/2) : threshold n ≤ err n x t := by
  have hn' : 0 < n := by omega
  by_cases hnear : t * p (n-1) ≤ 1/2
  · exact endpoint hn' x hx t ht hnear
  have hfar := lt_of_not_ge hnear
  have hp := p_pos (n-1)
  have htpos : 0 < t := by by_contra! h; have := le_antisymm h ht; subst t; norm_num at hfar
  by_cases hsmall : n < 39
  · apply compact n hn hsmall x t _ ht'
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hth : threshold n ≤ 1 := sub_le_self _ (div_nonneg (sq_nonneg _) (total_pos hn').le)
  apply hth.trans
  let y : ℝ := 1/(2*t)
  have hty : t*y = 1/2 := by dsimp [y]; field_simp
  by_cases hy : 167 ≤ y
  · obtain ⟨A,hA,ha⟩ := window y hy
    apply density_to_error hn' x t y htpos hty _ A hA ha
    apply (le_of_mul_le_mul_left _ htpos)
    linarith
  · have hl : 1/334 ≤ t := by
      have : 1/(2*t) < 167 := lt_of_not_ge hy
      have hb := (div_lt_iff₀ (show 0 < 2*t by positivity)).mp this
      linarith
    apply (compact39 x t hl ht').trans
    apply Finset.sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
    exact fun _ _ _ => sq_nonneg _

lemma finBridgeInput
    (half : ∀ {n : ℕ}, 19 ≤ n → ∀ x : ℕ → ℤ, (∃ j < n, x j ≠ 0) → ∀ t : ℝ,
      0 ≤ t → t ≤ 1/2 → threshold n ≤ err n x t)
    {n : ℕ} (hn : 19 ≤ n) (x : Fin n → ℤ) (hx : x ≠ 0) (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1/2) :
    total (n-1) / total n ≤ ∑ i : Fin n, ((x i : ℝ) - t * p i)^2 := by
  let z (i : ℕ) : ℤ := if hi : i < n then x ⟨i,hi⟩ else 0
  have hz : ∃ j < n, z j ≠ 0 := by
    by_contra! h
    exact hx (funext (fun i => by simpa [z, i.isLt] using h i i.isLt))
  have hh := half hn z hz t ht ht'
  have he : err n z t = ∑ i : Fin n, ((x i : ℝ) - t*p i)^2 := by
    rw [err, ← Fin.sum_univ_eq_sum_range]
    simp [z]
  rw [he] at hh
  suffices h : total (n-1) / total n = threshold n by rwa [h]
  have hs : total n = total (n-1) + p (n-1)^2 := by
    cases n with
    | zero => omega
    | succ n => exact sum_range_succ _ _
  change _ = 1 - _ / total n
  field_simp [(total_pos (show 0<n by omega)).ne']
  linarith

end A059804


namespace A059804Cert

def ps : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167]

def primeAt (i : ℕ) : ℕ := ps[i]?.getD 0

def S (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, primeAt i ^ 2

private abbrev D : ℕ := 65536

/-- Lower bound on the scaled distance to *any* multiple of `D`, on `[l*p,r*p]`.
If the interval crosses the next multiple, the truncated subtraction gives zero. -/
private def gap (l r p : ℕ) : ℕ :=
  min ((l*p) % D) (((l*p)/D + 1)*D - r*p)

private theorem gap_sq (l r p : ℕ) (x : ℤ) (t : ℝ)
    (hl : (l : ℝ) ≤ D*t) (hr : D*t ≤ (r : ℝ)) :
    (gap l r p : ℝ)^2 ≤ (D : ℝ)^2 * ((x : ℝ)-t*p)^2 := by
  let q := l*p/D
  have decomp : (l*p)%D + D*q = l*p := Nat.mod_add_div _ _
  have h0 : (0 : ℝ) ≤ gap l r p := by positivity
  have hp : (0 : ℝ) ≤ p := by positivity
  by_cases hx : x ≤ (q : ℤ)
  · have hq : (x : ℝ) ≤ (q : ℝ) := by exact_mod_cast hx
    have hb : gap l r p ≤ (l*p)%D := min_le_left _ _
    have hn : gap l r p + D*q ≤ l*p := by omega
    have hb' : (gap l r p : ℝ) + D*(q : ℝ) ≤ (l : ℝ)*p := by exact_mod_cast hn
    have hz : (gap l r p : ℝ) ≤ (D : ℝ)*(t*p - x) := by
      nlinarith only [hb', mul_le_mul_of_nonneg_right hl hp, hq]
    nlinarith only [sq_le_sq' (by linarith : -((D : ℝ)*(t*p - x)) ≤ gap l r p) hz]
  · have hqi : (q : ℤ)+1 ≤ x := by omega
    have hq : (q : ℝ)+1 ≤ (x : ℝ) := by exact_mod_cast hqi
    by_cases h : r*p ≤ (q+1)*D
    · have hb : gap l r p ≤ (q+1)*D-r*p := min_le_right _ _
      have hn : gap l r p + r*p ≤ (q+1)*D := by omega
      have hb' : (gap l r p : ℝ) + (r : ℝ)*p ≤ ((q : ℝ)+1)*D := by exact_mod_cast hn
      have hz : (gap l r p : ℝ) ≤ (D : ℝ)*(x-t*p) := by
        nlinarith only [hb', mul_le_mul_of_nonneg_right hr hp, hq]
      nlinarith only [sq_le_sq' (by linarith : -((D : ℝ)*(x-t*p)) ≤ gap l r p) hz]
    · have hz : gap l r p = 0 := by
        exact le_antisymm ((min_le_right _ _).trans (Nat.sub_eq_zero_of_le (le_of_not_ge h)).le) (Nat.zero_le _)
      rw [hz]; norm_num; positivity

private def score (l r : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => score l r n + gap l r (primeAt n) ^ 2

/-- Bounded-depth bisection: each accepted leaf proves its lower bound on the entire closed cell. -/
private def cover (n k : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | h+1, l, r => if k ≤ score l r n then true else
      cover n k h l ((l+r)/2) && cover n k h ((l+r)/2) r

private theorem score_le (n l r : ℕ) (x : ℕ → ℤ) (t : ℝ)
    (hl : (l : ℝ) ≤ D*t) (hr : D*t ≤ (r : ℝ)) :
    (score l r n : ℝ) ≤ (D : ℝ)^2 * ∑ i ∈ Finset.range n, ((x i : ℝ)-t*primeAt i)^2 := by
  induction n with
  | zero => simp [score]
  | succ n ih =>
    rw [score, Nat.cast_add, Nat.cast_pow, Finset.sum_range_succ, mul_add]
    exact add_le_add ih (gap_sq _ _ _ _ _ hl hr)

private theorem cover_sound (n k h l r : ℕ) (x : ℕ → ℤ) (t : ℝ)
    (hc : cover n k h l r = true) (hl : (l : ℝ) ≤ D*t) (hr : D*t ≤ (r : ℝ)) :
    (k : ℝ) ≤ (D : ℝ)^2 * ∑ i ∈ Finset.range n, ((x i : ℝ)-t*primeAt i)^2 := by
  induction h generalizing l r with
  | zero => simp [cover] at hc
  | succ h ih =>
    rw [cover] at hc
    split at hc
    · rename_i hk
      exact (Nat.cast_le.mpr hk).trans (score_le n l r x t hl hr)
    · rw [Bool.and_eq_true] at hc
      rcases le_total (D*t) (((l+r)/2 : ℕ) : ℝ) with hh | hh
      · exact ih _ _ hc.1 hl hh
      · exact ih _ _ hc.2 hh hr

private def leftEnd (n : ℕ) : ℕ := D / (2 * primeAt (n-1))

private def required (n : ℕ) : ℕ :=
  if n = 39 then D^2 else D^2 * (S n - primeAt (n-1)^2) / S n + 1

set_option maxHeartbeats 8000000 in
private theorem certificates (n : ℕ) (hn : 19 ≤ n) (hm : n ≤ 39) :
    cover n (required n) 16 (leftEnd n) (D/2) = true ∧
    D^2 * S n ≤ required n * S n + D^2 * primeAt (n-1)^2 ∧
    0 < S n ∧ 0 < primeAt (n-1) := by
  interval_cases n <;> decide +kernel

private theorem scaled_lo (n : ℕ) (t : ℝ) (hp : 0 < primeAt (n-1))
    (hl : 1 / (2 * (primeAt (n-1) : ℝ)) ≤ t) : (leftEnd n : ℝ) ≤ D*t := by
  have hpn : (0 : ℝ) < primeAt (n-1) := by exact_mod_cast hp
  have hu : (leftEnd n : ℝ) * (2 * (primeAt (n-1) : ℝ)) ≤ D := by
    exact_mod_cast Nat.div_mul_le_self D (2 * primeAt (n-1))
  have hz := (le_div_iff₀ (by positivity : (0 : ℝ) < 2*primeAt (n-1))).mpr hu
  calc
    (leftEnd n : ℝ) ≤ D / (2 * primeAt (n-1)) := hz
    _ = D * (1 / (2 * primeAt (n-1))) := by ring
    _ ≤ D*t := mul_le_mul_of_nonneg_left hl (by positivity)

/-- All closed cells between the first rounding transition and the midpoint. -/
theorem compact (n : ℕ) (hn : 19 ≤ n) (hm : n ≤ 39) (x : ℕ → ℤ) (t : ℝ)
    (hl : 1 / (2 * (primeAt (n-1) : ℝ)) ≤ t) (hr : t ≤ 1/2) :
    1 - (primeAt (n-1) : ℝ)^2 / S n ≤ ∑ i ∈ Finset.range n, ((x i : ℝ)-t*primeAt i)^2 := by
  obtain ⟨hc, hk, hs, hp⟩ := certificates n hn hm
  have h := cover_sound _ _ _ _ _ x t hc (scaled_lo n t hp hl) (by norm_num [D]; linarith)
  have hsp : (0 : ℝ) < S n := by exact_mod_cast hs
  have hk' : (D : ℝ)^2 * S n ≤ (required n : ℝ)*S n + (D : ℝ)^2 * (primeAt (n-1) : ℝ)^2 := by
    exact_mod_cast hk
  calc
    1 - (primeAt (n-1) : ℝ)^2 / S n ≤ (required n : ℝ) / D^2 := by
      field_simp [ne_of_gt hsp]; nlinarith only [hk']
    _ ≤ _ := by apply (div_le_iff₀ (by positivity)).mpr; linarith only [h]

/-- The last prefix gives a stronger bound than needed for the finite cases. -/
theorem compact39 (x : ℕ → ℤ) (t : ℝ) (hl : 1/334 ≤ t) (hr : t ≤ 1/2) :
    1 ≤ ∑ i ∈ Finset.range 39, ((x i : ℝ)-t*primeAt i)^2 := by
  have hc := (certificates 39 (by decide) (by decide)).1
  have h := cover_sound _ _ _ _ _ x t hc (by change (196 : ℝ) ≤ 65536*t; linarith)
    (by change 65536*t ≤ (32768 : ℝ); linarith)
  change (4294967296 : ℝ) ≤ (65536 : ℝ)^2 * _ at h
  linarith only [h]

end A059804Cert

namespace A059804
open A059804Cert
set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem primeAt_eq {i : ℕ} (hi : i < 39) : (primeAt i : ℝ) = p i := by
  have ht : ∀ j : Fin 39, (primeAt j).Prime ∧ Nat.count Nat.Prime (primeAt j) = j := by decide +kernel
  obtain ⟨hp,hc⟩ := ht ⟨i,hi⟩
  have hh := Nat.nth_count hp
  rw [show Nat.count Nat.Prime (primeAt i) = i from hc] at hh
  exact_mod_cast hh.symm
private theorem certS {n : ℕ} (hn : n ≤ 39) : (S n : ℝ) = total n := by
  simp only [S,Nat.cast_sum,Nat.cast_pow,total]
  apply Finset.sum_congr rfl
  intro i hi
  rw [primeAt_eq (lt_of_lt_of_le (Finset.mem_range.mp hi) hn)]
private theorem certErr {n : ℕ} (hn : n ≤ 39) (x : ℕ → ℤ) (t : ℝ) :
    (∑ i ∈ Finset.range n, ((x i : ℝ)-t*(primeAt i : ℝ))^2) = err n x t := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [primeAt_eq (lt_of_lt_of_le (Finset.mem_range.mp hi) hn)]

lemma finishFromWindow (window : ∀ y : ℝ, 167 ≤ y → ∃ A : Finset ℕ, A.card = 16 ∧ ∀ q ∈ A, q.Prime ∧ y/2 < (q:ℝ) ∧ (q:ℝ) ≤ y) :
    ∀ n : ℕ, 19 ≤ n → OMA.S_oeis_a059804.d n * ‖OMA.S_oeis_a059804.v n‖ ^ 2 = total (n-1) := by
  intro n hn
  apply OMA.S_oeis_a059804.bridge059804 n hn
  apply halfBound _ _ _ hn
  · intro n hn hm x t hl hr
    have hle : n ≤ 39 := by omega
    have hlast := primeAt_eq (i := n-1) (by omega)
    obtain hh := compact n hn hle x t (by rwa [hlast]) hr
    rwa [hlast, certS hle, certErr hle] at hh
  · intro x t hl hr
    have hh := compact39 x t hl hr
    rwa [certErr (le_refl 39)] at hh
  · intro y hy
    obtain ⟨A,hA,ha⟩ := window y hy
    exact ⟨A,hA.ge,ha⟩
end A059804


/-! The large-window part of an elementary sixteen-prime bound.

The prime-factor partition follows the proof in Mathlib's `NumberTheory/Bertrand.lean`,
which is due to Patrick Stevens and Bolton Bailey (Apache 2.0). We retain and count the
prime factors above `m` instead of assuming there are none.
-/

namespace OMA.S_oeis_a059804.PrimeWindow

open Finset

/-- A cover by blocks of ratio four, later split into two dyadic half-blocks. -/
private theorem block (m : ℕ) (hm : 4096 ≤ m) :
    ∃ k : ℕ, 4096 * 4 ^ k ≤ m ∧ m < 16384 * 4 ^ k := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h : m < 16384
    · exact ⟨0, by simpa using hm, by simpa using h⟩
    · obtain ⟨k, h₁, h₂⟩ := ih (m / 4) (by omega) (by omega)
      refine ⟨k + 1, ?_, ?_⟩ <;> rw [pow_succ] <;> omega

/-- On jumping two dyadic scales, the exponent budget grows by at most four. -/
private theorem budget (a s b : ℕ) (ha : 2 ≤ a) (hbase : 3 * (a * (s + 16)) ≤ 2 * b)
    (k : ℕ) : 3 * ((a + 2 * k) * (s * 2 ^ k + 16)) ≤ 2 * b * 4 ^ k := by
  induction k with
  | zero => simpa using hbase
  | succ k ih =>
    have h₁ : a + 2 * (k + 1) ≤ 2 * (a + 2 * k) := by omega
    have h₂ : s * 2 ^ (k + 1) + 16 ≤ 2 * (s * 2 ^ k + 16) := by
      rw [pow_succ, ← mul_assoc, mul_comm (s * 2 ^ k) 2]
      omega
    calc
      _ ≤ 3 * ((2 * (a + 2 * k)) * (2 * (s * 2 ^ k + 16))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul h₁ h₂)
      _ = (3 * ((a + 2 * k) * (s * 2 ^ k + 16))) * 4 := by ring
      _ ≤ (2 * b * 4 ^ k) * 4 := Nat.mul_le_mul_right _ ih
      _ = _ := by rw [pow_succ, mul_assoc]

/-- The common estimate for the two dyadic half-blocks. -/
private theorem growth_on_block (m a s b k : ℕ) (ha : 2 ≤ a) (hs : 2 ^ a ≤ s ^ 2)
    (hbase : 3 * (a * (s + 16)) ≤ 2 * b)
    (hlo : b * 4 ^ k ≤ m) (hhi : 2 * m ≤ 2 ^ a * 4 ^ k) :
    m * ((2 * m) ^ (Nat.sqrt (2 * m) + 15) * 4 ^ (2 * m / 3)) ≤ 4 ^ m := by
  have hsq : (2 ^ k : ℕ) ^ 2 = 4 ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  have hsqrt : Nat.sqrt (2 * m) ≤ s * 2 ^ k := by
    have H : 2 * m ≤ (s * 2 ^ k) ^ 2 := by
      rw [mul_pow, hsq]
      exact hhi.trans (Nat.mul_le_mul_right _ hs)
    simpa only [pow_two, Nat.sqrt_eq] using Nat.sqrt_le_sqrt H
  have hexp : (a + 2 * k) * (s * 2 ^ k + 16) ≤ 2 * (m - 2 * m / 3) := by
    have H := budget a s b ha hbase k
    rw [mul_assoc] at H
    replace H := H.trans (Nat.mul_le_mul_left 2 hlo)
    omega
  have hbase' : 2 * m ≤ 2 ^ (a + 2 * k) := by
    rw [pow_add, pow_mul]
    norm_num
    exact hhi
  have hbound : m * (2 * m) ^ (Nat.sqrt (2 * m) + 15) ≤ 4 ^ (m - 2 * m / 3) := by
    calc
      _ ≤ (2 * m) * (2 * m) ^ (Nat.sqrt (2 * m) + 15) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = (2 * m) ^ (Nat.sqrt (2 * m) + 16) := by
        calc
          _ = (2 * m) ^ (Nat.sqrt (2 * m) + 15) * (2 * m) := mul_comm _ _
          _ = (2 * m) ^ ((Nat.sqrt (2 * m) + 15) + 1) := (pow_succ _ _).symm
          _ = _ := by rw [add_assoc]
      _ ≤ (2 ^ (a + 2 * k)) ^ (s * 2 ^ k + 16) := by
        gcongr
        exact Nat.one_le_pow _ _ (by decide)
      _ = 2 ^ ((a + 2 * k) * (s * 2 ^ k + 16)) := by rw [pow_mul]
      _ ≤ 2 ^ (2 * (m - 2 * m / 3)) := Nat.pow_le_pow_right (by decide) hexp
      _ = 4 ^ (m - 2 * m / 3) := by rw [pow_mul]; norm_num
  rw [← mul_assoc]
  refine (Nat.mul_le_mul_right _ hbound).trans_eq ?_
  rw [← pow_add, Nat.sub_add_cancel (by omega : 2 * m / 3 ≤ m)]

private theorem growth (m : ℕ) (hm : 4096 ≤ m) :
    m * ((2 * m) ^ (Nat.sqrt (2 * m) + 15) * 4 ^ (2 * m / 3)) ≤ 4 ^ m := by
  obtain ⟨k, h₁, h₂⟩ := block m hm
  by_cases h : m < 8192 * 4 ^ k
  · apply growth_on_block m 14 128 4096 k (by decide) (by decide) (by decide) h₁
    norm_num
    omega
  · apply growth_on_block m 15 192 8192 k (by decide) (by decide) (by decide) (by omega)
    norm_num
    omega

/-- The primes in the natural half-open interval `(lo, hi]`. -/
def primesBetween (lo hi : ℕ) : Finset ℕ :=
  (Ioc lo hi).filter Nat.Prime

theorem mem_primesBetween {lo hi p : ℕ} :
    p ∈ primesBetween lo hi ↔ p.Prime ∧ lo < p ∧ p ≤ hi := by
  simp only [primesBetween, mem_filter, mem_Ioc]
  tauto

/-- Bertrand's binomial-coefficient bound with the prime factors above `m` retained. -/
theorem centralBinom_le_of_card_le_fifteen (m : ℕ) (hm : 2 < m)
    (hcard : (primesBetween m (2 * m)).card ≤ 15) :
    m.centralBinom ≤ (2 * m) ^ (Nat.sqrt (2 * m) + 15) * 4 ^ (2 * m / 3) := by
  let S := (range (2 * m / 3 + 1)).filter Nat.Prime
  let T := primesBetween m (2 * m)
  let f (p : ℕ) := p ^ m.centralBinom.factorization p
  have hpos : 0 < 2 * m := by omega
  have hmul : (∏ p ∈ S, f p) * (∏ p ∈ T, f p) = m.centralBinom := by
    rw [← Finset.prod_union, ← Nat.prod_pow_factorization_centralBinom m]
    · apply Finset.prod_subset
      · intro p hp
        rcases Finset.mem_union.mp hp with hp | hp
        · have h₁ := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
          exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (by have := (mem_primesBetween.mp hp).2.2; omega)
      · intro p hp hnot
        have hhigh : p ≤ 2 * m := by have := Finset.mem_range.mp hp; omega
        have hs : p ∉ S := fun h => hnot (Finset.mem_union_left _ h)
        have ht : p ∉ T := fun h => hnot (Finset.mem_union_right _ h)
        by_cases hp' : p.Prime
        · have hlo : p ≤ m := by
            by_contra! hh
            exact ht (mem_primesBetween.mpr ⟨hp', hh, hhigh⟩)
          have hmid : 2 * m < 3 * p := by
            by_contra! hh
            apply hs
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp'⟩
          simp only [f, Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hm hlo hmid,
            pow_zero]
        · simp only [f, Nat.factorization_eq_zero_of_not_prime _ hp', pow_zero]
    · refine Finset.disjoint_left.mpr fun p hs ht => ?_
      have h₁ := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
      have h₂ := (mem_primesBetween.mp ht).2.1
      omega
  have hS : ∏ p ∈ S, f p ≤ (2 * m) ^ Nat.sqrt (2 * m) * 4 ^ (2 * m / 3) := by
    rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * m))]
    apply mul_le_mul'
    · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * m)).trans ?_
      · exact Nat.pow_factorization_choose_le hpos
      have hc : (Finset.Icc 1 (Nat.sqrt (2 * m))).card = Nat.sqrt (2 * m) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
      rw [Finset.prod_const]
      refine Nat.pow_le_pow_right hpos ((Finset.card_le_card fun p hp => ?_).trans_eq hc)
      obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp h₁).2.one_lt.le, h₂⟩
    · refine le_trans ?_ (primorial_le_four_pow _)
      refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
      · obtain ⟨h₁, h₂⟩ := Finset.mem_filter.mp hp
        refine (pow_right_mono₀ (Finset.mem_filter.mp h₁).2.one_lt.le ?_).trans_eq (pow_one p)
        exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp h₂))
      exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
        (fun p hp _ => (Finset.mem_filter.mp hp).2.one_lt.le)
  have hT : ∏ p ∈ T, f p ≤ (2 * m) ^ 15 := by
    refine (Finset.prod_le_prod' (fun p _ => (Nat.pow_factorization_choose_le hpos :
      f p ≤ 2 * m))).trans ?_
    rw [Finset.prod_const]
    exact Nat.pow_le_pow_right hpos hcard
  calc
    m.centralBinom = (∏ p ∈ S, f p) * (∏ p ∈ T, f p) := hmul.symm
    _ ≤ ((2 * m) ^ Nat.sqrt (2 * m) * 4 ^ (2 * m / 3)) * (2 * m) ^ 15 :=
      Nat.mul_le_mul hS hT
    _ = _ := by rw [mul_right_comm, ← pow_add]

/-- For every `m ≥ 4096`, the interval `(m, 2*m]` contains at least sixteen primes. -/
theorem card_primesBetween_double_eventually {m : ℕ} (hm : 4096 ≤ m) :
    16 ≤ (primesBetween m (2 * m)).card := by
  by_contra! h
  have hl := Nat.four_pow_lt_mul_centralBinom m (by omega)
  have hu := centralBinom_le_of_card_le_fifteen m (by omega) (by omega)
  exact (not_lt_of_ge ((Nat.mul_le_mul_left m hu).trans (growth m hm))) hl

/-- For natural `N ≥ 8192`, the interval `(⌊N/2⌋, N]` contains at least sixteen primes. -/
theorem card_primesBetween_half_eventually {N : ℕ} (hN : 8192 ≤ N) :
    16 ≤ (primesBetween (N / 2) N).card := by
  refine (card_primesBetween_double_eventually (m := N / 2) (by omega)).trans
    (Finset.card_le_card ?_)
  intro p hp
  obtain ⟨hp', hlo, hhi⟩ := mem_primesBetween.mp hp
  exact mem_primesBetween.mpr ⟨hp', hlo, by omega⟩

/-- A sixteen-element finset of prime witnesses in the real interval `(y/2, y]`.
The cutoff `8192` is auxiliary: smaller `y` require a separate bounded certificate. -/
theorem sixteen_primes_real_eventually {y : ℝ} (hy : 8192 ≤ y) :
    ∃ s : Finset ℕ, s.card = 16 ∧ ∀ p ∈ s, p.Prime ∧ y / 2 < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  let m := ⌊y / 2⌋₊
  have hhalf : 0 ≤ y / 2 := by linarith
  have hm : 4096 ≤ m := Nat.le_floor (by norm_num; linarith)
  obtain ⟨s, hsub, hcard⟩ :=
    Finset.exists_subset_card_eq (card_primesBetween_double_eventually hm)
  refine ⟨s, hcard, fun p hp => ?_⟩
  obtain ⟨hp', hlo, hhi⟩ := mem_primesBetween.mp (hsub hp)
  refine ⟨hp', (Nat.floor_lt hhalf).mp hlo, ?_⟩
  have hcast : (p : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hhi
  have hfloor : (m : ℝ) ≤ y / 2 := Nat.floor_le hhalf
  linarith


end OMA.S_oeis_a059804.PrimeWindow

namespace A059804PrimeWindow

private theorem of_bounds (a b : ℕ) (S : Finset ℕ) (hc : S.card = 16)
    (hp : ∀ p ∈ S, p.Prime ∧ p ≤ a ∧ b ≤ 2 * p)
    (y : ℝ) (hy : (a : ℝ) ≤ y) (hy' : y < (b : ℝ)) :
    ∃ T : Finset ℕ, T.card = 16 ∧ ∀ p ∈ T, p.Prime ∧ y / 2 < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  refine ⟨S, hc, ?_⟩
  intro p hmem
  obtain ⟨hP, hpa, hbp⟩ := hp p hmem
  have hp_le : (p : ℝ) ≤ (a : ℝ) := by exact_mod_cast hpa
  have hb_le : (b : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hbp
  exact ⟨hP, by linarith, hp_le.trans hy⟩

/-- The short gap between the compact geometry calculation and the large prime window. -/
theorem finite_window (y : ℝ) (h167 : 167 ≤ y) (h8192 : y < 8192) :
    ∃ S : Finset ℕ, S.card = 16 ∧ ∀ p ∈ S, p.Prime ∧ y / 2 < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  by_cases h178 : y < 178
  · exact of_bounds 167 178 ({89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y h167 h178
  ·
    by_cases h194 : y < 194
    · exact of_bounds 178 194 ({97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y (le_of_not_gt h178) h194
    ·
      by_cases h218 : y < 218
      · exact of_bounds 194 218 ({109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y (le_of_not_gt h194) h218
      ·
        by_cases h262 : y < 262
        · exact of_bounds 218 262 ({131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y (le_of_not_gt h218) h262
        ·
          by_cases h346 : y < 346
          · exact of_bounds 262 346 ({173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y (le_of_not_gt h262) h346
          ·
            by_cases h482 : y < 482
            · exact of_bounds 346 482 ({241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y (le_of_not_gt h346) h482
            ·
              by_cases h778 : y < 778
              · exact of_bounds 482 778 ({389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y (le_of_not_gt h482) h778
              ·
                by_cases h1346 : y < 1346
                · exact of_bounds 778 1346 ({673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y (le_of_not_gt h778) h1346
                ·
                  by_cases h2462 : y < 2462
                  · exact of_bounds 1346 2462 ({1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y (le_of_not_gt h1346) h2462
                  ·
                    by_cases h4702 : y < 4702
                    · exact of_bounds 2462 4702 ({2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y (le_of_not_gt h2462) h4702
                    ·
                      exact of_bounds 4702 8192 ({4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691} : Finset ℕ) (by decide) (by simp only [Finset.forall_mem_insert, Finset.mem_singleton]; norm_num) y (le_of_not_gt h4702) h8192

end A059804PrimeWindow

namespace A059804PrimeWindow

lemma window_exact (y : ℝ) (hy : 167 ≤ y) :
    ∃ s : Finset ℕ, s.card = 16 ∧ ∀ p ∈ s, p.Prime ∧ y / 2 < (p : ℝ) ∧ (p : ℝ) ≤ y := by
  by_cases hh : y < 8192
  · exact finite_window y hy hh
  · exact OMA.S_oeis_a059804.PrimeWindow.sixteen_primes_real_eventually (le_of_not_gt hh)

end A059804PrimeWindow

theorem OMA.solution : type_of% @OMA.S_oeis_a059804.main :=
  A059804.finishFromWindow A059804PrimeWindow.window_exact
