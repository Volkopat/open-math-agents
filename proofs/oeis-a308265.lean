import OMAStatements.S_oeis_a308265

/-!
Remove one counter from each of the three piles when the smallest pile has at least
two counters. The remaining partitions start with a pile of size one. Their middle
pile determines the last one, so their total contribution is an arithmetic progression.
-/

open Finset PowerSeries OMA.S_oeis_a308265

namespace ThreePiles

private def bump (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ := (t.1+1,t.2.1+1,t.2.2+1)
private def edge (n j : ℕ) : ℕ × ℕ × ℕ := (1, j+1, n+1-j)
private def width (n : ℕ) := (n+2)/2

private theorem bump_inj : Function.Injective bump := by
  rintro ⟨a,b,c⟩ ⟨d,e,f⟩ h
  simpa [bump] using h

private theorem edge_inj (n : ℕ) : Function.Injective (edge n) := by
  intro j k h
  simpa [edge] using congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) h

private theorem mem_tri (n x y z : ℕ) :
    (x,y,z) ∈ tri n ↔ 1 ≤ x ∧ x ≤ y ∧ y ≤ z ∧ x+y+z=n := by
  simp [tri]
  omega

private theorem split (n : ℕ) :
    tri (n+3) = (tri n).image bump ∪ (range (width n)).image (edge n) := by
  ext ⟨x,y,z⟩
  rw [mem_tri, mem_union, mem_image, mem_image]
  constructor
  · rintro ⟨hx,hxy,hyz,hs⟩
    by_cases hx1 : x=1
    · right
      refine ⟨y-1, mem_range.mpr ?_, ?_⟩
      · unfold width
        omega
      · simp only [edge, Prod.mk.injEq]
        omega
    · left
      exact ⟨(x-1,y-1,z-1), (mem_tri ..).2 (by omega), by simp [bump]; omega⟩
  · rintro (⟨⟨u,v,w⟩,ht,he⟩ | ⟨j,hj,he⟩)
    · have ht' := (mem_tri ..).1 ht
      simp only [bump, Prod.mk.injEq] at he
      omega
    · have hj' := mem_range.mp hj
      simp only [edge, Prod.mk.injEq] at he
      unfold width at hj'
      omega

private theorem separated (n : ℕ) :
    Disjoint ((tri n).image bump) ((range (width n)).image (edge n)) := by
  rw [disjoint_left]
  rintro _ hx hy
  obtain ⟨⟨u,v,w⟩, ht, rfl⟩ := mem_image.mp hx
  obtain ⟨j, _, he⟩ := mem_image.mp hy
  have hu := (mem_tri ..).1 ht
  simp only [bump, edge, Prod.mk.injEq] at he
  omega

private def p (n : ℕ) : ℚ := (tri n).card
private def mass (n : ℕ) : ℚ := a n
private def boundary (n : ℕ) : ℚ := (width n : ℚ) * (2*n+3-width n)/2

private lemma card_step (n : ℕ) : p (n+3) = p n + width n := by
  simp [p, split n, card_union_of_disjoint (separated n),
    card_image_of_injective _ bump_inj, card_image_of_injective _ (edge_inj n)]

private lemma sum_numbers (k : ℕ) :
    2*(∑ j ∈ range k, (j:ℚ)) = k*(k-1) := by
  induction k with
  | zero => simp
  | succ k h =>
    rw [sum_range_succ]
    push_cast
    linarith

private lemma weight_step (n : ℕ) : mass (n+3) = mass n + p n + boundary n := by
  have h (k : ℕ) : mass k = ∑ t ∈ tri k, (t.2.2:ℚ) := by simp [mass,a]
  rw [h, h, split, sum_union (separated n), sum_image (fun _ _ _ _ h => bump_inj h),
    sum_image (fun _ _ _ _ h => edge_inj n h)]
  simp only [bump, edge, Nat.cast_add, Nat.cast_one, sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
  have tail : (∑ j ∈ range (width n), ((n+1-j:ℕ):ℚ)) = ∑ j ∈ range (width n), ((n:ℚ)+1-j) := by
    refine sum_congr rfl (fun j hj => ?_)
    have hj' := mem_range.mp hj
    unfold width at hj'
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  rw [tail, sum_sub_distrib, sum_const, nsmul_eq_mul, card_range]
  unfold p boundary
  linarith [sum_numbers (width n)]

private def correction (n : ℕ) : ℚ := width n + boundary (n+3) - boundary n

private lemma second_difference (n : ℕ) :
    mass (n+6) - 2*mass (n+3) + mass n = correction n := by
  have hs := weight_step (n+3)
  rw [show n+3+3=n+6 by omega] at hs
  unfold correction
  linarith [weight_step n, card_step n]

private lemma correction_affine (n : ℕ) :
    correction (n+4) - 2*correction (n+2) + correction n = 0 := by
  have w (k : ℕ) : width (k+2) = width k + 1 := by unfold width; omega
  have wb (k : ℕ) : boundary (k+4) - 2*boundary (k+2) + boundary k = 3 := by
    unfold boundary
    rw [show width (k+4) = width k + 2 by unfold width; omega, w]
    push_cast
    ring
  unfold correction
  rw [show width (n+4) = width n + 2 by unfold width; omega, w]
  push_cast
  have h := wb (n+3)
  rw [show n+3+4=n+4+3 by omega, show n+3+2=n+2+3 by omega] at h
  linarith [wb n]

private lemma annihilates (n : ℕ) :
    mass (n+10) - 2*mass (n+8) - 2*mass (n+7) + mass (n+6) + 4*mass (n+5) +
    mass (n+4) - 2*mass (n+3) - 2*mass (n+2) + mass n = 0 := by
  have h0 := second_difference n
  have h2 := second_difference (n+2)
  have h4 := second_difference (n+4)
  simp only [Nat.add_assoc] at h2 h4
  linarith [correction_affine n]

set_option maxRecDepth 8000 in
private lemma initials :
    [a 0,a 1,a 2,a 3,a 4,a 5,a 6,a 7,a 8,a 9] = [0,0,0,1,2,5,9,15,22,34] := by
  decide

theorem equation : A * den = num := by
  rw [show A * den = A - C 2 * (A*X^2) - C 2 * (A*X^3) + A*X^4 + C 4 * (A*X^5) +
        A*X^6 - C 2 * (A*X^7) - C 2 * (A*X^8) + A*X^10 by
    simp only [den, map_ofNat]; ring]
  rw [show num = X^3 + C (2:ℚ)*(X^4) + C 3*(X^5) + C 3*(X^6) + C 2*(X^7) by
    simp only [num, map_ofNat]; ring]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, A, coeff_mk]
  by_cases hn : n<10
  · have hi := initials
    simp only [List.cons.injEq, and_true] at hi
    rcases hi with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
    interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  · obtain ⟨k,rfl⟩ : ∃ k, n = k+10 := ⟨n-10,by omega⟩
    simp (disch := omega) only [if_pos,if_neg,coeff_C,add_zero,
      show k+10-2=k+8 by omega, show k+10-3=k+7 by omega, show k+10-4=k+6 by omega,
      show k+10-5=k+5 by omega, show k+10-6=k+4 by omega, show k+10-7=k+3 by omega,
      show k+10-8=k+2 by omega, show k+10-10=k by omega]
    exact annihilates k

end ThreePiles

theorem OMA.solution : type_of% @OMA.S_oeis_a308265.main := by
  constructor
  · have h : constantCoeff den ≠ 0 := by simp [den]
    rw [← ThreePiles.equation, mul_assoc, PowerSeries.mul_inv_cancel _ h, mul_one]
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n=k+10 := ⟨n-10, by omega⟩
    have h := ThreePiles.annihilates k
    simp only [ThreePiles.mass] at h
    simp only [show k+10-2=k+8 by omega, show k+10-3=k+7 by omega,
      show k+10-4=k+6 by omega, show k+10-5=k+5 by omega, show k+10-6=k+4 by omega,
      show k+10-7=k+3 by omega, show k+10-8=k+2 by omega, show k+10-10=k by omega]
    have hr : (a (k+10) : ℚ) = 2*a (k+8)+2*a (k+7)-a (k+6)-4*a (k+5)-a (k+4)+
        2*a (k+3)+2*a (k+2)-a k := by linarith
    exact_mod_cast hr
