import OMAStatements.S_oeis_a024162

/-!
Write the sides as x < y < z, and set h = ⌈n/2⌉ for perimeter n. The three
distinct positive integers h-z < h-y < h-x sum to 3h-n. Subtracting their
successive minimum gaps gives a count by lattice points 3i+2j+6 ≤ 3h-n.
The six-step recurrence for this count gives quadratic upper and lower bounds.

An even perimeter loses at least the triangles whose sides are all even.
For an odd perimeter, every nonprimitive triangle is a multiple by some odd
integer at least three. A telescoping bound for the sum of their inverse squares
leaves enough primitive triangles for k ≥ 65. The remaining cases are finite.
-/

namespace PrimitiveTriangle

open Finset OMA.S_oeis_a024162

private abbrev Pair := ℕ × ℕ
private def third (n : ℕ) (v : Pair) := n - v.1 - v.2

private def shapes (n : ℕ) : Finset Pair :=
  (range (n + 1) ×ˢ range (n + 1)).filter fun v =>
    0 < v.1 ∧ v.1 < v.2 ∧ v.2 < third n v ∧ v.1 + v.2 + third n v = n ∧ third n v < v.1 + v.2

private theorem mem_shapes {n x y : ℕ} : (x,y) ∈ shapes n ↔
    0 < x ∧ x < y ∧ y < n - x - y ∧ x + y + (n - x - y) = n ∧ n - x - y < x + y := by
  unfold shapes
  rw [Finset.mem_filter, Finset.mem_product]
  simp only [third, Finset.mem_range]
  omega

private def common (n : ℕ) (v : Pair) := Nat.gcd (Nat.gcd v.1 v.2) (third n v)

private theorem primitive (n : ℕ) : a n = ((shapes n).filter fun v => common n v = 1).card := by
  unfold a
  apply congrArg Finset.card
  ext ⟨x,y⟩
  rw [Finset.mem_filter, Finset.mem_filter, mem_shapes, Finset.mem_product]
  simp only [common, third, mem_range]
  omega

private def row (s i : ℕ) := if 3 * i + 6 ≤ s then (s - (3 * i + 6)) / 2 + 1 else 0
private def grid (s : ℕ) : Finset (Σ _ : ℕ, ℕ) := (range (s + 1)).sigma fun i => range (row s i)
private def Q (s : ℕ) := (grid s).card

private theorem mem_grid {s i j : ℕ} : (⟨i,j⟩ : Σ _ : ℕ, ℕ) ∈ grid s ↔ 3*i+2*j+6 ≤ s := by
  simp only [grid, mem_sigma, mem_range, row]
  split_ifs <;> omega

private def half (n : ℕ) := (n + 1) / 2
private def size (n : ℕ) := 3 * half n - n
private def encode (n : ℕ) (v : Pair) : Σ _ : ℕ, ℕ :=
  ⟨half n - third n v - 1, third n v - v.2 - 1⟩
private def decode (n : ℕ) (v : Σ _ : ℕ, ℕ) : Pair :=
  let z := half n - v.1 - 1
  let y := z - v.2 - 1
  (n - z - y, y)

private theorem shape_count (n : ℕ) : (shapes n).card = Q (size n) := by
  apply card_nbij' (encode n) (decode n)
  · rintro ⟨x,y⟩ h
    have hh := mem_shapes.mp h
    apply mem_grid.mpr
    dsimp [encode, size, half, third]
    omega
  · rintro ⟨i,j⟩ h
    have hh := mem_grid.mp h
    dsimp [size, half] at hh
    apply mem_shapes.mpr
    dsimp [decode, half]
    omega
  · rintro ⟨x,y⟩ h
    have hh := mem_shapes.mp h
    apply Prod.ext <;> dsimp [encode, decode, half, third] <;> omega
  · rintro ⟨i,j⟩ h
    have hh := mem_grid.mp h
    dsimp [size, half] at hh
    apply Sigma.ext
    · dsimp [encode, decode, half, third]; omega
    · apply heq_of_eq
      dsimp [encode, decode, half, third]; omega

private theorem count_rows (s : ℕ) : Q s = ∑ i ∈ range (s + 1), row s i := by
  simp [Q, grid, card_sigma]

private theorem step (s : ℕ) (hs : 0 < s) : Q (s + 6) = Q s + s := by
  rw [count_rows, count_rows]
  have tail (j : ℕ) : row (s + 6) (j + 2) = row s j := by
    unfold row
    split_ifs <;> omega
  have split : s + 6 + 1 = 2 + (s + 5) := by omega
  rw [split, sum_range_add]
  simp_rw [Nat.add_comm 2 _, tail]
  rw [show s + 5 = (s + 1) + 4 by omega, sum_range_add]
  have vanish (j : ℕ) : row s (s + 1 + j) = 0 := by
    rw [row, if_neg (by omega)]
  simp_rw [vanish]
  simp only [sum_const_zero, add_zero, sum_range_succ, sum_range_zero, zero_add]
  have first : row (s+6) 0 + row (s+6) 1 = s := by unfold row; split_ifs <;> omega
  omega

private theorem bounds (s : ℕ) (hs : 0 < s) :
    ((s : ℚ) - 3)^2 - 4 ≤ 12 * (Q s : ℚ) ∧ 12 * (Q s : ℚ) ≤ ((s : ℚ) - 3)^2 + 3 := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases small : s ≤ 6
    · interval_cases s <;> decide +kernel
    have hpos : 0 < s - 6 := by omega
    obtain ⟨hl,hu⟩ := ih (s-6) (by omega) hpos
    have corr := step (s-6) hpos
    rw [show s - 6 + 6 = s by omega] at corr
    rw [corr]
    push_cast
    have hcast : ((s-6 : ℕ) : ℚ) = (s : ℚ) - 6 := Nat.cast_sub (by omega)
    rw [hcast] at hl hu ⊢
    constructor <;> nlinarith

private theorem shape_bounds (n : ℕ) (hn : 0 < n) :
    let delta : ℚ := if n % 2 = 1 then 3 else 6
    ((n : ℚ) - delta)^2 - 16 ≤ 48 * ((shapes n).card : ℚ) ∧
      48 * ((shapes n).card : ℚ) ≤ ((n : ℚ) - delta)^2 + 12 := by
  have sp : 0 < size n := by dsimp [size, half]; omega
  obtain ⟨hl,hu⟩ := bounds (size n) sp
  rw [shape_count]
  dsimp only
  split_ifs with odd
  · have e : 2 * size n = n + 3 := by dsimp [size, half]; omega
    have e' : 2 * (size n : ℚ) = n + 3 := by exact_mod_cast e
    constructor <;> nlinarith [sq_nonneg ((size n : ℚ) - 3), congrArg (fun x : ℚ => x^2) e']
  · have e : 2 * size n = n := by dsimp [size, half]; omega
    have e' : 2 * (size n : ℚ) = n := by exact_mod_cast e
    constructor <;> nlinarith [congrArg (fun x : ℚ => x^2) e']

private theorem shape_upper (n : ℕ) : 48 * ((shapes n).card : ℚ) ≤ (n : ℚ)^2 := by
  by_cases h : n ≤ 3
  · interval_cases n <;> decide +kernel
  have large : (4 : ℚ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
  have hu := (shape_bounds n (by omega)).2
  split_ifs at hu <;> nlinarith

private theorem shape_lower (n : ℕ) (h : 6 ≤ n) :
    ((n : ℚ) - 6)^2 - 16 ≤ 48 * ((shapes n).card : ℚ) := by
  have large : (6 : ℚ) ≤ n := by exact_mod_cast h
  have hl := (shape_bounds n (by omega)).1
  split_ifs at hl <;> nlinarith

private def scale (d : ℕ) (v : Pair) : Pair := (d * v.1, d * v.2)

private theorem scale_mem {d n : ℕ} (hd : 0 < d) (v : Pair) :
    scale d v ∈ shapes (d*n) ↔ v ∈ shapes n := by
  obtain ⟨x,y⟩ := v
  unfold scale
  rw [mem_shapes, mem_shapes]
  simp only [← Nat.mul_sub, ← Nat.mul_add, Nat.mul_lt_mul_left hd,
    Nat.mul_right_inj (Nat.ne_of_gt hd), Nat.mul_pos_iff_of_pos_left hd]

private theorem even_bound (k : ℕ) : a (2*k) + (shapes k).card ≤ (shapes (2*k)).card := by
  let bad := (shapes (2*k)).filter (fun v => ¬common (2*k) v = 1)
  have incl : (shapes k).image (scale 2) ⊆ bad := by
    intro w hw
    obtain ⟨⟨x,y⟩,hv,rfl⟩ := mem_image.mp hw
    apply mem_filter.mpr
    refine ⟨(scale_mem (by decide) _).mpr hv, ?_⟩
    simp [common, third, scale, ← Nat.mul_sub, Nat.gcd_mul_left]
  have hinj : Function.Injective (scale 2) := by
    rintro ⟨x,y⟩ ⟨u,v⟩ he
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp [scale] at hx hy
    exact Prod.ext (by omega) (by omega)
  have hb := Finset.card_le_card incl
  rw [card_image_of_injective _ hinj] at hb
  have total := card_filter_add_card_filter_not (s := shapes (2*k)) (fun v => common (2*k) v = 1)
  rw [primitive]
  dsimp [bad] at hb
  omega

private theorem odd_bound (n : ℕ) (odd : n % 2 = 1) :
    (shapes n).card ≤ a n + ∑ j ∈ range n, (shapes (n / (2*j+3))).card := by
  let multiples (j : ℕ) := (shapes (n/(2*j+3))).image (scale (2*j+3))
  let bad := (shapes n).filter (fun v => ¬common n v = 1)
  have cover : bad ⊆ (range n).biUnion multiples := by
    rintro ⟨x,y⟩ hv
    obtain ⟨hs,not_one⟩ := mem_filter.mp hv
    obtain ⟨hx,_,_,he,_⟩ := mem_shapes.mp hs
    let d := common n (x,y)
    have dd : d ∣ Nat.gcd x y := Nat.gcd_dvd_left _ _
    have dx := dd.trans (Nat.gcd_dvd_left x y)
    have dy := dd.trans (Nat.gcd_dvd_right x y)
    have dz : d ∣ n - x - y := Nat.gcd_dvd_right _ _
    have dn : d ∣ n := he ▸ dvd_add (dvd_add dx dy) dz
    have dp := Nat.pos_of_dvd_of_pos dx hx
    have nd := Nat.le_of_dvd (by omega : 0 < n) dn
    have odd_d : d % 2 = 1 := by
      by_contra hd
      have ht : 2 ∣ d := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
      have hn := Nat.dvd_iff_mod_eq_zero.mp (ht.trans dn)
      omega
    have d1 : d ≠ 1 := not_one
    let j := (d-3)/2
    have idx : 2*j+3 = d := by dsimp [j]; omega
    refine mem_biUnion.mpr ⟨j, mem_range.mpr (by dsimp [j]; omega), ?_⟩
    dsimp [multiples]
    rw [idx]
    obtain ⟨u,hu⟩ := dx
    obtain ⟨v,hy⟩ := dy
    have hp : scale d (u,v) = (x,y) := Prod.ext hu.symm hy.symm
    refine mem_image.mpr ⟨(u,v), (scale_mem dp _).mp ?_, hp⟩
    rw [hp, Nat.mul_div_cancel' dn]
    exact hs
  have hb := (card_le_card cover).trans card_biUnion_le
  have hc : bad.card ≤ ∑ j ∈ range n, (shapes (n/(2*j+3))).card := by
    exact hb.trans (sum_le_sum fun _ _ => card_image_le)
  have total := card_filter_add_card_filter_not (s := shapes n) (fun v => common n v = 1)
  rw [primitive]
  dsimp [bad] at hc
  omega

private theorem tail (m : ℕ) :
    (∑ j ∈ range m, 1 / (2*(j : ℚ)+5)^2) + 1/(4*((m : ℚ)+2)) ≤ 1/8 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [sum_range_succ, Nat.cast_succ]
    have hstep : 1 / (2*(m : ℚ)+5)^2 + 1/(4*((m : ℚ)+1+2)) ≤ 1/(4*((m : ℚ)+2)) := by
      field_simp
      nlinarith [show 0 ≤ (m : ℚ) by positivity]
    linarith

private theorem reciprocal_bound (n : ℕ) : (∑ j ∈ range n, 1/(2*(j : ℚ)+3)^2) ≤ 17/72 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [sum_range_succ']
    have tr := tail n
    have hp : 0 < 1/(4*((n : ℚ)+2)) := by positivity
    simp only [Nat.cast_succ, Nat.cast_zero, mul_zero, zero_add]
    simp_rw [show ∀ j : ℚ, 2*(j+1)+3=2*j+5 by intro j; ring]
    linarith

private theorem odd_deficit (n : ℕ) (odd : n % 2 = 1) :
    48 * ((shapes n).card : ℚ) ≤ 48 * (a n : ℚ) + (n : ℚ)^2 * (17/72) := by
  have h : ((shapes n).card : ℚ) ≤ a n + ∑ j ∈ range n, ((shapes (n/(2*j+3))).card : ℚ) := by
    exact_mod_cast odd_bound n odd
  have each (j : ℕ) : 48 * ((shapes (n/(2*j+3))).card : ℚ) ≤ (n : ℚ)^2 * (1/(2*(j : ℚ)+3)^2) := by
    apply (shape_upper _).trans
    have hd : (0 : ℚ) < 2*(j : ℚ)+3 := by positivity
    have hle : ((n/(2*j+3) : ℕ) : ℚ) * (2*(j : ℚ)+3) ≤ n := by exact_mod_cast Nat.div_mul_le_self n (2*j+3)
    rw [mul_one_div, le_div_iff₀ (sq_pos_of_pos hd), ←mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle _
  have all := sum_le_sum (s := range n) (fun j _ => each j)
  rw [← mul_sum, ← mul_sum] at all
  have hb := mul_le_mul_of_nonneg_left (reciprocal_bound n) (sq_nonneg (n : ℚ))
  linarith

private theorem large_case (k : ℕ) (hk : 65 ≤ k) : a (2*k) ≤ a (2*k-1) := by
  let n := 2*k-1
  have odd : n % 2 = 1 := by dsimp [n]; omega
  have hc : (n : ℚ) = 2*(k : ℚ)-1 := by
    dsimp [n]
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have ol := (shape_bounds n (by dsimp [n]; omega)).1
  rw [if_pos odd] at ol
  have eu := (shape_bounds (2*k) (by omega)).2
  rw [if_neg (by omega)] at eu
  have el := shape_lower k (by omega)
  have ed : (a (2*k) : ℚ) + (shapes k).card ≤ (shapes (2*k)).card := by exact_mod_cast even_bound k
  have od := odd_deficit n odd
  rw [hc] at ol od
  push_cast at eu
  have room : (65 : ℚ) ≤ k := by exact_mod_cast hk
  change a (2*k) ≤ a n
  suffices (a (2*k) : ℚ) ≤ a n by exact_mod_cast this
  nlinarith only [ol, eu, el, ed, od, room, sq_nonneg ((k : ℚ)-65)]

private def sumBelow (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | m+1 => sumBelow f m + f m

private theorem sumBelow_eq (f : ℕ → ℕ) (m : ℕ) :
    sumBelow f m = ∑ i ∈ range m, f i := by
  induction m with
  | zero => simp [sumBelow]
  | succ m ih => rw [sumBelow, ih, sum_range_succ]

private abbrev isPrimitive (n x y : ℕ) : Prop :=
  0 < x ∧ x < y ∧ x + 2*y < n ∧ n < 2*(x+y) ∧ Nat.gcd (Nat.gcd x y) (n-x-y) = 1

private def quick (n : ℕ) : ℕ :=
  sumBelow (fun x => sumBelow (fun y => if isPrimitive n x y then 1 else 0)
    (n/2+1)) (n/3+1)

private theorem quick_eq (n : ℕ) : a n = quick n := by
  let box := range (n/3+1) ×ˢ range (n/2+1)
  have rect : ((shapes n).filter fun v => common n v = 1) =
      box.filter (fun v => isPrimitive n v.1 v.2) := by
    apply Finset.ext
    rintro ⟨x,y⟩
    rw [mem_filter, mem_filter, mem_shapes]
    simp only [box, mem_product, mem_range, common, third, isPrimitive]
    omega
  rw [primitive, rect, card_filter]
  simp only [box, sum_product, quick, sumBelow_eq]

set_option maxRecDepth 150000 in
set_option maxHeartbeats 4000000 in
private theorem small_cases : ∀ i : Fin 65, a (2*i.val) ≤ a (2*i.val-1) := by
  have checked : ∀ i : Fin 65, quick (2*i.val) ≤ quick (2*i.val-1) := by decide +kernel
  intro i
  rw [quick_eq, quick_eq]
  exact checked i

end PrimitiveTriangle

open OMA.S_oeis_a024162 PrimitiveTriangle

theorem OMA.solution : type_of% @OMA.S_oeis_a024162.main := by
  intro k _
  by_cases hk : k < 65
  · exact small_cases ⟨k, hk⟩
  · exact large_case k (by omega)
