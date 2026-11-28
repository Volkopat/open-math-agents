import OMAStatements.S_oeis_a084029

namespace OMA.S_oeis_a084029

private abbrev width (a : ℕ) := (Nat.digits 10 a).length
private abbrev ds (a : ℕ) := (Nat.digits 10 a).sum

private theorem dsStep (m : ℕ) : ds m = m%10 + ds (m/10) := by
  cases m with
  | zero => decide
  | succ m => unfold ds; rw [Nat.digits_def' (by decide : 1 < 10) (Nat.succ_pos m), List.sum_cons]

/-- The complementary positions add to 9, including padded leading zeros. -/
private theorem complement (u a : ℕ) (h : a < 10^u) : ds a + ds (10^u-1-a) = 9*u := by
  induction u generalizing a with
  | zero =>
    obtain rfl : a = 0 := by simpa using h
    decide
  | succ u ih =>
    rw [pow_succ] at h ⊢
    have hdiv : a/10 < 10^u := by omega
    have hc := ih (a/10) hdiv
    rw [dsStep a, dsStep (10^u*10-1-a),
      show (10^u*10-1-a)/10 = 10^u-1-a/10 by omega,
      show (10^u*10-1-a)%10 = 9-a%10 by omega]
    omega

private theorem digitBound (n : ℕ) : ds n ≤ 9*width n := by
  simpa [mul_comm] using List.sum_le_card_nsmul _ 9 fun x hx =>
    Nat.le_of_lt_succ (Nat.digits_lt_base (by decide) hx)

private theorem widthBound {n : ℕ} (hn : 36 ≤ n) : 18*width n ≤ n := by
  have hp (i : ℕ) : 18*(i+3) ≤ 10^(i+2) := by
    induction i with
    | zero => decide
    | succ i ih => rw [show i+1+2 = (i+2)+1 by omega, pow_succ]; omega
  by_cases hd : width n ≤ 2
  · omega
  · obtain ⟨i, hi⟩ : ∃ i, width n = i+3 := ⟨width n - 3, by omega⟩
    have hlow := (Nat.lt_digits_length_iff (k := i+2) (by decide : 1 < 10) n).mp (by change i+2 < width n; omega)
    rw [hi]
    exact (hp i).trans hlow

private theorem joined {lo hi k : ℕ} (hlo : width lo ≤ k) (hhi : 0 < hi) :
    width (lo + 10^k*hi) = k + width hi ∧ ds (lo + 10^k*hi) = ds lo + ds hi := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hlo
  have he := Nat.digits_append_zeroes_append_digits (b := 10) (n := lo) (k := v) (by decide) hhi
  unfold width ds
  rw [← he]
  simp [Nat.add_assoc]

private def glue (n hi lo j : ℕ) := 10^j*lo + 10^(n-width hi)*hi

private theorem glueSpec {n W hi lo j : ℕ} (hh : 0 < hi) (hl : 0 < lo)
    (hwh : width hi ≤ W) (hwl : width lo ≤ W) (hj : j+W ≤ n-W) (hW : W ≤ n)
    (hs : ds lo + ds hi = n) (hdh : n ∣ hi) (hdl : n ∣ lo) :
    qualifies n (glue n hi lo j) ∧ glue n hi lo j % 10^(n-W) = 10^j*lo := by
  have hword := Nat.digits_base_pow_mul (b := 10) (k := j) (by decide) hl
  have hwidth : width (10^j*lo) = j + width lo := by simp [width, hword]
  have hsum : ds (10^j*lo) = ds lo := by simp [ds, hword]
  have hcut : n-W ≤ n-width hi := by omega
  have hlow : width (10^j*lo) ≤ n-W := by omega
  obtain ⟨hw, hds⟩ := joined (hlow.trans hcut) hh
  have hpow : 10^(n-W) ∣ 10^(n-width hi)*hi := dvd_mul_of_dvd_left (Nat.pow_dvd_pow 10 hcut) _
  have hlt := (Nat.digits_length_le_iff (by decide : 1 < 10) (10^j*lo)).mp hlow
  unfold glue
  constructor
  · refine ⟨?_, dvd_add (dvd_mul_of_dvd_right hdl _) (dvd_mul_of_dvd_right hdh _), ?_⟩
    · change width _ = _
      omega
    · change ds _ = _
      omega
  · rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hpow, Nat.mod_eq_of_lt hlt, Nat.add_zero, Nat.mod_eq_of_lt hlt]

/-- The blocks `n` and `n*(10^u-1)` have digit sums adding to `n`. Either
block can lead; the other may move among the unused positions below it. -/
private theorem largeRow {n : ℕ} (hn : 20 ≤ n) :
    ∃ s : Finset ℕ, n ≤ s.card ∧ ∀ m ∈ s, qualifies n m := by
  let d := width n
  let u := (n-ds n)/9
  let W := u+d
  let A := n*(10^u-1)
  have hd : 0 < d := List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr (by omega))
  have h18 : 18*d ≤ n ∨ d = 2 ∧ ds n + 9*(n/10) = n := by
    by_cases h : 36 ≤ n
    · exact .inl (widthBound h)
    · have e : Nat.digits 10 n = [n % 10, n / 10] := by
        rw [Nat.digits_def' (by decide : 1 < 10) (show 0 < n by omega),
          Nat.digits_def' (by decide : 1 < 10) (show 0 < n / 10 by omega),
          show n / 10 / 10 = 0 by omega, Nat.digits_zero, Nat.mod_eq_of_lt (show n / 10 < 10 by omega)]
      right
      simp [d, width, ds, e] <;> omega
  have h9 : ds n ≤ 9*d := digitBound n
  have hmod : n%9 = ds n%9 := Nat.modEq_nine_digits_sum n
  have htotal : ds n + 9*u = n := by dsimp [u]; omega
  have hdu : d ≤ u := by omega
  have hW : 4*W ≤ n := by dsimp [W]; omega
  have hpow : n < 10^d := Nat.lt_base_pow_length_digits (by decide)
  have hnu : n < 10^u := hpow.trans_le (Nat.pow_le_pow_right (by decide) hdu)
  have hA : 0 < A := by dsimp [A]; exact Nat.mul_pos (by omega) (by omega)
  have hWA : width A ≤ W := by
    apply (Nat.digits_length_le_iff (by decide : 1 < 10) A).mpr
    dsimp only [A, W]
    rw [pow_add, Nat.mul_comm (10^u)]
    exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans_lt (Nat.mul_lt_mul_of_pos_right hpow (by positivity))
  have hsplit : A = (10^u-n) + 10^u*(n-1) := by
    dsimp only [A]
    zify [show 1 ≤ n by omega, show 1 ≤ 10^u by omega, hnu.le]
    ring
  have hsub : width (10^u-n) ≤ u := (Nat.digits_length_le_iff (by decide : 1 < 10) _).mpr (by omega)
  have hsumA : ds A = 9*u := by
    rw [hsplit, (joined hsub (show 0 < n-1 by omega)).2]
    have hc := complement u (n-1) (by omega)
    rw [show 10^u-1-(n-1) = 10^u-n by omega] at hc
    omega
  let K := n/2+1
  let f : Bool × Fin K → ℕ := fun p =>
    if p.1 then glue n A n p.2.val else glue n n A p.2.val
  have spec (p : Bool × Fin K) : qualifies n (f p) ∧
      f p % 10^(n-W) = 10^p.2.val * (if p.1 then n else A) := by
    obtain ⟨b,i⟩ := p
    have hi : i.val+W ≤ n-W := by have := i.isLt; dsimp [K] at this; omega
    have hdn : width n ≤ W := by change d ≤ u+d; omega
    cases b
    · exact glueSpec (by omega) hA hdn hWA hi (by omega) (by omega) dvd_rfl (dvd_mul_right ..)
    · exact glueSpec hA (by omega) hWA hdn hi (by omega) (by omega) (dvd_mul_right ..) dvd_rfl
  have hdiff (i j : ℕ) : 10^i*A ≠ 10^j*n := by
    intro he
    have hc : 10^i*(10^u-1) = 10^j :=
      Nat.eq_of_mul_eq_mul_left (show 0 < n by omega) (by dsimp [A] at he; linarith)
    have hh := congrArg (fun x : ℕ => x%3) hc
    have hzero : (10^u-1)%3 = 0 := by have := Nat.pow_mod 10 u 3; simp at this; omega
    simp [Nat.mul_mod, Nat.pow_mod, hzero] at hh
  have same (z : ℕ) (hz : 0 < z) {i j : Fin K} (h : 10^i.val*z = 10^j.val*z) : i = j := by
    exact Fin.ext ((Nat.pow_right_inj (by decide : 1 < 10)).mp (Nat.eq_of_mul_eq_mul_right hz h))
  have hinj : Function.Injective f := by
    rintro ⟨b,i⟩ ⟨c,j⟩ he
    have hl := congrArg (fun x : ℕ => x % 10^(n-W)) he
    change f (b,i) % _ = f (c,j) % _ at hl
    rw [(spec (b,i)).2, (spec (c,j)).2] at hl
    cases b <;> cases c
    · exact congrArg (Prod.mk false) (same A hA hl)
    · exact (hdiff _ _ hl).elim
    · exact (hdiff _ _ hl.symm).elim
    · exact congrArg (Prod.mk true) (same n (by omega) hl)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj]
    simp [K]
    omega
  · intro m hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    exact (spec i).1

-- Offsets from the first n-digit integer in the finitely many short rows.
private def offsets : ℕ → List ℕ
  | 1 => [0]
  | 3 => [2, 11, 20]
  | 4 => [12, 120, 300, 1020]
  | 5 => [40, 130, 220, 310, 400]
  | 6 => [14, 32, 50, 104, 122, 140]
  | 7 => [6, 132, 321, 510, 1014, 1140, 1203]
  | 8 => [16, 160, 232, 304, 520, 1024, 1240, 1312]
  | 9 => [8, 17, 26, 35, 44, 53, 62, 71, 80]
  | 10 => [90, 180, 270, 360, 450, 540, 630, 720, 810, 900]
  | 11 => [109, 208, 307, 406, 505, 604, 703, 802, 901, 10009, 10108]
  | 12 => [56, 92, 128, 164, 236, 272, 308, 344, 380, 416, 452, 524]
  | 13 => [129, 246, 363, 480, 714, 831, 1065, 1182, 1416, 1533, 1650, 2118, 2235]
  | 14 => [256, 382, 508, 634, 760, 1138, 1264, 1390, 1516, 1642, 2146, 2272, 2524, 2650]
  | 15 => [95, 185, 275, 365, 455, 545, 590, 635, 680, 725, 770, 815, 860, 905, 950]
  | 16 => [96, 384, 528, 672, 816, 960, 1248, 1392, 1536, 1680, 1824, 2256, 2544, 2832, 3264, 3408]
  | 17 => [169, 475, 628, 781, 934, 1087, 1393, 1546, 1852, 2158, 2464, 2617, 2770, 2923, 3076, 3229, 3382]
  | 18 => [98, 188, 278, 296, 368, 386, 458, 476, 494, 548, 566, 584, 638, 656, 674, 692, 728, 746]
  | 19 => [189, 873, 1386, 1557, 1728, 2583, 2754, 2925, 3096, 3267, 3438, 3609, 3780, 3951, 4293, 4464, 4635, 4806, 5148]
  | _ => []

private def shortEntries (n : ℕ) : Finset ℕ :=
  ((offsets n).map (fun i => 10^(n-1) + i)).toFinset

private theorem shortRows (j : Fin 20) : 0 < j.val → j.val ≠ 2 →
    j.val ≤ (shortEntries j.val).card ∧ ∀ m ∈ shortEntries j.val, qualifies j.val m := by
  revert j
  unfold qualifies
  decide +kernel

private theorem second (m : ℕ) : qualifies 2 m ↔ m = 20 := by
  constructor
  · intro h
    have hm : m < 100 := (Nat.digits_length_le_iff (by decide : 1 < 10) m).mp h.1.le
    have check : ∀ j : Fin 100, qualifies 2 j.val → j.val = 20 := by unfold qualifies; decide +kernel
    exact check ⟨m,hm⟩ h
  · rintro rfl
    unfold qualifies
    decide +kernel

end OMA.S_oeis_a084029

open OMA.S_oeis_a084029 in
theorem OMA.solution : type_of% @OMA.S_oeis_a084029.main := by
  exact ⟨second, fun n hn h2 => if h : 20 ≤ n then largeRow h else
    ⟨shortEntries n, shortRows ⟨n, by omega⟩ hn h2⟩⟩
