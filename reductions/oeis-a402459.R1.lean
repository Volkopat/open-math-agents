import OMAStatements.S_oeis_a402459

/-!
# A402459: factor pairs of ternary repunits

Credit: @jiyongparkphysics. Source statement by @rodolfoquint.
The difference-of-squares factorization appears in https://oeis.org/A402459 .
For an admissible square x² of length L, its digits give both x² ≤ R
and 2R < 3x², where R is the L-digit base-three repunit. The two factors
of R attached to a pair of squares must therefore satisfy 4d < e < 6d.
-/

namespace OMA.R_oeis_a402459_R1

private theorem shift_twice (ds : List ℕ) :
    2*Nat.ofDigits 3 (ds.map (fun d => d+1)) + 1 =
    2*Nat.ofDigits 3 ds + 3^ds.length := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, pow_succ]
    omega

private theorem digit_bound (ds : List ℕ) (h : ∀ d ∈ ds, d ≤ 1) :
    2*Nat.ofDigits 3 ds < 3^ds.length := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    have ha := h d (by simp)
    have hb := ih (fun t ht => h t (List.mem_cons_of_mem _ ht))
    simp only [Nat.ofDigits_cons, List.length_cons, pow_succ]
    omega

private theorem ratio {d e x : ℕ} (hd : 0 < d) (he : e = d+2*x)
    (hu : x*x ≤ d*e) (hl : 2*(d*e) < 3*(x*x)) :
    4*d < e ∧ e < 6*d := by
  zify at *
  constructor
  · by_contra! h
    have hs : (0:ℤ) ≤ 3*d-2*x := by omega
    have ht : (0:ℤ) ≤ 6*x+d := by positivity
    rw [he] at hl
    nlinarith [mul_nonneg hs ht, sq_nonneg (d:ℤ)]
  · by_contra! h
    have hs : (0:ℤ) ≤ 2*x-5*d := by omega
    have ht : (0:ℤ) ≤ 2*x+d := by positivity
    rw [he] at hu
    nlinarith [mul_nonneg hs ht, mul_pos hd hd]

/-- The finite range of positive squares with up to 128 ternary digits. -/
def H1 : Prop := ∀ m : ℕ, 0 < m → (Nat.digits 3 m).length ≤ 128 →
  IsSquare m → 2 ∉ Nat.digits 3 m →
  ¬ IsSquare (Nat.ofDigits (3 : ℕ) ((Nat.digits 3 m).map (fun d => d+1)))

/-- In larger lengths check only comparable repunit factors giving an integer root. -/
def H2 : Prop := ∀ L d e x : ℕ, 128 < L → d*e = (3^L-1)/2 →
  4*d < e → e < 6*d → e = d+2*x →
  (Nat.digits 3 (x*x)).length = L → 2 ∈ Nat.digits 3 (x*x)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a402459.main := by
  intro small large
  rintro ⟨m,hm,hs,hdig,ht⟩
  by_cases hlen : (Nat.digits 3 m).length ≤ 128
  · exact small m hm hlen hs hdig ht
  obtain ⟨x,hx⟩ := hs
  obtain ⟨y,hy⟩ := ht
  let L := (Nat.digits 3 m).length
  have shift := shift_twice (Nat.digits 3 m)
  rw [Nat.ofDigits_digits,hy] at shift
  change 2*(y*y)+1 = 2*m+3^L at shift
  have low := Nat.base_pow_length_digits_le 3 m (by decide) hm.ne'
  change 3^L ≤ 3*m at low
  have high := digit_bound (Nat.digits 3 m) (by
    intro i hi
    have ha := Nat.digits_lt_base (by decide : 1 < 3) hi
    have hb : i ≠ 2 := fun h => hdig (h ▸ hi)
    omega)
  rw [Nat.ofDigits_digits] at high
  change 2*m < 3^L at high
  have hpow : 1 < 3^L := Nat.one_lt_pow (by dsimp [L]; omega) (by decide)
  have hxy : x < y := by
    by_contra! h
    have := Nat.mul_self_le_mul_self h
    rw [hx] at shift
    omega
  let d := y-x
  let e := y+x
  have hd : 0 < d := Nat.sub_pos_of_lt hxy
  have heq : d+x = y := Nat.sub_add_cancel hxy.le
  have he : e = d+2*x := by dsimp [e]; omega
  have hw : 2*(d*e)+1 = 3^L := by
    rw [hx, ← heq] at shift
    rw [he]
    nlinarith [shift]
  have hprod : d*e = (3^L-1)/2 := by omega
  have hr := ratio hd he (by rw [← hx]; omega) (by rw [← hx]; omega)
  apply hdig
  rw [hx]
  exact large L d e x (by dsimp [L]; omega) hprod hr.1 hr.2 he (by rw [← hx])

end OMA.R_oeis_a402459_R1
