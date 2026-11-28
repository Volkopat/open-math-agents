import OMAStatements.S_mo_394327

-- Credit: @connoranderson (complete counterexample and Lean proof).
-- Independent audit and proof-stage assembly: @CubeJerry.
-- uses note #94224
-- Source: https://github.com/connoranderson/open-math-agents/blob/3551e9ce5486f9f672009d9e63d1eeffed465bfc/proofs/mo-394327.lean

/-!
Take the decreasing shifts 65, 64, 1 and the positive integer nodes 1, 2, 3, 4.
The four-column evaluation determinant is 12 at exponent 1. At exponent 3/2,
integer square-root bounds put the determinant between -8845058 and -8845034. The intermediate value theorem and a nonzero kernel vector give
four simultaneous integer zeros.

The evaluation determinant occurs in user44143's comment on the question:
https://mathoverflow.net/questions/394327#comment1007280_394327 .
The shifts, the sign certificate, and the resulting counterexample are derived here.
-/

namespace OMA.S_mo_394327
open Matrix

noncomputable def A (t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, (66:ℝ)^t, (4290:ℝ)^t, (8580:ℝ)^t;
    1, (67:ℝ)^t, (4422:ℝ)^t, (13266:ℝ)^t;
    1, (68:ℝ)^t, (4556:ℝ)^t, (18224:ℝ)^t;
    1, (69:ℝ)^t, (4692:ℝ)^t, (23460:ℝ)^t]

noncomputable def D (t : ℝ) : ℝ :=
  ((7161211920:ℝ)^t + (5560470432:ℝ)^t + (4232596896:ℝ)^t + (5643462528:ℝ)^t + (6846847920:ℝ)^t + (3989033136:ℝ)^t + (6843751200:ℝ)^t + (5238124320:ℝ)^t + (3926868660:ℝ)^t + (2697243120:ℝ)^t + (2697243120:ℝ)^t + (2579971680:ℝ)^t) -
      ((5728969536:ℝ)^t + (7054328160:ℝ)^t + (4170352824:ℝ)^t + (7054328160:ℝ)^t + (5318710848:ℝ)^t + (4108108752:ℝ)^t + (5394486240:ℝ)^t + (6743107800:ℝ)^t + (3869957520:ℝ)^t + (2737500480:ℝ)^t + (2619062160:ℝ)^t + (2617912440:ℝ)^t)

theorem det_expand (t : ℝ) : (A t).det = D t := by
  have group (a b c : ℕ) : (a:ℝ)^t*(b:ℝ)^t*(c:ℝ)^t = ((a*b*c : ℕ):ℝ)^t := by
    push_cast
    rw [Real.mul_rpow (by positivity : 0 ≤ (a:ℝ)*b) (by positivity),Real.mul_rpow (by positivity) (by positivity)]
  calc
    _ = (((67:ℝ)^t*(4556:ℝ)^t*(23460:ℝ)^t) + ((69:ℝ)^t*(4422:ℝ)^t*(18224:ℝ)^t) + ((68:ℝ)^t*(4692:ℝ)^t*(13266:ℝ)^t) + ((66:ℝ)^t*(4692:ℝ)^t*(18224:ℝ)^t) + ((66:ℝ)^t*(4422:ℝ)^t*(23460:ℝ)^t) + ((66:ℝ)^t*(4556:ℝ)^t*(13266:ℝ)^t) + ((68:ℝ)^t*(4290:ℝ)^t*(23460:ℝ)^t) + ((67:ℝ)^t*(4290:ℝ)^t*(18224:ℝ)^t) + ((69:ℝ)^t*(4290:ℝ)^t*(13266:ℝ)^t) + ((69:ℝ)^t*(4556:ℝ)^t*(8580:ℝ)^t) + ((67:ℝ)^t*(4692:ℝ)^t*(8580:ℝ)^t) + ((68:ℝ)^t*(4422:ℝ)^t*(8580:ℝ)^t)) -
      (((67:ℝ)^t*(4692:ℝ)^t*(18224:ℝ)^t) + ((68:ℝ)^t*(4422:ℝ)^t*(23460:ℝ)^t) + ((69:ℝ)^t*(4556:ℝ)^t*(13266:ℝ)^t) + ((66:ℝ)^t*(4556:ℝ)^t*(23460:ℝ)^t) + ((66:ℝ)^t*(4422:ℝ)^t*(18224:ℝ)^t) + ((66:ℝ)^t*(4692:ℝ)^t*(13266:ℝ)^t) + ((69:ℝ)^t*(4290:ℝ)^t*(18224:ℝ)^t) + ((67:ℝ)^t*(4290:ℝ)^t*(23460:ℝ)^t) + ((68:ℝ)^t*(4290:ℝ)^t*(13266:ℝ)^t) + ((68:ℝ)^t*(4692:ℝ)^t*(8580:ℝ)^t) + ((67:ℝ)^t*(4556:ℝ)^t*(8580:ℝ)^t) + ((69:ℝ)^t*(4422:ℝ)^t*(8580:ℝ)^t)) := by
      rw [Matrix.det_succ_row_zero]
      simp only [Fin.sum_univ_four,Matrix.det_fin_three,Matrix.submatrix_apply]
      change ((-1:ℝ)^0*1*((67:ℝ)^t*(4556:ℝ)^t*(23460:ℝ)^t - (67:ℝ)^t*(18224:ℝ)^t*(4692:ℝ)^t - (4422:ℝ)^t*(68:ℝ)^t*(23460:ℝ)^t + (4422:ℝ)^t*(18224:ℝ)^t*(69:ℝ)^t + (13266:ℝ)^t*(68:ℝ)^t*(4692:ℝ)^t - (13266:ℝ)^t*(4556:ℝ)^t*(69:ℝ)^t)) +
        ((-1:ℝ)^1*(66:ℝ)^t*(1*(4556:ℝ)^t*(23460:ℝ)^t - 1*(18224:ℝ)^t*(4692:ℝ)^t - (4422:ℝ)^t*1*(23460:ℝ)^t + (4422:ℝ)^t*(18224:ℝ)^t*1 + (13266:ℝ)^t*1*(4692:ℝ)^t - (13266:ℝ)^t*(4556:ℝ)^t*1)) +
        ((-1:ℝ)^2*(4290:ℝ)^t*(1*(68:ℝ)^t*(23460:ℝ)^t - 1*(18224:ℝ)^t*(69:ℝ)^t - (67:ℝ)^t*1*(23460:ℝ)^t + (67:ℝ)^t*(18224:ℝ)^t*1 + (13266:ℝ)^t*1*(69:ℝ)^t - (13266:ℝ)^t*(68:ℝ)^t*1)) +
        ((-1:ℝ)^3*(8580:ℝ)^t*(1*(68:ℝ)^t*(4692:ℝ)^t - 1*(4556:ℝ)^t*(69:ℝ)^t - (67:ℝ)^t*1*(4692:ℝ)^t + (67:ℝ)^t*(4556:ℝ)^t*1 + (4422:ℝ)^t*1*(69:ℝ)^t - (4422:ℝ)^t*(68:ℝ)^t*1)) = _
      ring
    _ = _ := by
      have h0 := group 67 4556 23460
      have h1 := group 67 4692 18224
      have h2 := group 68 4422 23460
      have h3 := group 69 4422 18224
      have h4 := group 68 4692 13266
      have h5 := group 69 4556 13266
      have h6 := group 66 4556 23460
      have h7 := group 66 4692 18224
      have h8 := group 66 4422 23460
      have h9 := group 66 4422 18224
      have h10 := group 66 4692 13266
      have h11 := group 66 4556 13266
      have h12 := group 68 4290 23460
      have h13 := group 69 4290 18224
      have h14 := group 67 4290 23460
      have h15 := group 67 4290 18224
      have h16 := group 69 4290 13266
      have h17 := group 68 4290 13266
      have h18 := group 68 4692 8580
      have h19 := group 69 4556 8580
      have h20 := group 67 4692 8580
      have h21 := group 67 4556 8580
      have h22 := group 69 4422 8580
      have h23 := group 68 4422 8580
      norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23
      simp only [D,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23]

lemma three_halves_bound (n a : ℕ) (hl : a^2 ≤ n^3) (hu : n^3 ≤ (a+1)^2) :
    (a:ℝ) ≤ (n:ℝ)^(3/2:ℝ) ∧ (n:ℝ)^(3/2:ℝ) ≤ (a:ℝ)+1 := by
  have hs : ((n:ℝ)^(3/2:ℝ))^2 = (n:ℝ)^3 := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
    norm_num
  have hp : 0 ≤ (n:ℝ)^(3/2:ℝ) := Real.rpow_nonneg (by positivity) _
  constructor
  · apply (sq_le_sq₀ (by positivity) hp).mp
    rw [hs]; exact_mod_cast hl
  · apply (sq_le_sq₀ hp (by positivity)).mp
    rw [hs]; exact_mod_cast hu

theorem D_one : D 1 = 12 := by norm_num [D]

theorem D_three_halves : D (3/2) < 0 := by
  have h0 := (three_halves_bound 7161211920 606009997416204 (by norm_num) (by norm_num)).2
  have h1 := (three_halves_bound 5728969536 433625455765473 (by norm_num) (by norm_num)).1
  have h2 := (three_halves_bound 7054328160 592493360638390 (by norm_num) (by norm_num)).1
  have h3 := (three_halves_bound 5560470432 414636283906170 (by norm_num) (by norm_num)).2
  have h4 := (three_halves_bound 4232596896 275366030218913 (by norm_num) (by norm_num)).2
  have h5 := (three_halves_bound 4170352824 269314166395140 (by norm_num) (by norm_num)).1
  have h6 := (three_halves_bound 7054328160 592493360638390 (by norm_num) (by norm_num)).1
  have h7 := (three_halves_bound 5643462528 423953737793516 (by norm_num) (by norm_num)).2
  have h8 := (three_halves_bound 6846847920 566547101946548 (by norm_num) (by norm_num)).2
  have h9 := (three_halves_bound 5318710848 387890881866656 (by norm_num) (by norm_num)).1
  have h10 := (three_halves_bound 4108108752 263307298881727 (by norm_num) (by norm_num)).1
  have h11 := (three_halves_bound 3989033136 251942518194655 (by norm_num) (by norm_num)).2
  have h12 := (three_halves_bound 6843751200 566162785096437 (by norm_num) (by norm_num)).2
  have h13 := (three_halves_bound 5394486240 396209728064155 (by norm_num) (by norm_num)).1
  have h14 := (three_halves_bound 6743107800 553719928311349 (by norm_num) (by norm_num)).1
  have h15 := (three_halves_bound 5238124320 379108657624189 (by norm_num) (by norm_num)).2
  have h16 := (three_halves_bound 3926868660 246076172910279 (by norm_num) (by norm_num)).2
  have h17 := (three_halves_bound 3869957520 240746120144883 (by norm_num) (by norm_num)).1
  have h18 := (three_halves_bound 2737500480 143229114186333 (by norm_num) (by norm_num)).1
  have h19 := (three_halves_bound 2697243120 140081292743121 (by norm_num) (by norm_num)).2
  have h20 := (three_halves_bound 2697243120 140081292743121 (by norm_num) (by norm_num)).2
  have h21 := (three_halves_bound 2619062160 134035151306296 (by norm_num) (by norm_num)).1
  have h22 := (three_halves_bound 2617912440 133946902552682 (by norm_num) (by norm_num)).1
  have h23 := (three_halves_bound 2579971680 131045589313275 (by norm_num) (by norm_num)).2
  unfold D
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23]

theorem D_cont : Continuous D := by unfold D; fun_prop (disch := norm_num)

end OMA.S_mo_394327

namespace OMA.S_mo_394327
open Matrix Set

lemma row_value (t : ℝ) (c : Fin 4 → ℝ) (i : Fin 4) :
    ((A t) *ᵥ c) i = f 65 64 1 t c ((i.val:ℝ)+1) := by
  have group (a b : ℕ) : (a:ℝ)^t*(b:ℝ)^t = ((a*b : ℕ):ℝ)^t := by
    push_cast; rw [Real.mul_rpow (by positivity) (by positivity)]
  fin_cases i
  · have hab := group 66 65
    have habc := group 4290 2
    norm_num at hab habc
    simp only [mulVec,dotProduct,Fin.sum_univ_four]
    change 1*c 0 + (66:ℝ)^t*c 1 + (4290:ℝ)^t*c 2 + (8580:ℝ)^t*c 3 =
      f 65 64 1 t c (((0 : ℕ) : ℝ) + 1)
    norm_num [f]
    rw [← habc,← hab]; ring
  · have hab := group 67 66
    have habc := group 4422 3
    norm_num at hab habc
    simp only [mulVec,dotProduct,Fin.sum_univ_four]
    change 1*c 0 + (67:ℝ)^t*c 1 + (4422:ℝ)^t*c 2 + (13266:ℝ)^t*c 3 =
      f 65 64 1 t c (((1 : ℕ) : ℝ) + 1)
    norm_num [f]
    rw [← habc,← hab]; ring
  · have hab := group 68 67
    have habc := group 4556 4
    norm_num at hab habc
    simp only [mulVec,dotProduct,Fin.sum_univ_four]
    change 1*c 0 + (68:ℝ)^t*c 1 + (4556:ℝ)^t*c 2 + (18224:ℝ)^t*c 3 =
      f 65 64 1 t c (((2 : ℕ) : ℝ) + 1)
    norm_num [f]
    rw [← habc,← hab]; ring
  · have hab := group 69 68
    have habc := group 4692 5
    norm_num at hab habc
    simp only [mulVec,dotProduct,Fin.sum_univ_four]
    change 1*c 0 + (69:ℝ)^t*c 1 + (4692:ℝ)^t*c 2 + (23460:ℝ)^t*c 3 =
      f 65 64 1 t c (((3 : ℕ) : ℝ) + 1)
    norm_num [f]
    rw [← habc,← hab]; ring

/-- Four positive integer roots at one exponent strictly between 1 and 3/2. -/
theorem four_integer_roots : ∃ t : ℝ, 1 < t ∧ t < 3/2 ∧ ∃ c : Fin 4 → ℝ, c ≠ 0 ∧
    ∀ i : Fin 4, f 65 64 1 t c ((i.val:ℝ)+1) = 0 := by
  obtain ⟨t,ht,he⟩ := intermediate_value_Ioo' (f:=D) (a:=(1:ℝ)) (b:=3/2)
    (by norm_num) D_cont.continuousOn (show 0 ∈ Ioo (D (3/2)) (D 1) from ⟨D_three_halves,by rw [D_one]; norm_num⟩)
  obtain ⟨c,hc,hzero⟩ := (Matrix.exists_mulVec_eq_zero_iff (M:=A t)).mpr ((det_expand t).trans he)
  refine ⟨t,ht.1,ht.2,c,hc,fun i => ?_⟩
  simpa only [row_value,Pi.zero_apply] using congrFun hzero i

end OMA.S_mo_394327

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_394327.main) := by
  intro h
  obtain ⟨t,ht,_,c,hc,hr⟩ := OMA.S_mo_394327.four_integer_roots
  have ub := (h 65 64 1 (Or.inr (by norm_num)) t ht c hc).2 ({1,2,3,4} : Finset ℕ)
  have h4 : ({1,2,3,4} : Finset ℕ).card ≤ 3 := by
    apply ub
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact ⟨by norm_num,by simpa using hr 0⟩
    · exact ⟨by norm_num,by have hz := hr (1 : Fin 4); norm_num at hz ⊢; exact hz⟩
    · exact ⟨by norm_num,by have hz := hr (2 : Fin 4); norm_num at hz ⊢; exact hz⟩
    · exact ⟨by norm_num,by have hz := hr (3 : Fin 4); norm_num at hz ⊢; exact hz⟩
  norm_num at h4
