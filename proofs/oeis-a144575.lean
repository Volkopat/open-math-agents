import OMAStatements.S_oeis_a144575
import Mathlib

/-!
# A144575: Mathar's recurrence for the EGF exp(1 - sqrt(1 - 2x - 3x^2))

Write `q = 1 - 2x - 3x^2`, `w = 1 + 3x` and `f = exp(1 - sqrt q)`. Near `0` the function
`f` satisfies `E := q w f'' - 4 f' - w^3 f = 0`, because `f' = f w / sqrt q` and
`3 q + w^2 = 4`. The recurrence is the `n`th derivative at `0` of the fourth-order equation
`L := q f'''' - (5 + 15x) f''' - (10 + 6x + 9x^2) f'' - (15 + 45x) f' - 27 f = 0`, and
`w^2 L = w E'' - 3 E'` identically, so `L = 0` near `0` as well.
-/

open scoped ContDiff

namespace OMA.A144575Proof

open OMA.S_oeis_a144575

noncomputable def f : ℝ → ℝ := fun x : ℝ => Real.exp (1-Real.sqrt (1-2*x-3*x^2))

noncomputable def D (k : ℕ) : ℝ → ℝ := iteratedDeriv k f

def U : Set ℝ := {x | 0 < 1 - 2 * x - 3 * x ^ 2} ∩ {x | 0 < 1 + 3 * x}

theorem U_open : IsOpen U :=
  (isOpen_lt continuous_const (by fun_prop)).inter (isOpen_lt continuous_const (by fun_prop))

theorem zero_mem : (0 : ℝ) ∈ U := by
  constructor <;> simp

theorem f_cd : ContDiffOn ℝ ∞ f U := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  unfold f
  apply Real.contDiff_exp.contDiffAt.comp
  apply contDiffAt_const.sub
  exact (Real.contDiffAt_sqrt hx.1.ne').comp x (by fun_prop)

theorem D_cd (k : ℕ) : ContDiffOn ℝ ∞ (D k) U := by
  induction k with
  | zero => simpa [D] using f_cd
  | succ k ih =>
    have := ih.deriv_of_isOpen U_open (m := ∞) (by simp)
    simpa [D, iteratedDeriv_succ] using this

theorem D_hasDeriv (k : ℕ) {x : ℝ} (hx : x ∈ U) : HasDerivAt (D k) (D (k + 1) x) x := by
  have h := ((D_cd k).contDiffAt (U_open.mem_nhds hx)).differentiableAt (by simp)
  have := h.hasDerivAt
  simpa [D, iteratedDeriv_succ] using this

theorem hq (x : ℝ) : HasDerivAt (fun y : ℝ => 1 - 2 * y - 3 * y ^ 2) (-2 - 6 * x) x := by
  have := (((hasDerivAt_id' x).const_mul (2 : ℝ)).const_sub 1).sub
    ((hasDerivAt_pow 2 x).const_mul (3 : ℝ))
  refine this.congr_deriv ?_
  norm_num; ring

theorem hw (x : ℝ) : HasDerivAt (fun y : ℝ => 1 + 3 * y) 3 x := by
  have := ((hasDerivAt_id' x).const_mul (3 : ℝ)).const_add 1
  exact this.congr_deriv (by ring)

theorem hs (x : ℝ) (hx : x ∈ U) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 - 2 * y - 3 * y ^ 2))
      ((-2 - 6 * x) / (2 * Real.sqrt (1 - 2 * x - 3 * x ^ 2))) x :=
  (hq x).sqrt hx.1.ne'

/-- `f' = f w / sqrt q`. -/
noncomputable def G1 (y : ℝ) : ℝ := f y * ((1 + 3 * y) / Real.sqrt (1 - 2 * y - 3 * y ^ 2))

theorem f_hasDeriv (x : ℝ) (hx : x ∈ U) : HasDerivAt f (G1 x) x := by
  have := ((hs x hx).const_sub 1).exp
  unfold G1 f
  convert this using 1
  have h0 : 0 < Real.sqrt (1 - 2 * x - 3 * x ^ 2) := Real.sqrt_pos.mpr hx.1
  field_simp
  ring

theorem D1_eq (x : ℝ) (hx : x ∈ U) : D 1 x = G1 x := by
  simp only [D, iteratedDeriv_one]
  exact (f_hasDeriv x hx).deriv

theorem D2_eq (x : ℝ) (hx : x ∈ U) :
    D 2 x = G1 x * ((1 + 3 * x) / Real.sqrt (1 - 2 * x - 3 * x ^ 2)) +
      f x * ((3 * Real.sqrt (1 - 2 * x - 3 * x ^ 2) - (1 + 3 * x) *
        ((-2 - 6 * x) / (2 * Real.sqrt (1 - 2 * x - 3 * x ^ 2)))) /
          Real.sqrt (1 - 2 * x - 3 * x ^ 2) ^ 2) := by
  have hev : D 1 =ᶠ[nhds x] G1 := by
    filter_upwards [U_open.mem_nhds hx] with y hy
    exact D1_eq y hy
  have h2 : D 2 x = deriv (D 1) x := by simp [D, iteratedDeriv_succ]
  rw [h2, hev.deriv_eq]
  have h0 : Real.sqrt (1 - 2 * x - 3 * x ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hx.1).ne'
  have := (f_hasDeriv x hx).mul ((hw x).div (hs x hx) h0)
  exact this.deriv

/-- The second-order equation. -/
theorem E_zero (x : ℝ) (hx : x ∈ U) :
    (1 - 2 * x - 3 * x ^ 2) * (1 + 3 * x) * D 2 x - 4 * D 1 x - (1 + 3 * x) ^ 3 * D 0 x = 0 := by
  rw [D2_eq x hx, D1_eq x hx]
  have hD0 : D 0 x = f x := by simp [D]
  rw [hD0]
  unfold G1
  set s := Real.sqrt (1 - 2 * x - 3 * x ^ 2) with hs_def
  have hs0 : s ≠ 0 := (Real.sqrt_pos.mpr hx.1).ne'
  have hs2 : s ^ 2 = 1 - 2 * x - 3 * x ^ 2 := Real.sq_sqrt hx.1.le
  rw [← hs2]
  field_simp
  linear_combination (18 * x * f x + 6 * f x) * hs2

/-- A term `(a + b y + c y^2 + d y^3) * f^(k)(y)`. -/
structure Term where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  k : ℕ

noncomputable def Term.ev (t : Term) (y : ℝ) : ℝ :=
  (t.a + t.b * y + t.c * y ^ 2 + t.d * y ^ 3) * D t.k y

def Term.dl (t : Term) : List Term :=
  [⟨t.b, 2 * t.c, 3 * t.d, 0, t.k⟩, ⟨t.a, t.b, t.c, t.d, t.k + 1⟩]

noncomputable def evl (l : List Term) (y : ℝ) : ℝ := (l.map fun t => t.ev y).sum

def dll (l : List Term) : List Term := l.flatMap Term.dl

theorem Term.hasDeriv (t : Term) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt t.ev (evl t.dl x) x := by
  have hp : HasDerivAt (fun y : ℝ => t.a + t.b * y + t.c * y ^ 2 + t.d * y ^ 3)
      (t.b + 2 * t.c * x + 3 * t.d * x ^ 2) x := by
    have := ((((hasDerivAt_id' x).const_mul t.b).const_add t.a).add
      ((hasDerivAt_pow 2 x).const_mul t.c)).add ((hasDerivAt_pow 3 x).const_mul t.d)
    refine this.congr_deriv ?_
    norm_num; ring
  have := hp.mul (D_hasDeriv t.k hx)
  unfold Term.ev
  refine this.congr_deriv ?_
  simp [evl, Term.dl, Term.ev]

theorem ev_hasDeriv (l : List Term) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (evl l) (evl (dll l) x) x := by
  induction l with
  | nil =>
    have e : evl [] = fun _ => 0 := by funext y; simp [evl]
    rw [e]; simpa [evl, dll] using hasDerivAt_const x (0 : ℝ)
  | cons t l ih =>
    have := (t.hasDeriv hx).add ih
    have e1 : evl (t :: l) = fun y => t.ev y + evl l y := by
      funext y; simp [evl]
    have e2 : evl (dll (t :: l)) x = evl t.dl x + evl (dll l) x := by
      simp [evl, dll, List.flatMap_cons, List.map_append, List.sum_append]
    rw [e1, e2]
    exact this

theorem ev_dl_zero (l : List Term) (h : ∀ y ∈ U, evl l y = 0) : ∀ y ∈ U, evl (dll l) y = 0 := by
  intro x hx
  have hev : evl l =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [U_open.mem_nhds hx] with y hy
    exact h y hy
  have := (ev_hasDeriv l hx).deriv
  rw [hev.deriv_eq] at this
  simpa using this.symm

def E0 : List Term := [⟨1, 1, -9, -9, 2⟩, ⟨-4, 0, 0, 0, 1⟩, ⟨-1, -9, -27, -27, 0⟩]

theorem E0_zero : ∀ y ∈ U, evl E0 y = 0 := by
  intro y hy
  have := E_zero y hy
  simp [evl, E0, Term.ev]
  linear_combination this

/-- The fourth-order equation near `0`. -/
theorem L_zero (x : ℝ) (hx : x ∈ U) :
    (1 - 2 * x - 3 * x ^ 2) * D 4 x - (5 + 15 * x) * D 3 x - (10 + 6 * x + 9 * x ^ 2) * D 2 x -
      (15 + 45 * x) * D 1 x - 27 * D 0 x = 0 := by
  have h1 := ev_dl_zero _ E0_zero x hx
  have h2 := ev_dl_zero _ (ev_dl_zero _ E0_zero) x hx
  simp [evl, dll, E0, Term.dl, Term.ev] at h1 h2
  have hw : 1 + 3 * x ≠ 0 := hx.2.ne'
  have : (1 + 3 * x) ^ 2 * ((1 - 2 * x - 3 * x ^ 2) * D 4 x - (5 + 15 * x) * D 3 x -
      (10 + 6 * x + 9 * x ^ 2) * D 2 x - (15 + 45 * x) * D 1 x - 27 * D 0 x) = 0 := by
    linear_combination (1 + 3 * x) * h2 - 3 * h1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd ((pow_eq_zero_iff two_ne_zero).mp h) hw
  · exact h

theorem itD (n k : ℕ) : iteratedDeriv n (D k) = D (n + k) := by
  simp only [D, iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem cdD (n k : ℕ) : ContDiffAt ℝ n (D k) 0 :=
  ((D_cd k).contDiffAt (U_open.mem_nhds zero_mem)).of_le (by exact_mod_cast le_top)

theorem m1 (n k : ℕ) (hk : 1 ≤ k) :
    iteratedDeriv n (fun y => y * D k y) 0 = n * D (n + k - 1) 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) (cdD n k)]
  simp only [iteratedDeriv_fun_id_zero, itD]
  rcases n with _ | m
  · simp
  · rw [Finset.sum_eq_single 1]
    · simp only [Nat.choose_one_right]
      congr 2
      · push_cast; ring
      · omega
    · intro b _ hb; simp [hb]
    · intro h; simp at h

theorem m2 (n k : ℕ) (hk : 2 ≤ k) :
    iteratedDeriv n (fun y => y ^ 2 * D k y) 0 = n * (n - 1) * D (n + k - 2) 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) (cdD n k)]
  simp only [iteratedDeriv_fun_pow_zero, itD]
  rcases n with _ | _ | m
  · simp
  · simp
  · rw [Finset.sum_eq_single 2]
    · simp only []
      rw [show m + 1 + 1 - 2 + k = m + 1 + 1 + k - 2 by omega, Nat.cast_choose_two]
      push_cast
      ring
    · intro b _ hb; simp [hb]
    · intro h; simp at h

theorem recurrence (n : ℕ) :
    a (n+4) - (2*(n:ℝ)+5)*a (n+3) - (3*(n:ℝ)^2+12*n+10)*a (n+2) -
      3*(2*(n:ℝ)+5)*a (n+1) - 9*((n:ℝ)+3)*(n+1)*a n = 0 := by
  set L : ℝ → ℝ := fun y => D 4 y + (-2) * (y * D 4 y) + (-3) * (y ^ 2 * D 4 y) + (-5) * D 3 y +
    (-15) * (y * D 3 y) + (-10) * D 2 y + (-6) * (y * D 2 y) + (-9) * (y ^ 2 * D 2 y) +
    (-15) * D 1 y + (-45) * (y * D 1 y) + (-27) * D 0 y with hL
  have hev : L =ᶠ[nhds 0] fun _ => 0 := by
    filter_upwards [U_open.mem_nhds zero_mem] with y hy
    have := L_zero y hy
    simp only [hL]
    linear_combination this
  have h := hev.iteratedDeriv_eq n
  have hD := cdD n
  rw [hL] at h
  simp (disch := fun_prop) only [iteratedDeriv_fun_add, iteratedDeriv_const_mul_field] at h
  rw [m1 n 4 (by norm_num), m2 n 4 (by norm_num), m1 n 3 (by norm_num), m1 n 2 (by norm_num),
    m2 n 2 (by norm_num), m1 n 1 (by norm_num)] at h
  simp only [itD] at h
  have e0 : iteratedDeriv n (fun _ : ℝ => (0 : ℝ)) 0 = 0 := by
    rcases n with _ | n
    · simp
    · simp
  rw [e0] at h
  have ha : ∀ m, a m = D m 0 := fun m => rfl
  simp only [ha]
  simp only [show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega,
    show n + 3 - 1 = n + 2 by omega, show n + 2 - 1 = n + 1 by omega,
    show n + 2 - 2 = n by omega, show n + 1 - 1 = n by omega] at h
  rw [show n + 4 = n + 4 from rfl] at h
  linear_combination h

end OMA.A144575Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a144575.main :=
  OMA.A144575Proof.recurrence
