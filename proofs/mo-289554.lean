import OMAStatements.S_mo_289554

/-!
The Pell argument in Schinzel and Sierpiński, Sur les sommes de quatre cubes,
Acta Arithmetica 4 (1958), pp. 20–21, Theorem 1 and its preceding lemma.
-/

namespace OMA.FourCubesPell

/-- A parity-preserving infinite family in an indefinite weighted-square fiber. -/
theorem weighted_family {r s u₀ v₀ : ℤ} (hr : 0 < r) (hs : 0 < s)
    (hNS : ¬ IsSquare (r * s)) (hNZ : u₀ ≠ 0 ∨ v₀ ≠ 0) :
    ∃ f : ℕ → ℤ × ℤ, Function.Injective f ∧ ∀ n,
      r * (f n).1 ^ 2 - s * (f n).2 ^ 2 = r * u₀ ^ 2 - s * v₀ ^ 2 ∧
      (f n).1 % 2 = u₀ % 2 ∧ (f n).2 % 2 = v₀ % 2 := by
  obtain ⟨w, hX, hY⟩ := Pell.Solution₁.exists_pos_of_not_isSquare (mul_pos hr hs) hNS
  let A : ℤ := r * s * w.y ^ 2
  let B : ℤ := w.x * w.y
  have hA : 0 < A := mul_pos (mul_pos hr hs) (pow_pos hY _)
  have hB : 0 < B := mul_pos (by omega) hY
  have hUnit : (1 + 2 * A) ^ 2 - r * s * (2 * B) ^ 2 = 1 := by
    dsimp only [A, B]
    linear_combination (-4 * r * s * w.y ^ 2) * w.prop
  let next (p : ℤ × ℤ) : ℤ × ℤ :=
    (p.1 + 2 * (A * p.1 + s * B * p.2), p.2 + 2 * (r * B * p.1 + A * p.2))
  let f : ℕ → ℤ × ℤ := Nat.rec (|u₀|, |v₀|) (fun _ p => next p)
  have h_base_pos : 0 < |u₀| + |v₀| := by
    rcases hNZ with h | h
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr h) (abs_nonneg _)
    · exact add_pos_of_nonneg_of_pos (abs_nonneg _) (abs_pos.mpr h)
  have hNonneg (n : ℕ) : 0 ≤ (f n).1 ∧ 0 ≤ (f n).2 ∧ 0 < (f n).1 + (f n).2 := by
    induction n with
    | zero => exact ⟨abs_nonneg _, abs_nonneg _, h_base_pos⟩
    | succ n ih =>
      obtain ⟨hu, hv, huv⟩ := ih
      let u := (f n).1
      let v := (f n).2
      change 0 ≤ u + 2 * (A * u + s * B * v) ∧
        0 ≤ v + 2 * (r * B * u + A * v) ∧
        0 < u + 2 * (A * u + s * B * v) + (v + 2 * (r * B * u + A * v))
      have hl : 0 ≤ A * u + s * B * v :=
        add_nonneg (mul_nonneg hA.le hu) (mul_nonneg (mul_nonneg hs.le hB.le) hv)
      have hh : 0 ≤ r * B * u + A * v :=
        add_nonneg (mul_nonneg (mul_nonneg hr.le hB.le) hu) (mul_nonneg hA.le hv)
      change 0 ≤ u at hu
      change 0 ≤ v at hv
      change 0 < u + v at huv
      omega
  have hStrict : StrictMono (fun n => (f n).1 + (f n).2) := by
    apply strictMono_nat_of_lt_succ
    intro n
    obtain ⟨hu, hv, huv⟩ := hNonneg n
    let u := (f n).1
    let v := (f n).2
    change u + v <
      u + 2 * (A * u + s * B * v) + (v + 2 * (r * B * u + A * v))
    have hAu : 0 < A * (u + v) := mul_pos hA huv
    have hcv : 0 ≤ s * B * v := mul_nonneg (mul_nonneg hs.le hB.le) hv
    have hcu : 0 ≤ r * B * u := mul_nonneg (mul_nonneg hr.le hB.le) hu
    linarith only [hAu, hcv, hcu]
  refine ⟨f, fun i j h => hStrict.injective (congrArg (fun q : ℤ × ℤ => q.1 + q.2) h), ?_⟩
  intro n
  induction n with
  | zero =>
    change r * |u₀| ^ 2 - s * |v₀| ^ 2 = r * u₀ ^ 2 - s * v₀ ^ 2 ∧
      |u₀| % 2 = u₀ % 2 ∧ |v₀| % 2 = v₀ % 2
    refine ⟨by rw [sq_abs, sq_abs], ?_, ?_⟩
    · by_cases h : 0 ≤ u₀
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (by omega : u₀ < 0)]
        omega
    · by_cases h : 0 ≤ v₀
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (by omega : v₀ < 0)]
        omega
  | succ n ih =>
    obtain ⟨he, hu, hv⟩ := ih
    let u := (f n).1
    let v := (f n).2
    have hu' : u % 2 = u₀ % 2 := hu
    have hv' : v % 2 = v₀ % 2 := hv
    change r * (u + 2 * (A * u + s * B * v)) ^ 2 -
        s * (v + 2 * (r * B * u + A * v)) ^ 2 = _ ∧
      (u + 2 * (A * u + s * B * v)) % 2 = u₀ % 2 ∧
      (v + 2 * (r * B * u + A * v)) % 2 = v₀ % 2
    refine ⟨?_, by omega, by omega⟩
    calc
      _ = ((1 + 2 * A) ^ 2 - r * s * (2 * B) ^ 2) * (r * u ^ 2 - s * v ^ 2) := by ring
      _ = _ := by rw [hUnit, one_mul]; exact he

/-- With fixed pair sums, the four-cube value is controlled by one weighted-square form. -/
private theorem four_cubes_identity (a b c d : ℤ) :
    4 * (a ^ 3 + b ^ 3 - c ^ 3 - d ^ 3) =
      (a + b) ^ 3 - (c + d) ^ 3 + 3 * ((a + b) * (a - b) ^ 2 - (c + d) * (c - d) ^ 2) := by
  ring

/-- Schinzel–Sierpiński's seed criterion for infinitely many four-cube representations. -/
theorem infinite_of_nonsquare_pair_sums (a b c d : ℤ)
    (hPos : 0 < (a + b) * (c + d)) (hNS : ¬ IsSquare ((a + b) * (c + d)))
    (hNe : a ≠ b ∨ c ≠ d) :
    {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 =
        a ^ 3 + b ^ 3 - c ^ 3 - d ^ 3}.Infinite := by
  let r := a + b
  let s := c + d
  let u₀ := a - b
  let v₀ := c - d
  have hNZ : u₀ ≠ 0 ∨ v₀ ≠ 0 := by
    dsimp only [u₀, v₀]
    omega
  have hF : ∃ f : ℕ → ℤ × ℤ, Function.Injective f ∧ ∀ n,
      r * (f n).1 ^ 2 - s * (f n).2 ^ 2 = r * u₀ ^ 2 - s * v₀ ^ 2 ∧
      (f n).1 % 2 = u₀ % 2 ∧ (f n).2 % 2 = v₀ % 2 := by
    change 0 < r * s at hPos
    change ¬ IsSquare (r * s) at hNS
    rcases mul_pos_iff.mp hPos with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · exact weighted_family hr hs hNS hNZ
    · have hEq : (-r) * (-s) = r * s := by ring
      obtain ⟨f, hinj, hf⟩ :=
        weighted_family (r := -r) (s := -s) (neg_pos.mpr hr) (neg_pos.mpr hs)
          (hEq.symm ▸ hNS) hNZ
      refine ⟨f, hinj, fun n => ?_⟩
      obtain ⟨he, hu, hv⟩ := hf n
      exact ⟨by linear_combination -he, hu, hv⟩
  obtain ⟨f, hinj, hf⟩ := hF
  let g (n : ℕ) : ℤ × ℤ × ℤ × ℤ :=
    ((r + (f n).1) / 2, (r - (f n).1) / 2, -((s + (f n).2) / 2), -((s - (f n).2) / 2))
  have hParts (n : ℕ) :
      (g n).1 + (g n).2.1 = r ∧ (g n).1 - (g n).2.1 = (f n).1 ∧
      -(g n).2.2.1 - (g n).2.2.2 = s ∧ -(g n).2.2.1 + (g n).2.2.2 = (f n).2 := by
    obtain ⟨_, hu, hv⟩ := hf n
    have hr' : u₀ % 2 = r % 2 := by dsimp [u₀, r]; omega
    have hs' : v₀ % 2 = s % 2 := by dsimp [v₀, s]; omega
    dsimp only [g]
    rw [hr'] at hu
    rw [hs'] at hv
    omega
  have hg : Function.Injective g := by
    intro i j he
    have hi := hParts i
    have hj := hParts j
    apply hinj
    apply Prod.ext
    · exact hi.2.1.symm.trans ((congrArg (fun v : ℤ × ℤ × ℤ × ℤ => v.1 - v.2.1) he).trans hj.2.1)
    · exact hi.2.2.2.symm.trans
        ((congrArg (fun v : ℤ × ℤ × ℤ × ℤ => -v.2.2.1 + v.2.2.2) he).trans hj.2.2.2)
  apply Set.infinite_of_injective_forall_mem hg
  intro n
  obtain ⟨hp, hu, hq, hv⟩ := hParts n
  have hN := four_cubes_identity a b c d
  have hG := four_cubes_identity (g n).1 (g n).2.1 (-(g n).2.2.1) (-(g n).2.2.2)
  have hsums : -(g n).2.2.1 + -(g n).2.2.2 = s := by linarith only [hq]
  have hdiff : -(g n).2.2.1 - -(g n).2.2.2 = (f n).2 := by linarith only [hv]
  rw [hp, hu, hsums, hdiff, (hf n).1] at hG
  change 4 * (a ^ 3 + b ^ 3 - c ^ 3 - d ^ 3) =
    r ^ 3 - s ^ 3 + 3 * (r * u₀ ^ 2 - s * v₀ ^ 2) at hN
  change (g n).1 ^ 3 + (g n).2.1 ^ 3 + (g n).2.2.1 ^ 3 + (g n).2.2.2 ^ 3 = _
  apply mul_left_cancel₀ (a := (4 : ℤ)) (by norm_num)
  linear_combination hG - hN

end OMA.FourCubesPell

/-!
The elementary residue classes of Schinzel and Sierpiński, Sur les sommes de
quatre cubes, Acta Arithmetica 4 (1958), Corollaries 1–7.
-/

namespace OMA.FourCubesResidues

open OMA.FourCubesPell

abbrev Fiber (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {v | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = n}

private theorem fromSeed {n : ℤ} (a b c d : ℤ)
    (he : a ^ 3 + b ^ 3 - c ^ 3 - d ^ 3 = n)
    (hp : 0 < (a+b)*(c+d)) (hSq : ¬ IsSquare ((a+b)*(c+d)))
    (hne : a ≠ b ∨ c ≠ d) : (Fiber n).Infinite := by
  rw [← he]
  exact infinite_of_nonsquare_pair_sums a b c d hp hSq hne

private theorem nonsquare_between {q x : ℤ} (hq : 0 ≤ q)
    (h₁ : q ^ 2 < x) (h₂ : x < (q + 1) ^ 2) : ¬ IsSquare x := by
  rintro ⟨r, hr⟩
  have he : |r| ^ 2 = x := by rw [sq_abs, sq, hr]
  by_cases h : |r| ≤ q
  · have hle := pow_le_pow_left₀ (abs_nonneg r) h 2
    omega
  · have hle : q + 1 ≤ |r| := by omega
    have hge := pow_le_pow_left₀ (show 0 ≤ q + 1 by omega) hle 2
    omega

private theorem nonsquare_step_five {x : ℤ} (hx : 5 ≤ x) :
    ¬ IsSquare (x * (x + 5)) :=
  nonsquare_between (q := x + 2) (by omega)
    (by nlinarith only [hx]) (by nlinarith only [hx])

private theorem nonsquare_step_eight {x : ℤ} (hx : 5 ≤ x) :
    ¬ IsSquare (x * (x + 8)) :=
  nonsquare_between (q := x + 3) (by omega)
    (by nlinarith only [hx]) (by nlinarith only [hx])

private theorem fiber_neg {n : ℤ} (h : (Fiber (-n)).Infinite) : (Fiber n).Infinite := by
  let neg (v : ℤ × ℤ × ℤ × ℤ) := (-v.1, -v.2.1, -v.2.2.1, -v.2.2.2)
  have hneg (v) : neg (neg v) = v := by
    rcases v with ⟨a,b,c,d⟩
    simp [neg]
  have hinj : Function.Injective neg := fun x y he => (hneg x).symm.trans
    ((congrArg neg he).trans (hneg y))
  refine ((Set.infinite_image_iff hinj.injOn).mpr h).mono ?_
  rintro _ ⟨v,hv,rfl⟩
  simp only [Fiber, neg, Set.mem_ofPred_eq] at hv ⊢
  linear_combination -hv

theorem six_mul_add_three (k : ℤ) : (Fiber (6*k+3)).Infinite := by
  suffices h : ∀ k : ℤ, 0 ≤ k → (Fiber (6*k+3)).Infinite by
    by_cases hk : 0 ≤ k
    · exact h k hk
    · have hn := h (-k - 1) (by omega)
      have he : 6*(-k-1)+3 = -(6*k+3) := by ring
      rw [he] at hn
      exact fiber_neg hn
  intro j hj
  apply fromSeed (j+1) (2*j+7) (j+5) (2*j+6) (by ring)
  · positivity
  · have hEq : (j+1+(2*j+7)) * (j+5+(2*j+6)) = (3*j+8)*((3*j+8)+3) := by ring
    rw [hEq]
    apply nonsquare_between (q := 3*j+9)
    · omega
    · nlinarith only [hj]
    · nlinarith only [hj]
  · exact Or.inl (by omega)

theorem eighteen_mul_add_one (k : ℤ) : (Fiber (18*k+1)).Infinite := by
  have hGeneric (hp : 0 < (5*k+44)*(5*k+49)) (hNS : ¬ IsSquare ((5*k+44)*(5*k+49))) :
      (Fiber (18*k+1)).Infinite := by
    apply fromSeed (2*k+14) (3*k+30) (2*k+23) (3*k+26) (by ring)
    · convert hp using 1
      ring
    · convert hNS using 2
      ring
    · omega
  by_cases hHigh : -7 ≤ k
  · refine hGeneric ?_ ?_
    · exact mul_pos (show 0 < 5*k+44 by omega) (show 0 < 5*k+49 by omega)
    · have hEq : 5*k+49 = (5*k+44)+5 := by ring
      rw [hEq]
      exact nonsquare_step_five (x := 5*k+44) (by omega)
  by_cases hLow : k ≤ -11
  · have hEq : (5*k+44)*(5*k+49) = (-(5*k+49)) * ((-(5*k+49))+5) := by ring
    refine hGeneric ?_ ?_
    · exact mul_pos_of_neg_of_neg (show 5*k+44 < 0 by omega) (show 5*k+49 < 0 by omega)
    · rw [hEq]
      exact nonsquare_step_five (x := -(5*k+49)) (by omega)
  have cases : k = -10 ∨ k = -9 ∨ k = -8 := by omega
  rcases cases with rfl | rfl | rfl
  · exact hGeneric (by decide) (by decide +kernel)
  · exact fromSeed 3 3 6 (-1) (by norm_num) (by decide) (by decide +kernel) (by decide)
  · exact fromSeed 2 1 5 3 (by norm_num) (by decide) (by decide +kernel) (by decide)

theorem eighteen_mul_add_eight (k : ℤ) : (Fiber (18*k+8)).Infinite := by
  have hGeneric (hp : 0 < (4*k-35)*(4*k-43)) (hNS : ¬ IsSquare ((4*k-35)*(4*k-43))) :
      (Fiber (18*k+8)).Infinite := by
    apply fromSeed (k-5) (3*k-30) (k-14) (3*k-29) (by ring)
    · convert hp using 1
      ring
    · convert hNS using 2
      ring
    · omega
  by_cases hHigh : 12 ≤ k
  · have hEq : (4*k-35)*(4*k-43) = (4*k-43)*((4*k-43)+8) := by ring
    refine hGeneric ?_ ?_
    · exact mul_pos (show 0 < 4*k-35 by omega) (show 0 < 4*k-43 by omega)
    · rw [hEq]
      exact nonsquare_step_eight (x := 4*k-43) (by omega)
  by_cases hLow : k ≤ 7
  · have hEq : (4*k-35)*(4*k-43) = (35-4*k)*((35-4*k)+8) := by ring
    refine hGeneric ?_ ?_
    · exact mul_pos_of_neg_of_neg (show 4*k-35 < 0 by omega) (show 4*k-43 < 0 by omega)
    · rw [hEq]
      exact nonsquare_step_eight (x := 35-4*k) (by omega)
  have cases : k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  · exact hGeneric (by decide) (by decide +kernel)
  · exact fromSeed 6 2 3 3 (by norm_num) (by decide) (by decide +kernel) (by decide)
  · exact fromSeed 6 0 3 1 (by norm_num) (by decide) (by decide +kernel) (by decide)
  · exact fromSeed 6 (-2) 1 1 (by norm_num) (by decide) (by decide +kernel) (by decide)

private theorem positive_sub_one_product_nonsquare {p n : ℕ} (hpn : 1 ≤ p*n)
    (hNo : ¬ IsSquare (-1 : ZMod p)) : ¬ IsSquare (n*(p*n-1)) := by
  intro h
  let m := p*n-1
  have hg₁ : Nat.gcd m n ∣ n := Nat.gcd_dvd_right _ _
  have hg₂ : Nat.gcd m n ∣ m := Nat.gcd_dvd_left _ _
  have hg : Nat.gcd m n ∣ 1 := by
    have he : p*n-m = 1 := by dsimp [m]; omega
    rw [← he]
    exact Nat.dvd_sub (dvd_mul_of_dvd_right hg₁ _) hg₂
  have hunit : IsUnit (gcd m n) := by
    change IsUnit (Nat.gcd m n)
    rw [Nat.dvd_antisymm hg (one_dvd _)]
    exact isUnit_one
  obtain ⟨q,hq⟩ := h
  have hpow : m*n = q^2 := by
    rw [mul_comm, pow_two]
    exact hq
  obtain ⟨t,ht⟩ := exists_eq_pow_of_mul_eq_pow hunit hpow
  apply hNo
  refine ⟨(t : ZMod p), ?_⟩
  have hcast := congrArg (fun x : ℕ => (x : ZMod p)) ht
  simp only [m, Nat.cast_sub hpn, Nat.cast_mul, ZMod.natCast_self, zero_mul,
    Nat.cast_one, zero_sub, pow_two] at hcast
  exact hcast

private theorem nine_mul_nonsquare {k : ℕ} (h : ¬ IsSquare k) : ¬ IsSquare (9*k) := by
  rintro ⟨r,hr⟩
  have hD : 3 ∣ r*r := by
    rw [← hr]
    exact dvd_mul_of_dvd_left (by decide : 3 ∣ 9) _
  have hrD : 3 ∣ r := (Nat.prime_three.dvd_mul.mp hD).elim id id
  obtain ⟨q,rfl⟩ := hrD
  have he : 9*k = 9*(q*q) := by
    calc
      _ = (3*q)*(3*q) := hr
      _ = _ := by ring
  exact h ⟨q, Nat.eq_of_mul_eq_mul_left (by decide : 0 < 9) he⟩

theorem eighteen_mul_add_seven (k : ℤ) : (Fiber (18*k+7)).Infinite := by
  by_cases hk₀ : k = 0
  · subst k
    apply Set.infinite_of_injective_forall_mem
      (f := fun t : ℤ => (2, -1, t, -t)) (fun _ _ he => congrArg (fun v => v.2.2.1) he)
    intro t
    change (2 : ℤ)^3 + (-1)^3 + t^3 + (-t)^3 = 18*0+7
    ring
  by_cases hk : 0 < k
  · let n := k.toNat
    have hn : (n : ℤ) = k := Int.toNat_of_nonneg hk.le
    have hn₁ : 1 ≤ 3*n := by omega
    have hNS : ¬ IsSquare (9*(n*(3*n-1))) :=
      nine_mul_nonsquare (positive_sub_one_product_nonsquare hn₁ (by decide +kernel))
    apply fromSeed (8*k-2) (k+2) (9*k-2) (-6*k+1) (by ring)
    · have he : (8*k-2+(k+2))*(9*k-2+(-6*k+1)) = (9*k)*(3*k-1) := by ring
      rw [he]
      exact mul_pos (show 0 < 9*k by omega) (show 0 < 3*k-1 by omega)
    · have he : (8*k-2+(k+2))*(9*k-2+(-6*k+1)) =
          ((9*(n*(3*n-1)) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hn₁, hn]
        ring
      rw [he, Int.isSquare_natCast_iff]
      exact hNS
    · omega
  · let n := (-k).toNat
    have hn : (n : ℤ) = -k := Int.toNat_of_nonneg (by omega)
    have hn₁ : 1 ≤ 7*n := by omega
    have hNS : ¬ IsSquare (n*(7*n-1)) :=
      positive_sub_one_product_nonsquare hn₁ (by decide +kernel)
    apply fromSeed (-9*k+2) (8*k-2) (-6*k+1) (-k-2) (by ring)
    · have he : (-9*k+2+(8*k-2))*(-6*k+1+(-k-2)) = (-k)*(-7*k-1) := by ring
      rw [he]
      exact mul_pos (show 0 < -k by omega) (show 0 < -7*k-1 by omega)
    · have he : (-9*k+2+(8*k-2))*(-6*k+1+(-k-2)) =
          ((n*(7*n-1) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hn₁, hn]
        ring
      rw [he, Int.isSquare_natCast_iff]
      exact hNS
    · omega

theorem six_mul (k : ℤ) : (Fiber (6*k)).Infinite := by
  suffices h : ∀ k : ℤ, 0 ≤ k → (Fiber (6*k)).Infinite by
    by_cases hk : 0 ≤ k
    · exact h k hk
    · have hn := h (-k) (by omega)
      rw [mul_neg] at hn
      exact fiber_neg hn
  intro j hj
  by_cases hzero : j = 0
  · subst j
    apply Set.infinite_of_injective_forall_mem
      (f := fun t : ℤ => (t, -t, 0, 0)) (fun _ _ he => congrArg Prod.fst he)
    intro t
    change t^3 + (-t)^3 + (0 : ℤ)^3 + 0^3 = 6*0
    ring
  by_cases hone : j = 1
  · subst j
    exact fromSeed 6 5 7 (-2) (by norm_num) (by decide) (by decide +kernel) (by decide)
  have hJ : 2 ≤ j := by omega
  have hmod : ∀ t : ZMod 6, t^7 = t := by decide +kernel
  have hd : (6 : ℤ) ∣ j^7-j := by
    apply Int.modEq_iff_dvd.mp
    apply (ZMod.intCast_eq_intCast_iff j (j^7) 6).mp
    simpa only [Int.cast_pow] using (hmod (j : ZMod 6)).symm
  obtain ⟨l,hl⟩ := hd
  have hl0 : 0 ≤ l := by
    have hj7 : j ≤ j^7 := le_self_pow₀ (show 1 ≤ j by omega) (by decide)
    omega
  let q := (j+1)*l
  let a := j*l+j+1
  let b := l-j^3
  let c := j*l-j+1
  let d := l+j^3
  have hValue : a^3+b^3-c^3-d^3 = 6*j := by
    dsimp only [a,b,c,d]
    linear_combination (-2*j^2)*hl
  have hProduct : (a+b)*(c+d) = (q+1)^2 - (j^3-j)^2 := by
    dsimp only [a,b,c,d,q]
    ring
  have hlarge : 3*j^6 ≤ j^8 := by
    have hj2 : 3 ≤ j^2 :=
      (by norm_num : (3 : ℤ) ≤ 2^2).trans (pow_le_pow_left₀ (by norm_num) hJ 2)
    calc
      _ ≤ j^2*j^6 := mul_le_mul_of_nonneg_right hj2 (by positivity)
      _ = _ := by ring
  have hsmall : 4*j^2+j ≤ 6*j^4 := by
    have hj2 : j ≤ j^2 := le_self_pow₀ (show 1 ≤ j by omega) (by decide)
    have hj4 : j^2 ≤ j^4 := pow_le_pow_right₀ (show 1 ≤ j by omega) (by decide)
    linarith only [hj2,hj4,show 0 ≤ j^2 by positivity]
  have hcube : 0 < j^3-j := by
    have hJ2 : 4 ≤ j^2 := by
      simpa using (pow_le_pow_left₀ (by norm_num : (0 : ℤ) ≤ 2) hJ 2)
    have hm := mul_le_mul_of_nonneg_left hJ2 hj
    nlinarith only [hm,hJ]
  have hq : 6*q = (j+1)*(j^7-j) := by
    dsimp only [q]
    linear_combination -(j+1)*hl
  have hLower : q^2 < (a+b)*(c+d) := by
    rw [hProduct]
    nlinarith only [hq,hlarge,hsmall,show 0 ≤ j^7 by positivity]
  have hUpper : (a+b)*(c+d) < (q+1)^2 := by
    rw [hProduct]
    exact sub_lt_self _ (pow_pos hcube _)
  have hPos : 0 < (a+b)*(c+d) := (sq_nonneg q).trans_lt hLower
  have hNS : ¬ IsSquare ((a+b)*(c+d)) :=
    nonsquare_between (mul_nonneg (by omega : 0 ≤ j+1) hl0) hLower hUpper
  apply fromSeed a b c d hValue hPos hNS
  by_contra! he
  obtain ⟨hab,hcd⟩ := he
  dsimp only [a,b,c,d] at hab hcd
  nlinarith only [hab,hcd,hcube,hJ]

theorem proved_h1 (N : ℤ)
    (h : N % 3 = 0 ∨ N % 18 = 1 ∨ N % 18 = 7 ∨ N % 18 = 8) : (Fiber N).Infinite := by
  rcases h with hd | h1 | h7 | h8
  · by_cases h6 : N % 6 = 0
    · have he : N = 6*(N/6) := by omega
      rw [he]
      exact six_mul (N/6)
    · have he : N = 6*(N/6)+3 := by omega
      rw [he]
      exact six_mul_add_three (N/6)
  · have he : N = 18*(N/18)+1 := by omega
    rw [he]
    exact eighteen_mul_add_one (N/18)
  · have he : N = 18*(N/18)+7 := by omega
    rw [he]
    exact eighteen_mul_add_seven (N/18)
  · have he : N = 18*(N/18)+8 := by omega
    rw [he]
    exact eighteen_mul_add_eight (N/18)

end OMA.FourCubesResidues

/-!
Watkins's choice of the ternary linear forms and auxiliary prime 83 for
Dem'yanenko's Pell construction, with the residue cover computed in ZMod 1494.
-/

namespace OMA.FourCubesWatkins

open Finset

abbrev Fiber (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) :=
  {v | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = n}

private def coeffs (R : Type*) [CommRing R] : ℕ → R × R
  | 0 => (1,0)
  | n+1 =>
    let q := coeffs R n
    (-3041*q.1 - 177840*q.2, -52*q.1 - 3041*q.2)

private def cubeRemainder {R : Type*} [CommRing R] (a b : R) : R :=
  27720*a^3 - 4708779*a^2*b + 277109259*a*b^2 - 5645559977*b^3

-- The third component of Watkins's vector w has a minus sign in the cube identity.
private def cubeVector (a b k : ℤ) : ℤ × ℤ × ℤ × ℤ :=
  (10*k+27*a-928*b, -19*k-9*a-602*b, -24*k+25*a-2937*b, 27*k-19*a+2746*b)

private theorem cubeVector_identity (a b k : ℤ) :
    let v := cubeVector a b k
    v.1^3 + v.2.1^3 + v.2.2.1^3 + v.2.2.2^3 =
      cubeRemainder a b + 1494*k*(a^2-3420*b^2) := by
  dsimp [cubeVector, cubeRemainder]
  ring

private theorem norm_coeffs (n : ℕ) :
    (coeffs ℤ n).1^2 - 3420*(coeffs ℤ n).2^2 = 1 := by
  induction n with
  | zero => norm_num [coeffs]
  | succ n ih =>
    simp only [coeffs]
    linear_combination ih

private theorem strict_coeffs_imag : StrictMono (fun n => |(coeffs ℤ n).2|) := by
  have hSigns (n : ℕ) :
      (0 < (coeffs ℤ n).1 ∧ 0 ≤ (coeffs ℤ n).2) ∨
      ((coeffs ℤ n).1 < 0 ∧ (coeffs ℤ n).2 ≤ 0) := by
    induction n with
    | zero => norm_num [coeffs]
    | succ n ih =>
      simp only [coeffs]
      omega
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := hSigns n
  · simp only [coeffs, abs_of_nonneg hb]
    rw [abs_of_neg (by omega : -52*(coeffs ℤ n).1 - 3041*(coeffs ℤ n).2 < 0)]
    omega
  · simp only [coeffs, abs_of_nonpos hb]
    rw [abs_of_nonneg (by omega : 0 ≤ -52*(coeffs ℤ n).1 - 3041*(coeffs ℤ n).2)]
    omega

private theorem coeffs_cast (n : ℕ) :
    (((coeffs ℤ n).1 : ZMod 1494), ((coeffs ℤ n).2 : ZMod 1494)) =
      coeffs (ZMod 1494) n := by
  induction n with
  | zero => simp [coeffs]
  | succ n ih =>
    have h1 := congrArg Prod.fst ih
    have h2 := congrArg Prod.snd ih
    simp only [coeffs, Int.cast_sub, Int.cast_mul, Int.cast_neg, Int.cast_ofNat]
    dsimp only at h1 h2
    rw [h1, h2]

private theorem coeffs_succ {R : Type*} [CommRing R] (n : ℕ) :
    coeffs R n.succ =
      (-3041*(coeffs R n).1-177840*(coeffs R n).2,
        -52*(coeffs R n).1-3041*(coeffs R n).2) := rfl

private theorem coeffs_period (n : ℕ) :
    coeffs (ZMod 1494) (n+738) = coeffs (ZMod 1494) n := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [Nat.succ_add, coeffs_succ, coeffs_succ n, ih]

private theorem coeffs_repeat (n k : ℕ) :
    coeffs (ZMod 1494) (n+738*k) = coeffs (ZMod 1494) n := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, coeffs_period, ih]

private def residues : Finset ℕ :=
  ((List.range 82).map (fun j =>
    let q := coeffs (ZMod 1494) (3*j+1)
    (cubeRemainder q.1 q.2).val)).toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem residues_exact :
    residues = (range 1494).filter (fun t => t % 18 = 2 ∧ t % 83 ≠ 0) := by
  decide +kernel

private theorem find_pell_exponent {n : ℤ} (h18 : n % 18 = 2) (h83 : n % 83 ≠ 0) :
    ∃ t : ℕ, cubeRemainder (coeffs (ZMod 1494) t).1 (coeffs (ZMod 1494) t).2 =
      (n : ZMod 1494) := by
  let r := (n : ZMod 1494).val
  have hr : (r : ℤ) = n % 1494 := ZMod.val_intCast n
  have hrlt : r < 1494 := ZMod.val_lt (n : ZMod 1494)
  have hr18 : r % 18 = 2 := by omega
  have hr83 : r % 83 ≠ 0 := by omega
  have hm : r ∈ residues := by
    rw [residues_exact]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hrlt, hr18, hr83⟩
  simp only [residues, List.mem_toFinset, List.mem_map, List.mem_range] at hm
  obtain ⟨j, _, he⟩ := hm
  exact ⟨3*j+1, ZMod.val_injective _ he⟩

private theorem cubeVector_imag_injective {a b k a' b' k' : ℤ}
    (h : cubeVector a b k = cubeVector a' b' k') : b = b' := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg (fun v => v.2.1) h
  have h4 := congrArg (fun v => v.2.2.2) h
  dsimp only [cubeVector] at h1 h2 h4
  have he : 47808*b = 47808*b' := by linear_combination 604*h1+919*h2+423*h4
  omega

/-- Four-cube representations for the nonzero classes modulo Watkins's auxiliary prime. -/
theorem infinite_of_mod_eighteen_two_not_dvd_83 (n : ℤ) (h18 : n % 18 = 2)
    (h83 : n % 83 ≠ 0) : (Fiber n).Infinite := by
  obtain ⟨t, ht⟩ := find_pell_exponent h18 h83
  let q (j : ℕ) := coeffs ℤ (t+738*j)
  have hm (j : ℕ) : (1494 : ℤ) ∣ n - cubeRemainder (q j).1 (q j).2 := by
    apply Int.modEq_iff_dvd.mp
    apply (ZMod.intCast_eq_intCast_iff _ _ 1494).mp
    have hp := (coeffs_cast (t+738*j)).trans (coeffs_repeat t j)
    have h1 := congrArg Prod.fst hp
    have h2 := congrArg Prod.snd hp
    change ((q j).1 : ZMod 1494) = (coeffs (ZMod 1494) t).1 at h1
    change ((q j).2 : ZMod 1494) = (coeffs (ZMod 1494) t).2 at h2
    simp only [cubeRemainder, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]
    simpa only [cubeRemainder, h1, h2] using ht
  let f (j : ℕ) :=
    cubeVector (q j).1 (q j).2 ((n - cubeRemainder (q j).1 (q j).2) / 1494)
  have hf : Function.Injective f := by
    intro i j he
    have h := cubeVector_imag_injective he
    have htj : t+738*i = t+738*j := strict_coeffs_imag.injective (congrArg abs h)
    omega
  apply Set.infinite_of_injective_forall_mem hf
  intro j
  change (f j).1^3 + (f j).2.1^3 + (f j).2.2.1^3 + (f j).2.2.2^3 = n
  dsimp only [f]
  rw [cubeVector_identity, norm_coeffs (t+738*j), mul_one]
  rw [mul_comm (1494 : ℤ), Int.ediv_mul_cancel (hm j)]
  ring

end OMA.FourCubesWatkins

/-!
The remaining residue classes in Dem'yanenko's 1966 four-cube theorem.
For the class 38 modulo 108 we use Watkins's specialization to 83 and
re-pair the four cubes so that the product of pair sums is 20 modulo 32.
-/

namespace OMA.FourCubesDivisible

open OMA.FourCubesPell OMA.FourCubesWatkins

private theorem fromSeed {n : ℤ} (a b c d : ℤ)
    (he : a^3 + b^3 - c^3 - d^3 = n)
    (hp : 0 < (a+b)*(c+d)) (hSq : ¬ IsSquare ((a+b)*(c+d)))
    (hne : a ≠ b ∨ c ≠ d) : (Fiber n).Infinite := by
  rw [← he]
  exact infinite_of_nonsquare_pair_sums a b c d hp hSq hne

private theorem nonsquare_between {q x : ℤ} (hq : 0 ≤ q)
    (h₁ : q^2 < x) (h₂ : x < (q + 1)^2) : ¬ IsSquare x := by
  rintro ⟨r, hr⟩
  have he : |r|^2 = x := by rw [sq_abs, sq, hr]
  by_cases h : |r| ≤ q
  · have hle := pow_le_pow_left₀ (abs_nonneg r) h 2
    omega
  · have hle : q+1 ≤ |r| := by omega
    have hge := pow_le_pow_left₀ (show 0 ≤ q+1 by omega) hle 2
    omega

private theorem sq_dominates_abs (x : ℤ) : |x| ≤ x^2 := by
  by_cases hx : x = 0
  · simp [hx]
  have h : 1 ≤ |x| := by
    have := abs_pos.mpr hx
    omega
  have hp := mul_le_mul_of_nonneg_left h (abs_nonneg x)
  rw [mul_one, ← sq, sq_abs] at hp
  exact hp

private theorem quad_pos (A B C x : ℤ) (hA : |B| ≤ A) (hC : 0 < C) :
    0 < A*x^2+B*x+C := by
  have h₀ : 0 ≤ A := (abs_nonneg B).trans hA
  have h₁ : -(B*x) ≤ |B| * |x| := by
    rw [← abs_mul]
    exact neg_le_abs _
  have h₂ : |B| * |x| ≤ A*x^2 :=
    (mul_le_mul_of_nonneg_right hA (abs_nonneg x)).trans
      (mul_le_mul_of_nonneg_left (sq_dominates_abs x) h₀)
  linarith only [h₁, h₂, hC]

private theorem case_54_add_2 (x : ℤ) : (Fiber (54*x+2)).Infinite := by
  let a := 29484*x^2+2211*x+43
  let b := 9828*x^2+485*x+4
  let c := 29484*x^2+2157*x+41
  let d := 9828*x^2+971*x+22
  let q := 39312*x^2+2912*x+55
  let u := 216*x+8
  have hp : (a+b)*(c+d) = q^2-u^2 := by
    dsimp [a,b,c,d,q,u]
    ring
  have hq : 0 ≤ q-1 := by
    dsimp [q]
    nlinarith only [quad_pos 39312 2912 54 x (by norm_num) (by norm_num)]
  have h₀ : 0 < 2*q-1-u^2 := by
    dsimp [q,u]
    nlinarith only [quad_pos 31968 2368 45 x (by norm_num) (by norm_num)]
  have hu : u ≠ 0 := by
    dsimp [u]
    omega
  have hl : (q-1)^2 < (a+b)*(c+d) := by
    rw [hp]
    nlinarith only [h₀]
  have hh : (a+b)*(c+d) < ((q-1)+1)^2 := by
    rw [hp]
    nlinarith only [sq_pos_of_ne_zero hu]
  apply fromSeed a b c d
  · dsimp [a,b,c,d]
    ring
  · exact (sq_nonneg (q-1)).trans_lt hl
  · exact nonsquare_between hq hl hh
  · by_contra! h
    obtain ⟨h₁,h₂⟩ := h
    dsimp [a,b,c,d] at h₁ h₂
    have : 540*x+20 = 0 := by linear_combination h₁-h₂
    omega

private theorem step_eight {x : ℤ} (hx : 5 ≤ x) :
    0 < x*(x+8) ∧ ¬ IsSquare (x*(x+8)) := by
  constructor
  · exact mul_pos (by omega) (by omega)
  · exact nonsquare_between (q := x+3) (by omega)
      (by nlinarith only [hx]) (by nlinarith only [hx])

private theorem case_54_add_20 (x : ℤ) (hD : (83 : ℤ) ∣ 54*x+20) :
    (Fiber (54*x+20)).Infinite := by
  let a := 3*x-11
  let b := x+2
  let c := 3*x-10
  let d := x-7
  have hx : (83 : ℤ) ∣ x-15 := by
    rw [show x-15 = 20*(54*x+20)-83*(13*x+5) by ring]
    exact dvd_sub (dvd_mul_of_dvd_right hD _) (dvd_mul_right _ _)
  obtain ⟨k,hk⟩ := hx
  have hr : x ≤ 1 ∨ 6 ≤ x := by omega
  have hp : 0 < (a+b)*(c+d) ∧ ¬ IsSquare ((a+b)*(c+d)) := by
    obtain h | h := hr
    · rw [show (a+b)*(c+d) = (9-4*x)*((9-4*x)+8) by
        dsimp [a,b,c,d]
        ring]
      exact step_eight (by omega)
    · rw [show (a+b)*(c+d) = (4*x-17)*((4*x-17)+8) by
        dsimp [a,b,c,d]
        ring]
      exact step_eight (by omega)
  refine fromSeed a b c d ?_ hp.1 hp.2 ?_
  · dsimp [a,b,c,d]
    ring
  · left
    dsimp [a,b]
    omega

private theorem case_216_sub_16 (x : ℤ) : (Fiber (216*x-16)).Infinite := by
  let a := 14742*x^2-2157*x+82
  let b := 4914*x^2-971*x+44
  let c := 14742*x^2-2211*x+86
  let d := 4914*x^2-485*x+8
  let q := 19656*x^2-2912*x+110
  let u := -216*x+16
  have hp : (a+b)*(c+d) = q^2-u^2 := by
    dsimp [a,b,c,d,q,u]
    ring
  have hq : 0 ≤ q-2 := by
    dsimp [q]
    nlinarith only [quad_pos 19656 (-2912) 108 x (by norm_num) (by norm_num)]
  have h₀ : 0 < 4*q-4-u^2 := by
    dsimp [q,u]
    nlinarith only [quad_pos 31968 (-4736) 180 x (by norm_num) (by norm_num)]
  have h₁ : 0 < u^2-(2*q-1) := by
    dsimp [q,u]
    nlinarith only [quad_pos 7344 (-1088) 37 x (by norm_num) (by norm_num)]
  have hl : (q-2)^2 < (a+b)*(c+d) := by
    rw [hp]
    nlinarith only [h₀]
  have hh : (a+b)*(c+d) < ((q-2)+1)^2 := by
    rw [hp]
    nlinarith only [h₁]
  apply fromSeed a b c d
  · dsimp [a,b,c,d]
    ring
  · exact (sq_nonneg (q-2)).trans_lt hl
  · exact nonsquare_between hq hl hh
  · by_contra! h
    obtain ⟨ha,hb⟩ := h
    dsimp [a,b,c,d] at ha hb
    have : 540*x-40 = 0 := by linear_combination ha-hb
    omega

private theorem step_thirtytwo {u : ℤ} (hu : 113 ≤ u) :
    0 < u*(u+32) ∧ ¬ IsSquare (u*(u+32)) := by
  constructor
  · exact mul_pos (by omega) (by omega)
  · exact nonsquare_between (q := u+15) (by omega)
      (by nlinarith only [hu]) (by nlinarith only [hu])

private theorem case_216_add_92 (x : ℤ) (hD : (83 : ℤ) ∣ 216*x+92) :
    (Fiber (216*x+92)).Infinite := by
  let a := 3*x-164
  let b := x-35
  let c := 3*x-160
  let d := x-71
  have hx : (83 : ℤ) ∣ x-38 := by
    rw [show x-38 = 5*(216*x+92)-83*(13*x+6) by ring]
    exact dvd_sub (dvd_mul_of_dvd_right hD _) (dvd_mul_right _ _)
  obtain ⟨k,hk⟩ := hx
  have hr : x ≤ -45 ∨ x = 38 ∨ 121 ≤ x := by omega
  have hp : 0 < (a+b)*(c+d) ∧ ¬ IsSquare ((a+b)*(c+d)) := by
    obtain h | h | h := hr
    · rw [show (a+b)*(c+d) = (199-4*x)*((199-4*x)+32) by
        dsimp [a,b,c,d]
        ring]
      exact step_thirtytwo (by omega)
    · have hval : (a+b)*(c+d) = 3713 := by norm_num [a,b,c,d,h]
      rw [hval]
      exact ⟨by norm_num, nonsquare_between (q := 60) (by norm_num)
        (by norm_num) (by norm_num)⟩
    · rw [show (a+b)*(c+d) = (4*x-231)*((4*x-231)+32) by
        dsimp [a,b,c,d]
        ring]
      exact step_thirtytwo (by omega)
  refine fromSeed a b c d ?_ hp.1 hp.2 ?_
  · dsimp [a,b,c,d]
    ring
  · left
    dsimp [a,b]
    omega

private theorem case_83_mul_108_add_46 (x : ℤ) : (Fiber (83*(108*x+46))).Infinite := by
  let a := 29484*x^2+25143*x+5371
  let b := 9828*x^2+8129*x+1682
  let c := 29484*x^2+25089*x+5348
  let d := 9828*x^2+8615*x+1889
  have h₁ : a-d = 19656*x^2+16528*x+3482 := by
    dsimp [a,d]
    ring
  have h₂ : c-b = 19656*x^2+16960*x+3666 := by
    dsimp [c,b]
    ring
  apply fromSeed a (-d) c (-b)
  · dsimp [a,b,c,d]
    ring
  · change 0 < (a-d)*(c-b)
    rw [h₁,h₂]
    exact mul_pos (quad_pos 19656 16528 3482 x (by norm_num) (by norm_num))
      (quad_pos 19656 16960 3666 x (by norm_num) (by norm_num))
  · change ¬ IsSquare ((a-d)*(c-b))
    have hc : ∀ y : ZMod 32,
        (19656*y^2+16528*y+3482)*(19656*y^2+16960*y+3666) = 20 := by decide +kernel
    have hn : ¬ IsSquare (20 : ZMod 32) := by decide +kernel
    have hm : (((a-d)*(c-b) : ℤ) : ZMod 32) = 20 := by
      rw [h₁,h₂]
      push_cast
      apply hc
    rintro ⟨z,hz⟩
    apply hn
    refine ⟨(z : ZMod 32), ?_⟩
    rw [← hm, hz, Int.cast_mul]
  · by_contra! h
    obtain ⟨ha,hb⟩ := h
    dsimp [a,b,c,d] at ha hb
    have : 540*x+230 = 0 := by linear_combination ha-hb
    omega

private theorem mul_ediv_add_of_emod {n m r : ℤ} (h : n % m = r) :
    m*(n/m)+r = n := by
  rw [← h]
  exact Int.mul_ediv_add_emod n m

private theorem last_residues {n : ℤ} (h18 : n % 18 = 2) (h2 : n % 54 ≠ 2)
    (h20 : n % 54 ≠ 20) (h38 : n % 108 ≠ 38) :
    n % 216 = 92 ∨ n % 216 = 200 := by omega

theorem infinite_of_mod_eighteen_two_dvd_83 (n : ℤ) (h18 : n % 18 = 2)
    (h83 : n % 83 = 0) : (Fiber n).Infinite := by
  have hD : (83 : ℤ) ∣ n := Int.dvd_iff_emod_eq_zero.mpr h83
  by_cases h2 : n % 54 = 2
  · have he := mul_ediv_add_of_emod h2
    simpa only [he] using case_54_add_2 (n/54)
  by_cases h20 : n % 54 = 20
  · have he := mul_ediv_add_of_emod h20
    have hD' : (83 : ℤ) ∣ 54*(n/54)+20 := by rwa [he]
    simpa only [he] using case_54_add_20 (n/54) hD'
  by_cases h38 : n % 108 = 38
  · obtain ⟨m,hm⟩ := hD
    have hD₁ : (108 : ℤ) ∣ n-38 := ⟨n/108, by linarith only [mul_ediv_add_of_emod h38]⟩
    have hD₂ : (108 : ℤ) ∣ m-46 := by
      rw [show m-46 = 95*(n-38)-108*(73*m-33) by
        rw [hm]
        ring]
      exact dvd_sub (dvd_mul_of_dvd_right hD₁ _) (dvd_mul_right _ _)
    have hMod : (46 : ℤ) ≡ m [ZMOD 108] := Int.modEq_iff_dvd.mpr hD₂
    have hmMod : m % 108 = 46 := by simpa [Int.ModEq] using hMod.symm
    have he : 83*(108*(m/108)+46) = n := by rw [mul_ediv_add_of_emod hmMod, ← hm]
    simpa only [he] using case_83_mul_108_add_46 (m/108)
  have hLast := last_residues h18 h2 h20 h38
  obtain h92 | h200 := hLast
  · have he := mul_ediv_add_of_emod h92
    have hD' : (83 : ℤ) ∣ 216*(n/216)+92 := by rwa [he]
    simpa only [he] using case_216_add_92 (n/216) hD'
  · have he : 216*(n/216+1)-16 = n := by linarith only [mul_ediv_add_of_emod h200]
    simpa only [he] using case_216_sub_16 (n/216+1)

/-- Dem'yanenko's remaining residue class in the four-cube theorem. -/
theorem proved_h2 (n : ℤ) (h18 : n % 18 = 2) : (Fiber n).Infinite := by
  by_cases h83 : n % 83 = 0
  · exact infinite_of_mod_eighteen_two_dvd_83 n h18 h83
  · exact infinite_of_mod_eighteen_two_not_dvd_83 n h18 h83

end OMA.FourCubesDivisible

/-!
The two residue ranges in the four-cubes theorem. The first is the
Sierpiński–Schinzel range and the second is Dem'yanenko's Theorem 1.
-/

namespace OMA.R_mo_289554_R1

private theorem three_cubes_residue (a b c : ℤ) :
    (a ^ 3 + b ^ 3 + c ^ 3) % 9 ≠ 4 ∧ (a ^ 3 + b ^ 3 + c ^ 3) % 9 ≠ 5 := by
  have h : ∀ x y z : ZMod 9, x ^ 3 + y ^ 3 + z ^ 3 ≠ 4 ∧
      x ^ 3 + y ^ 3 + z ^ 3 ≠ 5 := by decide +kernel
  obtain ⟨h4, h5⟩ := h (a : ZMod 9) (b : ZMod 9) (c : ZMod 9)
  constructor
  · intro he
    apply h4
    have he' := (ZMod.intCast_eq_intCast_iff' (a ^ 3 + b ^ 3 + c ^ 3) 4 9).2 (by
      simpa using he)
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using he'
  · intro he
    apply h5
    have he' := (ZMod.intCast_eq_intCast_iff' (a ^ 3 + b ^ 3 + c ^ 3) 5 9).2 (by
      simpa using he)
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_ofNat] using he'

private theorem infinite_neg {N : ℤ}
    (h : {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = -N}.Infinite) :
    {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = N}.Infinite := by
  let f (v : ℤ × ℤ × ℤ × ℤ) := (-v.1, -v.2.1, -v.2.2.1, -v.2.2.2)
  have inv (v : ℤ × ℤ × ℤ × ℤ) : f (f v) = v := by
    rcases v with ⟨a, b, c, d⟩
    simp [f]
  have hinj : Function.Injective f := fun x y he =>
    (inv x).symm.trans ((congrArg f he).trans (inv y))
  refine ((Set.infinite_image_iff hinj.injOn).mpr h).mono ?_
  rintro _ ⟨v, hv, rfl⟩
  simp only [f, Set.mem_ofPred_eq] at hv ⊢
  linear_combination -hv

def H1 : Prop := ∀ N : ℤ, N % 3 = 0 ∨ N % 18 = 1 ∨ N % 18 = 7 ∨ N % 18 = 8 →
  {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = N}.Infinite

def H2 : Prop := ∀ N : ℤ, N % 18 = 2 →
  {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = N}.Infinite

theorem main : H1 → H2 → type_of% @OMA.S_mo_289554.main := by
  intro h1 h2 N hN
  obtain ⟨a, b, c, rfl⟩ := hN
  let n := a ^ 3 + b ^ 3 + c ^ 3
  change {v : ℤ × ℤ × ℤ × ℤ | v.1 ^ 3 + v.2.1 ^ 3 + v.2.2.1 ^ 3 + v.2.2.2 ^ 3 = n}.Infinite
  have ⟨h4, h5⟩ : n % 9 ≠ 4 ∧ n % 9 ≠ 5 := three_cubes_residue a b c
  by_cases hPos : n % 3 = 0 ∨ n % 18 = 1 ∨ n % 18 = 7 ∨ n % 18 = 8
  · exact h1 n hPos
  by_cases hNeg : (-n) % 3 = 0 ∨ (-n) % 18 = 1 ∨ (-n) % 18 = 7 ∨ (-n) % 18 = 8
  · exact infinite_neg (h1 (-n) hNeg)
  by_cases hTwo : n % 18 = 2
  · exact h2 n hTwo
  exact infinite_neg (h2 (-n) (by omega))

end OMA.R_mo_289554_R1

theorem OMA.solution : type_of% @OMA.S_mo_289554.main :=
  OMA.R_mo_289554_R1.main OMA.FourCubesResidues.proved_h1 OMA.FourCubesDivisible.proved_h2
