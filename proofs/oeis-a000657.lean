import OMAStatements.S_oeis_a000657

/-!
Peter Bala's eventual-periodicity conjecture for the median Euler numbers.
The finite functional below inverts the sum of a function and its translate,
up to one higher difference. Symmetrizing at opposite odd integers reproduces
the two passes of the Entringer triangle. At the median the evaluation bases
are products of consecutive integers, hence even.
Lean proof by KoaOkano, assisted by OpenAI Codex.
-/

namespace A000657Proof

open OMA.S_oeis_a000657

private abbrev F := ℕ → ℤ
private def diff (f : F) (x : ℕ) : ℤ := f (x+1) - f x

private def D : ℕ → F → F
  | 0, f => f
  | n+1, f => diff (D n f)

private theorem D_diff (n : ℕ) (f : F) : D n (diff f) = D (n+1) f := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg diff ih

private theorem D_scale (n : ℕ) (c : ℤ) (f : F) (t : ℕ) :
    D n (fun x => c * f x) t = c * D n f t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp only [D, diff, ih]; ring

-- The product rule after r+1 differences. At t = 0 both terms have a factor r+1.
private theorem D_times (r : ℕ) (f : F) (t : ℕ) :
    D (r+1) (fun x => (x:ℤ)*f x) t =
      ((t:ℤ)+r+1)*D (r+1) f t + (r+1:ℤ)*D r f t := by
  induction r generalizing t with
  | zero => simp [D, diff]; ring
  | succ r ih =>
    change D (r+1) _ (t+1) - D (r+1) _ t = _
    rw [ih, ih]
    simp only [D, diff, Nat.cast_add, Nat.cast_one]
    ring

private theorem D_const (r : ℕ) (c : ℤ) (t : ℕ) : D (r+1) (fun _ => c) t = 0 := by
  induction r generalizing t with
  | zero => simp [D, diff]
  | succ r ih => change D (r+1) _ (t+1) - D (r+1) _ t = 0; rw [ih, ih, sub_self]

private theorem D_high {d r : ℕ} (h : d < r) : D r (fun t => (t:ℤ)^d) 0 = 0 := by
  induction d generalizing r with
  | zero => obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0); simp [D_const]
  | succ d ih =>
    obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    simp only [pow_succ', D_times, Nat.cast_zero, zero_add]
    rw [ih (by omega), ih (by omega)]; ring

private def scale (m : ℕ) : ℤ := 2^m
private def modulus (m : ℕ) : ℤ := scale m * m

private theorem error_dvd {m : ℕ} (hm : 0 < m) (d : ℕ) :
    modulus m ∣ D m (fun t => (2*(t:ℤ))^d) 0 := by
  simp only [mul_pow, D_scale]
  by_cases h : d < m
  · simp [D_high h]
  · apply mul_dvd_mul (pow_dvd_pow 2 (by omega : m ≤ d))
    obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    cases d with
    | zero => simp [D_const]
    | succ d =>
      simp only [pow_succ', D_times, Nat.cast_zero, zero_add, Nat.cast_succ]
      exact dvd_add (dvd_mul_right ..) (dvd_mul_right ..)

private def W : ℕ → F → ℤ
  | 0, _ => 0
  | r+1, f => 2^r*f 0 - W r (diff f)

private theorem W_add (r : ℕ) (f g : F) :
    W r (fun t => f t + g t) = W r f + W r g := by
  induction r generalizing f g with
  | zero => simp [W]
  | succ r ih =>
    have e : diff (fun t => f t + g t) = fun t => diff f t + diff g t := by funext t; simp [diff]; ring
    simp only [W, e, ih]; ring

private theorem W_scale (r : ℕ) (c : ℤ) (f : F) : W r (fun t => c*f t) = c * W r f := by
  induction r generalizing f with
  | zero => simp [W]
  | succ r ih =>
    have e : diff (fun t => c*f t) = fun t => c * diff f t := by funext t; simp [diff]; ring
    simp only [W, e, ih]; ring

private theorem W_zero (r : ℕ) : W r (fun _ => 0) = 0 := by
  simpa using W_scale r 0 (fun _ => 1)

private theorem W_shift (r : ℕ) (f : F) :
    W r (fun t => f t + f (t+1)) = 2^r * f 0 - (-1)^r * D r f 0 := by
  induction r generalizing f with
  | zero => simp [W,D]
  | succ r ih =>
    have e : diff (fun t => f t + f (t+1)) = fun t => diff f t + diff f (t+1) := by
      funext t; simp [diff]; ring
    rw [W, e, ih, D_diff]
    simp only [diff, pow_succ]; ring

private theorem W_congr {m : ℕ} {f g : F} (r : ℕ)
    (h : ∀ t, f t ≡ g t [ZMOD modulus m]) : W r f ≡ W r g [ZMOD modulus m] := by
  induction r generalizing f g with
  | zero => rfl
  | succ r ih => exact ((h 0).mul_left _).sub (ih (fun t => (h (t+1)).sub (h t)))

private def z (t : ℕ) : ℤ := 2*t+1
private def moment (m p q : ℕ) : ℤ := W m (fun t =>
  (z t)^p*(z t+1)^q + (-(z t))^p*(1-z t)^q)

private theorem moment_step (m p q : ℕ) : moment m p (q+1) = moment m (p+1) q + moment m p q := by
  unfold moment
  rw [← W_add]
  congr 1; funext t; simp only [pow_succ]; ring

private theorem moment_init {m : ℕ} (hm : 0 < m) : moment m 0 0 = scale m := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have e : diff (fun _ => (2:ℤ)) = fun _ => 0 := by funext t; simp [diff]
  simp [moment, W, e, W_zero, scale, pow_succ]

private theorem odd_boundary (m k : ℕ) : moment m (2*k+1) 0 = 0 := by
  unfold moment
  convert W_zero m using 1
  congr 1
  funext t
  simp [pow_add, pow_mul]

private theorem even_boundary {m : ℕ} (hm : 0 < m) (k : ℕ) :
    moment m 0 (2*(k+1)) ≡ 0 [ZMOD modulus m] := by
  let d := 2*(k+1)
  let f : F := fun t => (2*(t:ℤ))^d
  have e : moment m 0 d = W m (fun t => f t + f (t+1)) := by
    unfold moment
    congr 1; funext t
    have ht : 1-z t = -(2*(t:ℤ)) := by unfold z; ring
    have hu : z t+1 = 2*((t+1:ℕ):ℤ) := by push_cast; unfold z; ring
    simp only [ht,hu,f,d,pow_zero,one_mul,pow_mul,neg_sq]; ring
  change moment m 0 d ≡ 0 [ZMOD modulus m]
  rw [e, W_shift]
  have h0 : f 0 = 0 := by simp [f,d]
  rw [h0,mul_zero,zero_sub]
  apply Int.modEq_zero_iff_dvd.mpr
  exact dvd_neg.mpr (dvd_mul_of_dvd_right (error_dvd hm d) _)

private theorem row_length (r : ℕ) : (entringerRow r).length = r+1 := by
  induction r with
  | zero => rfl
  | succ r ih => simp [entringerRow, ih]

private def entry (r j : ℕ) : ℤ := (entringerRow r).getD j 0

private theorem entry_in (r j : ℕ) (h : j < (entringerRow r).length) :
    entry r j = ((entringerRow r)[j] : ℤ) := by
  simp [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

private theorem start_zero (r : ℕ) : entry (r+1) 0 = 0 := by
  simp [entry, entringerRow, List.getD_eq_getElem?_getD]

private theorem entry_step (r j : ℕ) (hj : j ≤ r) :
    entry (r+1) (j+1) = entry (r+1) j + entry r (r-j) := by
  rw [entry_in _ _ (by rw [row_length]; omega), entry_in (r+1) j (by rw [row_length]; omega),
    entry_in r (r-j) (by rw [row_length]; omega)]
  simp only [entringerRow, List.getElem_succ_scanl, List.getElem_reverse, row_length,
    Nat.add_sub_cancel, Nat.cast_add]

private abbrev Eform (m k : ℕ) := ∀ j, j ≤ 2*k →
  scale m * entry (2*k) j ≡ (-1)^k * moment m j (2*k-j) [ZMOD modulus m]

private abbrev Oform (m k : ℕ) := ∀ j, j ≤ 2*k+1 →
  scale m * entry (2*k+1) j ≡ (-1)^k * moment m (2*k+1-j) j [ZMOD modulus m]

private theorem odd_row {m k : ℕ} (he : Eform m k) : Oform m k := by
  intro j
  induction j with
  | zero => intro _; simp [start_zero, odd_boundary]
  | succ j ih =>
    intro hj
    have h := (ih (by omega)).add (he (2*k-j) (by omega))
    rw [entry_step (2*k) j (by omega), mul_add]
    rw [show 2*k+1-(j+1) = 2*k-j by omega, moment_step, mul_add]
    simpa only [show 2*k+1-j = (2*k-j)+1 by omega, show 2*k-(2*k-j) = j by omega] using h

private theorem even_row {m k : ℕ} (hm : 0 < m) (ho : Oform m k) : Eform m (k+1) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h := (even_boundary hm k).symm.mul_left ((-1:ℤ)^(k+1))
    simpa [show 2*(k+1) = (2*k+1)+1 by omega, start_zero] using h
  | succ j ih =>
    intro hj
    let q := 2*k+1-j
    have h := (ih (by omega)).add (ho q (by dsimp [q]; omega))
    have e : 2*(k+1) = (2*k+1)+1 := by omega
    have e₁ : 2*(k+1)-j = q+1 := by dsimp [q]; omega
    have e₂ : 2*k+1-q = j := by dsimp [q]; omega
    have e₃ : 2*(k+1)-(j+1) = q := by dsimp [q]; omega
    rw [e₁,e₂,moment_step] at h
    rw [e₃,e,entry_step (2*k+1) j (by omega),mul_add]
    rw [e] at h
    convert h using 1
    simp only [pow_succ]
    ring

private theorem all_even {m : ℕ} (hm : 0 < m) (k : ℕ) : Eform m k := by
  induction k with
  | zero =>
    intro j hj
    have e : j = 0 := by omega
    subst j
    simp [entry, entringerRow, moment_init hm]
  | succ k ih => exact even_row hm (odd_row ih)

-- Euler's theorem for a unit, and eventual vanishing for a nonunit, in each prime power.
private theorem powers_stabilize {m : ℕ} : 0 < m → ∀ b n d : ℕ, m ≤ n →
    m.totient ∣ d → b^(n+d) ≡ b^n [MOD m] := by
  induction m using Nat.recOnPrimeCoprime with
  | zero => omega
  | prime_pow p e hp =>
    intro hm b n d hn hd
    by_cases hb : p ∣ b
    · have he : e ≤ n := by
        have := Nat.lt_two_pow_self (n := e)
        have := Nat.pow_le_pow_left hp.two_le e
        omega
      have h := (pow_dvd_pow_of_dvd hb e).trans (pow_dvd_pow b he)
      exact (h.trans (pow_dvd_pow b (by omega : n ≤ n+d))).modEq_zero_nat.trans h.modEq_zero_nat.symm
    · have hc := (hp.coprime_iff_not_dvd.mpr hb).symm.pow_right e
      obtain ⟨t,rfl⟩ := hd
      have h := ((Nat.ModEq.pow_totient hc).pow t).mul_left (b^n)
      simpa only [pow_add,pow_mul,one_pow,mul_one] using h
  | coprime u v hu hv huv ihu ihv =>
    intro hm b n d hn hd
    apply (Nat.modEq_and_modEq_iff_modEq_mul huv).mp
    constructor
    · exact ihu (by omega) b n d ((Nat.le_of_dvd hm (dvd_mul_right u v)).trans hn)
        ((Nat.totient_dvd_of_dvd (dvd_mul_right u v)).trans hd)
    · exact ihv (by omega) b n d ((Nat.le_of_dvd hm (dvd_mul_left v u)).trans hn)
        ((Nat.totient_dvd_of_dvd (dvd_mul_left v u)).trans hd)

private theorem even_powers {m n : ℕ} (hm : 0 < m) (hn : 2*m ≤ n) (b : ℤ) (hb : 2 ∣ b) :
    b^(n+m.totient) ≡ b^n [ZMOD modulus m] := by
  have : NeZero m := ⟨hm.ne'⟩
  let k := n-m
  have hk : m ≤ k := by dsimp [k]; omega
  have eq : n = m+k := by dsimp [k]; omega
  let a : ZMod m := b
  have h := (ZMod.natCast_eq_natCast_iff _ _ m).2 (powers_stabilize hm a.val k _ hk (dvd_refl m.totient))
  have h' : b^(k+m.totient) ≡ b^k [ZMOD (m:ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff _ _ _).1
    simpa [a] using h
  rw [Int.modEq_iff_dvd] at h' ⊢
  have := mul_dvd_mul (pow_dvd_pow_of_dvd hb m) h'
  rw [eq, Nat.add_assoc, pow_add b m, pow_add b m, ← mul_sub]
  exact this

private def plusBase (t : ℕ) : ℤ := -(z t * (z t+1))
private def minusBase (t : ℕ) : ℤ := -(-z t * (1-z t))

private theorem median_formula {m : ℕ} (hm : 0 < m) (n : ℕ) :
    scale m * (medianEuler n : ℤ) ≡
      W m (fun t => (plusBase t)^n + (minusBase t)^n) [ZMOD modulus m] := by
  have h := all_even hm n n (by omega)
  rw [show 2*n-n=n by omega] at h
  change scale m * entry (2*n) n ≡ _ [ZMOD modulus m]
  convert h using 1
  unfold moment
  rw [← W_scale]
  congr 1; funext t
  rw [show plusBase t = (-1) * (z t * (z t+1)) by unfold plusBase; ring,
    show minusBase t = (-1) * ((-z t) * (1-z t)) by unfold minusBase; ring]
  simp only [mul_pow]; ring

end A000657Proof

open A000657Proof OMA.S_oeis_a000657 in
theorem OMA.solution : type_of% @OMA.S_oeis_a000657.main := by
  intro m hm
  refine ⟨2*m, m.totient, Nat.totient_pos.mpr hm, dvd_refl _, ?_⟩
  intro n hn
  have h := W_congr (m := m) m (fun t =>
    (even_powers hm hn (plusBase t) (by unfold plusBase z; exact ⟨-((2*(t:ℤ)+1)*(t+1)), by ring⟩)).add
    (even_powers hm hn (minusBase t) (by unfold minusBase z; exact ⟨-(2*(t:ℤ)+1)*t, by ring⟩)))
  apply Int.natCast_modEq_iff.mp
  apply Int.ModEq.mul_left_cancel' (c := scale m) (by unfold scale; positivity)
  exact (median_formula hm _).trans (h.trans (median_formula hm _).symm)
