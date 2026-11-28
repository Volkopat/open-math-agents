import OMAStatements.S_oeis_a338278

-- Credit: @RiverMint78

namespace OMA.Hanna
open Finset PowerSeries S_oeis_a338278

private def diff (c : ℤ) (f : ℕ → ℤ) (m : ℕ) := f (m+1) - c * f m

/-- Some iterate of the weighted forward difference vanishes. -/
private inductive FiniteDiff (c : ℤ) : (ℕ → ℤ) → Prop
  | zero : FiniteDiff c (fun _ => 0)
  | step {f} : FiniteDiff c (diff c f) → FiniteDiff c f

private theorem fdAdd {c f g} (hf : FiniteDiff c f) (hg : FiniteDiff c g) :
    FiniteDiff c (fun m => f m + g m) := by
  induction hf generalizing g with
  | zero => simpa using hg
  | @step f _ ih =>
    cases hg with
    | zero => simpa using (FiniteDiff.step ‹FiniteDiff c (diff c f)›)
    | @step g hg =>
      apply FiniteDiff.step
      convert ih hg using 1
      funext m
      simp [diff]
      ring

private theorem fdScale {c f} (z : ℤ) (hf : FiniteDiff c f) :
    FiniteDiff c (fun m => z * f m) := by
  induction hf with
  | zero => simpa using (FiniteDiff.zero (c := c))
  | step _ ih =>
    apply FiniteDiff.step
    convert ih using 1
    funext m
    simp [diff]
    ring

private theorem fdMul {b f} (hb : FiniteDiff 1 b) (hf : FiniteDiff 2 f) :
    FiniteDiff 2 (fun m => b m * f m) := by
  induction hb generalizing f with
  | zero => simpa using (FiniteDiff.zero (c := 2))
  | @step b hb outer =>
    induction hf with
    | zero => simpa using (FiniteDiff.zero (c := 2))
    | @step f hf inner =>
      apply FiniteDiff.step
      convert fdAdd (fdAdd (outer hf) (fdScale 2 (outer (.step hf)))) inner using 1
      funext m
      simp [diff]
      ring

private theorem fdSum {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℤ)
    (h : ∀ i ∈ s, FiniteDiff 2 (f i)) : FiniteDiff 2 (fun m => ∑ i ∈ s, f i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (FiniteDiff.zero (c := 2))
  | @insert i s hi ih =>
    simpa [hi] using fdAdd (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

private theorem chooseFD (s : ℤ) (k : ℕ) :
    FiniteDiff 1 (fun m : ℕ => Ring.choose ((m : ℤ) + s) k) := by
  induction k with
  | zero =>
    apply FiniteDiff.step
    convert (FiniteDiff.zero (c := 1)) using 1
    funext m
    simp [diff]
  | succ k ih =>
    apply FiniteDiff.step
    convert ih using 1
    funext m
    simp only [diff, Nat.cast_add, Nat.cast_one, one_mul, show (m : ℤ) + 1 + s = ((m : ℤ) + s) + 1 by ring,
      Ring.choose_succ_succ]
    ring

private noncomputable def prodSeries (s : ℤ) (p : ℤ⟦X⟧) : ℕ → ℤ⟦X⟧
  | 0 => p
  | m+1 => (1 + binomialSeries ℤ ((m : ℤ)+s)) * prodSeries s p m

private theorem coeffFD (s : ℤ) (p : ℤ⟦X⟧) (n : ℕ) :
    FiniteDiff 2 (fun m => coeff n (prodSeries s p m)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    apply FiniteDiff.step
    have h := fdSum (range n)
      (fun j m => Ring.choose ((m : ℤ)+s) (j+1) * coeff (n-(j+1)) (prodSeries s p m))
      (fun j hj => fdMul (chooseFD s (j+1)) (ih _ (by simp only [mem_range] at hj; omega)))
    convert h using 1
    funext m
    rw [diff, prodSeries, add_mul, one_mul, map_add, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        coeff i (binomialSeries ℤ ((m : ℤ)+s)) * coeff j (prodSeries s p m)), sum_range_succ']
    simp only [binomialSeries_coeff, zsmul_eq_mul, mul_one, Ring.choose_zero_right,
      Int.cast_id, Nat.sub_zero, Nat.sub_add_eq]
    ring

/-- The integer Newton basis for shift minus two. Each basis vector has weighted sum one. -/
private def basis (k m : ℕ) : ℤ := (m.choose k : ℤ) * 2 ^ (m-k)

private theorem basisStep (k m : ℕ) :
    basis (k+1) (m+1) = 2 * basis (k+1) m + basis k m := by
  by_cases h : k+1 ≤ m
  · simp only [basis, Nat.choose_succ_succ, Nat.cast_add, Nat.add_sub_add_right]
    rw [show m-k = m-(k+1)+1 by omega, pow_succ]
    ring
  · simp only [basis, Nat.choose_succ_succ, Nat.choose_eq_zero_of_lt (by omega : m < k+1),
      add_zero, Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_add_right]

private inductive Expansion : (ℕ → ℤ) → Prop
  | zero : Expansion (fun _ => 0)
  | term {f} (z : ℤ) (k : ℕ) : Expansion f → Expansion (fun m => z * basis k m + f m)

private theorem primitive {f} (hf : Expansion f) :
    ∃ g, Expansion g ∧ g 0 = 0 ∧ ∀ m, g (m+1) = 2 * g m + f m := by
  induction hf with
  | zero => exact ⟨_, .zero, rfl, by simp⟩
  | term z k _ ih =>
    obtain ⟨g,hg,h0,hs⟩ := ih
    exact ⟨_, .term z (k+1) hg, by simp [basis,h0], fun m => by rw [basisStep, hs]; ring⟩

private theorem expand {f} (hf : FiniteDiff 2 f) : Expansion f := by
  induction hf with
  | zero => exact .zero
  | @step f _ ih =>
    obtain ⟨g,hg,h0,hs⟩ := primitive ih
    convert Expansion.term (f 0) 0 hg using 1
    funext m
    induction m with
    | zero => simp [basis,h0]
    | succ m ih =>
      rw [hs]
      simp only [basis, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, pow_succ] at *
      simp only [diff] at *
      linarith

private theorem basisSum (k : ℕ) : HasSum (fun m => (basis k m : ℝ) / 3^(m+1)) 1 := by
  rw [← hasSum_nat_add_iff' k]
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one k (r := (2/3 : ℝ)) (by norm_num)).mul_right
    (1 / 3^(k+1))
  have hzero : (∑ i ∈ range k, (basis k i : ℝ) / 3^(i+1)) = 0 := by
    apply sum_eq_zero
    intro i hi
    simp [basis, Nat.choose_eq_zero_of_lt (mem_range.mp hi)]
  rw [hzero, sub_zero]
  convert! h using 1
  · funext m
    simp only [basis, Nat.add_sub_cancel, Int.cast_mul, Int.cast_natCast, Int.cast_pow,
      Int.cast_ofNat, div_pow]
    rw [show m+k+1 = m+(k+1) by omega, pow_add]
    ring
  · rw [show (1:ℝ) - 2/3 = 1/3 by norm_num, div_pow, one_pow]
    field_simp

private theorem integerSum {f} (hf : FiniteDiff 2 f) :
    ∃ z : ℤ, HasSum (fun m => (f m : ℝ) / 3^(m+1)) (z : ℝ) := by
  have he := expand hf
  clear hf
  induction he with
  | zero => exact ⟨0, by simp⟩
  | term z k _ ih =>
    obtain ⟨v,h⟩ := ih
    refine ⟨z+v, ?_⟩
    convert! ((basisSum k).mul_left (z : ℝ)).add h using 1
    · funext m
      push_cast
      ring
    · push_cast
      ring

private noncomputable abbrev A := prodSeries 1 1
private noncomputable abbrev Q : ℤ⟦X⟧ := 1 + X
private noncomputable abbrev E := prodSeries (-1) Q

private theorem ordinary (m : ℕ) :
    A m = ((numerator m).map (Nat.castRingHom ℤ) : Polynomial ℤ) := by
  induction m with
  | zero => simp [A, prodSeries, numerator]
  | succ m ih =>
    change (1 + binomialSeries ℤ ((m : ℤ)+1)) * A m = _
    rw [ih, ← Nat.cast_one (R := ℤ), ← Nat.cast_add, binomialSeries_nat]
    simp [numerator, Finset.prod_Icc_succ_top (by omega : 1 ≤ m+1), mul_comm]

private theorem ordinaryCoeff (m n : ℕ) :
    coeff n (A m) = ((numerator m).coeff n : ℤ) := by
  rw [ordinary, Polynomial.coeff_coe, Polynomial.coeff_map]
  rfl

private theorem extOne : E 1 = Q + 1 := by
  change (1 + binomialSeries ℤ ((0:ℤ)+(-1))) * Q = _
  rw [zero_add, add_mul, one_mul]
  congr 1
  have h := binomialSeries_add (A := ℤ) (-1 : ℤ) 1
  simpa [show binomialSeries ℤ (1 : ℤ) = Q by simpa using (binomialSeries_nat (A := ℤ) (R := ℤ) 1)] using h.symm

private theorem extTail (m : ℕ) : E (m+2) = (2 * (Q+1)) * A m := by
  induction m with
  | zero =>
    change (1+binomialSeries ℤ ((1:ℤ)+(-1))) * E 1 = _ * (1 : ℤ⟦X⟧)
    rw [extOne]
    simp only [add_neg_cancel, binomialSeries_zero, mul_one]
    ring
  | succ m ih =>
    change (1 + binomialSeries ℤ (((m+2 : ℕ):ℤ)+(-1))) * E (m+2) =
      _ * ((1 + binomialSeries ℤ ((m:ℤ)+1)) * A m)
    rw [ih, show ((m+2 : ℕ):ℤ)+(-1) = (m:ℤ)+1 by omega]
    ring

private theorem extCoeff (m n : ℕ) : coeff (n+1) (E (m+2)) =
    4 * coeff (n+1) (A m) + 2 * coeff n (A m) := by
  rw [extTail]
  have h : (2 * (Q+1)) * A m = A m + A m + A m + A m + A m * X + A m * X := by
    unfold Q
    ring
  rw [h]
  simp only [map_add, coeff_succ_mul_X]
  ring

private theorem extInitial (n : ℕ) :
    coeff (n+1) (E 0) = (if n=0 then 1 else 0) ∧
    coeff (n+1) (E 1) = (if n=0 then 1 else 0) := by
  change coeff (n+1) Q = _ ∧ _
  rw [extOne]
  cases n <;> simp [Q, coeff_X]

private theorem firstSum :
    HasSum (fun m => ((coeff 0 (A m) : ℤ) : ℝ) / 3^(m+1)) 1 := by
  have h (m : ℕ) : coeff 0 (A m) = 2^m := by
    induction m with
    | zero => simp [A, prodSeries]
    | succ m ih =>
      change coeff 0 ((1 + binomialSeries ℤ ((m : ℤ)+1)) * A m) = _
      simp only [coeff_mul, Nat.antidiagonal_zero, sum_singleton, map_add,
        binomialSeries_coeff, Ring.choose_zero_right, one_smul, coeff_zero_one, ih, pow_succ]
      ring
  simpa only [h, basis, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] using basisSum 0

/-- Starting the product two places earlier gives an integral sum, hence a multiple of nine
after shifting back. The two prefix terms contribute only in degrees zero and one. -/
private theorem congrStep (n : ℕ) (u v : ℤ)
    (hu : HasSum (fun m => ((coeff n (A m) : ℤ) : ℝ) / 3^(m+1)) (u : ℝ))
    (hv : HasSum (fun m => ((coeff (n+1) (A m) : ℤ) : ℝ) / 3^(m+1)) (v : ℝ)) :
    ∃ w : ℤ, 9*w = 4*v + 2*u + (if n=0 then 4 else 0) := by
  obtain ⟨w, hw⟩ := integerSum (coeffFD (-1) Q (n+1))
  refine ⟨w, ?_⟩
  let t (m : ℕ) : ℝ := ((coeff (n+1) (E m) : ℤ) : ℝ) / 3^(m+1)
  change HasSum t (w : ℝ) at hw
  have shifted : HasSum (fun m => t (m+2)) ((((4:ℝ)*v + 2*u)/9)) := by
    convert! (((hv.mul_left 4).add (hu.mul_left 2)).mul_right (1/9)) using 1
    · funext m
      simp only [t, extCoeff, Int.cast_add, Int.cast_mul, Int.cast_ofNat, pow_add]
      ring
    · ring
  have hx := shifted.unique ((hasSum_nat_add_iff' 2).mpr hw)
  have hi := extInitial n
  simp only [sum_range_succ, range_zero, sum_empty, zero_add, t, hi.1, hi.2] at hx
  split_ifs at * <;> norm_num at hx
  · exact_mod_cast (show (9:ℝ)*w = 4*v+2*u+4 by linarith)
  · exact_mod_cast (show (9:ℝ)*w = 4*v+2*u+0 by linarith)

private theorem nextResidue (u v w : ℤ) (hu : u % 9 = 3) (hw : 9*w = 4*v + 2*u) :
    v % 9 = 3 := by
  have h : u = 9*(u/9)+3 := by omega
  have e : v = 9*(7*w-14*(u/9)-3*v-5)+3 := by linarith
  omega

end OMA.Hanna

open OMA.Hanna PowerSeries OMA.S_oeis_a338278 in
theorem OMA.solution : type_of% @OMA.S_oeis_a338278.main := by
  choose z hz using fun n => integerSum (coeffFD 1 1 n)
  have hzero : z 0 = 1 := by exact_mod_cast (hz 0).unique firstSum
  have hm (n : ℕ) : z (n+1) % 9 = 3 := by
    induction n with
    | zero =>
      obtain ⟨w,hw⟩ := congrStep 0 _ _ (hz 0) (hz 1)
      change 9*w = 4*z 1 + 2*z 0 + 4 at hw
      rw [hzero] at hw
      change z 1 % 9 = 3
      omega
    | succ n ih =>
      obtain ⟨w,hw⟩ := congrStep (n+1) _ _ (hz (n+1)) (hz (n+2))
      change 9*w = 4 * z (n+1+1) + 2*z (n+1) + 0 at hw
      exact nextResidue _ _ _ ih (by simpa only [add_zero] using hw)
  intro n hn
  have he := hz n
  simp only [ordinaryCoeff, Int.cast_natCast] at he
  have hpos : 0 ≤ z n := by
    exact_mod_cast he.nonneg (fun m => by positivity)
  refine ⟨(z n).toNat, ?_, ?_⟩
  · have heq : (((z n).toNat : ℕ) : ℝ) = (z n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hpos
    rw [heq]
    exact he
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hv := hm k
    change (z (k+1)).toNat % 9 = 3
    have hpos₁ : 0 ≤ z (k+1) := hpos
    exact_mod_cast (show (((z (k+1)).toNat : ℕ) : ℤ) % (9:ℤ) = 3 by rw [Int.toNat_of_nonneg hpos₁]; exact hv)
