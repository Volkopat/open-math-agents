import OMAStatements.S_oeis_a347293

namespace OMA.A347293
open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

lemma sum_range_eq_univ (d : ℕ) [NeZero d] (F : ZMod d → ℂ) :
    ∑ x ∈ range d, F x = ∑ u : ZMod d, F u := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by have := NeZero.ne d; omega⟩
  rw [← Fin.sum_univ_eq_sum_range (fun i => F i) (k + 1)]
  apply Fintype.sum_congr
  intro i
  congr 1
  exact Fin.cast_val_eq_self i

lemma sum_range_mul (d : ℕ) [NeZero d] (F : ZMod d → ℂ) (m : ℕ) :
    ∑ x ∈ range (d * m), F x = m * ∑ u : ZMod d, F u := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [mul_add, mul_one, sum_range_add, ih, ← sum_range_eq_univ]
    have : ∀ x ∈ range d, F ((d * m + x : ℕ) : ZMod d) = F x := by
      intro x _
      congr 1
      push_cast
      simp
    rw [sum_congr rfl this]
    push_cast; ring

lemma sum_Icc_eq_range (n : ℕ) (G : ℕ → ℂ) (hG : G 0 = G n) :
    ∑ x ∈ Icc 1 n, G x = ∑ x ∈ range n, G x := by
  have a1 : ∑ k ∈ range (n + 1), G k = ∑ k ∈ range n, G k + G n := sum_range_succ _ _
  have a2 : ∑ k ∈ range (n + 1), G k = ∑ k ∈ Icc 1 n, G k + G 0 := by
    rw [sum_range_succ', show Icc 1 n = Ico 1 (n + 1) by ext; simp, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    congr 1
    apply sum_congr rfl; intro i _; rw [add_comm]
  rw [a1, hG] at a2
  exact (add_right_cancel a2).symm

lemma sum_pairs (n d : ℕ) (hd : d ∣ n) [NeZero d] (F : ZMod d → ZMod d → ℂ) :
    ∑ i ∈ Icc 1 n, ∑ k ∈ Icc 1 n, F (i : ZMod d) (k : ZMod d) =
      ((n / d : ℕ) : ℂ) ^ 2 * ∑ u : ZMod d, ∑ v : ZMod d, F u v := by
  obtain ⟨m, rfl⟩ := hd
  have hd0 : d ≠ 0 := NeZero.ne d
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
  have inner : ∀ x, ∑ y ∈ Icc 1 (d * m), F (x : ZMod d) (y : ZMod d) =
      m * ∑ v : ZMod d, F (x : ZMod d) v := by
    intro x
    rw [sum_Icc_eq_range _ (fun y => F (x : ZMod d) (y : ZMod d)) (by simp), sum_range_mul]
  simp only [inner]
  rw [sum_Icc_eq_range _ (fun x => (m : ℂ) * ∑ v : ZMod d, F (x : ZMod d) v) (by simp),
    sum_range_mul d (fun u => (m : ℂ) * ∑ v : ZMod d, F u v), ← mul_sum]
  ring

lemma count_units (d : ℕ) [NeZero d] :
    ∑ u : ZMod d, ∑ v : ZMod d, (if 1 + (u - 1) * (v - 1) = 0 then (1 : ℂ) else 0) =
      (Nat.totient d : ℂ) := by
  rw [Fintype.sum_equiv (Equiv.subRight (1 : ZMod d))
    (fun u => ∑ v : ZMod d, (if 1 + (u - 1) * (v - 1) = 0 then (1 : ℂ) else 0))
    (fun u => ∑ v : ZMod d, (if 1 + u * (v - 1) = 0 then (1 : ℂ) else 0)) (fun _ => rfl)]
  have h1 : ∀ u : ZMod d, ∑ v : ZMod d, (if 1 + u * (v - 1) = 0 then (1 : ℂ) else 0) =
      ∑ v : ZMod d, (if 1 + u * v = 0 then (1 : ℂ) else 0) := fun u =>
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod d))
      (fun v => (if 1 + u * (v - 1) = 0 then (1 : ℂ) else 0))
      (fun v => (if 1 + u * v = 0 then (1 : ℂ) else 0)) (fun _ => rfl)
  simp only [h1]
  have h2 : ∀ u : ZMod d, ∑ v : ZMod d, (if 1 + u * v = 0 then (1 : ℂ) else 0) =
      if IsUnit u then 1 else 0 := by
    intro u
    by_cases hu : IsUnit u
    · rw [if_pos hu]
      have : ∀ v : ZMod d, (1 + u * v = 0 ↔ v = -↑(hu.unit⁻¹)) := by
        intro v
        constructor
        · intro h
          have h' : u * v = -1 := by linear_combination h
          calc v = ↑(hu.unit⁻¹) * (u * v) := by
                rw [← mul_assoc, show (↑(hu.unit⁻¹) : ZMod d) * u = 1 from hu.val_inv_mul, one_mul]
            _ = -↑(hu.unit⁻¹) := by rw [h']; ring
        · rintro rfl
          have : u * ↑(hu.unit⁻¹) = 1 := hu.mul_val_inv
          linear_combination -this
      simp only [this]
      simp
    · rw [if_neg hu]
      refine sum_eq_zero fun v _ => ?_
      rw [if_neg]
      intro h
      exact hu (IsUnit.of_mul_eq_one (-v) (by linear_combination -h))
  simp only [h2]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  congr 1
  have : (univ.filter (fun u : ZMod d => IsUnit u)) =
      (univ : Finset (ZMod d)ˣ).map ⟨Units.val, Units.val_injective⟩ := by
    ext u; simp [IsUnit, eq_comm]
  rw [this, card_map, card_univ, ZMod.card_units_eq_totient]

lemma count (n d : ℕ) (hn : 1 ≤ n) (hd : d ∣ n) :
    ∑ i ∈ Icc 1 n, ∑ k ∈ Icc 1 n, (if d ∣ 1 + (i - 1) * (k - 1) then (1 : ℂ) else 0) =
      ((n / d : ℕ) : ℂ) ^ 2 * (Nat.totient d : ℂ) := by
  have hd0 : d ≠ 0 := by rintro rfl; rw [zero_dvd_iff] at hd; omega
  have : NeZero d := ⟨hd0⟩
  have key : ∀ i ∈ Icc 1 n, ∀ k ∈ Icc 1 n,
      (if d ∣ 1 + (i - 1) * (k - 1) then (1 : ℂ) else 0) =
        (fun (u v : ZMod d) => if 1 + (u - 1) * (v - 1) = 0 then (1 : ℂ) else 0)
          (i : ZMod d) (k : ZMod d) := by
    intro i hi k hk
    have hi1 : 1 ≤ i := (mem_Icc.mp hi).1
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    simp only
    congr 1
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub hi1, Nat.cast_sub hk1]
    rfl
  rw [sum_congr rfl fun i hi => sum_congr rfl fun k hk => key i hi k hk,
    sum_pairs n d hd (fun u v => if 1 + (u - 1) * (v - 1) = 0 then (1 : ℂ) else 0), count_units]

/-- Part (1). -/
theorem part1 (f : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd (1 + (i - 1) * (k - 1)) n) =
      ∑ d ∈ n.divisors, (((n / d) ^ 2 : ℕ) : ℂ) *
        ((Nat.totient d : ℂ) *
          ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) * f (d / e)) := by
  set h : ℕ → ℂ := fun d => ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) * f (d / e)
    with hh
  let F : ArithmeticFunction ℂ := ⟨fun m => if m = 0 then 0 else f m, by simp⟩
  have hFapp : ∀ m, m ≠ 0 → F m = f m := fun m hm => by simp [F, hm]
  -- Moebius inversion
  have hinv : ∀ g, g ≠ 0 → ∑ e ∈ g.divisors, h e = f g := by
    intro g hg
    have h1 : (((μ : ArithmeticFunction ℂ) * F) * (ζ : ArithmeticFunction ℂ)) g = F g := by
      rw [mul_comm (μ : ArithmeticFunction ℂ) F, mul_assoc, coe_moebius_mul_coe_zeta, mul_one]
    rw [coe_mul_zeta_apply, hFapp g hg] at h1
    rw [← h1]
    refine sum_congr rfl fun e he => ?_
    rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => (μ : ArithmeticFunction ℂ) x * F y)]
    refine sum_congr rfl fun c hc => ?_
    have he0 : e ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors he)
    have hc0 : c ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hc)
    have hq : e / c ≠ 0 := (Nat.div_pos (Nat.divisor_le hc) (Nat.pos_of_ne_zero hc0)).ne'
    rw [hFapp _ hq, intCoe_apply]
  have step : ∀ i ∈ Icc 1 n, ∀ k ∈ Icc 1 n, f (Nat.gcd (1 + (i - 1) * (k - 1)) n) =
      ∑ e ∈ n.divisors, (if e ∣ 1 + (i - 1) * (k - 1) then (1 : ℂ) else 0) * h e := by
    intro i _ k _
    have hg : Nat.gcd (1 + (i - 1) * (k - 1)) n ≠ 0 := (Nat.gcd_pos_of_pos_right _ (by omega)).ne'
    rw [← hinv _ hg]
    simp only [ite_mul, one_mul, zero_mul]
    rw [← sum_filter]
    congr 1
    ext e
    simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, by omega⟩, h1⟩
    · rintro ⟨⟨h2, _⟩, h1⟩; exact ⟨⟨h1, h2⟩, hg⟩
  rw [sum_congr rfl fun i hi => sum_congr rfl fun k hk => step i hi k hk]
  calc _ = ∑ i ∈ Icc 1 n, ∑ e ∈ n.divisors, ∑ k ∈ Icc 1 n,
        (if e ∣ 1 + (i - 1) * (k - 1) then (1 : ℂ) else 0) * h e :=
        sum_congr rfl fun i _ => sum_comm
    _ = ∑ e ∈ n.divisors, ∑ i ∈ Icc 1 n, ∑ k ∈ Icc 1 n,
        (if e ∣ 1 + (i - 1) * (k - 1) then (1 : ℂ) else 0) * h e := sum_comm
    _ = ∑ e ∈ n.divisors, (∑ i ∈ Icc 1 n, ∑ k ∈ Icc 1 n,
        (if e ∣ 1 + (i - 1) * (k - 1) then (1 : ℂ) else 0)) * h e := by
        simp only [sum_mul]
    _ = _ := by
        refine sum_congr rfl fun d hd => ?_
        rw [count n d hn (Nat.dvd_of_mem_divisors hd)]
        push_cast
        ring


lemma conv (X Y : ArithmeticFunction ℂ) (n : ℕ) :
    (X * Y) n = ∑ d ∈ n.divisors, X d * Y (n / d) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => X x * Y y)]

def toF (f : ℕ → ℂ) : ArithmeticFunction ℂ := ⟨fun m => if m = 0 then 0 else f m, by simp⟩
lemma toF_apply (f : ℕ → ℂ) {m : ℕ} (hm : m ≠ 0) : toF f m = f m := by simp [toF, hm]

def PhiC : ArithmeticFunction ℂ := ⟨fun n => (Nat.totient n : ℂ), by simp⟩
def Pw : ArithmeticFunction ℂ := ⟨fun n => (n : ℂ) ^ 2, by simp⟩

lemma PhiC_mult : IsMultiplicative PhiC :=
  ⟨by simp [PhiC], fun {m n} h => by simp only [PhiC, coe_mk]; rw [Nat.totient_mul h]; push_cast; ring⟩
lemma Pw_mult : IsMultiplicative Pw :=
  ⟨by simp [Pw], fun {m n} _ => by simp only [Pw, coe_mk]; push_cast; ring⟩

lemma muF_apply (f : ℕ → ℂ) {e : ℕ} (_he : e ≠ 0) :
    ((μ : ArithmeticFunction ℂ) * toF f) e =
      ∑ c ∈ e.divisors, ((ArithmeticFunction.moebius c : ℤ) : ℂ) * f (e / c) := by
  rw [conv]
  refine sum_congr rfl fun c hc => ?_
  have hc0 : c ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hc)
  have hq : e / c ≠ 0 := (Nat.div_pos (Nat.divisor_le hc) (Nat.pos_of_ne_zero hc0)).ne'
  rw [toF_apply f hq, intCoe_apply]

lemma a_eq (f : ℕ → ℂ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd (1 + (i - 1) * (k - 1)) n) =
      (pmul PhiC ((μ : ArithmeticFunction ℂ) * toF f) * Pw) n := by
  rw [part1 f n hn, conv]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)
  rw [pmul_apply, muF_apply f hd0]
  simp only [PhiC, Pw, coe_mk]
  push_cast; ring

theorem part2 (f : ℕ → ℂ) (hf : f 1 = 1 ∧ ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) :
    (∑ i ∈ Finset.Icc 1 1, ∑ k ∈ Finset.Icc 1 1, f (Nat.gcd (1 + (i - 1) * (k - 1)) 1) = 1) ∧
    ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → Nat.Coprime m n →
      ∑ i ∈ Finset.Icc 1 (m * n), ∑ k ∈ Finset.Icc 1 (m * n),
          f (Nat.gcd (1 + (i - 1) * (k - 1)) (m * n)) =
        (∑ i ∈ Finset.Icc 1 m, ∑ k ∈ Finset.Icc 1 m, f (Nat.gcd (1 + (i - 1) * (k - 1)) m)) *
        (∑ i ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, f (Nat.gcd (1 + (i - 1) * (k - 1)) n)) := by
  have hFm : IsMultiplicative (toF f) := by
    refine ⟨by simp [toF, hf.1], fun {m n} hmn => ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [toF]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [toF]
    rw [toF_apply f (by positivity), toF_apply f (by omega), toF_apply f (by omega), hf.2 m n hmn]
  have hA : IsMultiplicative (pmul PhiC ((μ : ArithmeticFunction ℂ) * toF f) * Pw) :=
    (PhiC_mult.pmul (isMultiplicative_moebius.intCast.mul hFm)).mul Pw_mult
  refine ⟨by simp [hf.1], fun m n hm hn hmn => ?_⟩
  rw [a_eq f _ (Nat.one_le_iff_ne_zero.mpr (by positivity)), a_eq f m hm, a_eq f n hn,
    hA.map_mul_of_coprime hmn]

def Phi : ArithmeticFunction ℤ := ⟨fun n => (Nat.totient n : ℤ), by simp⟩
def I : ArithmeticFunction ℤ := ⟨fun n => (n : ℤ), by simp⟩

lemma phi_sum (d : ℕ) :
    ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) * ((d / e : ℕ) : ℂ) =
      (Nat.totient d : ℂ) := by
  have hPhiZ : Phi * (ζ : ArithmeticFunction ℤ) = I := by
    ext n
    rw [coe_mul_zeta_apply]
    simp only [Phi, I, coe_mk]
    exact_mod_cast Nat.sum_totient n
  have hPhi : Phi = (μ : ArithmeticFunction ℤ) * I := by
    calc Phi = Phi * ((ζ : ArithmeticFunction ℤ) * μ) := by rw [coe_zeta_mul_moebius, mul_one]
      _ = (Phi * ζ) * μ := by ring
      _ = μ * I := by rw [hPhiZ, mul_comm]
  have h := congrArg (fun F => F d) hPhi
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => (μ : ArithmeticFunction ℤ) x * I y)] at h
  simp only [Phi, I, coe_mk] at h
  have h' := congrArg (Int.cast : ℤ → ℂ) h.symm
  push_cast at h'
  exact h'

theorem part3 (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, ∑ i ∈ Finset.Icc 1 n, Nat.gcd (1 + (i - 1) * (k - 1)) n =
      ∑ d ∈ n.divisors, (n / d) ^ 2 * (Nat.totient d) ^ 2 := by
  apply Nat.cast_injective (R := ℂ)
  push_cast
  rw [sum_comm, part1 (fun m => (m : ℂ)) n hn]
  refine sum_congr rfl fun d _ => ?_
  rw [phi_sum]
  push_cast; ring

theorem sol : type_of% @OMA.S_oeis_a347293.main :=
  ⟨part1, part2, part3⟩

end OMA.A347293

theorem OMA.solution : type_of% @OMA.S_oeis_a347293.main := OMA.A347293.sol

