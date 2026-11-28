import OMAStatements.S_oeis_a265210
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic

open OMA.S_oeis_a265210 Finset Function

namespace TernaryColumns

/-- Cubing lifts the first nonzero ternary digit of 4^(3^j)-1 by one place. -/
private lemma lift_four (j : ℕ) :
    ∃ c : ℕ, 2^(2*3^j) = 1+3^(j+1)*c ∧ c % 3 = 1 := by
  induction j with
  | zero => exact ⟨1, by decide, by decide⟩
  | succ j ih =>
    obtain ⟨c, hc, hmod⟩ := ih
    use c + 3*(3^j*c^2+(3^j)^2*c^3)
    constructor
    · rw [show 2*3^(j+1) = (2*3^j)*3 by ring, pow_mul, hc]
      simp only [pow_succ 3]
      ring
    · omega

private lemma minus_one (j : ℕ) : 2^(3^j) ≡ 3^(j+1)-1 [MOD 3^(j+1)] := by
  have lift (l : ℕ) : ∃ c : ℤ, (2:ℤ)^(3^l) = 3^(l+1)*c-1 := by
    induction l with
    | zero => exact ⟨1, by decide⟩
    | succ l ih =>
      obtain ⟨c, hc⟩ := ih
      use c - 3*3^l*c^2 + 3*(3^l)^2*c^3
      rw [pow_succ 3 l, pow_mul, hc]
      simp only [pow_succ (3:ℤ)]
      ring
  obtain ⟨c, hc⟩ := lift j
  have hdZ : (3:ℤ)^(j+1) ∣ (2:ℤ)^(3^j)+1 := ⟨c, by linarith⟩
  have hd : (3:ℕ)^(j+1) ∣ 2^(3^j)+1 := by exact_mod_cast hdZ
  apply Nat.ModEq.add_right_cancel' 1
  rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))]
  exact (Nat.modEq_zero_iff_dvd.mpr hd).trans (dvd_refl _).zero_modEq_nat

private lemma top_of_mod {a b q : ℕ} (h : a ≡ b [MOD q*3]) :
    a/q%3 = b/q%3 := by
  rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self]
  exact congrArg (· / q) h

private lemma full_period (j : ℕ) : Periodic (digit j) (2*3^j) := by
  obtain ⟨c, hc, _⟩ := lift_four j
  intro n
  apply top_of_mod
  rw [pow_add, hc]
  have hm : 1 + 3^(j+1)*c ≡ 1 [MOD 3^j*3] := by simp [Nat.ModEq, pow_succ]
  simpa using hm.mul_left (2^n)

private lemma third_digit (j n : ℕ) :
    digit (j+1) (n+2*3^j) = (digit (j+1) n + 2^n % 3) % 3 := by
  obtain ⟨c, hc, hmod⟩ := lift_four j
  have hpos : 0 < 3^(j+1) := by positivity
  unfold digit
  rw [pow_add, hc, show 2^n*(1+3^(j+1)*c) = 2^n+3^(j+1)*(2^n*c) by ring,
    Nat.add_mul_div_left _ _ hpos, Nat.mod_add_mod, Nat.add_mod_mod]
  calc
    _ = (2^n / 3^(j+1) % 3 + (2^n * c) % 3) % 3 := Nat.add_mod _ _ _
    _ = _ := by rw [Nat.mul_mod, hmod]; simp [Nat.add_mod]

private lemma third_residue (j n : ℕ) : 2^(n+2*3^j) % 3 = 2^n % 3 := by
  obtain ⟨c, hc, _⟩ := lift_four j
  rw [pow_add, hc, Nat.mul_mod]
  simp [pow_succ', Nat.mul_assoc]

private lemma not_half (j : ℕ) : ¬ Periodic (digit j) (3^j) := by
  intro h
  have hn := h 0
  rw [zero_add] at hn
  have hval : digit j (3^j) = 2 := by
    have he := top_of_mod (q := 3^j) (by simpa only [pow_succ] using minus_one j)
    change 2^(3^j) / 3^j % 3 = 2
    rw [he]
    have hpositive : 0 < 3^j := by positivity
    have hd : (3^j*3-1) / 3^j = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hd]
  have hzero : digit j 0 ≤ 1 := by
    unfold digit
    simp only [pow_zero]
    exact (Nat.mod_le _ _).trans (Nat.div_le_self _ _)
  omega

private lemma not_third (j : ℕ) : ¬ Periodic (digit (j+1)) (2*3^j) := by
  intro h
  have ht := third_digit j 0
  have he := h 0
  have hz : digit (j+1) 0 = 0 := by
    have hpos := one_lt_pow₀ (by decide : 1 < (3:ℕ)) (Nat.succ_ne_zero j)
    simp [digit, Nat.div_eq_of_lt hpos]
  simp [hz] at ht he
  omega

private def shift (f : ℕ → ℕ) (n : ℕ) := f (n+1)

private lemma shift_iterate (t : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    (shift^[t] f) n = f (n+t) := by
  induction t generalizing f n with
  | zero => simp
  | succ t ih => rw [Function.iterate_succ_apply, ih]; rfl

private lemma shift_period {f : ℕ → ℕ} {t : ℕ} :
    IsPeriodicPt shift t f ↔ Periodic f t := by
  change shift^[t] f = f ↔ ∀ n, f (n+t) = f n
  constructor
  · intro h n
    simpa only [shift_iterate] using congrFun h n
  · intro h
    funext n
    simpa only [shift_iterate] using h n

/-- It suffices to rule out the quotient of the period by each of its prime
divisors. The minimal positive period of the shift divides every period. -/
private lemma least_from_prime_divisors {f : ℕ → ℕ} {P t : ℕ}
    (hp : Periodic f P) (bad : ∀ r, r.Prime → r ∣ P → ¬ Periodic f (P/r))
    (ht : 0 < t) (h : Periodic f t) : P ≤ t := by
  let a := minimalPeriod shift f
  have ha : a ∣ P := (shift_period.mpr hp).minimalPeriod_dvd
  obtain ⟨c, hc⟩ := ha
  have hc1 : c = 1 := by
    by_contra hne
    obtain ⟨r, hr, b, hb⟩ := Nat.exists_prime_and_dvd hne
    have hpform : P = r*(a*b) := by rw [hc, hb]; ring
    have hrP : r ∣ P := ⟨_, hpform⟩
    have had : a ∣ P/r := by
      rw [hpform, Nat.mul_div_cancel_left _ hr.pos]
      exact dvd_mul_right _ _
    exact bad r hr hrP (shift_period.mp ((isPeriodicPt_minimalPeriod shift f).trans_dvd had))
  have heq : P = a := by simpa [hc1] using hc
  rw [heq]
  exact (shift_period.mpr h).minimalPeriod_le ht

private lemma minimal (j t : ℕ) (ht : 0 < t) (h : Periodic (digit j) t) : 2*3^j ≤ t := by
  apply least_from_prime_divisors (full_period j) _ ht h
  intro r hr hrd
  rcases hr.dvd_mul.mp hrd with hr2 | hr3
  · have he := (Nat.dvd_prime Nat.prime_two).mp hr2
    rcases he with h1 | rfl
    · exact (hr.ne_one h1).elim
    · simpa using not_half j
  · have he := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp (hr.dvd_of_dvd_pow hr3)
    rcases he with h1 | rfl
    · exact (hr.ne_one h1).elim
    · cases j with
      | zero => simp at hr3
      | succ j => simpa [pow_succ, ← Nat.mul_assoc] using not_third j

private lemma extend_period {j t : ℕ} (h : columnPeriod j t) : Periodic (digit j) t := by
  let P := 2*3^j
  let s := 3^j * P
  have hs : Periodic (digit j) s := (full_period j).nat_mul (3^j)
  intro n
  have hsge : 3^j ≤ s := by
    have hP : 1 ≤ P := by change 0 < 2*3^j; positivity
    simpa [s] using Nat.mul_le_mul_left (3^j) hP
  have hlarge : 3^j ≤ 2^(n+s) := (by omega : 3^j ≤ n+s).trans Nat.lt_two_pow_self.le
  exact (hs (n+t)).symm.trans <|
    (by simpa only [Nat.add_right_comm] using h (n+s) hlarge :
      digit j (n+t+s) = digit j (n+s)).trans (hs n)

/-- Stepping by a third of a period adds the same nonzero residue each
time. The three entries in the resulting orbit contain each digit once. -/
private lemma triple (j n d : ℕ) (hd : d < 3) :
    let t := 2*3^j
    (if digit (j+1) n = d then 1 else 0) +
      ((if digit (j+1) (n+t) = d then 1 else 0) +
       (if digit (j+1) (n+t+t) = d then 1 else 0)) = 1 := by
  dsimp only
  rw [third_digit j (n+2*3^j), third_residue, third_digit j n]
  have hbase : digit (j+1) n < 3 := Nat.mod_lt _ (by decide)
  have hr : 2^n % 3 ≠ 0 := by
    intro h
    have := (by decide : Nat.Prime 3).dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h)
    exact (by decide : ¬3 ∣ 2) this
  have table : ∀ a b d : Fin 3, b.val ≠ 0 →
      (if a.val = d.val then 1 else 0) +
       ((if (a.val+b.val)%3 = d.val then 1 else 0) +
         (if ((a.val+b.val)%3+b.val)%3 = d.val then 1 else 0)) = 1 := by decide
  exact table ⟨_, hbase⟩ ⟨_, Nat.mod_lt _ (by decide)⟩ ⟨_, hd⟩ hr

private lemma balanced (j start d : ℕ) (hd : d < 3) :
    ((range (2*3^(j+1))).filter (fun i => digit (j+1) (start+i) = d)).card = (2*3^(j+1))/3 := by
  let t := 2*3^j
  have he : 2*3^(j+1) = t+(t+t) := by dsimp [t]; ring
  rw [he, show (t+(t+t))/3 = t by omega]
  have hsum := Finset.sum_boole (R := ℕ) (fun i => digit (j+1) (start+i) = d) (range (t+(t+t)))
  simp only [Nat.cast_id] at hsum
  rw [← hsum]
  rw [Finset.sum_range_add, Finset.sum_range_add]
  simp only [← Finset.sum_add_distrib]
  calc
    _ = ∑ _i ∈ range t, (1:ℕ) := by
      apply sum_congr rfl
      intro i _
      simpa only [t, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using triple j (start+i) d hd
    _ = t := by simp

end TernaryColumns

theorem OMA.solution : type_of% @OMA.S_oeis_a265210.main := by
  intro j
  constructor
  · refine ⟨⟨by positivity, fun n _ => TernaryColumns.full_period j n⟩, ?_⟩
    rintro t ⟨ht, hp⟩
    exact TernaryColumns.minimal j t ht (TernaryColumns.extend_period hp)
  · intro hj start _ d hd
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    exact TernaryColumns.balanced k start d hd
