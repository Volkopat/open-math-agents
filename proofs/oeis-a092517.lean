import OMAStatements.S_oeis_a092517

/-!
The admissible bases are exactly d+1 for positive divisors d of n(n+1).
For sufficiency we first write the square in its ordinary base expansion.
If x > 0, the number s of summands in that expansion satisfies s² < b*x.
Applying this to the quotient after removing the final digit of the square
leaves fewer than n+b summands. The congruence modulo b-1 then allows us
to split powers until exactly n+1 summands remain.
-/

namespace SquarePowerBases

open OMA.S_oeis_a092517

private def total (b : ℕ) (l : List ℕ) : ℕ := (l.map (fun e => b^e)).sum

private theorem total_cons (b e : ℕ) (l : List ℕ) :
    total b (e::l) = b^e + total b l := rfl

private theorem shift (b : ℕ) (l : List ℕ) : total b (l.map Nat.succ) = b * total b l := by
  induction l with
  | nil => simp [total]
  | cons x l ih => simp only [List.map_cons, total_cons, ih, pow_succ]; ring

private theorem digit (b r : ℕ) (l : List ℕ) :
    total b (List.replicate r 0 ++ l.map Nat.succ) = r + b * total b l := by
  have add (u v : List ℕ) : total b (u ++ v) = total b u + total b v := by simp [total]
  rw [add, shift]
  simp [total]

private theorem append_digit_bound {b s r : ℕ} (hr : r < b) :
    (s+r)^2 ≤ b*(s^2+r) := by
  have cross : 2*s ≤ s^2+1 := by cases s <;> nlinarith
  calc
    (s+r)^2 ≤ (r+1)*(s^2+r) := by nlinarith [Nat.mul_le_mul_left r cross]
    _ ≤ b*(s^2+r) := Nat.mul_le_mul_right _ hr

private theorem short (b : ℕ) (hb : 2 ≤ b) (x : ℕ) (hx : 0 < x) :
    ∃ l : List ℕ, total b l = x ∧ l.length^2 < b*x := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    by_cases tiny : x < b
    · refine ⟨List.replicate x 0, by simp [total], ?_⟩
      simpa [pow_two] using Nat.mul_lt_mul_of_pos_right tiny hx
    · let q := x / b
      let r := x % b
      have hr : r < b := Nat.mod_lt _ (by omega)
      have hq : 0 < q := Nat.div_pos (by omega) (by omega)
      have decomp : r + b*q = x := Nat.mod_add_div x b
      obtain ⟨l, hl, small⟩ := ih q (Nat.div_lt_self hx hb) hq
      refine ⟨List.replicate r 0 ++ l.map Nat.succ, by rw [digit, hl, decomp], ?_⟩
      simp only [List.length_append, List.length_replicate, List.length_map]
      calc
        (r+l.length)^2 = (l.length+r)^2 := by rw [Nat.add_comm]
        _ ≤ b*(l.length^2+r) := append_digit_bound hr
        _ < b*(b*q+r) := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        _ = b*x := by rw [Nat.add_comm (b*q), decomp]

private theorem total_mod (d : ℕ) (l : List ℕ) :
    l.length ≡ total (d+1) l [MOD d] := by
  have unit : 1 ≡ d+1 [MOD d] := (Nat.modEq_iff_dvd' (by omega)).2 (by simp)
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.length_cons, total_cons, Nat.add_comm l.length]
    simpa using (unit.pow e).add ih

private theorem split_power {b : ℕ} (hb : 2 ≤ b) (l : List ℕ) (h : l.length < total b l) :
    ∃ s : List ℕ, s.length = l.length + (b-1) ∧ total b s = total b l := by
  induction l with
  | nil => simp [total] at h
  | cons e l ih =>
    cases e with
    | zero =>
      rw [List.length_cons, total_cons, pow_zero] at h
      obtain ⟨s, hs, he⟩ := ih (by omega)
      exact ⟨0::s, by simp only [List.length_cons]; omega, by simp [total_cons, he]⟩
    | succ e =>
      refine ⟨List.replicate b e ++ l, by simp; omega, ?_⟩
      simp [total, pow_succ, mul_comm]

private theorem expand {d : ℕ} (hd : 0 < d) (j : ℕ) (l : List ℕ)
    (h : l.length+d*j ≤ total (d+1) l) :
    ∃ s : List ℕ, s.length = l.length+d*j ∧ total (d+1) s = total (d+1) l := by
  induction j generalizing l with
  | zero => exact ⟨l, by simp, rfl⟩
  | succ j ih =>
    rw [Nat.mul_succ] at h ⊢
    obtain ⟨t, ht, he⟩ := split_power (by omega : 2 ≤ d+1) l (by omega)
    obtain ⟨s, hs, hval⟩ := ih t (by omega)
    exact ⟨s, by omega, hval.trans he⟩

private theorem as_list (m b x : ℕ) :
    (∃ f : Fin m → ℕ, (∑ i, b^f i) = x) ↔
      ∃ l : List ℕ, l.length = m ∧ total b l = x := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨List.ofFn f, by simp, by simpa [total, List.map_ofFn, List.sum_ofFn, Function.comp_def] using hf⟩
  · rintro ⟨l, rfl, hx⟩
    refine ⟨l.get, ?_⟩
    simpa [total, List.map_ofFn, List.sum_ofFn, Function.comp_def] using
      (show total b (List.ofFn l.get) = x by simpa using hx)

private theorem eligible (n d : ℕ) (hn : 1 ≤ n) :
    IsValidBase n (d+1) ↔ d ∣ n*(n+1) := by
  let m := n+1
  have diff : m^2-m = n*(n+1) := by
    have : m^2 = m + n*(n+1) := by dsimp [m]; ring
    omega
  have large : m ≤ m^2 := by dsimp [m]; nlinarith
  change (0 < d+1 ∧ ∃ f : Fin m → ℕ, (∑ i, (d+1)^f i) = m^2) ↔ _
  rw [as_list]
  constructor
  · rintro ⟨_, l, hl, he⟩
    have h := total_mod d l
    rw [hl, he] at h
    simpa [diff] using (Nat.modEq_iff_dvd' large).mp h
  · intro hdvd
    have prodpos : 0 < n*(n+1) := by positivity
    have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd prodpos
    have dbound := Nat.le_of_dvd prodpos hdvd
    have base_le : d+1 ≤ m^2 := by omega
    have mod_square : m ≡ m^2 [MOD d] := (Nat.modEq_iff_dvd' large).2 (diff ▸ hdvd)
    let b := d+1
    let q := m^2 / b
    let r := m^2 % b
    have hr : r < b := Nat.mod_lt _ (by dsimp [b]; omega)
    have decomp : r+b*q = m^2 := Nat.mod_add_div _ _
    obtain ⟨l, hl, hs⟩ := short b (by dsimp [b]; omega) q (Nat.div_pos base_le (by omega))
    have lt_m : l.length < m := by
      by_contra! hc
      have := Nat.pow_le_pow_left hc 2
      omega
    let t := List.replicate r 0 ++ l.map Nat.succ
    have ht : t.length = r+l.length := by simp [t]
    have value : total (d+1) t = m^2 := by
      change total b (List.replicate r 0 ++ l.map Nat.succ) = _
      rw [digit, hl, decomp]
    have same := total_mod d t
    rw [value] at same
    have congruent := same.trans mod_square.symm
    have bound : t.length < m+d := by dsimp [b] at hr; omega
    have small : t.length ≤ m := by
      by_contra! longer
      have dv := (Nat.modEq_iff_dvd' longer.le).mp congruent.symm
      have := Nat.le_of_dvd (show 0 < t.length-m by omega) dv
      omega
    obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' small).mp congruent
    have size : t.length+d*j = m := by omega
    obtain ⟨s, hlen, hval⟩ := expand hd j t (by rw [size, value]; exact large)
    exact ⟨by omega, s, hlen.trans size, hval.trans value⟩

end SquarePowerBases

open OMA.S_oeis_a092517 SquarePowerBases

theorem OMA.solution : type_of% @OMA.S_oeis_a092517.main := by
  intro n hn
  have pos : n*(n+1) ≠ 0 := by positivity
  have eq : {b : ℕ | IsValidBase n b} =
      ((n*(n+1)).divisors.image Nat.succ : Finset ℕ) := by
    ext b
    cases b with
    | zero => simp [IsValidBase]
    | succ d => simp [eligible n d hn, Nat.mem_divisors, pos]
  rw [eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ Nat.succ_injective]
  exact (show n.Coprime (n+1) by simp).card_divisors_mul
