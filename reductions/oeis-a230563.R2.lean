import OMAStatements.S_oeis_a230563
import Mathlib.Tactic

-- Credit: @Pixelstorm44
namespace OMA.R_oeis_a230563_R2

/-- After canceling a common base, the two remaining pairs must nest.
The gap between their larger bases is less than b/n. -/
def H1 : Prop := ∀ n c a b d : ℕ, 7 ≤ n → 0 < c → c < a → a ≤ b → b < d →
    n * (d - b) < b → a ^ n + b ^ n ≠ c ^ n + d ^ n

/-- Without a common base, orient the triples by increasing maximum.
Only gaps between the maxima below 2z/n can contribute. -/
def H2 : Prop := ∀ n x y z u v w : ℕ, 7 ≤ n →
    0 < x → x ≤ y → y ≤ z → 0 < u → u ≤ v → v ≤ w →
    List.Disjoint [x, y, z] [u, v, w] → z < w → n * (w - z) < 2 * z →
    x ^ n + y ^ n + z ^ n ≠ u ^ n + v ^ n + w ^ n

/-- A denominator-free version of Bernoulli's inequality. -/
theorem growth (b g n : ℕ) :
    (b + n * g) * b ^ n ≤ b * (b + g) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have step := Nat.mul_le_mul_right (b + g) ih
    simp only [pow_succ]
    nlinarith only [step, Nat.zero_le (n * g * g * b ^ n)]

theorem close_max {b d n k : ℕ} (hb : 0 < b) (hbd : b ≤ d)
    (h : d ^ n < (k + 1) * b ^ n) : n * (d - b) < k * b := by
  have lower := growth b (d - b) n
  rw [Nat.add_sub_of_le hbd] at lower
  have upper := Nat.mul_lt_mul_of_pos_left h hb
  by_contra! far
  have scale := Nat.mul_le_mul_right (b ^ n) far
  nlinarith only [lower, upper, scale]

theorem pairs {n : ℕ} (hp : H1) (hn : 7 ≤ n) {a b c d : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d)
    (eqn : a ^ n + b ^ n = c ^ n + d ^ n) : a = c ∧ b = d := by
  have nested : ∀ {i j k l : ℕ}, 0 < i → i ≤ j → 0 < k → j < l →
      i ^ n + j ^ n = k ^ n + l ^ n → False := by
    intro i j k l hi hij hk hjl he
    have strict := Nat.pow_lt_pow_left hjl (by omega : n ≠ 0)
    have hki : k < i := by
      by_contra! hh
      have := Nat.pow_le_pow_left hh n
      omega
    have hmax : l ^ n < (1 + 1) * j ^ n := by
      have := Nat.pow_le_pow_left hij n
      have := pow_pos hk n
      omega
    have gap := close_max (k := 1) (by omega) hjl.le hmax
    exact hp n k i j l hn hk hki hij hjl (by simpa using gap) he
  rcases lt_trichotomy b d with h | rfl | h
  · exact (nested ha hab hc h eqn).elim
  · have hpow : a ^ n = c ^ n := by omega
    exact ⟨(Nat.pow_left_inj (by omega : n ≠ 0)).mp hpow, rfl⟩
  · exact (nested hc hcd ha h eqn.symm).elim

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a230563.main := by
  intro hp ht n hn x y z u v w hx hxy hyz hu huv hvw he
  by_cases disj : List.Disjoint [x, y, z] [u, v, w]
  · have oriented : ∀ {a b c d e f : ℕ}, 0 < a → a ≤ b → b ≤ c →
        0 < d → d ≤ e → e ≤ f → List.Disjoint [a, b, c] [d, e, f] → c < f →
        a ^ n + b ^ n + c ^ n = d ^ n + e ^ n + f ^ n → False := by
      intro a b c d e f ha hab hbc hd hde hef hdis hcf h
      have hmax : f ^ n < (2 + 1) * c ^ n := by
        have := Nat.pow_le_pow_left (hab.trans hbc) n
        have := Nat.pow_le_pow_left hbc n
        have := pow_pos hd n
        omega
      exact ht n a b c d e f hn ha hab hbc hd hde hef hdis hcf
        (close_max (by omega) hcf.le hmax) h
    have hzw : z ≠ w := by
      rintro rfl
      exact List.disjoint_left.mp disj (by simp : z ∈ [x,y,z]) (by simp)
    rcases lt_or_gt_of_ne hzw with h | h
    · exact (oriented hx hxy hyz hu huv hvw disj h he).elim
    · exact (oriented hu huv hvw hx hxy hyz disj.symm h he.symm).elim
  · -- For each possible shared base, cancel its power and compare the ordered pairs.
    have shared : x = u ∨ x = v ∨ x = w ∨ y = u ∨ y = v ∨ y = w ∨
        z = u ∨ z = v ∨ z = w := by
      simp only [List.disjoint_cons_left, List.disjoint_nil_left, List.mem_cons,
        List.not_mem_nil, or_false, and_true] at disj
      tauto
    simp only [Prod.mk.injEq]
    rcases shared with h | h | h | h | h | h | h | h | h
    · subst u
      have := pairs hp hn (a := y) (b := z) (c := v) (d := w)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
    · subst v
      have := pairs hp hn (a := y) (b := z) (c := u) (d := w)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
    · subst w
      have := pairs hp hn (a := y) (b := z) (c := u) (d := v)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
    · subst u
      have := pairs hp hn (a := x) (b := z) (c := v) (d := w)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
    · subst v
      have := pairs hp hn (a := x) (b := z) (c := u) (d := w)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
    · subst w
      have := pairs hp hn (a := x) (b := z) (c := u) (d := v)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
    · subst u
      have := pairs hp hn (a := x) (b := y) (c := v) (d := w)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
    · subst v
      have := pairs hp hn (a := x) (b := y) (c := u) (d := w)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      omega
    · subst w
      have := pairs hp hn (a := x) (b := y) (c := u) (d := v)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      omega

end OMA.R_oeis_a230563_R2
