import OMAStatements.S_oeis_a305562

/-!
# The diagonal numerators of A386393

Mikhail Kurkov recorded the rational triangle at https://oeis.org/A386393.
For its connection to https://oeis.org/A305562, see Max Alekseyev's proof at
https://mathoverflow.net/a/498031.

The binomial theorem applied to the shift `f i ↦ f (i + 1) / 2` gives a
recurrence for the diagonal. Clearing powers of two recovers the recurrence
for `a`. Since every `a n` is odd, the corresponding fraction is in lowest terms.
-/

open OMA.S_oeis_a305562

namespace A305562Proof

def b (n : ℕ) : ℚ := row n 0

def halfShift : Module.End ℚ (ℕ → ℚ) where
  toFun f i := f (i + 1) / 2
  map_add' f g := by
    funext i
    exact add_div (f (i + 1)) (g (i + 1)) 2
  map_smul' r f := by
    funext i
    change (r * f (i + 1)) / 2 = r * (f (i + 1) / 2)
    ring

lemma halfShift_pow (k : ℕ) (f : ℕ → ℚ) (s : ℕ) :
    (halfShift ^ k) f s = (1 / 2 : ℚ) ^ k * f (s + k) := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    change (halfShift ^ k) f (s + 1) / 2 = _
    rw [ih, pow_succ]
    rw [show s + 1 + k = s + (k + 1) by omega]
    ring

/-- Applying the row recurrence `k` times expresses column `k` in terms of column zero. -/
lemma row_binomial (k s : ℕ) :
    row (s + k) k = ((halfShift + 1) ^ k) b s := by
  induction k generalizing s with
  | zero => simp [b]
  | succ k ih =>
    rw [show s + (k + 1) = (s + k) + 1 by omega, row, pow_succ', Module.End.mul_apply]
    change row (s + k + 1) k / 2 + row (s + k) k =
      ((halfShift + 1) ^ k) b (s + 1) / 2 + ((halfShift + 1) ^ k) b s
    rw [show s + k + 1 = (s + 1) + k by omega, ih, ih]

lemma diag_rec (n : ℕ) : b (n + 1) =
    ∑ j : Fin (n + 1), (n.choose j.val : ℚ) * (1 / 2 : ℚ) ^ j.val * b j.val := by
  have hdiag : b (n + 1) = row (0 + n) n := by simp [b, row]
  rw [hdiag, row_binomial, (Commute.one_right halfShift).add_pow,
    Fin.sum_univ_eq_sum_range
      (fun j => (n.choose j : ℚ) * (1 / 2 : ℚ) ^ j * b j) (n + 1)]
  simp only [one_pow, mul_one, LinearMap.sum_apply, Finset.sum_apply,
    Module.End.mul_apply, Module.End.natCast_apply, halfShift_pow,
    nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma tri_mono : Monotone tri := by
  apply monotone_nat_of_le_succ
  intro n
  simp [tri]

/-- Each summand except the last has a factor of two. The last summand is `a n`. -/
lemma odd_seq (n : ℕ) : Odd (a n) := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    rw [a, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.choose_self, one_mul,
      Nat.sub_self, pow_zero, mul_one]
    refine Even.add_odd ?_ ih
    apply Finset.even_sum
    intro j _
    have hj : tri (j.val + 1) ≤ tri n := tri_mono j.isLt
    have hlt : tri (j.val + 1) < tri (n + 1) := by
      change tri (j.val + 1) < tri n + n
      have := j.isLt
      omega
    exact ((even_two : Even (2 : ℕ)).pow_of_ne_zero (Nat.sub_pos_of_lt hlt).ne').mul_left _

lemma num_div (n : ℕ) : ((a n : ℚ) / (2 : ℚ) ^ tri n).num = (a n : ℤ) := by
  have hcop : Nat.Coprime (a n) (2 ^ tri n) :=
    (odd_seq n).coprime_two_right.pow_right _
  have hn := Rat.num_div_eq_of_coprime (a := (a n : ℤ))
    (b := ((2 ^ tri n : ℕ) : ℤ)) (by positivity) (by simpa using hcop)
  simpa using hn

/-- Clearing the common power of two gives the integer recurrence for `a`. -/
lemma normalized (n : ℕ) : b n = (a n : ℚ) / (2 : ℚ) ^ tri n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [b, row, a, tri]
    | succ n =>
      rw [diag_rec, a, eq_div_iff (by positivity), Finset.sum_mul]
      push_cast
      apply Finset.sum_congr rfl
      intro j _
      rw [ih j.val j.isLt]
      have hj : tri (j.val + 1) ≤ tri (n + 1) := tri_mono (by omega)
      have hp : (2 : ℚ) ^ tri (n + 1) =
          2 ^ (tri (n + 1) - tri (j.val + 1)) * (2 ^ tri j.val * 2 ^ j.val) := by
        rw [← pow_add, ← pow_add]
        congr 1
        exact (Nat.sub_add_cancel hj).symm
      rw [div_pow, one_pow, hp]
      field_simp

end A305562Proof

open A305562Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a305562.main := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
    change (a (n + 1) : ℤ) = (row n n).num
    have hd : b (n + 1) = row n n := by rw [b, row]
    rw [← hd, normalized, num_div]
