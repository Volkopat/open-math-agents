import OMAStatements.S_oeis_a027117

namespace OMA.P027117

open OMA.S_oeis_a027117

/-- The tribonacci numbers 1, 1, 2, 4, 7, 13, ... -/
def tr : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | n + 3 => tr n + tr (n + 1) + tr (n + 2)

lemma tr_rec (i j k l : ℕ) (hj : j = i + 1) (hk : k = i + 2) (hl : l = i + 3) :
    tr l = tr i + tr j + tr k := by
  subst hj hk hl
  rw [tr]

lemma T_step (n k : ℕ) (h : k + 3 ≤ 2 * (n + 1) - 1) :
    T (n + 1) (k + 3) = T n k + T n (k + 1) + T n (k + 2) := by
  conv_lhs => rw [T]
  rw [if_pos h]

lemma T_gen (n K x y z : ℕ) (h : K ≤ 2 * n + 1) (hx : x + 3 = K) (hy : y + 2 = K)
    (hz : z + 1 = K) : T (n + 1) K = T n x + T n y + T n z := by
  subst hx
  have e1 : y = x + 1 := by omega
  have e2 : z = x + 2 := by omega
  subst e1 e2
  exact T_step n x (by omega)

lemma T0 (n : ℕ) : T (n + 1) 0 = 1 := by rw [T]
lemma T1 (n : ℕ) : T (n + 1) 1 = 1 := by rw [T]
lemma T2 (n : ℕ) : T (n + 1) 2 = 2 := by rw [T]

lemma left : ∀ n k : ℕ, k ≤ n + 2 → T (n + 1) k = tr k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    interval_cases k
    · exact T0 0
    · exact T1 0
    · exact T2 0
  | succ n ih =>
    intro k hk
    match k, hk with
    | 0, _ => exact T0 (n + 1)
    | 1, _ => exact T1 (n + 1)
    | 2, _ => exact T2 (n + 1)
    | j + 3, hj =>
      rw [T_step (n + 1) j (by omega), ih j (by omega), ih (j + 1) (by omega),
        ih (j + 2) (by omega)]
      rw [tr]

lemma leftg (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n + 1) : T n k = tr k := by
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
  exact left p k (by omega)

/-- The diagonal T(n, n+4). -/
def A (i : ℕ) : ℤ := T i (i + 4)

/-- The diagonal T(n, n+3). -/
def B (i : ℕ) : ℤ := T i (i + 3)

/-- The diagonal T(n, n+2). -/
def Cc (i : ℕ) : ℤ := T i (i + 2)

lemma A_succ (i j : ℕ) (hj : j = i + 1) (hi : 4 ≤ i) : A j = A i + B i + Cc i := by
  subst hj
  unfold A B Cc
  rw [T_gen i (i + 1 + 4) (i + 2) (i + 3) (i + 4) (by omega) (by omega) (by omega) (by omega)]
  ring

lemma B_succ (i j : ℕ) (hj : j = i + 1) (hi : 3 ≤ i) : B j = B i + Cc i + tr j := by
  subst hj
  unfold B Cc
  rw [T_gen i (i + 1 + 3) (i + 1) (i + 2) (i + 3) (by omega) (by omega) (by omega) (by omega),
    leftg i (i + 1) (by omega) (by omega)]
  ring

lemma C_succ (i j : ℕ) (hj : j = i + 1) (hi : 2 ≤ i) : Cc j = Cc i + tr i + tr j := by
  subst hj
  unfold Cc
  rw [T_gen i (i + 1 + 2) i (i + 1) (i + 2) (by omega) (by omega) (by omega) (by omega),
    leftg i i (by omega) (by omega), leftg i (i + 1) (by omega) (by omega)]
  ring

end OMA.P027117

open OMA.S_oeis_a027117 OMA.P027117 in
theorem OMA.solution : type_of% @OMA.S_oeis_a027117.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  have e1 : m + 10 - 1 = m + 9 := by omega
  have e2 : m + 10 - 2 = m + 8 := by omega
  have e3 : m + 10 - 3 = m + 7 := by omega
  have e4 : m + 10 - 4 = m + 6 := by omega
  have e5 : m + 10 - 5 = m + 5 := by omega
  have e6 : m + 10 - 6 = m + 4 := by omega
  rw [e1, e2, e3, e4, e5, e6]
  show A (m + 10) = 4 * A (m + 9) - 5 * A (m + 8) + 2 * A (m + 7) - A (m + 6) + 2 * A (m + 5)
    - A (m + 4)
  have a4 := A_succ (m + 4) (m + 5) rfl (by omega)
  have a5 := A_succ (m + 5) (m + 6) rfl (by omega)
  have a6 := A_succ (m + 6) (m + 7) rfl (by omega)
  have a7 := A_succ (m + 7) (m + 8) rfl (by omega)
  have a8 := A_succ (m + 8) (m + 9) rfl (by omega)
  have a9 := A_succ (m + 9) (m + 10) rfl (by omega)
  have b4 := B_succ (m + 4) (m + 5) rfl (by omega)
  have b5 := B_succ (m + 5) (m + 6) rfl (by omega)
  have b6 := B_succ (m + 6) (m + 7) rfl (by omega)
  have b7 := B_succ (m + 7) (m + 8) rfl (by omega)
  have b8 := B_succ (m + 8) (m + 9) rfl (by omega)
  have c4 := C_succ (m + 4) (m + 5) rfl (by omega)
  have c5 := C_succ (m + 5) (m + 6) rfl (by omega)
  have c6 := C_succ (m + 6) (m + 7) rfl (by omega)
  have c7 := C_succ (m + 7) (m + 8) rfl (by omega)
  have c8 := C_succ (m + 8) (m + 9) rfl (by omega)
  have t7 := tr_rec (m + 4) (m + 5) (m + 6) (m + 7) rfl rfl rfl
  have t8 := tr_rec (m + 5) (m + 6) (m + 7) (m + 8) rfl rfl rfl
  have t9 := tr_rec (m + 6) (m + 7) (m + 8) (m + 9) rfl rfl rfl
  linarith
