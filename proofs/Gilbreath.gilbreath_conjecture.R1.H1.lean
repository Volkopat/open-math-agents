import OMAReductions.R_Gilbreath_gilbreath_conjecture_R1
import Mathlib

/-! Gilbreath for `k ≤ 500`. The first 501 primes are certified in the kernel as a chain of
consecutive primes (so `Nat.nth Nat.Prime j` is the `j`-th entry, via `Nat.nth_count`), the
difference table is computed row by row, and every row from `1` to `500` starts with `1`. -/

namespace OMA.Step_Gilbreath_gilbreath_conjecture_R1_H1

-- ### Primality certificates

/-- Trial division of `n` by `d, d + 1, ...`, for at most `fuel` divisors, succeeding once
`d * d > n`. Running out of fuel counts as failure. -/
def noDiv (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | fuel + 1, d => if n < d * d then true else (n % d != 0) && noDiv n fuel (d + 1)

theorem noDiv_spec (n : ℕ) : ∀ fuel d : ℕ, noDiv n fuel d = true →
    ∀ m : ℕ, d ≤ m → m * m ≤ n → ¬ m ∣ n := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [noDiv] at h
  | succ fuel ih =>
    intro d h m hdm hmn hdiv
    unfold noDiv at h
    by_cases hlt : n < d * d
    · have : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · rw [if_neg hlt] at h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      rcases Nat.eq_or_lt_of_le hdm with rfl | hlt'
      · exact h.1 (Nat.mod_eq_zero_of_dvd hdiv)
      · exact ih (d + 1) h.2 m hlt' hmn hdiv

/-- A sound Boolean primality test. -/
def isPrimeB (n : ℕ) : Bool := decide (2 ≤ n) && noDiv n n 2

theorem isPrimeB_spec {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  simp only [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h2, hd⟩ := h
  by_contra hnp
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hne : n ≠ 1 := by omega
  have hmin := (Nat.minFac_prime hne).two_le
  exact noDiv_spec n n 2 hd (Nat.minFac n) hmin (by nlinarith) (Nat.minFac_dvd n)

/-- `m` has a divisor in `[d, d + fuel)` strictly between `1` and `m`. -/
def hasDiv (m : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, d => (decide (2 ≤ d) && decide (d < m) && m % d == 0) || hasDiv m f (d + 1)

theorem hasDiv_spec (m : ℕ) : ∀ f d : ℕ, hasDiv m f d = true → ¬ Nat.Prime m := by
  intro f
  induction f with
  | zero => intro d h; simp [hasDiv] at h
  | succ f ih =>
    intro d h hp
    simp only [hasDiv, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    rcases h with ⟨⟨h2, hlt⟩, hmod⟩ | h
    · rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega
    · exact ih (d + 1) h hp

/-- Every `m` in `[s, s + c)` is not prime. -/
def allComp (s : ℕ) : ℕ → Bool
  | 0 => true
  | c + 1 => hasDiv (s + c) 64 2 && allComp s c

theorem allComp_spec (s : ℕ) : ∀ c : ℕ, allComp s c = true → ∀ m, s ≤ m → m < s + c → ¬ Nat.Prime m := by
  intro c
  induction c with
  | zero => intro _ m h1 h2; omega
  | succ c ih =>
    intro h m h1 h2
    simp only [allComp, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge m (s + c) with hlt | hge
    · exact ih h.2 m h1 hlt
    · have : m = s + c := by omega
      subst this
      exact hasDiv_spec _ _ _ h.1

/-- Consecutive primes: `q` is prime, `q < q'`, and nothing strictly between is prime. -/
def chainB : List ℕ → Bool
  | [] => true
  | [q] => isPrimeB q
  | q :: q' :: rest => isPrimeB q && decide (q < q') && allComp (q + 1) (q' - q - 1) &&
      chainB (q' :: rest)

theorem count_step {q q' : ℕ} (hq : Nat.Prime q) (hlt : q < q')
    (hgap : ∀ m, q + 1 ≤ m → m < q' → ¬ Nat.Prime m) :
    Nat.count Nat.Prime q' = Nat.count Nat.Prime q + 1 := by
  have key : ∀ t, t ≤ q' - q - 1 → Nat.count Nat.Prime (q + 1 + t) = Nat.count Nat.Prime q + 1 := by
    intro t
    induction t with
    | zero => intro _; rw [Nat.add_zero, Nat.count_succ, if_pos hq]
    | succ t ih =>
      intro ht
      rw [← Nat.add_assoc, Nat.count_succ, if_neg (hgap _ (by omega) (by omega)), ih (by omega)]
  have := key (q' - q - 1) le_rfl
  rwa [show q + 1 + (q' - q - 1) = q' by omega] at this

theorem chainB_spec : ∀ (l : List ℕ) (q i : ℕ), chainB (q :: l) = true → Nat.count Nat.Prime q = i →
    ∀ j < l.length + 1, Nat.Prime ((q :: l).getD j 0) ∧
      Nat.count Nat.Prime ((q :: l).getD j 0) = i + j := by
  intro l
  induction l with
  | nil =>
    intro q i h hc j hj
    have : j = 0 := by simp at hj; omega
    subst this
    exact ⟨isPrimeB_spec (by simpa [chainB] using h), by simpa using hc⟩
  | cons q' rest ih =>
    intro q i h hc j hj
    simp only [chainB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hp, hlt⟩, hgap⟩, hrest⟩ := h
    have hqp := isPrimeB_spec hp
    have hc' : Nat.count Nat.Prime q' = i + 1 := by
      rw [count_step hqp hlt (fun m h1 h2 => allComp_spec _ _ hgap m h1 (by omega)), hc]
    rcases j with _ | j
    · exact ⟨hqp, by simpa using hc⟩
    · have := ih q' (i + 1) hrest hc' j (by simp at hj ⊢; omega)
      simp only [List.getD_cons_succ]
      rw [show i + (j + 1) = i + 1 + j by omega]
      exact this

-- ### The first 501 primes

/-- The primes up to `3581`, the `500`-th prime (counting from `0`). -/
def L : List ℕ := (List.range 3582).filter isPrimeB

theorem L_chain : chainB L = true ∧ L.length = 501 ∧ L.getD 0 0 = 2 := by decide +kernel

theorem nth_eq (j : ℕ) (hj : j ≤ 500) : Nat.nth Nat.Prime j = L.getD j 0 := by
  obtain ⟨hch, hlen, h0⟩ := L_chain
  have hc2 : Nat.count Nat.Prime 2 = 0 := by decide
  cases hL : L with
  | nil => rw [hL] at hlen; simp at hlen
  | cons q rest =>
    rw [hL] at hch hlen h0
    simp only [List.getD_cons_zero] at h0
    subst h0
    obtain ⟨hp, hc⟩ := chainB_spec rest 2 0 hch hc2 j (by simp at hlen; omega)
    rw [Nat.zero_add] at hc
    conv_lhs => rw [← hc]
    exact Nat.nth_count hp

-- ### Rows of absolute differences

/-- `|a - b|` on natural numbers. -/
def ad (a b : ℕ) : ℕ := if a ≤ b then b - a else a - b

/-- Absolute differences of neighbours. -/
def diffs : List ℕ → List ℕ
  | a :: b :: t => ad a b :: diffs (b :: t)
  | _ => []

theorem diffs_length : ∀ l : List ℕ, (diffs l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by simp [diffs, diffs_length (b :: t)]

theorem diffs_getD : ∀ (l : List ℕ) (n : ℕ), n + 1 < l.length →
    (diffs l).getD n 0 = ad (l.getD n 0) (l.getD (n + 1) 0)
  | [], n, h => by simp at h
  | [_], n, h => by simp at h
  | a :: b :: t, 0, _ => by simp [diffs]
  | a :: b :: t, n + 1, h => by
    simp only [diffs, List.getD_cons_succ]
    exact diffs_getD (b :: t) n (by simp at h ⊢; omega)

/-- Row `k` of the difference table of the first 501 primes. -/
def row : ℕ → List ℕ
  | 0 => L
  | k + 1 => diffs (row k)

theorem row_length (k : ℕ) : (row k).length = 501 - k := by
  induction k with
  | zero => exact L_chain.2.1
  | succ k ih => rw [row, diffs_length, ih]; omega

theorem d_succ (k n : ℕ) :
    Gilbreath.d (k + 1) n = Int.natAbs ((Gilbreath.d k (n + 1) : ℤ) - Gilbreath.d k n) := rfl

theorem d_eq_row : ∀ k n : ℕ, n + k ≤ 500 → Gilbreath.d k n = (row k).getD n 0 := by
  intro k
  induction k with
  | zero => intro n hn; exact nth_eq n (by omega)
  | succ k ih =>
    intro n hn
    rw [d_succ, ih n (by omega), ih (n + 1) (by omega), row,
      diffs_getD _ _ (by rw [row_length]; omega), ad]
    split_ifs with h <;> omega

-- ### The check

/-- Rows `k + 1, ..., k + c` all begin with `1`, given row `k` as `l`. -/
def allOnes : ℕ → List ℕ → Bool
  | 0, _ => true
  | c + 1, l => let l' := diffs l; l'.getD 0 0 == 1 && allOnes c l'

theorem allOnes_spec : ∀ c k : ℕ, allOnes c (row k) = true →
    ∀ j, 1 ≤ j → j ≤ c → (row (k + j)).getD 0 0 = 1 := by
  intro c
  induction c with
  | zero => intro k _ j h1 h2; omega
  | succ c ih =>
    intro k h j h1 h2
    simp only [allOnes, Bool.and_eq_true, beq_iff_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · have := ih (k + 1) h.2 (j - 1) (by omega) (by omega)
      rwa [show k + 1 + (j - 1) = k + j by omega] at this

theorem check : allOnes 500 (row 0) = true := by decide +kernel

theorem gilbreath_le (k : ℕ+) (hk : (k : ℕ) ≤ 500) : Gilbreath.d k 0 = 1 := by
  rw [d_eq_row _ _ (by omega)]
  have := allOnes_spec 500 0 check k k.pos hk
  rwa [Nat.zero_add] at this

end OMA.Step_Gilbreath_gilbreath_conjecture_R1_H1

theorem OMA.solution : OMA.R_Gilbreath_gilbreath_conjecture_R1.H1 :=
  OMA.Step_Gilbreath_gilbreath_conjecture_R1_H1.gilbreath_le
