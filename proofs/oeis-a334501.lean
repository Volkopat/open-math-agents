import OMAStatements.S_oeis_a334501

/- An independent finite counterexample to Barker's recurrence.
kinoyu-ai previously published the full width classification, the generating
function, and counterexamples at widths 10 and 11 on 27 November 2026.
https://github.com/kinoyu-ai/rule190-period
The finite return certificates and proofs below were independently written
for the project's own representation. -/

namespace OMA.S_oeis_a334501

private theorem forward (n a b : Nat) (h : state n a = state n b) (k : Nat) :
    state n (a+k) = state n (b+k) := by
  induction k with
  | zero => exact h
  | succ k ih => exact congrArg (step n) ih

private theorem repeatCycle {n T d : Nat} (h : state n (T+d) = state n T) (k m : Nat) :
    state n ((T+k) + m*d) = state n (T+k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have eq := forward n (T+d) T h (k + m*d)
    rw [Nat.succ_mul]
    calc
      state n (T + k + (m * d + d)) = state n (T + d + (k + m*d)) := by congr 1 <;> omega
      _ = state n (T + (k + m*d)) := eq
      _ = state n (T + k) := by rw [← Nat.add_assoc, ih]

/-- A finite certificate for minimal eventual period of the observed cell.
At the start of the cycle the full state returns after d steps; each smaller
positive lag is contradicted by at least one pair of observations. -/
private theorem fundamental_of_cycle {n T d : Nat} (hd : 0 < d)
    (h : state n (T+d) = state n T)
    (small : ∀ q : Fin d, 0 < q.val → ∃ r : Fin d,
      bit n (T+r.val+q.val) ≠ bit n (T+r.val)) : Fundamental n d := by
  constructor
  · refine ⟨hd, T, ?_⟩
    intro t ht
    have v := forward n (T+d) T h (t-T)
    have v₁ : T + d + (t-T) = t+d := by omega
    have v₂ : T + (t-T) = t := by omega
    rw [v₁,v₂] at v
    exact congrArg (· % 2) v
  · intro q hq
    rcases hq with ⟨hq, U, hu⟩
    apply Nat.le_of_not_lt
    intro bad
    obtain ⟨r, hr⟩ := small ⟨q, bad⟩ hq
    have ht : U ≤ T + r.val + U*d := by
      have := Nat.le_mul_of_pos_right U hd
      omega
    have e := hu (T+r.val+U*d) ht
    have e₁ := repeatCycle h (r.val+q) U
    have e₂ := repeatCycle h r.val U
    have eq₁ : (T+r.val+U*d)+q = (T+(r.val+q))+U*d := by omega
    rw [bit, bit, eq₁, e₁, e₂] at e
    exact hr (by simpa only [bit, Nat.add_assoc] using e)

private theorem value_of_fundamental {n p : Nat} (hn : n ≠ 0) (hp : Fundamental n p) : a n = p := by
  classical
  have hi : ∃ q, Fundamental n q := ⟨p, hp⟩
  have hh := Classical.choose_spec hi
  simp only [a, if_neg hn, dif_pos hi]
  exact Nat.le_antisymm (hh.2 p hp.1) (hp.2 _ hh.1)

theorem value_two : a 2 = 1 := value_of_fundamental (by decide)
  (@fundamental_of_cycle 2 1 1 (by decide) (by decide) (by decide))

theorem value_six : a 6 = 6 := value_of_fundamental (by decide)
  (@fundamental_of_cycle 6 3 6 (by decide) (by decide) (by decide))

theorem value_ten : a 10 = 10 := value_of_fundamental (by decide)
  (@fundamental_of_cycle 10 5 10 (by decide) (by decide) (by decide))

theorem barker_recurrence_false : ¬ recurrence := by
  intro h
  have contra := h 10 (by decide)
  change (a 10 : Int) = 2 * (a 6 : Int) - (a 2 : Int) at contra
  rw [value_ten, value_six, value_two] at contra
  contradiction


end OMA.S_oeis_a334501

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a334501.main) := by
  intro h
  exact OMA.S_oeis_a334501.barker_recurrence_false h.2
