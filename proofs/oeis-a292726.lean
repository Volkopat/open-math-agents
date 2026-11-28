import OMAStatements.S_oeis_a292726

/-!
# Proof of the two conjectures of A292726 (equal-piles stone game)

Undo moves: an inverse move splits an even pile into two equal halves, or replaces two piles of
equal parity by two copies of their average. Each inverse move strictly decreases the sum of the
squares of the pile sizes, and the only states without an inverse move are those whose piles are
all equal to the same odd number `d` (with `d ∣ n`). Hence every state is reached from such a
state. Such a state with `d > 1` is unreachable from the all-ones state (its only predecessor is
itself), and so is the state `2d, d, …, d` when `d < n`. This gives:
* `n = 2^k`: the only odd divisor is `1`, so every partition is reachable;
* `n` an odd prime: exactly the one-pile state `n` is unreachable;
* otherwise `n` has an odd divisor `1 < d < n`, giving at least two unreachable states.
-/

namespace OMA.A292726Proof

open OMA.S_oeis_a292726 Multiset Relation

/-- All piles are nonempty. -/
def Pos (s : Multiset ℕ) : Prop := ∀ x ∈ s, 0 < x

/-- Sum of squares of the pile sizes. -/
def Φ (s : Multiset ℕ) : ℕ := (s.map fun x => x ^ 2).sum

lemma filter_ne_zero_of_pos {r : Multiset ℕ} (hr : Pos r) : r.filter (· ≠ 0) = r :=
  Multiset.filter_eq_self.mpr fun x hx => (hr x hx).ne'

lemma fcons_pos {x : ℕ} (s : Multiset ℕ) (hx : x ≠ 0) :
    (x ::ₘ s).filter (· ≠ 0) = x ::ₘ s.filter (· ≠ 0) := filter_cons_of_pos _ hx

lemma fcons_neg {x : ℕ} (s : Multiset ℕ) (hx : x = 0) :
    (x ::ₘ s).filter (· ≠ 0) = s.filter (· ≠ 0) := filter_cons_of_neg _ (by simpa using hx)

lemma sum_filter_ne_zero (s : Multiset ℕ) : (s.filter (· ≠ 0)).sum = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih => by_cases hx : x = 0 <;> simp [hx, ih]

lemma move_sum {s t : Multiset ℕ} (h : Move s t) : t.sum = s.sum := by
  obtain ⟨r, a, k, ha, hk, rfl, rfl⟩ := h
  rw [sum_filter_ne_zero]
  simp only [sum_cons]
  omega

lemma move_pos {s t : Multiset ℕ} (h : Move s t) : Pos t := by
  obtain ⟨r, a, k, ha, hk, rfl, rfl⟩ := h
  intro x hx
  rw [mem_filter] at hx
  exact Nat.pos_of_ne_zero hx.2

lemma rtg_sum {s t : Multiset ℕ} (h : ReflTransGen Move s t) : t.sum = s.sum := by
  induction h with
  | refl => rfl
  | tail _ hm ih => rw [move_sum hm, ih]

lemma rtg_pos {s t : Multiset ℕ} (h : ReflTransGen Move s t) (hs : Pos s) : Pos t := by
  induction h with
  | refl => exact hs
  | tail _ hm _ => exact move_pos hm

lemma pos_replicate_one (n : ℕ) : Pos (replicate n 1) := by
  intro x hx
  rw [eq_of_mem_replicate hx]
  exact Nat.one_pos

lemma reachable_pos {n : ℕ} {s : Multiset ℕ} (h : reachable n s) : Pos s :=
  rtg_pos h (pos_replicate_one n)

lemma reachable_sum {n : ℕ} {s : Multiset ℕ} (h : reachable n s) : s.sum = n := by
  rw [rtg_sum h]
  simp

lemma Φ_cons (x : ℕ) (s : Multiset ℕ) : Φ (x ::ₘ s) = x ^ 2 + Φ s := by
  simp [Φ]

/-- Every state with nonempty piles is reached from a state whose piles are all equal and odd:
undoing moves strictly decreases the sum of squares. -/
lemma descend : ∀ (m : ℕ) (s : Multiset ℕ), Φ s = m → Pos s →
    ∃ c d : ℕ, Odd d ∧ ReflTransGen Move (replicate c d) s := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro s hm hs
  by_cases he : ∃ e ∈ s, Even e
  · obtain ⟨e, he, b, rfl⟩ := he
    have hb : 0 < b := by have := hs _ he; omega
    have hsr : s = (b + b) ::ₘ s.erase (b + b) := (cons_erase he).symm
    have hr : Pos (s.erase (b + b)) := fun x hx => hs x (mem_of_mem_erase hx)
    have hmove : Move (b ::ₘ b ::ₘ s.erase (b + b)) s := by
      refine ⟨s.erase (b + b), b, b, hb, le_rfl, rfl, ?_⟩
      rw [fcons_pos _ (show b + b ≠ 0 by omega), fcons_neg _ (Nat.sub_self b),
        filter_ne_zero_of_pos hr]
      exact hsr
    have hlt : Φ (b ::ₘ b ::ₘ s.erase (b + b)) < m := by
      rw [← hm, hsr, Φ_cons, Φ_cons, Φ_cons, erase_cons_head]
      nlinarith
    have hpos : Pos (b ::ₘ b ::ₘ s.erase (b + b)) := by
      intro x hx
      simp only [mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hb
      · exact hb
      · exact hr x hx
    obtain ⟨c, d, hd, hreach⟩ := ih _ hlt _ rfl hpos
    exact ⟨c, d, hd, hreach.tail hmove⟩
  · push Not at he
    have hodd : ∀ x ∈ s, Odd x := fun x hx => Nat.not_even_iff_odd.mp (he x hx)
    by_cases hd : ∃ x ∈ s, ∃ y ∈ s, y < x
    · obtain ⟨x, hx, y, hy, hxy⟩ := hd
      have hy' : y ∈ s.erase x := mem_erase_of_ne (ne_of_lt hxy) |>.mpr hy
      set r := (s.erase x).erase y with hr_def
      have hsr : s = x ::ₘ y ::ₘ r := by
        rw [hr_def, cons_erase hy', cons_erase hx]
      have hr : Pos r := fun z hz => hs z (mem_of_mem_erase (mem_of_mem_erase hz))
      obtain ⟨p, rfl⟩ := hodd x hx
      obtain ⟨q, rfl⟩ := hodd y hy
      obtain ⟨e, rfl⟩ : ∃ e, p = q + e + 1 := ⟨p - q - 1, by omega⟩
      have hmove : Move ((2 * q + e + 2) ::ₘ (2 * q + e + 2) ::ₘ r) s := by
        refine ⟨r, 2 * q + e + 2, e + 1, by omega, by omega, rfl, ?_⟩
        have h1 : 2 * q + e + 2 + (e + 1) = 2 * (q + e + 1) + 1 := by omega
        have h2 : 2 * q + e + 2 - (e + 1) = 2 * q + 1 := by omega
        rw [h1, h2, fcons_pos _ (show 2 * (q + e + 1) + 1 ≠ 0 by omega),
          fcons_pos _ (show 2 * q + 1 ≠ 0 by omega), filter_ne_zero_of_pos hr]
        exact hsr
      have hlt : Φ ((2 * q + e + 2) ::ₘ (2 * q + e + 2) ::ₘ r) < m := by
        rw [← hm, hsr, Φ_cons, Φ_cons, Φ_cons, Φ_cons]
        nlinarith
      have hpos : Pos ((2 * q + e + 2) ::ₘ (2 * q + e + 2) ::ₘ r) := by
        intro z hz
        simp only [mem_cons] at hz
        rcases hz with rfl | rfl | hz
        · omega
        · omega
        · exact hr z hz
      obtain ⟨c, d, hd, hreach⟩ := ih _ hlt _ rfl hpos
      exact ⟨c, d, hd, hreach.tail hmove⟩
    · push Not at hd
      rcases Multiset.empty_or_exists_mem s with h0 | ⟨d, hdm⟩
      · subst h0
        exact ⟨0, 1, odd_one, by simp; exact ReflTransGen.refl⟩
      · have hall : ∀ b ∈ s, b = d := fun b hb =>
          le_antisymm (hd b hb d hdm) (hd d hdm b hb)
        have hs' : replicate (card s) d = s := (eq_replicate.mpr ⟨rfl, hall⟩).symm
        refine ⟨card s, d, hodd d hdm, ?_⟩
        generalize card s = c at hs' ⊢
        rw [hs']

/-- A set of states closed under taking predecessors and avoiding the start is unreachable. -/
lemma not_reachable_of_closed (n : ℕ) (B : Multiset ℕ → Prop)
    (hB : ∀ s t, Pos s → Move s t → B t → B s) (h1 : ¬ B (replicate n 1)) :
    ∀ s, reachable n s → ¬ B s := by
  intro s hs
  induction hs with
  | refl => exact h1
  | tail hst hm ih => exact fun hb => ih (hB _ _ (rtg_pos hst (pos_replicate_one n)) hm hb)

lemma mem_of_move_eq {t r : Multiset ℕ} {a k : ℕ} (ha : 0 < a) (hr : Pos r)
    (h : t = ((a + k) ::ₘ (a - k) ::ₘ r).filter (· ≠ 0)) :
    a + k ∈ t ∧ (k < a → a - k ∈ t ∧ t = (a + k) ::ₘ (a - k) ::ₘ r) ∧
      (k = a → t = (a + k) ::ₘ r) := by
  rw [fcons_pos _ (show a + k ≠ 0 by omega)] at h
  refine ⟨by rw [h]; exact mem_cons_self _ _, fun hk => ?_, fun hk => ?_⟩
  · rw [fcons_pos _ (show a - k ≠ 0 by omega), filter_ne_zero_of_pos hr] at h
    exact ⟨by rw [h]; simp, h⟩
  · rw [fcons_neg _ (show a - k = 0 by omega), filter_ne_zero_of_pos hr] at h
    exact h

lemma pos_tail {a : ℕ} {r : Multiset ℕ} (h : Pos (a ::ₘ a ::ₘ r)) : Pos r :=
  fun x hx => h x (mem_cons_of_mem (mem_cons_of_mem hx))

/-- A state with all piles equal to the same odd number has no predecessor but itself. -/
lemma pred_replicate {c d : ℕ} (hd : Odd d) {s : Multiset ℕ} (hs : Pos s)
    (hm : Move s (replicate c d)) : s = replicate c d := by
  obtain ⟨r, a, k, ha, hk, rfl, ht⟩ := hm
  have hr := pos_tail hs
  obtain ⟨h1, h2, h3⟩ := mem_of_move_eq ha hr ht
  have e1 := eq_of_mem_replicate h1
  rcases lt_or_eq_of_le hk with hk | hk
  · obtain ⟨h4, h5⟩ := h2 hk
    have e2 := eq_of_mem_replicate h4
    have : k = 0 := by omega
    subst this
    simpa using h5.symm
  · obtain ⟨j, hj⟩ := hd
    omega

lemma replicate_ne_ones {n c d : ℕ} (hn : 1 ≤ n) (hd : 1 < d) : replicate n 1 ≠ replicate c d := by
  intro h
  have : (1 : ℕ) ∈ replicate c d := h ▸ mem_replicate.mpr ⟨by omega, rfl⟩
  have := eq_of_mem_replicate this
  omega

/-- For `d` odd, `d > 1`, the state with all piles equal to `d` is unreachable. -/
lemma unreachable_replicate {n c d : ℕ} (hn : 1 ≤ n) (hd : Odd d) (hd1 : 1 < d) :
    ¬ reachable n (replicate c d) :=
  not_reachable_of_closed n (fun s => s = replicate c d)
    (fun s t hs hm ht => by subst ht; exact pred_replicate hd hs hm)
    (replicate_ne_ones hn hd1) _ |> fun h hr => h hr rfl

/-- The state `2d, d, …, d` (with `c ≥ 2` piles before merging) is unreachable too. -/
lemma unreachable_merged {n c d : ℕ} (hn : 1 ≤ n) (hd : Odd d) (hd1 : 1 < d) :
    ¬ reachable n ((2 * d) ::ₘ replicate c d) := by
  intro hr
  refine not_reachable_of_closed n
    (fun s => s = replicate (c + 2) d ∨ s = (2 * d) ::ₘ replicate c d) ?_ ?_ _ hr (Or.inr rfl)
  · rintro s t hs hm (rfl | rfl)
    · exact Or.inl (pred_replicate hd hs hm)
    · obtain ⟨r, a, k, ha, hk, rfl, ht⟩ := hm
      have hr := pos_tail hs
      obtain ⟨h1, h2, h3⟩ := mem_of_move_eq ha hr ht
      have memv : ∀ x ∈ (2 * d) ::ₘ replicate c d, x = 2 * d ∨ x = d := by
        intro x hx
        rw [mem_cons] at hx
        rcases hx with h | h
        · exact Or.inl h
        · exact Or.inr (eq_of_mem_replicate h)
      obtain ⟨j, hj⟩ := hd
      rcases lt_or_eq_of_le hk with hk | hk
      · obtain ⟨h4, h5⟩ := h2 hk
        rcases memv _ h1 with e1 | e1 <;> rcases memv _ h4 with e2 | e2
        · -- both piles `2d`: but `2d` occurs only once
          exfalso
          have hk0 : k = 0 := by omega
          subst hk0
          rw [show a + 0 = 2 * d by omega, show a - 0 = 2 * d by omega] at h5
          have hc := congrArg (count (2 * d)) h5
          rw [count_cons_self, count_cons_self, count_cons_self,
            count_eq_zero.mpr (fun h => by have := eq_of_mem_replicate h; omega)] at hc
          omega
        · exfalso; omega
        · exfalso; omega
        · right
          have hk0 : k = 0 := by omega
          subst hk0
          simpa using h5.symm
      · left
        subst hk
        have e1 := memv _ h1
        have had : k = d := by omega
        subst had
        have := h3 rfl
        rw [show k + k = 2 * k by ring, cons_inj_right] at this
        rw [← this, replicate_succ, replicate_succ]
  · rintro (h | h)
    · exact replicate_ne_ones hn hd1 h
    · have : (2 * d) ∈ replicate n 1 := h ▸ mem_cons_self _ _
      have := eq_of_mem_replicate this
      omega

/-- From a single pile no move is possible. -/
lemma rtg_singleton {n : ℕ} {s : Multiset ℕ} (h : ReflTransGen Move {n} s) : s = {n} := by
  induction h with
  | refl => rfl
  | tail _ hm ih =>
    subst ih
    obtain ⟨r, a, k, -, -, h, -⟩ := hm
    have := congrArg card h
    simp at this

def mk {n : ℕ} (s : Multiset ℕ) (hs : Pos s) (hsum : s.sum = n) : Nat.Partition n :=
  ⟨s, fun hx => hs _ hx, hsum⟩

lemma pos_replicate {c d : ℕ} (hd : 0 < d) : Pos (replicate c d) := by
  intro x hx; rw [eq_of_mem_replicate hx]; exact hd

open Classical in
lemma diff_eq (n : ℕ) : Fintype.card (Nat.Partition n) - a n =
    (Finset.univ.filter fun p : Nat.Partition n => ¬ reachable n p.parts).card := by
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Nat.Partition n)))
    (fun p => reachable n p.parts)
  rw [Finset.card_univ] at this
  unfold a
  omega

/-- Every state is reached from the all-ones state or from an all-`d` state, `d > 1` odd. -/
lemma reach_or_stuck {n : ℕ} (p : Nat.Partition n) :
    reachable n p.parts ∨ ∃ c d, Odd d ∧ 1 < d ∧ c * d = n ∧
      ReflTransGen Move (replicate c d) p.parts := by
  obtain ⟨c, d, hd, h⟩ := descend _ p.parts rfl (fun x hx => p.parts_pos hx)
  have hsum := rtg_sum h
  rw [p.parts_sum, sum_replicate, smul_eq_mul] at hsum
  rcases Nat.lt_or_ge 1 d with h1 | h1
  · exact Or.inr ⟨c, d, hd, h1, hsum.symm, h⟩
  · left
    have : d = 1 := by obtain ⟨j, hj⟩ := hd; omega
    subst this
    rw [mul_one] at hsum
    subst hsum
    exact h

lemma all_reachable_pow2 {k : ℕ} (p : Nat.Partition (2 ^ k)) : reachable (2 ^ k) p.parts := by
  rcases reach_or_stuck p with h | ⟨c, d, hd, hd1, hcd, -⟩
  · exact h
  · exfalso
    have hdvd : d ∣ 2 ^ k := ⟨c, by rw [← hcd]; ring⟩
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    rcases i with _ | i
    · simp at hd1
    · rw [pow_succ] at hd
      exact Nat.not_even_iff_odd.mpr hd (even_two.mul_left _)

open Classical in
lemma diff_pos {n d : ℕ} (hn : 1 ≤ n) (hd : Odd d) (hd1 : 1 < d) (hdn : d ∣ n) :
    1 ≤ Fintype.card (Nat.Partition n) - a n := by
  obtain ⟨c, rfl⟩ := hdn
  rw [diff_eq, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro h
  refine h (Finset.mem_univ (mk (replicate c d) (pos_replicate (by omega)) ?_)) ?_
  · simp [mul_comm]
  · exact unreachable_replicate hn hd hd1

open Classical in
lemma diff_two {n d : ℕ} (hn : 1 ≤ n) (hd : Odd d) (hd1 : 1 < d) (hdn : d ∣ n) (hlt : d < n) :
    2 ≤ Fintype.card (Nat.Partition n) - a n := by
  obtain ⟨c, rfl⟩ := hdn
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by
    rcases c with _ | _ | c
    · simp at hn
    · simp at hlt
    · omega⟩
  rw [diff_eq]
  have hdpos : 0 < d := by omega
  let p := mk (n := d * (c + 2)) (replicate (c + 2) d) (pos_replicate hdpos)
    (by simp only [sum_replicate, smul_eq_mul]; ring)
  let q := mk (n := d * (c + 2)) ((2 * d) ::ₘ replicate c d)
    (by intro x hx; rw [mem_cons] at hx; rcases hx with rfl | hx
        · omega
        · exact pos_replicate hdpos x hx)
    (by simp; ring)
  have hpq : p ≠ q := by
    intro h
    have h' := congrArg Nat.Partition.parts h
    have : (2 * d) ∈ replicate (c + 2) d := by
      change replicate (c + 2) d = (2 * d) ::ₘ replicate c d at h'
      rw [h']; exact mem_cons_self _ _
    have := eq_of_mem_replicate this
    omega
  have : 1 < (Finset.univ.filter fun p : Nat.Partition (d * (c + 2)) =>
      ¬ reachable (d * (c + 2)) p.parts).card := by
    rw [Finset.one_lt_card]
    refine ⟨p, ?_, q, ?_, hpq⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact unreachable_replicate hn hd hd1
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact unreachable_merged hn hd hd1
  omega

open Classical in
lemma diff_prime {n : ℕ} (hp : n.Prime) (ho : Odd n) : Fintype.card (Nat.Partition n) - a n = 1 := by
  rw [diff_eq, Finset.card_eq_one]
  have hn : 0 < n := hp.pos
  refine ⟨mk {n} (by intro x hx; rw [mem_singleton] at hx; omega) (by simp), ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  constructor
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := unreachable_replicate (n := n) (c := 1) hn ho hp.one_lt
    rw [replicate_one] at this
    exact this
  · intro p hp'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp'
    rcases reach_or_stuck p with h | ⟨c, d, hd, hd1, hcd, h⟩
    · exact absurd h hp'
    · have hdvd : d ∣ n := ⟨c, by rw [← hcd]; ring⟩
      rcases hp.eq_one_or_self_of_dvd d hdvd with rfl | rfl
      · omega
      · have : c = 1 := by
          have := hp.pos
          nlinarith [Nat.mul_right_cancel this (show c * d = 1 * d by omega)]
        subst this
        rw [replicate_one] at h
        apply Nat.Partition.ext
        exact rtg_singleton h

lemma odd_proper_divisor {n : ℕ} (hn : 1 ≤ n) (h2 : ¬ ∃ k : ℕ, n = 2 ^ k)
    (hpo : ¬ (n.Prime ∧ Odd n)) : ∃ d, Odd d ∧ 1 < d ∧ d ∣ n ∧ d < n := by
  obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hm1 : m ≠ 1 := by rintro rfl; exact h2 ⟨j, by ring⟩
  have hm3 : 3 ≤ m := by obtain ⟨i, rfl⟩ := hm; omega
  rcases j with _ | j
  · simp only [pow_zero, one_mul] at hpo ⊢
    have hnp : ¬ m.Prime := fun hp => hpo ⟨hp, hm⟩
    refine ⟨m.minFac, hm.of_dvd_nat (Nat.minFac_dvd m), (Nat.minFac_prime hm1).one_lt,
      Nat.minFac_dvd m, (Nat.not_prime_iff_minFac_lt (by omega)).mp hnp⟩
  · refine ⟨m, hm, by omega, dvd_mul_left _ _, ?_⟩
    have : 2 ≤ 2 ^ (j + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith

open Classical in
theorem solution : ∀ n : ℕ, 1 ≤ n →
    (Fintype.card (Nat.Partition n) - a n = 0 ↔ ∃ k : ℕ, n = 2 ^ k) ∧
    (Fintype.card (Nat.Partition n) - a n = 1 ↔ n.Prime ∧ Odd n) := by
  intro n hn
  have pow2 : ∀ k, n = 2 ^ k → Fintype.card (Nat.Partition n) - a n = 0 := by
    rintro k rfl
    rw [diff_eq, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p _ hp
    exact hp (all_reachable_pow2 p)
  constructor
  · constructor
    · intro h0
      by_contra h2
      obtain ⟨j, m, hm, hjm⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
      have hm1 : m ≠ 1 := by rintro rfl; exact h2 ⟨j, by rw [hjm]; ring⟩
      have hm3 : 1 < m := by obtain ⟨i, rfl⟩ := hm; omega
      have := diff_pos hn hm hm3 ⟨2 ^ j, by rw [hjm]; ring⟩
      omega
    · rintro ⟨k, hk⟩
      exact pow2 k hk
  · constructor
    · intro h1
      by_contra hpo
      by_cases h2 : ∃ k : ℕ, n = 2 ^ k
      · obtain ⟨k, hk⟩ := h2
        have := pow2 k hk
        omega
      · obtain ⟨d, hd, hd1, hdn, hlt⟩ := odd_proper_divisor hn h2 hpo
        have := diff_two hn hd hd1 hdn hlt
        omega
    · rintro ⟨hp, ho⟩
      exact diff_prime hp ho

end OMA.A292726Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a292726.main := OMA.A292726Proof.solution
