import OMAStatements.S_oeis_a278898

/-!
# A278898: Barker's recurrence and g.f. for the x-axis of the 2D Rule 107

Normalize by the background (OFF at even stages, ON at odd stages). From stage 8 on the
automaton has an exact description (`closed_all`), with `r = t / 2`:

* stage `2r`: the ON cells are the cells of the box `|i|, |j| ≤ r` with `i + j` even, except the
  origin (`E`);
* stage `2r + 1`: the OFF cells are the cells of the box `|i|, |j| ≤ r + 1` with `i + j` odd that
  are neither on the ring `max(|i|, |j|) = r` nor next to the origin (`F`).

`step_even` and `step_odd` check that one step maps each description to the next (`r ≥ 3`), by a
case analysis closed with `omega`. Stage 8 itself comes from the light cone (`far`: beyond taxicab
distance `t` a cell has the background value) and tables of stages `0, …, 8` checked by the kernel
(`check_steps`, `table`, `base8`).

On the axis this gives closed forms by `n mod 4` (`a4`, `a4_1`, `a4_2`, `a4_3`): with `n = 4q + s`,
`a(4q) = a(4q+2) = 100 (100^q - 1)/99`, `a(4q+1) = (10^(4q+2) - 1)/9 - (10 · 100^(q+1) - 1000)/99`,
`a(4q+3) = (10^(4q+4) - 1)/9 - (10 · 100^q - 1000)/99` for `q ≥ 2`. The recurrence for `n ≥ 16`
(`recur`) is then an identity, and the generating function (`gf`) follows from it and the values
`a(0), …, a(15)`.
-/

open OMA.S_oeis_a278898

namespace A278898P
open OMA.S_oeis_a278898

/-- In the box of radius `k`. -/
def Box (k i j : ℤ) : Prop := -k ≤ i ∧ i ≤ k ∧ -k ≤ j ∧ j ≤ k

/-- ON cells at stage `2r`. -/
def E (r i j : ℤ) : Prop := Box r i j ∧ (i + j) % 2 = 0 ∧ ¬ (i = 0 ∧ j = 0)

/-- OFF cells at stage `2r+1` (the background there is ON). -/
def F (r i j : ℤ) : Prop :=
  Box (r + 1) i j ∧ ¬ (Box r i j ∧ ¬ Box (r - 1) i j) ∧ (i + j) % 2 = 1 ∧
    ¬ ((i = 0 ∧ (j = 1 ∨ j = -1)) ∨ (j = 0 ∧ (i = 1 ∨ i = -1)))

instance (k i j : ℤ) : Decidable (Box k i j) := by unfold Box; infer_instance
instance (r i j : ℤ) : Decidable (E r i j) := by unfold E; infer_instance
instance (r i j : ℤ) : Decidable (F r i j) := by unfold F; infer_instance

theorem toNat_decide (p : Prop) [Decidable p] : (decide p).toNat = if p then 1 else 0 := by
  by_cases h : p <;> simp [h]

set_option maxHeartbeats 4000000 in
theorem step_even (r : ℤ) (hr : 2 ≤ r) (t : ℕ)
    (h : ∀ i j, cell 107 t i j = decide (E r i j)) (i j : ℤ) :
    cell 107 (t + 1) i j = decide (¬ F r i j) := by
  show Nat.testBit 107 _ = _
  rw [h, h, h, h, h]
  simp only [toNat_decide]
  by_cases h0 : E r i j <;> by_cases h1 : E r (i + 1) j <;> by_cases h2 : E r (i - 1) j <;>
    by_cases h3 : E r i (j + 1) <;> by_cases h4 : E r i (j - 1) <;> by_cases h5 : F r i j <;>
    simp only [h0, h1, h2, h3, h4, h5, if_true, if_false, not_true_eq_false, not_false_eq_true,
      decide_true, decide_false] <;>
    first | rfl | (exfalso; unfold E F Box at *; omega)

set_option maxHeartbeats 4000000 in
theorem step_odd (r : ℤ) (hr : 3 ≤ r) (t : ℕ)
    (h : ∀ i j, cell 107 t i j = decide (¬ F r i j)) (i j : ℤ) :
    cell 107 (t + 1) i j = decide (E (r + 1) i j) := by
  show Nat.testBit 107 _ = _
  rw [h, h, h, h, h]
  simp only [toNat_decide]
  by_cases h0 : F r i j <;> by_cases h1 : F r (i + 1) j <;> by_cases h2 : F r (i - 1) j <;>
    by_cases h3 : F r i (j + 1) <;> by_cases h4 : F r i (j - 1) <;> by_cases h5 : E (r + 1) i j <;>
    simp only [h0, h1, h2, h3, h4, h5, if_true, if_false, not_true_eq_false, not_false_eq_true,
      decide_true, decide_false] <;>
    first | rfl | (exfalso; unfold E F Box at *; omega)


/-- Within distance `t` of the origin (taxicab). -/
def Near (t i j : ℤ) : Prop := i + j ≤ t ∧ i - j ≤ t ∧ -i + j ≤ t ∧ -i - j ≤ t

instance (t i j : ℤ) : Decidable (Near t i j) := by unfold Near; infer_instance

/-- Background value at stage `t`. -/
def bg (t : ℕ) : Bool := decide (t % 2 = 1)

/-- Beyond taxicab distance `t` every cell has the background value. -/
theorem far (t : ℕ) : ∀ i j : ℤ, ¬ Near t i j → cell 107 t i j = bg t := by
  induction t with
  | zero =>
    intro i j h
    unfold Near at h
    show decide (i = 0 ∧ j = 0) = bg 0
    simp only [bg]
    have : ¬ (i = 0 ∧ j = 0) := by omega
    simp [this]
  | succ t ih =>
    intro i j h
    show Nat.testBit 107 _ = _
    unfold Near at h
    push_cast at h
    rw [ih i j (by unfold Near; omega), ih (i + 1) j (by unfold Near; omega),
      ih (i - 1) j (by unfold Near; omega), ih i (j + 1) (by unfold Near; omega),
      ih i (j - 1) (by unfold Near; omega)]
    unfold bg
    rcases Nat.mod_two_eq_zero_or_one t with h2 | h2
    · have h3 : (t + 1) % 2 = 1 := by omega
      simp only [h2, h3, decide_true]
      decide
    · have h3 : ¬ ((t + 1) % 2 = 1) := by omega
      simp only [h2, h3, decide_true, decide_false]
      decide

/-- The cells within distance `t` at stages `t ≤ 8`, as bits `(i + 8) * 17 + (j + 8)`. -/
def code : ℕ → ℕ
  | 0 => 22300745198530623141535718272648361505980416
  | 1 => 22300745198530623141535718272648361505980416
  | 2 => 7307530487825066080292738778628906005930878959616
  | 3 => 50217197017209528069142747513682045079738403408652126912512
  | 4 => 2011407704989444373563450180710377478054154480071475200
  | 5 => 862741330538167974325133357736747840676591899259425526444405974630400
  | 6 => 533555275808129436540963681769714820708260978738879491211264
  | 7 => 14821783202805084702102973811128588796677992639275847257004074246611452295118848
  | 8 => 140279797073445681822614891904865575645735463556735242657909964800
  | _ => 0

/-- The stages `t ≤ 8`, read from the table inside the light cone. -/
def G (t : ℕ) (i j : ℤ) : Bool :=
  if Near t i j then Nat.testBit (code t) ((i + 8) * 17 + (j + 8)).toNat else bg t

theorem check_steps : ∀ t : ℕ, t < 8 → ∀ a : ℕ, a < 17 → ∀ b : ℕ, b < 17 →
    Near ((t : ℤ) + 1) ((a : ℤ) - 8) ((b : ℤ) - 8) →
      Nat.testBit 107 ((G t ((a : ℤ) - 8) ((b : ℤ) - 8)).toNat +
        2 * ((G t ((a : ℤ) - 8 + 1) ((b : ℤ) - 8)).toNat + (G t ((a : ℤ) - 8 - 1) ((b : ℤ) - 8)).toNat +
          (G t ((a : ℤ) - 8) ((b : ℤ) - 8 + 1)).toNat + (G t ((a : ℤ) - 8) ((b : ℤ) - 8 - 1)).toNat)) =
        G (t + 1) ((a : ℤ) - 8) ((b : ℤ) - 8) := by
  decide +kernel

theorem table (t : ℕ) (ht : t ≤ 8) : ∀ i j : ℤ, cell 107 t i j = G t i j := by
  induction t with
  | zero =>
    intro i j
    show decide (i = 0 ∧ j = 0) = G 0 i j
    unfold G
    by_cases h : Near ((0 : ℕ) : ℤ) i j
    · have hi : i = 0 := by unfold Near at h; push_cast at h; omega
      have hj : j = 0 := by unfold Near at h; push_cast at h; omega
      subst hi; subst hj
      rw [if_pos h]
      decide
    · rw [if_neg h]
      have : ¬ (i = 0 ∧ j = 0) := by
        rintro ⟨rfl, rfl⟩; exact h (by decide)
      simp [this, bg]
  | succ t ih =>
    intro i j
    have ih' := ih (by omega)
    by_cases hN : Near ((t + 1 : ℕ) : ℤ) i j
    · show Nat.testBit 107 _ = _
      rw [ih', ih', ih', ih', ih']
      have hi : -8 ≤ i ∧ i ≤ 8 := by unfold Near at hN; push_cast at hN; omega
      have hj : -8 ≤ j ∧ j ≤ 8 := by unfold Near at hN; push_cast at hN; omega
      have key := check_steps t (by omega) (i + 8).toNat (by omega) (j + 8).toNat (by omega)
      have ea : ((i + 8).toNat : ℤ) - 8 = i := by omega
      have eb : ((j + 8).toNat : ℤ) - 8 = j := by omega
      rw [ea, eb] at key
      exact key (by push_cast at hN; exact hN)
    · rw [far (t + 1) i j hN]
      unfold G
      rw [if_neg hN]

theorem base8 : ∀ i j : ℤ, cell 107 8 i j = decide (E 4 i j) := by
  intro i j
  rw [table 8 le_rfl]
  have chk : ∀ a : ℕ, a < 17 → ∀ b : ℕ, b < 17 → G 8 ((a : ℤ) - 8) ((b : ℤ) - 8) = decide (E 4 ((a : ℤ) - 8) ((b : ℤ) - 8)) := by
    decide +kernel
  by_cases h : -8 ≤ i ∧ i ≤ 8 ∧ -8 ≤ j ∧ j ≤ 8
  · have key := chk (i + 8).toNat (by omega) (j + 8).toNat (by omega)
    have ea : ((i + 8).toNat : ℤ) - 8 = i := by omega
    have eb : ((j + 8).toNat : ℤ) - 8 = j := by omega
    rw [ea, eb] at key
    exact key
  · have hN : ¬ Near ((8 : ℕ) : ℤ) i j := by unfold Near; push_cast; omega
    have hE : ¬ E 4 i j := by unfold E Box; omega
    unfold G
    rw [if_neg hN]
    simp [hE, bg]

theorem closed_all (s : ℕ) :
    (∀ i j, cell 107 (8 + 2 * s) i j = decide (E (4 + (s : ℤ)) i j)) ∧
    (∀ i j, cell 107 (9 + 2 * s) i j = decide (¬ F (4 + (s : ℤ)) i j)) := by
  induction s with
  | zero =>
    have h8 : ∀ i j, cell 107 8 i j = decide (E (4 + ((0 : ℕ) : ℤ)) i j) := by
      intro i j; rw [base8]; norm_num
    refine ⟨h8, fun i j => ?_⟩
    exact step_even _ (by norm_num) 8 h8 i j
  | succ s ih =>
    have hE : ∀ i j, cell 107 (8 + 2 * (s + 1)) i j = decide (E (4 + ((s + 1 : ℕ) : ℤ)) i j) := by
      intro i j
      have := step_odd (4 + (s : ℤ)) (by omega) (9 + 2 * s) ih.2 i j
      rw [show 8 + 2 * (s + 1) = 9 + 2 * s + 1 by ring]
      rw [this]; push_cast; ring_nf
    refine ⟨hE, fun i j => ?_⟩
    rw [show 9 + 2 * (s + 1) = 8 + 2 * (s + 1) + 1 by ring]
    exact step_even _ (by push_cast; omega) _ hE i j

/-- The x-axis read from the origin outwards: digit `m` is the cell `(-m, 0)`. -/
theorem a_refl (n : ℕ) :
    (a n : ℚ) = ∑ m ∈ Finset.range (n + 1), if cell 107 n (-(m : ℤ)) 0 then (10 : ℚ) ^ m else 0 := by
  unfold a
  push_cast
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ n := by have := Finset.mem_range.1 hm; omega
  have e1 : ((n + 1 - 1 - m : ℕ) : ℤ) - n = -(m : ℤ) := by omega
  have e2 : n - (n + 1 - 1 - m) = m := by omega
  rw [e1, e2]

theorem E_axis (r : ℤ) (hr : 0 ≤ r) (m : ℕ) :
    E r (-(m : ℤ)) 0 ↔ ((m : ℤ) ≤ r ∧ m % 2 = 0 ∧ m ≠ 0) := by
  unfold E Box; omega

theorem F_axis (r : ℤ) (hr : 1 ≤ r) (m : ℕ) :
    F r (-(m : ℤ)) 0 ↔ ((m : ℤ) ≤ r + 1 ∧ (m : ℤ) ≠ r ∧ m % 2 = 1 ∧ m ≠ 1) := by
  unfold F Box; omega

/-- Even digits `2, 4, …` up to `r`. -/
def Se (r : ℕ) : ℚ := ∑ m ∈ Finset.range (r + 1), if m % 2 = 0 ∧ m ≠ 0 then (10 : ℚ) ^ m else 0

theorem Se_closed (q : ℕ) : Se (2 * q) = 100 * (100 ^ q - 1) / 99 ∧ Se (2 * q + 1) = 100 * (100 ^ q - 1) / 99 := by
  induction q with
  | zero => refine ⟨?_, ?_⟩ <;> simp [Se, Finset.sum_range_succ]
  | succ q ih =>
    have h1 : Se (2 * (q + 1)) = Se (2 * q + 1) + 10 ^ (2 * q + 2) := by
      rw [show 2 * (q + 1) = 2 * q + 1 + 1 by ring, Se, Finset.sum_range_succ, ← Se]
      have : (2 * q + 1 + 1) % 2 = 0 ∧ 2 * q + 1 + 1 ≠ 0 := by omega
      rw [if_pos this]
    have h2 : Se (2 * (q + 1) + 1) = Se (2 * (q + 1)) := by
      rw [Se, Finset.sum_range_succ, ← Se]
      have : ¬ ((2 * (q + 1) + 1) % 2 = 0 ∧ 2 * (q + 1) + 1 ≠ 0) := by omega
      rw [if_neg this, add_zero]
    have h3 : (10 : ℚ) ^ (2 * q + 2) = 100 * 100 ^ q := by
      rw [pow_add, pow_mul]; norm_num; ring
    refine ⟨?_, ?_⟩
    · rw [h1, ih.2, h3]; ring
    · rw [h2, h1, ih.2, h3]; ring

/-- Odd digits `3, 5, …` below `2K`. -/
def To (K : ℕ) : ℚ := ∑ m ∈ Finset.range (2 * K), if m % 2 = 1 ∧ m ≠ 1 then (10 : ℚ) ^ m else 0

theorem To_closed (K : ℕ) (hK : 1 ≤ K) : To K = (10 * 100 ^ K - 1000) / 99 := by
  induction K, hK using Nat.le_induction with
  | base => simp [To, Finset.sum_range_succ]; norm_num
  | succ K hK ih =>
    have h1 : To (K + 1) = To K + 10 ^ (2 * K + 1) := by
      rw [To, show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ← To]
      have n1 : ¬ ((2 * K) % 2 = 1 ∧ 2 * K ≠ 1) := by omega
      have n2 : (2 * K + 1) % 2 = 1 ∧ 2 * K + 1 ≠ 1 := by omega
      rw [if_neg n1, if_pos n2, add_zero]
    rw [h1, ih, pow_succ, pow_mul]; norm_num; ring

/-- All digits below `N`. -/
theorem R_closed (N : ℕ) : ∑ m ∈ Finset.range N, (10 : ℚ) ^ m = (10 ^ N - 1) / 9 := by
  rw [geom_sum_eq (by norm_num)]; norm_num

theorem ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) (x : ℚ) :
    (if P then x else 0) = (if Q then x else 0) := if_congr h rfl rfl

theorem a_even (r : ℕ) (hr : 4 ≤ r) : (a (2 * r) : ℚ) = Se r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = 4 + s := ⟨r - 4, by omega⟩
  rw [a_refl, show 2 * (4 + s) = 8 + 2 * s by ring]
  have hc := (closed_all s).1
  rw [Se, show 8 + 2 * s + 1 = (4 + s + 1) + (4 + s) by ring, Finset.sum_range_add]
  have h2 : ∑ x ∈ Finset.range (4 + s), (if cell 107 (8 + 2 * s) (-((4 + s + 1 + x : ℕ) : ℤ)) 0 then
      (10 : ℚ) ^ (4 + s + 1 + x) else 0) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [hc, if_neg]
    rw [decide_eq_true_eq, E_axis _ (by omega)]
    push_cast; omega
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.1 hm
  rw [hc]
  simp only [decide_eq_true_eq]
  exact ite_iff (by rw [E_axis _ (by omega)]; omega) _

/-- Odd digits that are OFF at stage `2r+1`. -/
def Sodd (r : ℕ) : ℚ := ∑ m ∈ Finset.range (2 * r + 2),
  if (m : ℤ) ≤ (r : ℤ) + 1 ∧ (m : ℤ) ≠ r ∧ m % 2 = 1 ∧ m ≠ 1 then (10 : ℚ) ^ m else 0

theorem a_odd (r : ℕ) (hr : 4 ≤ r) : (a (2 * r + 1) : ℚ) = (10 ^ (2 * r + 2) - 1) / 9 - Sodd r := by
  obtain ⟨s, rfl⟩ : ∃ s, r = 4 + s := ⟨r - 4, by omega⟩
  rw [a_refl, show 2 * (4 + s) + 1 = 9 + 2 * s by ring]
  have hc := (closed_all s).2
  rw [← R_closed, Sodd, show 2 * (4 + s) + 2 = 9 + 2 * s + 1 by ring, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.1 hm
  rw [hc]
  simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not]
  have key : F (4 + (s : ℤ)) (-(m : ℤ)) 0 ↔
      ((m : ℤ) ≤ ((4 + s : ℕ) : ℤ) + 1 ∧ (m : ℤ) ≠ ((4 + s : ℕ) : ℤ) ∧ m % 2 = 1 ∧ m ≠ 1) := by
    rw [F_axis _ (by omega)]; rfl
  by_cases hF : F (4 + (s : ℤ)) (-(m : ℤ)) 0
  · rw [if_neg (not_not.2 hF), if_pos (key.1 hF)]; ring
  · rw [if_pos hF, if_neg (fun h => hF (key.2 h))]; ring

theorem Sodd_even (q : ℕ) : Sodd (2 * q) = To (q + 1) := by
  rw [Sodd, To, show 2 * (2 * q) + 2 = 2 * (q + 1) + 2 * q by ring, Finset.sum_range_add]
  have h2 : ∑ x ∈ Finset.range (2 * q), (if ((2 * (q + 1) + x : ℕ) : ℤ) ≤ ((2 * q : ℕ) : ℤ) + 1 ∧
      ((2 * (q + 1) + x : ℕ) : ℤ) ≠ ((2 * q : ℕ) : ℤ) ∧ (2 * (q + 1) + x) % 2 = 1 ∧
      2 * (q + 1) + x ≠ 1 then (10 : ℚ) ^ (2 * (q + 1) + x) else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => if_neg (by push_cast; omega)
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.1 hm
  exact ite_iff (by push_cast; omega) _

theorem Sodd_odd (q : ℕ) : Sodd (2 * q + 1) = To q := by
  rw [Sodd, To, show 2 * (2 * q + 1) + 2 = 2 * q + (2 * q + 4) by ring, Finset.sum_range_add]
  have h2 : ∑ x ∈ Finset.range (2 * q + 4), (if ((2 * q + x : ℕ) : ℤ) ≤ ((2 * q + 1 : ℕ) : ℤ) + 1 ∧
      ((2 * q + x : ℕ) : ℤ) ≠ ((2 * q + 1 : ℕ) : ℤ) ∧ (2 * q + x) % 2 = 1 ∧
      2 * q + x ≠ 1 then (10 : ℚ) ^ (2 * q + x) else 0) = 0 :=
    Finset.sum_eq_zero fun x _ => if_neg (by push_cast; omega)
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.1 hm
  exact ite_iff (by push_cast; omega) _

theorem a4 (q : ℕ) (hq : 2 ≤ q) : (a (4 * q) : ℚ) = 100 * (100 ^ q - 1) / 99 := by
  rw [show 4 * q = 2 * (2 * q) by ring, a_even _ (by omega), (Se_closed q).1]

theorem a4_2 (q : ℕ) (hq : 2 ≤ q) : (a (4 * q + 2) : ℚ) = 100 * (100 ^ q - 1) / 99 := by
  rw [show 4 * q + 2 = 2 * (2 * q + 1) by ring, a_even _ (by omega), (Se_closed q).2]

theorem a4_1 (q : ℕ) (hq : 2 ≤ q) :
    (a (4 * q + 1) : ℚ) = (10 ^ (4 * q + 2) - 1) / 9 - (10 * 100 ^ (q + 1) - 1000) / 99 := by
  rw [show 4 * q + 1 = 2 * (2 * q) + 1 by ring, a_odd _ (by omega), Sodd_even, To_closed _ (by omega),
    show 2 * (2 * q) + 2 = 4 * q + 2 by ring]

theorem a4_3 (q : ℕ) (hq : 2 ≤ q) :
    (a (4 * q + 3) : ℚ) = (10 ^ (4 * q + 4) - 1) / 9 - (10 * 100 ^ q - 1000) / 99 := by
  rw [show 4 * q + 3 = 2 * (2 * q + 1) + 1 by ring, a_odd _ (by omega), Sodd_odd, To_closed _ (by omega),
    show 2 * (2 * q + 1) + 2 = 4 * q + 4 by ring]

theorem recur (n : ℕ) (hn : 16 ≤ n) :
    (a n : ℚ) = 101 * a (n - 2) - 10100 * a (n - 6) + 10000 * a (n - 8) := by
  obtain ⟨p, s, hs, hp, rfl⟩ : ∃ p s, s < 4 ∧ 2 ≤ p ∧ n = 4 * (p + 2) + s :=
    ⟨(n - 8) / 4, (n - 8) % 4, by omega, by omega, by omega⟩
  interval_cases s
  · rw [show 4 * (p + 2) + 0 - 2 = 4 * (p + 1) + 2 by omega, show 4 * (p + 2) + 0 - 6 = 4 * p + 2 by omega,
      show 4 * (p + 2) + 0 - 8 = 4 * p by omega, Nat.add_zero,
      a4 _ (by omega), a4_2 _ (by omega), a4_2 _ hp, a4 _ hp]
    ring
  · rw [show 4 * (p + 2) + 1 - 2 = 4 * (p + 1) + 3 by omega, show 4 * (p + 2) + 1 - 6 = 4 * p + 3 by omega,
      show 4 * (p + 2) + 1 - 8 = 4 * p + 1 by omega,
      a4_1 _ (by omega), a4_3 _ (by omega), a4_3 _ hp, a4_1 _ hp]
    ring
  · rw [show 4 * (p + 2) + 2 - 2 = 4 * (p + 2) by omega, show 4 * (p + 2) + 2 - 6 = 4 * (p + 1) by omega,
      show 4 * (p + 2) + 2 - 8 = 4 * p + 2 by omega,
      a4_2 _ (by omega), a4 _ (by omega), a4 _ (by omega), a4_2 _ hp]
    ring
  · rw [show 4 * (p + 2) + 3 - 2 = 4 * (p + 2) + 1 by omega, show 4 * (p + 2) + 3 - 6 = 4 * (p + 1) + 1 by omega,
      show 4 * (p + 2) + 3 - 8 = 4 * p + 3 by omega,
      a4_3 _ (by omega), a4_1 _ (by omega), a4_1 _ (by omega), a4_3 _ hp]
    ring

theorem a_tab (n : ℕ) (hn : n ≤ 8) :
    a n = ∑ k ∈ Finset.range (n + 1), if G n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0 := by
  unfold a
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [table n hn]

theorem a_small : a 0 = 1 ∧ a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 1111 ∧ a 4 = 100 ∧ a 5 = 110111 ∧ a 6 = 0 ∧
    a 7 = 11110111 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [a_tab _ (by norm_num)]; decide +kernel)

theorem a_mid : (a 8 : ℚ) = 10100 ∧ (a 9 : ℚ) = 1111010111 ∧ (a 10 : ℚ) = 10100 ∧
    (a 11 : ℚ) = 111111110111 ∧ (a 12 : ℚ) = 1010100 ∧ (a 13 : ℚ) = 11111101010111 ∧
    (a 14 : ℚ) = 1010100 ∧ (a 15 : ℚ) = 1111111111010111 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 8 = 4 * 2 by rfl, a4 2 le_rfl]; norm_num
  · rw [show 9 = 4 * 2 + 1 by rfl, a4_1 2 le_rfl]; norm_num
  · rw [show 10 = 4 * 2 + 2 by rfl, a4_2 2 le_rfl]; norm_num
  · rw [show 11 = 4 * 2 + 3 by rfl, a4_3 2 le_rfl]; norm_num
  · rw [show 12 = 4 * 3 by rfl, a4 3 (by norm_num)]; norm_num
  · rw [show 13 = 4 * 3 + 1 by rfl, a4_1 3 (by norm_num)]; norm_num
  · rw [show 14 = 4 * 3 + 2 by rfl, a4_2 3 (by norm_num)]; norm_num
  · rw [show 15 = 4 * 3 + 3 by rfl, a4_3 3 (by norm_num)]; norm_num

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) *
    (1 - 10 * X ^ 2) * (1 + 10 * X ^ 2) : PowerSeries ℚ) = 1 + X - 100 * X ^ 2 + 1010 * X ^ 3 - X ^ 4 -
    2100 * X ^ 5 - 1000 * X ^ 7 + 10200 * X ^ 8 + 100000 * X ^ 9 - 10000 * X ^ 10 + 100000 * X ^ 11 -
    1010000 * X ^ 12 - 10100000 * X ^ 13 + 1000000 * X ^ 14 + 10000000 * X ^ 15 := by
  have hD : ((1 - X) * (1 + X) * (1 - 10 * X) * (1 + 10 * X) * (1 - 10 * X ^ 2) * (1 + 10 * X ^ 2) :
      PowerSeries ℚ) = 1 - C 101 * X ^ 2 + C 10100 * X ^ 6 - C 10000 * X ^ 8 := by
    simp only [map_ofNat]; ring
  have hN : (1 + X - 100 * X ^ 2 + 1010 * X ^ 3 - X ^ 4 - 2100 * X ^ 5 - 1000 * X ^ 7 + 10200 * X ^ 8 +
      100000 * X ^ 9 - 10000 * X ^ 10 + 100000 * X ^ 11 - 1010000 * X ^ 12 - 10100000 * X ^ 13 +
      1000000 * X ^ 14 + 10000000 * X ^ 15 : PowerSeries ℚ) = 1 + X ^ 1 - C 100 * X ^ 2 + C 1010 * X ^ 3 -
      X ^ 4 - C 2100 * X ^ 5 - C 1000 * X ^ 7 + C 10200 * X ^ 8 + C 100000 * X ^ 9 - C 10000 * X ^ 10 +
      C 100000 * X ^ 11 - C 1010000 * X ^ 12 - C 10100000 * X ^ 13 + C 1000000 * X ^ 14 +
      C 10000000 * X ^ 15 := by
    simp only [map_ofNat, pow_one]
  rw [hD, hN]
  ext n
  simp only [map_sub, map_add, coeff_C_mul_X_pow, coeff_one, coeff_X_pow]
  simp only [mul_sub, mul_add, mul_one, map_sub, map_add, mul_left_comm (mk _) (C _),
    coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := a_small
  obtain ⟨h8, h9, h10, h11, h12, h13, h14, h15⟩ := a_mid
  rcases Nat.lt_or_ge n 16 with h | h
  · interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] <;>
      norm_num
  · have := recur n h
    simp only [show 2 ≤ n by omega, show 6 ≤ n by omega, show 8 ≤ n by omega, ↓reduceIte,
      show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
      show n ≠ 9 by omega, show n ≠ 10 by omega, show n ≠ 11 by omega, show n ≠ 12 by omega,
      show n ≠ 13 by omega, show n ≠ 14 by omega, show n ≠ 15 by omega]
    linarith

end A278898P

theorem OMA.solution : type_of% @OMA.S_oeis_a278898.main :=
  ⟨fun n hn => A278898P.recur n hn, A278898P.gf⟩
