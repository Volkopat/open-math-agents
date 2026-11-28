import OMAStatements.S_oeis_a225034

/-! Proof. Counting by first letter: `N` (all valid words) and `T` (those starting with `1`)
satisfy local recurrences. With `W n k = ∑_{z≤k} N (n+1) z` (the coefficient of `y^k` in
`(1-y+y²)^n/(1-y)^(n+3)`), `a (n+1) = W n (n+1)`. `W` satisfies a first-order relation in `n` and a
holonomic relation in `k` (proved by induction); the recurrence is a fixed combination of these. -/

namespace OMA.S_oeis_a225034

def V (n z : ℕ) : Set (List Bool) :=
  {w | w.count true = n ∧ w.count false = z ∧ ¬ [true, false, true] <:+: w}

def Tset (n z : ℕ) : Set (List Bool) := {w | w ∈ V n z ∧ w.head? = some true}

noncomputable def N (n z : ℕ) : ℕ := (V n z).ncard
noncomputable def T (n z : ℕ) : ℕ := (Tset n z).ncard

lemma len_eq (w : List Bool) : w.length = w.count true + w.count false := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [List.length_cons, ih]; cases b <;> simp <;> omega

lemma V_fin (n z : ℕ) : (V n z).Finite :=
  (List.finite_length_eq Bool (n + z)).subset (fun w hw => by
    simp only [Set.mem_ofPred_eq]; rw [len_eq, hw.1, hw.2.1])

lemma T_fin (n z : ℕ) : (Tset n z).Finite := (V_fin n z).subset (fun w hw => hw.1)

lemma inf_false (w : List Bool) :
    [true, false, true] <:+: (false :: w) ↔ [true, false, true] <:+: w := by
  rw [List.infix_cons_iff]; simp

lemma inf_true (w : List Bool) :
    [true, false, true] <:+: (true :: w) ↔ ([false, true] <+: w ∨ [true, false, true] <:+: w) := by
  rw [List.infix_cons_iff, List.cons_prefix_cons]; simp

lemma cons_inj (b : Bool) : Function.Injective (List.cons b) := fun _ _ h => List.cons_injective h

-- FA
lemma V_succ (n z : ℕ) : V n (z+1) = Tset n (z+1) ∪ (List.cons false) '' V n z := by
  ext w
  simp only [Tset, V, Set.mem_union, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rcases w with _ | ⟨b, w⟩
    · simp at h2
    · cases b
      · right; refine ⟨w, ⟨?_, ?_, ?_⟩, rfl⟩
        · simpa [List.count_cons] using h1
        · simpa [List.count_cons] using h2
        · exact fun h => h3 ((inf_false w).2 h)
      · left; exact ⟨⟨h1, h2, h3⟩, rfl⟩
  · rintro (⟨h, -⟩ | ⟨w', ⟨h1, h2, h3⟩, rfl⟩)
    · exact h
    · refine ⟨?_, ?_, ?_⟩
      · simpa [List.count_cons] using h1
      · simp [List.count_cons, h2]
      · rw [inf_false]; exact h3

lemma FA (n z : ℕ) : N n (z+1) = N n z + T n (z+1) := by
  unfold N T
  rw [V_succ, Set.ncard_union_eq _ (T_fin _ _) ((V_fin _ _).image _),
    Set.ncard_image_of_injective _ (cons_inj false)]
  · ring
  · rw [Set.disjoint_left]
    rintro w ⟨-, hw⟩ ⟨w', -, rfl⟩
    simp at hw

lemma FA0 (n : ℕ) : N (n+1) 0 = T (n+1) 0 := by
  unfold N T
  congr 1
  ext w
  simp only [Tset, Set.mem_ofPred_eq, iff_self_and]
  rintro ⟨h1, h2, -⟩
  rcases w with _ | ⟨b, w⟩
  · simp at h1
  · cases b
    · simp [List.count_cons] at h2
    · rfl

lemma T_zero (z : ℕ) : T 0 z = 0 := by
  unfold T
  rw [Set.ncard_eq_zero (T_fin _ _)]
  ext w
  simp only [Tset, V, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨h1, -, -⟩, h⟩
  rcases w with _ | ⟨b, w⟩
  · simp at h
  · simp at h; subst h; simp [List.count_cons] at h1

lemma N_zero (z : ℕ) : N 0 z = 1 := by
  induction z with
  | zero =>
    unfold N
    rw [Set.ncard_eq_one]
    refine ⟨[], ?_⟩
    ext w
    simp only [V, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, -⟩
      have := len_eq w
      rw [h1, h2] at this
      exact List.eq_nil_of_length_eq_zero this
    · rintro rfl; simp
  | succ z ih => rw [FA, ih, T_zero]

-- Tset (n+1) z = cons true '' {w ∈ V n z | ¬ [false,true] <+: w}
lemma T_succ (n z : ℕ) :
    Tset (n+1) z = (List.cons true) '' {w | w ∈ V n z ∧ ¬ [false, true] <+: w} := by
  ext w
  simp only [Tset, V, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    rcases w with _ | ⟨b, w⟩
    · simp at h4
    · simp at h4; subst h4
      rw [inf_true] at h3
      refine ⟨w, ⟨⟨?_, ?_, fun h => h3 (Or.inr h)⟩, fun h => h3 (Or.inl h)⟩, rfl⟩
      · simpa [List.count_cons] using h1
      · simpa [List.count_cons] using h2
  · rintro ⟨w', ⟨⟨h1, h2, h3⟩, h4⟩, rfl⟩
    refine ⟨⟨?_, ?_, ?_⟩, rfl⟩
    · simp [List.count_cons, h1]
    · simpa [List.count_cons] using h2
    · rw [inf_true]; rintro (h | h)
      · exact h4 h
      · exact h3 h

lemma P_succ (n z : ℕ) :
    {w | w ∈ V n (z+1) ∧ [false, true] <+: w} = (List.cons false) '' Tset n z := by
  ext w
  simp only [Tset, V, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨⟨h1, h2, h3⟩, h4⟩
    rcases w with _ | ⟨b, w⟩
    · simp at h4
    · rw [List.cons_prefix_cons] at h4
      obtain ⟨rfl, h4⟩ := h4
      refine ⟨w, ⟨⟨?_, ?_, fun h => h3 ((inf_false w).2 h)⟩, ?_⟩, rfl⟩
      · simpa [List.count_cons] using h1
      · simpa [List.count_cons] using h2
      · rcases w with _ | ⟨c, w⟩
        · simp at h4
        · rw [List.cons_prefix_cons] at h4; rw [h4.1]; rfl
  · rintro ⟨w', ⟨⟨h1, h2, h3⟩, h4⟩, rfl⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · simpa [List.count_cons] using h1
    · simp [List.count_cons, h2]
    · rw [inf_false]; exact h3
    · rcases w' with _ | ⟨c, w'⟩
      · simp at h4
      · simp at h4; subst h4; simp

lemma P_zero (n : ℕ) : {w | w ∈ V n 0 ∧ [false, true] <+: w} = ∅ := by
  ext w
  simp only [V, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨⟨-, h2, -⟩, h4⟩
  rcases w with _ | ⟨b, w⟩
  · simp at h4
  · rw [List.cons_prefix_cons] at h4
    obtain ⟨rfl, -⟩ := h4
    simp [List.count_cons] at h2

lemma split_card (n z : ℕ) :
    ({w | w ∈ V n z ∧ ¬ [false, true] <+: w}).ncard + ({w | w ∈ V n z ∧ [false, true] <+: w}).ncard
      = N n z := by
  unfold N
  have : {w | w ∈ V n z ∧ ¬ [false, true] <+: w} = V n z \ {w | w ∈ V n z ∧ [false, true] <+: w} := by
    ext w; simp only [Set.mem_ofPred_eq, Set.mem_sdiff]; tauto
  rw [this]
  exact Set.ncard_sdiff_add_ncard_of_subset (fun w hw => hw.1) (V_fin n z)

lemma FB (n z : ℕ) : T (n+1) (z+1) + T n z = N n (z+1) := by
  rw [← split_card, P_succ, Set.ncard_image_of_injective _ (cons_inj false)]
  unfold T
  rw [T_succ, Set.ncard_image_of_injective _ (cons_inj true)]

lemma FB0 (n : ℕ) : T (n+1) 0 = N n 0 := by
  rw [← split_card, P_zero, Set.ncard_empty, add_zero]
  unfold T
  rw [T_succ, Set.ncard_image_of_injective _ (cons_inj true)]


noncomputable def Sn (n k : ℕ) : ℕ := ∑ z ∈ Finset.range (k+1), N (n+1) z

noncomputable def W (n : ℕ) (k : ℤ) : ℤ := if k < 0 then 0 else (Sn n k.toNat : ℤ)

lemma W_nat (n j : ℕ) : W n j = Sn n j := by simp [W]

lemma W_neg (n : ℕ) (k : ℤ) (h : k < 0) : W n k = 0 := by simp [W, h]

lemma Sn_succ (n j : ℕ) : Sn n (j+1) = Sn n j + N (n+1) (j+1) := by
  simp [Sn, Finset.sum_range_succ]

lemma Sn_zero (n : ℕ) : Sn n 0 = N (n+1) 0 := by simp [Sn]

lemma N_one (z : ℕ) : N 1 z = z + 1 := by
  induction z with
  | zero => rw [FA0 0, FB0 0, N_zero]
  | succ z ih =>
    have h : T 1 (z+1) + T 0 z = N 0 (z+1) := FB 0 z
    rw [T_zero, N_zero] at h
    rw [FA, ih]; omega

lemma W0 (k : ℤ) (hk : -2 ≤ k) : 2 * W 0 k = (k+1)*(k+2) := by
  rcases lt_or_ge k 0 with h | h
  · rw [W_neg _ _ h]
    have : k = -1 ∨ k = -2 := by omega
    rcases this with rfl | rfl <;> norm_num
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j := ⟨k.toNat, by omega⟩
    rw [W_nat]
    induction j with
    | zero => simp [Sn_zero, N_one]
    | succ j ih =>
      rw [Sn_succ, N_one]; push_cast
      have := ih (by omega) (by omega)
      linear_combination this

lemma KN0 (n : ℕ) : N (n+2) 0 = Sn n 0 := by
  rw [Sn_zero, show N (n+2) 0 = T (n+2) 0 from FA0 (n+1), show T (n+2) 0 = N (n+1) 0 from FB0 (n+1)]

lemma KN (n j : ℕ) : N (n+2) (j+1) + N (n+1) j = Sn n (j+1) := by
  induction j with
  | zero =>
    have h1 : T (n+2) 1 + T (n+1) 0 = N (n+1) 1 := FB (n+1) 0
    have h2 : N (n+2) 1 = N (n+2) 0 + T (n+2) 1 := FA (n+2) 0
    have h3 := KN0 n
    have h4 : N (n+1) 0 = T (n+1) 0 := FA0 n
    have h5 := Sn_succ n 0
    simp only [Nat.zero_add] at *
    omega
  | succ j ih =>
    have h1 : T (n+2) (j+2) + T (n+1) (j+1) = N (n+1) (j+2) := FB (n+1) (j+1)
    have h2 : N (n+2) (j+2) = N (n+2) (j+1) + T (n+2) (j+2) := FA (n+2) (j+1)
    have h4 : N (n+1) (j+1) = N (n+1) j + T (n+1) (j+1) := FA (n+1) j
    have h5 : Sn n (j+2) = Sn n (j+1) + N (n+1) (j+2) := Sn_succ n (j+1)
    show N (n+2) (j+2) + N (n+1) (j+1) = Sn n (j+2)
    omega

lemma D_rel (n : ℕ) (k : ℤ) :
    W (n+1) k - W (n+1) (k-1) = W n k - W n (k-1) + W n (k-2) := by
  rcases lt_or_ge k 0 with h | h
  · rw [W_neg _ _ h, W_neg _ _ (by omega), W_neg _ _ h, W_neg _ _ (by omega), W_neg _ _ (by omega)]
    ring
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j := ⟨k.toNat, by omega⟩
  rcases j with _ | _ | i
  · rw [W_neg (n+1) (((0:ℕ):ℤ)-1) (by norm_num), W_neg n (((0:ℕ):ℤ)-1) (by norm_num),
      W_neg n (((0:ℕ):ℤ)-2) (by norm_num), W_nat, W_nat]
    have h1 : Sn (n+1) 0 = N (n+2) 0 := Sn_zero (n+1)
    have h2 := KN0 n
    rw [h1, h2]; ring
  · rw [W_neg n (((0+1:ℕ):ℤ)-2) (by norm_num), show ((0+1 : ℕ) : ℤ) - 1 = ((0:ℕ):ℤ) by norm_num,
      W_nat, W_nat, W_nat, W_nat]
    have h1 : Sn (n+1) (0+1) = Sn (n+1) 0 + N (n+2) 1 := Sn_succ (n+1) 0
    have h2 := KN n 0
    have h3 := Sn_succ n 0
    have h4 := Sn_zero n
    rw [h1]; push_cast; simp only [Nat.zero_add] at *; omega
  · rw [show ((i+1+1 : ℕ) : ℤ) - 1 = ((i+1 : ℕ) : ℤ) by push_cast; ring,
      show ((i+1+1 : ℕ) : ℤ) - 2 = ((i : ℕ) : ℤ) by push_cast; ring, W_nat, W_nat, W_nat, W_nat, W_nat]
    have h1 : Sn (n+1) (i+1+1) = Sn (n+1) (i+1) + N (n+2) (i+2) := Sn_succ (n+1) (i+1)
    have h2 : N (n+2) (i+2) + N (n+1) (i+1) = Sn n (i+2) := KN n (i+1)
    have h3 : Sn n (i+1+1) = Sn n (i+1) + N (n+1) (i+2) := Sn_succ n (i+1)
    have h4 : Sn n (i+1) = Sn n i + N (n+1) (i+1) := Sn_succ n i
    rw [h1]; push_cast; simp only [show i + 1 + 1 = i + 2 from rfl] at *; omega

noncomputable def Rel (n : ℕ) (k : ℤ) : ℤ :=
  (k+1) * W n (k+1) - 2*k * W n k + 2*(k-1) * W n (k-1) - (k-2) * W n (k-2) - 3 * W n k
    - (2*(n:ℤ)-3) * W n (k-1) - (3-(n:ℤ)) * W n (k-2)

lemma Rel_low (n : ℕ) (k : ℤ) (hk : k ≤ -2) : Rel n k = 0 := by
  unfold Rel
  rw [W_neg _ _ (by omega), W_neg _ _ (by omega), W_neg _ _ (by omega), W_neg _ _ (by omega)]
  ring

lemma Rel_base (k : ℤ) : Rel 0 k = 0 := by
  rcases lt_or_ge k 0 with h | h
  · rcases lt_or_ge k (-1) with h' | h'
    · exact Rel_low _ _ (by omega)
    · have : k = -1 := by omega
      subst this; unfold Rel
      rw [W_neg 0 (-1) (by norm_num), W_neg 0 (-1-1) (by norm_num), W_neg 0 (-1-2) (by norm_num)]; ring
  · have h1 := W0 (k+1) (by omega)
    have h2 := W0 k (by omega)
    have h3 := W0 (k-1) (by omega)
    have h4 := W0 (k-2) (by omega)
    have : 2 * Rel 0 k = 0 := by
      unfold Rel
      push_cast
      linear_combination (k+1) * h1 - (2*k+3) * h2 + (2*k+1) * h3 - (k+1) * h4
    omega

lemma Rel_zero : ∀ n k, Rel n k = 0
  | 0, k => Rel_base k
  | n+1, k => by
    have step : ∀ k : ℤ, Rel (n+1) k = Rel (n+1) (k-1) := by
      intro k
      have d1 := D_rel n (k-2)
      have d2 := D_rel n (k-1)
      have d3 := D_rel n k
      have d4 := D_rel n (k+1)
      have r1 := Rel_zero n (k-2)
      have r2 := Rel_zero n (k-1)
      have r3 := Rel_zero n k
      unfold Rel at *
      push_cast at *
      ring_nf at *
      linear_combination (↑n+1-k) * d1 + (2*k-2*↑n-2) * d2 + (-2*k-2) * d3 + (k+1) * d4
        + r1 - r2 + r3
    rcases le_or_gt k (-2) with h | h
    · exact Rel_low _ _ h
    · induction k, (show (-2:ℤ) ≤ k by omega) using Int.le_induction with
      | base => exact Rel_low _ _ le_rfl
      | succ k hk ih =>
        rw [step, show k + 1 - 1 = k by ring]
        rcases eq_or_lt_of_le hk with h' | h'
        · rw [← h']; exact Rel_low _ _ le_rfl
        · exact ih (by omega)

lemma fin_rec (m : ℕ) (hm : 1 ≤ m) :
    ((m:ℤ)+4) * W (m+2) ((m:ℤ)+3) - (2*(m:ℤ)+9) * W (m+1) ((m:ℤ)+2) - 3*((m:ℤ)+1) * W m ((m:ℤ)+1) = 0 := by
  have hD : ((m:ℤ)*((m:ℤ)+1)*((m:ℤ)+2)*((m:ℤ)+3)) ≠ 0 := by positivity
  apply (mul_eq_zero.mp _).resolve_left hD
  have h0 := Rel_zero (m) ((m:ℤ)+(-3))
  have h1 := Rel_zero (m) ((m:ℤ)+(-2))
  have h2 := Rel_zero (m) ((m:ℤ)+(-1))
  have h3 := Rel_zero (m) ((m:ℤ)+(0))
  have h8 := Rel_zero (m+1) ((m:ℤ)+(-3))
  have h9 := Rel_zero (m+1) ((m:ℤ)+(-2))
  have h10 := Rel_zero (m+1) ((m:ℤ)+(-1))
  have h11 := Rel_zero (m+1) ((m:ℤ)+(0))
  have h12 := Rel_zero (m+1) ((m:ℤ)+(1))
  have h17 := Rel_zero (m+2) ((m:ℤ)+(-2))
  have h18 := Rel_zero (m+2) ((m:ℤ)+(-1))
  have h19 := Rel_zero (m+2) ((m:ℤ)+(0))
  have h20 := Rel_zero (m+2) ((m:ℤ)+(1))
  have h21 := Rel_zero (m+2) ((m:ℤ)+(2))
  have h24 := D_rel (m) ((m:ℤ)+(-3))
  have h25 := D_rel (m) ((m:ℤ)+(-2))
  have h26 := D_rel (m) ((m:ℤ)+(-1))
  have h32 := D_rel (m+1) ((m:ℤ)+(-3))
  have h33 := D_rel (m+1) ((m:ℤ)+(-2))
  have h34 := D_rel (m+1) ((m:ℤ)+(-1))
  unfold Rel at *
  push_cast at *
  ring_nf at *
  linear_combination (-8*(m:ℤ)^4 - 57*(m:ℤ)^3 - 142*(m:ℤ)^2 - 147*(m:ℤ) - 54) * h0 + (4*(m:ℤ)^4 + 33*(m:ℤ)^3 + 98*(m:ℤ)^2 + 123*(m:ℤ) + 54) * h1 + (-6*(m:ℤ)^4 - 45*(m:ℤ)^3 - 120*(m:ℤ)^2 - 135*(m:ℤ) - 54) * h2 + (-3*(m:ℤ)^4 - 18*(m:ℤ)^3 - 33*(m:ℤ)^2 - 18*(m:ℤ)) * h3 + (-16*(m:ℤ)^4 - 162*(m:ℤ)^3 - 584*(m:ℤ)^2 - 870*(m:ℤ) - 432) * h8 + (36*(m:ℤ)^3 + 249*(m:ℤ)^2 + 549*(m:ℤ) + 378) * h9 + (-8*(m:ℤ)^4 - 90*(m:ℤ)^3 - 361*(m:ℤ)^2 - 615*(m:ℤ) - 378) * h10 + (-4*(m:ℤ)^4 - 40*(m:ℤ)^3 - 129*(m:ℤ)^2 - 135*(m:ℤ)) * h11 + (-2*(m:ℤ)^4 - 17*(m:ℤ)^3 - 42*(m:ℤ)^2 - 27*(m:ℤ)) * h12 + (-16*(m:ℤ)^4 - 162*(m:ℤ)^3 - 584*(m:ℤ)^2 - 870*(m:ℤ) - 432) * h17 + (8*(m:ℤ)^4 + 93*(m:ℤ)^3 + 391*(m:ℤ)^2 + 696*(m:ℤ) + 432) * h18 + (4*(m:ℤ)^4 + 39*(m:ℤ)^3 + 125*(m:ℤ)^2 + 132*(m:ℤ)) * h19 + (2*(m:ℤ)^4 + 17*(m:ℤ)^3 + 43*(m:ℤ)^2 + 28*(m:ℤ)) * h20 + ((m:ℤ)^4 + 7*(m:ℤ)^3 + 14*(m:ℤ)^2 + 8*(m:ℤ)) * h21 + (-16*(m:ℤ)^4 - 114*(m:ℤ)^3 - 284*(m:ℤ)^2 - 294*(m:ℤ) - 108) * h24 + (28*(m:ℤ)^4 + 204*(m:ℤ)^3 + 524*(m:ℤ)^2 + 564*(m:ℤ) + 216) * h25 + (16*(m:ℤ)^5 + 122*(m:ℤ)^4 + 332*(m:ℤ)^3 + 382*(m:ℤ)^2 + 156*(m:ℤ)) * h26 + (-48*(m:ℤ)^4 - 486*(m:ℤ)^3 - 1752*(m:ℤ)^2 - 2610*(m:ℤ) - 1296) * h32 + (80*(m:ℤ)^4 + 834*(m:ℤ)^3 + 3118*(m:ℤ)^2 + 4872*(m:ℤ) + 2592) * h33 + (32*(m:ℤ)^5 + 352*(m:ℤ)^4 + 1414*(m:ℤ)^3 + 2444*(m:ℤ)^2 + 1518*(m:ℤ)) * h34


lemma a_eq (m : ℕ) : (a (m+1) : ℤ) = W m ((m:ℤ)+1) := by
  rw [show ((m:ℤ)+1) = ((m+1 : ℕ) : ℤ) by push_cast; ring, W_nat]
  unfold a Sn
  push_cast
  rfl

lemma W00 : W 0 0 = 1 := by have := W0 0 (by norm_num); omega
lemma W01 : W 0 1 = 3 := by have := W0 1 (by norm_num); omega
lemma W02 : W 0 2 = 6 := by have := W0 2 (by norm_num); omega
lemma W03 : W 0 3 = 10 := by have := W0 3 (by norm_num); omega

theorem solution_main :
    ∀ n : ℕ, 2 ≤ n →
      ((n : ℤ) + 1) * a n - (2 * n + 3) * a (n - 1) - 3 * ((n : ℤ) - 2) * a (n - 2) = 0 := by
  intro n hn
  have hneg : ∀ j : ℕ, ∀ k : ℤ, k < 0 → W j k = 0 := fun j k h => W_neg j k h
  have d0 := fun k => D_rel 0 k
  have d1 := fun k => D_rel 1 k
  have w0m1 := hneg 0 (-1) (by norm_num)
  have w0m2 := hneg 0 (-2) (by norm_num)
  have w1m1 := hneg 1 (-1) (by norm_num)
  have w1m2 := hneg 1 (-2) (by norm_num)
  have w2m1 := hneg 2 (-1) (by norm_num)
  have e10 := d0 0
  have e11 := d0 1
  have e12 := d0 2
  have e13 := d0 3
  have e20 := d1 0
  have e21 := d1 1
  have e22 := d1 2
  have e23 := d1 3
  norm_num at e10 e11 e12 e13 e20 e21 e22 e23
  have v := W00; have v1 := W01; have v2 := W02; have v3 := W03
  rcases (show n = 2 ∨ n = 3 ∨ 4 ≤ n by omega) with rfl | rfl | h4
  · have a2 := a_eq 1
    have a1 := a_eq 0
    norm_num at a2 a1 ⊢
    rw [a2, a1]
    linarith
  · have a3 := a_eq 2
    have a2 := a_eq 1
    have a1 := a_eq 0
    norm_num at a3 a2 a1 ⊢
    rw [a3, a2, a1]
    linarith
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 2 + 1 by omega, show m + 4 - 2 = m + 1 + 1 by omega,
      show m + 4 = m + 3 + 1 by omega, a_eq, a_eq, a_eq]
    have := fin_rec (m+1) (by omega)
    push_cast at this ⊢
    ring_nf at this ⊢
    linear_combination this

end OMA.S_oeis_a225034

theorem OMA.solution : type_of% @OMA.S_oeis_a225034.main := OMA.S_oeis_a225034.solution_main
