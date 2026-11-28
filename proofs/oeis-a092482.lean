import OMAStatements.S_oeis_a092482

open Finset

namespace OMA.P_a092482

/-- all base-3 digits are at most 1 -/
def D (x : ℕ) : Prop := ∀ i, x / 3 ^ i % 3 ≤ 1

lemma D_zero : D 0 := fun i => by simp

lemma D_step {r q : ℕ} (hr : r < 3) : D (r + 3 * q) ↔ r ≤ 1 ∧ D q := by
  have h0 : (r + 3 * q) / 3 ^ 0 % 3 = r := by rw [pow_zero, Nat.div_one]; omega
  have hs : ∀ i, (r + 3 * q) / 3 ^ (i + 1) = q / 3 ^ i := by
    intro i
    rw [pow_succ', ← Nat.div_div_eq_div_mul]
    congr 1
    omega
  constructor
  · intro h
    refine ⟨?_, fun i => ?_⟩
    · have := h 0
      rwa [h0] at this
    · have := h (i + 1)
      rwa [hs] at this
  · rintro ⟨h1, h2⟩ i
    cases i with
    | zero => rw [h0]; exact h1
    | succ i => rw [hs]; exact h2 i

lemma D_iff (x : ℕ) : D x ↔ x % 3 ≤ 1 ∧ D (x / 3) := by
  conv_lhs => rw [← Nat.mod_add_div x 3]
  exact D_step (Nat.mod_lt _ (by norm_num))

lemma D_ap : ∀ z x y, D x → D y → D z → x + y = 2 * z → x = z := by
  intro z
  induction z using Nat.strong_induction_on with
  | _ z ih =>
  intro x y hx hy hz h
  rcases Nat.eq_zero_or_pos z with rfl | hz0
  · omega
  rw [D_iff] at hx hy hz
  have := ih (z / 3) (by omega) (x / 3) (y / 3) hx.2 hy.2 hz.2 (by omega)
  omega

lemma compl : ∀ m v, D v → v < 3 ^ m → ∃ v', D v' ∧ 2 * (v + v') + 1 = 3 ^ m := by
  intro m
  induction m with
  | zero =>
    intro v _ hv
    obtain rfl : v = 0 := by simpa using hv
    exact ⟨0, D_zero, by simp⟩
  | succ m ih =>
    intro v hD hv
    rw [D_iff] at hD
    rw [pow_succ] at hv ⊢
    obtain ⟨q, hq, hq'⟩ := ih (v / 3) hD.2 (by omega)
    exact ⟨(1 - v % 3) + 3 * q, (D_step (by omega)).2 ⟨by omega, hq⟩, by omega⟩

lemma D_bound {m v : ℕ} (hD : D v) (hv : v < 3 ^ m) : 2 * v < 3 ^ m := by
  obtain ⟨v', -, h⟩ := compl m v hD hv
  omega

lemma D_add_pow : ∀ m v, D v → v < 3 ^ m → D (v + 3 ^ m) := by
  intro m
  induction m with
  | zero =>
    intro v _ hv
    obtain rfl : v = 0 := by simpa using hv
    exact (D_step (r := 1) (q := 0) (by norm_num)).2 ⟨le_rfl, D_zero⟩
  | succ m ih =>
    intro v hD hv
    rw [D_iff] at hD
    rw [pow_succ] at hv
    rw [show v + 3 ^ (m + 1) = v % 3 + 3 * (v / 3 + 3 ^ m) by rw [pow_succ]; omega,
      D_step (Nat.mod_lt _ (by norm_num))]
    exact ⟨hD.1, ih _ hD.2 (by omega)⟩

/-- the base-3 digits equal to 1 -/
def g : ℕ → ℕ
  | 0 => 0
  | w + 1 => (if (w + 1) % 3 = 1 then 1 else 0) + 3 * g ((w + 1) / 3)
decreasing_by omega

/-- the base-3 digits equal to 2, written as 1 -/
def k : ℕ → ℕ
  | 0 => 0
  | w + 1 => (if (w + 1) % 3 = 2 then 1 else 0) + 3 * k ((w + 1) / 3)
decreasing_by omega

lemma gk : ∀ w, w = g w + 2 * k w ∧ D (g w) ∧ D (k w) ∧ D (g w + k w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  rcases w with _ | w
  · simp [g, k, D_zero]
  obtain ⟨h1, h2, h3, h4⟩ := ih ((w + 1) / 3) (by omega)
  have eg : g (w + 1) = (if (w + 1) % 3 = 1 then 1 else 0) + 3 * g ((w + 1) / 3) := by rw [g]
  have ek : k (w + 1) = (if (w + 1) % 3 = 2 then 1 else 0) + 3 * k ((w + 1) / 3) := by rw [k]
  rw [eg, ek]
  refine ⟨by split_ifs <;> omega, (D_step (by split_ifs <;> omega)).2 ⟨by split_ifs <;> omega, h2⟩,
    (D_step (by split_ifs <;> omega)).2 ⟨by split_ifs <;> omega, h3⟩, ?_⟩
  rw [show (if (w + 1) % 3 = 1 then 1 else 0) + 3 * g ((w + 1) / 3) +
      ((if (w + 1) % 3 = 2 then 1 else 0) + 3 * k ((w + 1) / 3)) =
      ((if (w + 1) % 3 = 1 then 1 else 0) + (if (w + 1) % 3 = 2 then 1 else 0)) +
        3 * (g ((w + 1) / 3) + k ((w + 1) / 3)) by ring]
  exact (D_step (by split_ifs <;> omega)).2 ⟨by split_ifs <;> omega, h4⟩

lemma k_pos {w : ℕ} (h : ¬ D w) : 0 < k w := by
  obtain ⟨h1, h2, -, -⟩ := gk w
  by_contra h0
  apply h
  rw [h1]
  convert h2 using 1
  omega

/-- start of the `m`-th block -/
def c (m : ℕ) : ℕ := 1 + 2 ^ m + 3 ^ m

/-- the conjectured set of terms -/
def P (x : ℕ) : Prop := x = 1 ∨ x = 2 ∨ ∃ m e, D e ∧ e < 3 ^ m ∧ x = c m + e

lemma c_succ (m : ℕ) : c (m + 1) + 1 = 2 * c m + 3 ^ m := by
  unfold c; rw [pow_succ, pow_succ]; ring

lemma c_mono {m m' : ℕ} (h : m ≤ m') : c m ≤ c m' := by
  unfold c
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h
  have := Nat.pow_le_pow_right (by norm_num : 0 < 3) h
  omega

lemma c_block {m m' : ℕ} (h : m < m') : c m + 3 ^ m ≤ c m' := by
  unfold c
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h.le
  have := Nat.pow_le_pow_right (by norm_num : 0 < 3) (Nat.succ_le_of_lt h)
  rw [pow_succ] at this
  omega

lemma c_two (m : ℕ) : 2 ^ m ≤ 3 ^ m ∧ 1 ≤ 2 ^ m ∧ c m = 1 + 2 ^ m + 3 ^ m :=
  ⟨Nat.pow_le_pow_left (by norm_num) m, Nat.one_le_two_pow, rfl⟩

lemma P_zero : ¬ P 0 := by
  rintro (h | h | ⟨m, e, -, -, h⟩)
  · omega
  · omega
  · have : 1 ≤ c m := by unfold c; rw [add_assoc]; exact Nat.le_add_right 1 _
    omega

lemma P_block {m e : ℕ} (he : D e) (hm : e < 3 ^ m) : P (c m + e) := Or.inr (Or.inr ⟨m, e, he, hm, rfl⟩)

lemma two_mul_le {m e : ℕ} (he : D e) (hm : e < 3 ^ m) : 2 * (c m + e) ≤ c (m + 1) := by
  have := D_bound he hm
  have := c_succ m
  omega

lemma K1 (x y z : ℕ) (hx : P x) (h4 : 4 ≤ x) (hyz : y < z) (hzx : z < x) (hy : P y) (hz : P z) :
    y + x ≠ 2 * z := by
  intro heq
  obtain hx | hx | ⟨m, e, he, hem, rfl⟩ := hx
  · omega
  · omega
  obtain ⟨h23, h1, hc⟩ := c_two m
  have heb := D_bound he hem
  obtain hz | hz | ⟨m', e', he', hem', rfl⟩ := hz
  · omega
  · subst hz
    obtain rfl : y = 0 := by omega
    exact P_zero hy
  rcases lt_trichotomy m' m with hlt | rfl | hgt
  · have h1 := two_mul_le he' hem'
    have h2 := c_mono (show m' + 1 ≤ m by omega)
    obtain rfl : y = 0 := by omega
    exact P_zero hy
  · obtain hy | hy | ⟨m'', e'', he'', hem'', rfl⟩ := hy
    · omega
    · omega
    rcases lt_trichotomy m'' m' with hlt | rfl | hgt
    · have h1 := two_mul_le he'' hem''
      have h2 := c_mono (show m'' + 1 ≤ m' by omega)
      omega
    · have := D_ap e' e'' e he'' he he' (by omega)
      omega
    · have := c_block hgt
      omega
  · have := c_block hgt
    omega

lemma loc (x : ℕ) (hx : 3 ≤ x) : ∃ m, c m ≤ x ∧ x < c (m + 1) := by
  have hex : ∃ m, x < c m := ⟨x, by
    have := Nat.lt_pow_self (by norm_num : 1 < 3) (n := x)
    have h2 : 0 < 2 ^ x := by positivity
    unfold c; omega⟩
  have hM := Nat.find_spec hex
  have hM0 : Nat.find hex ≠ 0 := by
    intro h
    rw [h] at hM
    unfold c at hM
    simp at hM
    omega
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · exact not_lt.1 (Nat.find_min hex (by omega))
  · rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hM0)]

lemma cov : ∀ m t, 1 ≤ t → t < c m →
    ∃ y v, P y ∧ y < c m ∧ D v ∧ v < 3 ^ m ∧ t = y + 2 * v := by
  intro m
  induction m with
  | zero =>
    intro t h1 h2
    have h3 : c 0 = 3 := by norm_num [c]
    refine ⟨t, 0, ?_, by omega, D_zero, by simp, by omega⟩
    rcases (by omega : t = 1 ∨ t = 2) with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | succ m ih =>
    intro t h1 h2
    have hcs := c_succ m
    obtain ⟨h23, h1', hc⟩ := c_two m
    have h3 : 3 ^ (m + 1) = 3 * 3 ^ m := by rw [pow_succ]; ring
    by_cases ha : t < c m
    · obtain ⟨y, v, hy, hyc, hv, hvl, ht⟩ := ih t h1 ha
      exact ⟨y, v, hy, by omega, hv, by omega, ht⟩
    by_cases hb : t < c m + 3 ^ m
    · obtain ⟨hw, hg, hk, -⟩ := gk (t - c m)
      exact ⟨c m + g (t - c m), k (t - c m), P_block hg (by omega), by omega, hk, by omega, by omega⟩
    by_cases hd : t < c m + 2 * 3 ^ m
    · obtain ⟨y, v, hy, hyc, hv, hvl, ht⟩ := ih (t - 2 * 3 ^ m) (by omega) (by omega)
      exact ⟨y, v + 3 ^ m, hy, by omega, D_add_pow m v hv hvl, by omega, by omega⟩
    · obtain ⟨hw, hg, hk, -⟩ := gk (t - c m - 2 * 3 ^ m)
      refine ⟨c m + g (t - c m - 2 * 3 ^ m), k (t - c m - 2 * 3 ^ m) + 3 ^ m,
        P_block hg (by omega), by omega, D_add_pow m _ hk (by omega), by omega, by omega⟩

lemma K2 (x : ℕ) (h4 : 4 ≤ x) (hP : ¬ P x) :
    ∃ y z, y < z ∧ z < x ∧ P y ∧ P z ∧ y + x = 2 * z := by
  obtain ⟨m, hm1, hm2⟩ := loc x (by omega)
  have hcs := c_succ m
  obtain ⟨h23, h1', hc⟩ := c_two m
  by_cases hw : x < c m + 3 ^ m
  · have hDw : ¬ D (x - c m) := fun h => hP (by
      have := P_block (m := m) h (by omega)
      rwa [Nat.add_sub_cancel' hm1] at this)
    have hk0 := k_pos hDw
    obtain ⟨hgk, hg, -, hgk'⟩ := gk (x - c m)
    exact ⟨c m + g (x - c m), c m + (g (x - c m) + k (x - c m)), by omega, by omega,
      P_block hg (by omega), P_block hgk' (by omega), by omega⟩
  · obtain ⟨y, v', hy, hyc, hv', hv'l, ht⟩ := cov m (c (m + 1) - x) (by omega) (by omega)
    obtain ⟨v, hv, hvv⟩ := compl m v' hv' hv'l
    exact ⟨y, c m + v, by omega, by omega, hy, P_block hv (by omega), by omega⟩

lemma isTerm_iff : ∀ x, S_oeis_a092482.IsTerm x ↔ P x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
  rw [S_oeis_a092482.IsTerm]
  by_cases hx : x ≤ 3
  · have hP3 : P 3 := by
      have h := P_block (m := 0) D_zero (by norm_num)
      have h3 : c 0 + 0 = 3 := by norm_num [c]
      rwa [h3] at h
    interval_cases x
    · simp [P_zero]
    · simp [P]
    · simp [P]
    · simp [hP3]
  · constructor
    · rintro (h | h | h | ⟨-, h⟩)
      · omega
      · omega
      · omega
      by_contra hP
      obtain ⟨y, z, hyz, hzx, hy, hz, heq⟩ := K2 x (by omega) hP
      exact h y (by omega) z hzx hyz ((ih y (by omega)).2 hy) ((ih z hzx).2 hz) heq
    · intro hP
      refine Or.inr (Or.inr (Or.inr ⟨by omega, fun y hy z hz hyz hty htz => ?_⟩))
      exact K1 x y z hP (by omega) hyz hz ((ih y hy).1 hty) ((ih z hz).1 htz)

/-- binary digits read in base 3 -/
def T : ℕ → ℕ
  | 0 => 0
  | i + 1 => (i + 1) % 2 + 3 * T ((i + 1) / 2)
decreasing_by omega

lemma T_eq (i : ℕ) : T i = i % 2 + 3 * T (i / 2) := by
  rcases i with _ | i
  · simp [T]
  · rw [T]

lemma T_lin (j r : ℕ) (hr : r < 2) : T (r + 2 * j) = r + 3 * T j := by
  rw [T_eq]
  rw [show (r + 2 * j) % 2 = r by omega, show (r + 2 * j) / 2 = j by omega]

lemma T_zero : T 0 = 0 := by simp [T]

lemma T_D : ∀ i, D (T i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [T_zero]; exact D_zero
  rw [T_eq]
  exact (D_step (by omega)).2 ⟨by omega, ih _ (by omega)⟩

lemma T_succ : ∀ n, T (n + 1) = T n + (3 ^ padicValNat 2 (n + 1) + 1) / 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · have hv : padicValNat 2 (2 * j + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    have e0 := T_lin j 0 (by norm_num)
    have e1 := T_lin j 1 (by norm_num)
    simp only [zero_add] at e0
    rw [add_comm 1 (2 * j)] at e1
    rw [hv, e1, e0, pow_zero]
    omega
  · have hj := ih j (by omega)
    have hv : padicValNat 2 (2 * j + 1 + 1) = padicValNat 2 (j + 1) + 1 := by
      rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring, padicValNat.mul (by norm_num) (by omega),
        padicValNat.self (by norm_num)]
      ring
    have e2 := T_lin (j + 1) 0 (by norm_num)
    simp only [zero_add] at e2
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring] at e2
    have e1 := T_lin j 1 (by norm_num)
    rw [add_comm 1 (2 * j)] at e1
    have hodd : 3 ^ padicValNat 2 (j + 1) % 2 = 1 := by
      rw [Nat.pow_mod]; norm_num
    rw [hv, e2, e1, hj, pow_succ]
    omega

lemma sum_T : ∀ n, ∑ k ∈ Icc 1 n, (3 ^ padicValNat 2 k + 1) / 2 = T n := by
  intro n
  induction n with
  | zero => simp [T_zero]
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, T_succ]

lemma T_strictMono : StrictMono T := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rw [T_succ]
  have := Nat.one_le_pow (padicValNat 2 (n + 1)) 3 (by norm_num)
  omega

lemma T_surj : ∀ e, D e → ∃ i, T i = e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro h
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact ⟨0, T_zero⟩
  rw [D_iff] at h
  obtain ⟨j, hj⟩ := ih (e / 3) (by omega) h.2
  refine ⟨e % 3 + 2 * j, ?_⟩
  rw [T_lin j (e % 3) (by omega), hj]
  omega

lemma T_pow : ∀ m i, i < 2 ^ m → T (2 ^ m + i) = 3 ^ m + T i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by simpa using hi
    rw [T_eq]; simp [T_zero]
  | succ m ih =>
    intro i hi
    rw [pow_succ] at hi
    rw [show 2 ^ (m + 1) + i = i % 2 + 2 * (2 ^ m + i / 2) by rw [pow_succ]; omega,
      T_lin (2 ^ m + i / 2) (i % 2) (by omega), ih (i / 2) (by omega), T_eq i, pow_succ]
    ring

open Classical in
lemma count_D (i : ℕ) : Nat.count D (T i) = i := by
  rw [Nat.count_eq_card_filter_range]
  have : (range (T i)).filter D = (range i).image T := by
    ext e
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨he, hD⟩
      obtain ⟨j, rfl⟩ := T_surj e hD
      exact ⟨j, T_strictMono.lt_iff_lt.1 he, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨T_strictMono hj, T_D j⟩
  rw [this, card_image_of_injective _ T_strictMono.injective, card_range]

open Classical in
lemma count_block (m j : ℕ) (hj : j ≤ 3 ^ m) : Nat.count P (c m + j) = Nat.count P (c m) + Nat.count D j := by
  rw [Nat.count_add]
  congr 1
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
  congr 1
  refine filter_congr fun e he => ?_
  rw [mem_range] at he
  obtain ⟨h23, h1', hc⟩ := c_two m
  constructor
  · rintro (h | h | ⟨m', e', he', hlt', heq⟩)
    · omega
    · omega
    rcases lt_trichotomy m' m with hlt | rfl | hgt
    · have := c_block hlt; omega
    · obtain rfl : e = e' := by omega
      exact he'
    · have := c_block hgt; omega
  · intro hD
    exact P_block hD (by omega)

open Classical in
lemma count_gap (m : ℕ) : Nat.count P (c (m + 1)) = Nat.count P (c m + 3 ^ m) := by
  have hcs := c_succ m
  obtain ⟨h23, h1', hc⟩ := c_two m
  rw [show c (m + 1) = c m + 3 ^ m + (c m - 1) by omega, Nat.count_add, Nat.count_eq_card_filter_range
    (fun e => P (c m + 3 ^ m + e)), add_eq_left, card_eq_zero, filter_eq_empty_iff]
  intro e he
  rw [mem_range] at he
  rintro (h | h | ⟨m', e', he', hlt', heq⟩)
  · omega
  · omega
  rcases lt_trichotomy m' m with hlt | rfl | hgt
  · have := c_block hlt; omega
  · omega
  · have := c_mono (show m + 1 ≤ m' by omega); omega

open Classical in
lemma count_c : ∀ m, Nat.count P (c m) = 2 ^ m + 1 := by
  intro m
  induction m with
  | zero =>
    have h3 : c 0 = 3 := by norm_num [c]
    rw [h3, Nat.count_succ, Nat.count_succ, Nat.count_succ, Nat.count_zero]
    have h1 : P 1 := Or.inl rfl
    have h2 : P 2 := Or.inr (Or.inl rfl)
    simp [P_zero, h1, h2]
  | succ m ih =>
    have := T_pow m 0 (by positivity)
    rw [add_zero, T_zero, add_zero] at this
    rw [count_gap, count_block m _ le_rfl, ih, ← this, count_D, pow_succ]
    ring

end OMA.P_a092482

open OMA.P_a092482 in
theorem OMA.solution : type_of% @OMA.S_oeis_a092482.main := by
  classical
  intro n hn
  have hPS : S_oeis_a092482.IsTerm = P := funext fun x => propext (isTerm_iff x)
  unfold S_oeis_a092482.a
  rw [show n + 2 - 1 = n + 1 by omega, hPS, sum_T]
  have hm1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hm2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  rw [pow_succ] at hm2
  have hTn : T n = 3 ^ Nat.log 2 n + T (n - 2 ^ Nat.log 2 n) := by
    rw [← T_pow (Nat.log 2 n) (n - 2 ^ Nat.log 2 n) (by omega)]
    congr 1
    omega
  have hTl : T (n - 2 ^ Nat.log 2 n) < 3 ^ Nat.log 2 n := by
    have := T_strictMono (show n - 2 ^ Nat.log 2 n < 2 ^ Nat.log 2 n by omega)
    have h := T_pow (Nat.log 2 n) 0 (by positivity)
    rw [add_zero, T_zero, add_zero] at h
    rwa [h] at this
  have hx : P (c (Nat.log 2 n) + T (n - 2 ^ Nat.log 2 n)) := P_block (T_D _) hTl
  have hcount : Nat.count P (c (Nat.log 2 n) + T (n - 2 ^ Nat.log 2 n)) = n + 1 := by
    rw [count_block _ _ hTl.le, count_c, count_D]
    omega
  rw [hTn, ← hcount, Nat.nth_count hx]
  unfold c
  ring
