import OMAStatements.S_oeis_a107793

namespace OMA.S_oeis_a107793

/-! ### Definitions (as in the statement) -/










/-! ### Generic facts about sums of block lengths -/

/-- Start of block k in an infinite word built from the blocks h (Y 0), h (Y 1), ... -/
def bs (h : ℕ → List ℕ) (Y : ℕ → ℕ) (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, (h (Y j)).length

lemma bs_succ (h : ℕ → List ℕ) (Y : ℕ → ℕ) (k : ℕ) :
    bs h Y (k + 1) = bs h Y k + (h (Y k)).length := Finset.sum_range_succ _ _

lemma bs_zero (h : ℕ → List ℕ) (Y : ℕ → ℕ) : bs h Y 0 = 0 := by simp [bs]

lemma bs_shift (h : ℕ → List ℕ) (Y : ℕ → ℕ) (j k : ℕ) :
    bs h Y (j + k) = bs h Y j + bs h (fun i => Y (j + i)) k := by
  unfold bs
  rw [Finset.sum_range_add]

lemma bs_mono (h : ℕ → List ℕ) (Y : ℕ → ℕ) {k k' : ℕ} (hk : k ≤ k') : bs h Y k ≤ bs h Y k' :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hk)

lemma bs_congr (h : ℕ → List ℕ) {Y Y' : ℕ → ℕ} {k : ℕ} (hY : ∀ j < k, Y j = Y' j) :
    bs h Y k = bs h Y' k :=
  Finset.sum_congr rfl fun j hj => by rw [hY j (Finset.mem_range.mp hj)]

/-- Every position lies in a block, when every block has at least one letter. -/
lemma block_exists (h : ℕ → List ℕ) (Y : ℕ → ℕ) (hne : ∀ k, 1 ≤ (h (Y k)).length) (x : ℕ) :
    ∃ k, bs h Y k ≤ x ∧ x < bs h Y (k + 1) := by
  have hge : ∀ k, k ≤ bs h Y k := by
    intro k
    induction k with
    | zero => simp [bs]
    | succ k ih => rw [bs_succ]; have := hne k; omega
  classical
  have hex : ∃ k, x < bs h Y (k + 1) := ⟨x, by have := hge (x + 1); omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, bs_zero]
    exact Nat.zero_le _
  · have := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
    rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at this
    omega

/-- The blocks of a flatMap. -/
lemma flatMap_getD_block (h : ℕ → List ℕ) (L : List ℕ) (Y : ℕ → ℕ)
    (hY : ∀ j < L.length, L.getD j 0 = Y j) (k r : ℕ) (hk : k < L.length)
    (hr : r < (h (Y k)).length) :
    (L.flatMap h).getD (bs h Y k + r) 0 = (h (Y k)).getD r 0 := by
  induction L generalizing Y k with
  | nil => simp at hk
  | cons x L ih =>
    have hx : x = Y 0 := by simpa using hY 0 (by simp)
    rw [List.flatMap_cons]
    rcases k with _ | k
    · rw [bs_zero, zero_add, List.getD_append _ _ _ _ (by rw [hx]; exact hr), hx]
    · have hY' : ∀ j < L.length, L.getD j 0 = Y (1 + j) := by
        intro j hj
        have := hY (j + 1) (by simp; omega)
        simpa [add_comm] using this
      have hb : bs h Y (k + 1) = (h x).length + bs h (fun i => Y (1 + i)) k := by
        rw [add_comm k 1, bs_shift, hx]
        simp [bs]
      rw [hb, add_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]
      have := ih (fun i => Y (1 + i)) hY' k (by simp at hk; omega) (by rw [add_comm]; exact hr)
      rw [this, add_comm]

lemma flatMap_length_ge (h : ℕ → List ℕ) (hne : ∀ x, 1 ≤ (h x).length) (L : List ℕ) :
    L.length ≤ (L.flatMap h).length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := hne x
    omega

lemma flatMap_length_eq (h : ℕ → List ℕ) (L : List ℕ) (Y : ℕ → ℕ)
    (hY : ∀ j < L.length, L.getD j 0 = Y j) : (L.flatMap h).length = bs h Y L.length := by
  induction L generalizing Y with
  | nil => simp [bs]
  | cons x L ih =>
    have hx : x = Y 0 := by simpa using hY 0 (by simp)
    have hY' : ∀ j < L.length, L.getD j 0 = Y (1 + j) := by
      intro j hj
      have := hY (j + 1) (by simp; omega)
      simpa [add_comm] using this
    rw [List.flatMap_cons, List.length_append, ih _ hY', List.length_cons, add_comm L.length 1,
      bs_shift, hx]
    simp [bs]

lemma prefix_getD {A B : List ℕ} (h : A <+: B) {i : ℕ} (hi : i < A.length) :
    A.getD i 0 = B.getD i 0 := by
  obtain ⟨C, rfl⟩ := h
  rw [List.getD_append _ _ _ _ hi]

lemma flatMap_prefix (h : ℕ → List ℕ) {A B : List ℕ} (hAB : A <+: B) :
    A.flatMap h <+: B.flatMap h := by
  obtain ⟨C, rfl⟩ := hAB
  rw [List.flatMap_append]
  exact List.prefix_append _ _

/-! ### sigma-images -/

def Letter (y : ℕ) : Prop := y = 3 ∨ y = 5 ∨ y = 6

lemma sigma_len {y : ℕ} (hy : Letter y) : 4 ≤ (sigma y).length := by
  rcases hy with rfl | rfl | rfl <;> decide

lemma sigma_zero {y : ℕ} (hy : Letter y) : (sigma y).getD 0 0 = 3 := by
  rcases hy with rfl | rfl | rfl <;> decide

lemma sigma_ne_three {y r : ℕ} (hy : Letter y) (hr0 : 0 < r) (hr : r < (sigma y).length) :
    (sigma y).getD r 0 ≠ 3 := by
  rcases hy with rfl | rfl | rfl <;> simp [sigma] at hr ⊢ <;> interval_cases r <;> decide

lemma sigma_len_inj {y y' : ℕ} (hy : Letter y) (hy' : Letter y')
    (h : (sigma y).length = (sigma y').length) : y = y' := by
  rcases hy with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;> simp_all [sigma]

lemma sigma_prefix {y : ℕ} (hy : Letter y) : [3, 6, 5, 6] <+: sigma y := by
  rcases hy with rfl | rfl | rfl <;> decide

/-- X is the sigma-image of Y, block by block. -/
def Img (X Y : ℕ → ℕ) : Prop :=
  (∀ k, Letter (Y k)) ∧ ∀ k r, r < (sigma (Y k)).length →
    X (bs sigma Y k + r) = (sigma (Y k)).getD r 0

lemma bs_ge {Y : ℕ → ℕ} (hY : ∀ k, Letter (Y k)) (k : ℕ) : 4 * k ≤ bs sigma Y k := by
  induction k with
  | zero => simp [bs]
  | succ k ih => rw [bs_succ]; have := sigma_len (hY k); omega

lemma bs_strict {Y : ℕ → ℕ} (hY : ∀ k, Letter (Y k)) {k k' : ℕ} (h : k < k') :
    bs sigma Y k < bs sigma Y k' := by
  have h1 := bs_mono sigma Y (show k + 1 ≤ k' by omega)
  rw [bs_succ] at h1
  have := sigma_len (hY k)
  omega

lemma three_iff {X Y : ℕ → ℕ} (h : Img X Y) (x : ℕ) : X x = 3 ↔ ∃ k, x = bs sigma Y k := by
  obtain ⟨k, hk1, hk2⟩ := block_exists sigma Y (fun k => by have := sigma_len (h.1 k); omega) x
  rw [bs_succ] at hk2
  have hx := h.2 k (x - bs sigma Y k) (by omega)
  rw [show bs sigma Y k + (x - bs sigma Y k) = x by omega] at hx
  constructor
  · intro h3
    refine ⟨k, ?_⟩
    by_contra hne
    exact sigma_ne_three (h.1 k) (by omega) (by omega) (hx ▸ h3)
  · rintro ⟨k', rfl⟩
    have := h.2 k' 0 (by have := sigma_len (h.1 k'); omega)
    rw [add_zero] at this
    rw [this, sigma_zero (h.1 k')]

lemma img_shift {X Y : ℕ → ℕ} (h : Img X Y) (j : ℕ) :
    Img (fun i => X (bs sigma Y j + i)) (fun i => Y (j + i)) := by
  refine ⟨fun k => h.1 (j + k), fun k r hr => ?_⟩
  have := h.2 (j + k) r hr
  simp only
  rw [← add_assoc, ← bs_shift]
  exact this

lemma img_inj {X X' Y Y' : ℕ → ℕ} (hX : ∀ i, X i = X' i) (h : Img X Y) (h' : Img X' Y') :
    ∀ k, Y k = Y' k := by
  have key : ∀ k, bs sigma Y k = bs sigma Y' k ∧ Y k = Y' k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      have hbs : bs sigma Y k = bs sigma Y' k := by
        rcases k with _ | k
        · simp [bs]
        · rw [bs_succ, bs_succ, (ih k (by omega)).1, (ih k (by omega)).2]
      refine ⟨hbs, ?_⟩
      apply sigma_len_inj (h.1 k) (h'.1 k)
      -- the block length is the distance to the next 3
      have next : ∀ {Z W : ℕ → ℕ}, Img Z W → Z (bs sigma W k + (sigma (W k)).length) = 3 := by
        intro Z W hZ
        have := hZ.2 (k + 1) 0 (by have := sigma_len (hZ.1 (k + 1)); omega)
        rw [add_zero, bs_succ] at this
        rw [this, sigma_zero (hZ.1 (k + 1))]
      have inside : ∀ {Z W : ℕ → ℕ}, Img Z W → ∀ r, 0 < r → r < (sigma (W k)).length →
          Z (bs sigma W k + r) ≠ 3 := by
        intro Z W hZ r hr0 hr
        rw [hZ.2 k r hr]
        exact sigma_ne_three (hZ.1 k) hr0 hr
      rcases lt_trichotomy (sigma (Y k)).length (sigma (Y' k)).length with hlt | heq | hgt
      · exfalso
        have a1 := next h
        have a2 := inside h' (sigma (Y k)).length (by have := sigma_len (h.1 k); omega) hlt
        rw [← hbs, ← hX] at a2
        exact a2 a1
      · exact heq
      · exfalso
        have a1 := next h'
        have a2 := inside h (sigma (Y' k)).length (by have := sigma_len (h'.1 k); omega) hgt
        rw [hbs, hX] at a2
        exact a2 a1
  exact fun k => (key k).2

/-- A sigma-image of itself is not eventually periodic. -/
lemma aperiodic {X : ℕ → ℕ} (h : Img X X) :
    ∀ p, 1 ≤ p → ¬ ∃ a, ∀ i, X (a + i) = X (a + p + i) := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    rintro hp ⟨a, ha⟩
    set s := bs sigma X a with hs
    have hsa : a ≤ s := by have := bs_ge h.1 a; omega
    have h3 : X s = 3 := (three_iff h s).mpr ⟨a, rfl⟩
    have h3' : X (s + p) = 3 := by
      have := ha (s - a)
      rw [show a + (s - a) = s by omega, show a + p + (s - a) = s + p by omega] at this
      rw [← this, h3]
    obtain ⟨j', hj'⟩ := (three_iff h (s + p)).mp h3'
    have hj : a < j' := by
      by_contra hle
      push_neg at hle
      have := bs_mono sigma X hle
      omega
    have i1 := img_shift h a
    have i2 := img_shift h j'
    have heq : ∀ i, X (bs sigma X a + i) = X (bs sigma X j' + i) := by
      intro i
      rw [← hs, ← hj']
      have := ha (s - a + i)
      rw [show a + (s - a + i) = s + i by omega, show a + p + (s - a + i) = s + p + i by omega]
        at this
      exact this
    have hper := img_inj heq i1 i2
    have hb := bs_ge h.1
    have hdiff : 4 * (j' - a) ≤ p := by
      have e := bs_shift sigma X a (j' - a)
      rw [show a + (j' - a) = j' by omega] at e
      have := bs_ge (fun k => h.1 (a + k)) (j' - a)
      omega
    exact ih (j' - a) (by omega) (by omega) ⟨a, fun i => by
      have := hper i
      rw [this, show a + (j' - a) + i = j' + i by omega]⟩

/-! ### A275925 is a sigma-image of itself -/

lemma sigma_letters {y : ℕ} (hy : Letter y) : ∀ x ∈ sigma y, Letter x := by
  rcases hy with rfl | rfl | rfl <;> simp [sigma, Letter]

lemma letter_flatMap_sigma {L : List ℕ} (hL : ∀ x ∈ L, Letter x) :
    ∀ x ∈ L.flatMap sigma, Letter x := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := List.mem_flatMap.mp hx
  exact sigma_letters (hL y hy) x hxy

lemma four_mul_len_le {L : List ℕ} (hL : ∀ x ∈ L, Letter x) :
    4 * L.length ≤ (L.flatMap sigma).length := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.flatMap_cons, List.length_append, List.length_cons]
    have := sigma_len (hL x (by simp))
    have := ih (fun y hy => hL y (by simp [hy]))
    omega

lemma T_succ (k : ℕ) : T (k + 1) = (T k).flatMap sigma := by
  unfold T
  rw [Function.iterate_succ_apply']

lemma T_letter (k : ℕ) : ∀ x ∈ T k, Letter x := by
  induction k with
  | zero => simp [T, Letter]
  | succ k ih => rw [T_succ]; exact letter_flatMap_sigma ih

lemma T_len (k : ℕ) : k + 1 ≤ (T k).length := by
  induction k with
  | zero => simp [T]
  | succ k ih =>
    rw [T_succ]
    have := four_mul_len_le (T_letter k)
    omega

lemma T_prefix (k : ℕ) : T k <+: T (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih => rw [T_succ, T_succ (k + 1)]; exact flatMap_prefix sigma ih

lemma T_prefix_le {k k' : ℕ} (h : k ≤ k') : T k <+: T k' := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact List.prefix_refl _
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
    · exact (ih (by omega)).trans (T_prefix k')
    · have : k = k' + 1 := by omega
      subst this; exact List.prefix_refl _

lemma T_getD {K j : ℕ} (hj : j < (T K).length) : (T K).getD j 0 = t j := by
  unfold t
  rcases Nat.le_total (j + 1) K with h | h
  · exact (prefix_getD (T_prefix_le h) (by have := T_len (j + 1); omega)).symm
  · exact prefix_getD (T_prefix_le h) hj

lemma t_letter (j : ℕ) : Letter (t j) := by
  unfold t
  have hj : j < (T (j + 1)).length := by have := T_len (j + 1); omega
  rw [List.getD_eq_getElem _ _ hj]
  exact T_letter _ _ (List.getElem_mem hj)

lemma img_t : Img t t := by
  refine ⟨t_letter, fun k r hr => ?_⟩
  set K := bs sigma t k + r + k + 1 with hK
  have hTK : ∀ j < (T K).length, (T K).getD j 0 = t j := fun j hj => T_getD hj
  have hk : k < (T K).length := by have := T_len K; omega
  have hlen : (T (K + 1)).length = bs sigma t (T K).length := by
    rw [T_succ, flatMap_length_eq sigma (T K) t hTK]
  have hpos : bs sigma t k + r < (T (K + 1)).length := by
    rw [hlen]
    have h1 := bs_mono sigma t (show k + 1 ≤ (T K).length by omega)
    rw [bs_succ] at h1
    omega
  rw [← T_getD hpos, T_succ]
  exact flatMap_getD_block sigma (T K) t hTK k r hk hr

/-! ### The return words of 1 in A305390 -/

/-- The return words 123, 1233, 12323 of 1, labeled 3, 5, 6 (their lengths 3, 4, 5 relabeled). -/
def R : ℕ → List ℕ
  | 3 => [1, 2, 3]
  | 5 => [1, 2, 3, 3]
  | 6 => [1, 2, 3, 2, 3]
  | c => [c]

/-- The induced substitution on return words: sigma rotated by one letter. -/
def rho : ℕ → List ℕ
  | 3 => [6, 5, 6, 3]
  | 5 => [6, 5, 6, 5, 6, 3]
  | 6 => [6, 5, 6, 6, 5, 6, 3]
  | c => [c]

/-- f applied three times. -/
def phi (w : List ℕ) : List ℕ := ((w.flatMap f).flatMap f).flatMap f

lemma phi_append (A B : List ℕ) : phi (A ++ B) = phi A ++ phi B := by
  simp [phi, List.flatMap_append]

lemma S_add_three (n : ℕ) : S (n + 3) = phi (S n) := by
  unfold S phi
  rw [show n + 3 = ((n + 1) + 1) + 1 by ring, Function.iterate_succ_apply',
    Function.iterate_succ_apply', Function.iterate_succ_apply']

lemma phi_R {y : ℕ} (hy : Letter y) : phi (R y) = (rho y).flatMap R := by
  rcases hy with rfl | rfl | rfl <;> decide

lemma phi_flatMap_R {L : List ℕ} (hL : ∀ x ∈ L, Letter x) :
    phi (L.flatMap R) = (L.flatMap rho).flatMap R := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    rw [List.flatMap_cons, phi_append, phi_R (hL x (by simp)),
      ih (fun y hy => hL y (by simp [hy])), List.flatMap_cons, List.flatMap_append]

lemma rho_sigma {L : List ℕ} (hL : ∀ x ∈ L, Letter x) :
    [3] ++ L.flatMap rho = L.flatMap sigma ++ [3] := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    have hx : [3] ++ rho x = sigma x ++ [3] := by
      rcases hL x (by simp) with rfl | rfl | rfl <;> decide
    rw [List.flatMap_cons, List.flatMap_cons, ← List.append_assoc, hx, List.append_assoc,
      ih (fun y hy => hL y (by simp [hy])), List.append_assoc]

/-- The finite approximations of the relabeled OMA.S_oeis_a107793. -/
def E : ℕ → List ℕ
  | 0 => [5, 6, 3, 6, 5, 6]
  | k + 1 => [5, 6] ++ (E k).flatMap sigma ++ [3, 6, 5, 6]

lemma E_letter (k : ℕ) : ∀ x ∈ E k, Letter x := by
  induction k with
  | zero => simp [E, Letter]
  | succ k ih =>
    intro x hx
    simp only [E, List.mem_append] at hx
    rcases hx with (hx | hx) | hx
    · unfold Letter; simp at hx; omega
    · exact letter_flatMap_sigma ih x hx
    · unfold Letter; simp at hx; omega

lemma S_E (k : ℕ) : S (3 * k + 7) = [2, 3] ++ (E k).flatMap R ++ [1, 2, 3] := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 3 * (k + 1) + 7 = (3 * k + 7) + 3 by ring, S_add_three, ih, phi_append, phi_append,
      phi_flatMap_R (E_letter k)]
    have h23 : phi [2, 3] = [2, 3] ++ [5, 6, 3].flatMap R := by decide
    have h123 : phi [1, 2, 3] = [6, 5, 6, 3].flatMap R := by decide
    rw [h23, h123]
    have key : [5, 6, 3] ++ (E k).flatMap rho ++ [6, 5, 6, 3] =
        [5, 6] ++ (E k).flatMap sigma ++ [3, 6, 5, 6] ++ [3] := by
      have := rho_sigma (E_letter k)
      calc [5, 6, 3] ++ (E k).flatMap rho ++ [6, 5, 6, 3]
          = [5, 6] ++ ([3] ++ (E k).flatMap rho) ++ [6, 5, 6, 3] := by simp
        _ = [5, 6] ++ ((E k).flatMap sigma ++ [3]) ++ [6, 5, 6, 3] := by rw [this]
        _ = [5, 6] ++ (E k).flatMap sigma ++ [3, 6, 5, 6] ++ [3] := by simp
    have hr : ([5, 6] ++ (E k).flatMap sigma ++ [3, 6, 5, 6]).flatMap R ++ [1, 2, 3] =
        ([5, 6, 3] ++ (E k).flatMap rho ++ [6, 5, 6, 3]).flatMap R := by
      rw [key]
      simp [List.flatMap_append, R]
    simp only [E]
    conv_rhs => rw [List.append_assoc, hr]
    simp [List.flatMap_append]

lemma E_prefix (k : ℕ) : E k <+: E (k + 1) ∧ (E k).length < (E (k + 1)).length := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨⟨C, hC⟩, hlt⟩ := ih
    have hCne : C ≠ [] := by
      rintro rfl
      rw [List.append_nil] at hC
      rw [hC] at hlt
      exact lt_irrefl _ hlt
    obtain ⟨x, C', rfl⟩ := List.exists_cons_of_ne_nil hCne
    have hx : Letter x := E_letter (k + 1) x (by rw [← hC]; simp)
    constructor
    · show [5, 6] ++ (E k).flatMap sigma ++ [3, 6, 5, 6] <+:
        [5, 6] ++ (E (k + 1)).flatMap sigma ++ [3, 6, 5, 6]
      rw [← hC, List.flatMap_append, List.flatMap_cons]
      obtain ⟨D, hD⟩ := sigma_prefix hx
      rw [← hD]
      simp only [List.append_assoc]
      rw [List.prefix_append_right_inj, List.prefix_append_right_inj]
      exact List.prefix_append _ _
    · show ([5, 6] ++ (E k).flatMap sigma ++ [3, 6, 5, 6]).length <
        ([5, 6] ++ (E (k + 1)).flatMap sigma ++ [3, 6, 5, 6]).length
      rw [← hC, List.flatMap_append, List.flatMap_cons]
      simp only [List.length_append]
      have := sigma_len hx
      omega

lemma E_len (k : ℕ) : k + 6 ≤ (E k).length := by
  induction k with
  | zero => simp [E]
  | succ k ih => have := (E_prefix k).2; omega

lemma E_prefix_le {k k' : ℕ} (h : k ≤ k') : E k <+: E k' := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact List.prefix_refl _
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
    · exact (ih (by omega)).trans (E_prefix k').1
    · have : k = k' + 1 := by omega
      subst this; exact List.prefix_refl _

/-- The relabeled A107793, as the limit of the E k. -/
def N (j : ℕ) : ℕ := (E j).getD j 0

lemma E_getD {K j : ℕ} (hj : j < (E K).length) : (E K).getD j 0 = N j := by
  unfold N
  rcases Nat.le_total j K with h | h
  · exact (prefix_getD (E_prefix_le h) (by have := E_len j; omega)).symm
  · exact prefix_getD (E_prefix_le h) hj

lemma N_letter (j : ℕ) : Letter (N j) := by
  unfold N
  have hj : j < (E j).length := by have := E_len j; omega
  rw [List.getD_eq_getElem _ _ hj]
  exact E_letter _ _ (List.getElem_mem hj)

lemma N_zero : N 0 = 5 := rfl

lemma N_one : N 1 = 6 := by
  rw [← E_getD (K := 0) (by simp [E])]
  rfl

/-- N = 5 6 sigma(N). -/
lemma img_N : Img (fun i => N (i + 2)) N := by
  refine ⟨N_letter, fun k r hr => ?_⟩
  set K := bs sigma N k + r + k + 1 with hK
  have hEK : ∀ j < (E K).length, (E K).getD j 0 = N j := fun j hj => E_getD hj
  have hk : k < (E K).length := by have := E_len K; omega
  have hlen : ((E K).flatMap sigma).length = bs sigma N (E K).length :=
    flatMap_length_eq sigma (E K) N hEK
  have hpos : bs sigma N k + r < ((E K).flatMap sigma).length := by
    rw [hlen]
    have h1 := bs_mono sigma N (show k + 1 ≤ (E K).length by omega)
    rw [bs_succ] at h1
    omega
  have hpos' : bs sigma N k + r + 2 < (E (K + 1)).length := by
    simp only [E, List.length_append]
    simp at hpos ⊢
    omega
  simp only
  rw [← E_getD hpos']
  simp only [E]
  rw [List.append_assoc, show bs sigma N k + r + 2 = 2 + (bs sigma N k + r) by ring,
    List.getD_append_right _ _ _ _ (by simp), show 2 + (bs sigma N k + r) - [5, 6].length =
      bs sigma N k + r by simp, List.getD_append _ _ _ _ hpos]
  exact flatMap_getD_block sigma (E K) N hEK k r hk hr

/-! ### A305390, its 1s and A107793 -/

lemma phi_prefix {A B : List ℕ} (h : A <+: B) : phi A <+: phi B :=
  flatMap_prefix f (flatMap_prefix f (flatMap_prefix f h))

lemma S_prefix (k : ℕ) : S (3 * k + 1) <+: S (3 * (k + 1) + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show 3 * (k + 1) + 1 = (3 * k + 1) + 3 by ring, S_add_three,
      show 3 * (k + 1 + 1) + 1 = (3 * (k + 1) + 1) + 3 by ring, S_add_three]
    exact phi_prefix ih

lemma S_prefix_le {k k' : ℕ} (h : k ≤ k') : S (3 * k + 1) <+: S (3 * k' + 1) := by
  induction k' with
  | zero => have : k = 0 := by omega
            subst this; exact List.prefix_refl _
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
    · exact (ih (by omega)).trans (S_prefix k')
    · have : k = k' + 1 := by omega
      subst this; exact List.prefix_refl _

lemma S_len (k : ℕ) : k + 1 ≤ (S (3 * k + 1)).length := by
  rcases Nat.lt_or_ge k 2 with h | h
  · interval_cases k <;> decide
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [show 3 * (m + 2) + 1 = 3 * m + 7 by ring, S_E]
    have h1 := flatMap_length_ge R (fun x => by unfold R; split <;> simp) (E m)
    have h2 := E_len m
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma u_eq {x K : ℕ} (hx : x < (S (3 * K + 1)).length) : u x = (S (3 * K + 1)).getD x 0 := by
  unfold u
  rcases Nat.le_total x K with h | h
  · exact prefix_getD (S_prefix_le h) (by have := S_len x; omega)
  · exact (prefix_getD (S_prefix_le h) hx).symm

lemma R_len {y : ℕ} (hy : Letter y) : 3 ≤ (R y).length := by
  rcases hy with rfl | rfl | rfl <;> decide

lemma R_zero {y : ℕ} (hy : Letter y) : (R y).getD 0 0 = 1 := by
  rcases hy with rfl | rfl | rfl <;> decide

lemma R_ne_one {y r : ℕ} (hy : Letter y) (hr0 : 0 < r) (hr : r < (R y).length) :
    (R y).getD r 0 ≠ 1 := by
  rcases hy with rfl | rfl | rfl <;> simp [R] at hr ⊢ <;> interval_cases r <;> decide

lemma g_R {y : ℕ} (hy : Letter y) : g (R y).length = y := by
  rcases hy with rfl | rfl | rfl <;> decide

/-- Q n: the start of the n-th return word after the prefix 23. -/
def Q (n : ℕ) : ℕ := bs R N n

lemma Q_succ (n : ℕ) : Q (n + 1) = Q n + (R (N n)).length := bs_succ R N n

lemma Q_strict {n n' : ℕ} (h : n < n') : Q n < Q n' := by
  have h1 := bs_mono R N (show n + 1 ≤ n' by omega)
  have := R_len (N_letter n)
  unfold Q
  rw [bs_succ] at h1
  omega

lemma Q_ge (n : ℕ) : n ≤ Q n := by
  induction n with
  | zero => simp [Q, bs]
  | succ n ih => rw [Q_succ]; have := R_len (N_letter n); omega

/-- u read on the explicit prefix [2, 3] ++ R-blocks of E K. -/
lemma u_eq_E {x K : ℕ} (hx : x < 2 + ((E K).flatMap R).length) :
    u x = ([2, 3] ++ (E K).flatMap R ++ [1, 2, 3]).getD x 0 := by
  rw [← S_E, show 3 * K + 7 = 3 * (K + 2) + 1 by ring]
  apply u_eq
  rw [show 3 * (K + 2) + 1 = 3 * K + 7 by ring, S_E]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

lemma u_one_iff (x : ℕ) : u x = 1 ↔ ∃ n, x = 2 + Q n := by
  set K := x + 1 with hK
  have hEK : ∀ j < (E K).length, (E K).getD j 0 = N j := fun j hj => E_getD hj
  have hlenR : ((E K).flatMap R).length = Q (E K).length := flatMap_length_eq R (E K) N hEK
  have hEl := E_len K
  have hQbig : x < Q (E K).length := by have := Q_ge (E K).length; omega
  have hux := u_eq_E (K := K) (x := x) (by rw [hlenR]; omega)
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · constructor
    · intro h
      rw [hux] at h
      interval_cases x <;> simp at h
    · rintro ⟨n, hn⟩
      omega
  · obtain ⟨n, hn1, hn2⟩ := block_exists R N (fun k => by have := R_len (N_letter k); omega)
      (x - 2)
    have hnK : n < (E K).length := by
      by_contra hge
      push_neg at hge
      have := bs_mono R N hge
      unfold Q at hQbig
      omega
    have hn2' : x - 2 < bs R N n + (R (N n)).length := by rw [← bs_succ]; exact hn2
    have hxlt : x - 2 < ((E K).flatMap R).length := by
      rw [hlenR]
      have := bs_mono R N (show n + 1 ≤ (E K).length by omega)
      unfold Q
      omega
    have hletter : u x = (R (N n)).getD (x - 2 - bs R N n) 0 := by
      have e1 : ([2, 3] ++ (E K).flatMap R ++ [1, 2, 3]).getD x 0 =
          ((E K).flatMap R).getD (x - 2) 0 := by
        rw [List.append_assoc, List.getD_append_right _ _ _ _ (by simp; omega)]
        have : x - [2, 3].length = x - 2 := by simp
        rw [this, List.getD_append _ _ _ _ hxlt]
      have key := flatMap_getD_block R (E K) N hEK n (x - 2 - bs R N n) hnK (by omega)
      rw [show bs R N n + (x - 2 - bs R N n) = x - 2 by omega] at key
      rw [hux, e1]
      exact key
    rw [hletter]
    constructor
    · intro h
      refine ⟨n, ?_⟩
      by_contra hne
      have hr0 : 0 < x - 2 - bs R N n := by unfold Q at hne; omega
      exact R_ne_one (N_letter n) hr0 (by omega) h
    · rintro ⟨n', hn'⟩
      have : n' = n := by
        rcases Nat.lt_trichotomy n' n with h | h | h
        · have := Q_strict h
          unfold Q at *
          omega
        · exact h
        · have := bs_mono R N (show n + 1 ≤ n' by omega)
          unfold Q at *
          omega
      subst this
      rw [show x - 2 - bs R N n' = 0 by unfold Q at hn'; omega]
      exact R_zero (N_letter n')

lemma count_zero_of {P : ℕ → Prop} [DecidablePred P] {v : ℕ} (h : ∀ k < v, ¬ P k) :
    Nat.count P v = 0 := by
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk
  exact h k (Finset.mem_range.mp hk)

lemma count_one_of {P : ℕ → Prop} [DecidablePred P] {v w : ℕ} (hw : P w) (hwv : w < v)
    (h : ∀ k < v, P k → k = w) : Nat.count P v = 1 := by
  rw [Nat.count_eq_card_filter_range, Finset.card_eq_one]
  refine ⟨w, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hk1, hk2⟩
    exact h k hk1 hk2
  · rintro rfl
    exact ⟨hwv, hw⟩

lemma nth_one (n : ℕ) : Nat.nth (fun x => u x = 1) n = 2 + Q n := by
  classical
  have hc : ∀ n, Nat.count (fun x => u x = 1) (2 + Q n) = n := by
    intro n
    induction n with
    | zero =>
      apply count_zero_of
      intro k hk h1
      obtain ⟨m, hm⟩ := (u_one_iff k).mp h1
      have := Q_ge m
      simp [Q, bs] at hk
      omega
    | succ n ih =>
      rw [Q_succ, show 2 + (Q n + (R (N n)).length) = (2 + Q n) + (R (N n)).length by ring,
        Nat.count_add, ih]
      congr 1
      apply count_one_of (w := 0) (by rw [add_zero]; exact (u_one_iff _).mpr ⟨n, rfl⟩)
        (by have := R_len (N_letter n); omega)
      intro k hk h1
      obtain ⟨m, hm⟩ := (u_one_iff _).mp h1
      by_contra hne
      rcases Nat.lt_trichotomy m n with hlt | heq | hgt
      · have := Q_strict hlt
        omega
      · subst heq
        omega
      · have h2 := bs_mono R N (show n + 1 ≤ m by omega)
        have h3 := Q_succ n
        unfold Q at *
        omega
  have := Nat.nth_count (p := fun x => u x = 1) (n := 2 + Q n) ((u_one_iff _).mpr ⟨n, rfl⟩)
  rwa [hc] at this

lemma M_eq (i : ℕ) : M i = N (i + 2) := by
  unfold M d
  rw [nth_one, nth_one, Q_succ]
  rw [show 2 + (Q (i + 2) + (R (N (i + 2))).length) - (2 + Q (i + 2)) = (R (N (i + 2))).length
    by omega]
  exact g_R (N_letter _)

/-! ### The disproof -/

lemma N_two : N 2 = 3 := by
  have := img_N.2 0 0 (by have := sigma_len (N_letter 0); omega)
  simp only [bs_zero, add_zero, zero_add] at this
  rw [this, sigma_zero (N_letter 0)]

/-- Sloane's conjecture is false: no shift of A275925 (in either direction) is M. -/
theorem disproof : ¬ ∃ s : ℤ, ∀ i j : ℕ, (j : ℤ) = (i : ℤ) + s → M i = t j := by
  rintro ⟨s, hs⟩
  have hX := img_N
  have ht := img_t
  rcases le_or_gt 0 s with hs0 | hs0
  · obtain ⟨s0, rfl⟩ := Int.eq_ofNat_of_zero_le hs0
    have hM : ∀ i, N (i + 2) = t (s0 + i) := by
      intro i
      rw [← M_eq]
      exact hs i (s0 + i) (by push_cast; ring)
    have h3 : t s0 = 3 := by
      have := hM 0
      rw [add_zero, zero_add, N_two] at this
      exact this.symm
    obtain ⟨j, hj⟩ := (three_iff ht s0).mp h3
    have heq : ∀ i, N (i + 2) = t (bs sigma t j + i) := fun i => by rw [hM i, hj]
    have hNt := img_inj heq hX (img_shift ht j)
    have hper : ∀ i, t (j + 2 + i) = t (s0 + i) := by
      intro i
      rw [← hM i, hNt (i + 2)]
      ring_nf
    have hge := bs_ge ht.1 j
    rcases lt_trichotomy s0 (j + 2) with hlt | heq2 | hgt
    · exact aperiodic ht (j + 2 - s0) (by omega) ⟨s0, fun i => by
        rw [← hper i, show s0 + (j + 2 - s0) + i = j + 2 + i by omega]⟩
    · have hj0 : j = 0 := by omega
      subst hj0
      rw [bs_zero] at hj
      omega
    · exact aperiodic ht (s0 - (j + 2)) (by omega) ⟨j + 2, fun i => by
        rw [hper i, show j + 2 + (s0 - (j + 2)) + i = s0 + i by omega]⟩
  · obtain ⟨s1, hs1⟩ : ∃ s1 : ℕ, s = -((s1 : ℤ) + 1) := ⟨(-s - 1).toNat, by omega⟩
    subst hs1
    have hM : ∀ k, N (s1 + 1 + k + 2) = t k := by
      intro k
      rw [← M_eq]
      exact hs (s1 + 1 + k) k (by push_cast; ring)
    have h3 : N (s1 + 1 + 2) = 3 := by
      have := hM 0
      rw [add_zero] at this
      rw [this]
      have := ht.2 0 0 (by have := sigma_len (t_letter 0); omega)
      simp only [bs_zero, add_zero] at this
      rw [this, sigma_zero (t_letter 0)]
    obtain ⟨j, hj⟩ := (three_iff hX (s1 + 1)).mp h3
    have heq : ∀ k, N (bs sigma N j + k + 2) = t k := fun k => by rw [← hj]; exact hM k
    have hNt := img_inj heq (img_shift hX j) ht
    have hge := bs_ge hX.1 j
    -- hNt : N (j + k) = t k
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j
      · have := hNt 0
        rw [add_zero, N_zero] at this
        have h0 := ht.2 0 0 (by have := sigma_len (t_letter 0); omega)
        simp only [bs_zero, add_zero] at h0
        rw [h0, sigma_zero (t_letter 0)] at this
        omega
      · have := hNt 0
        rw [add_zero, N_one] at this
        have h0 := ht.2 0 0 (by have := sigma_len (t_letter 0); omega)
        simp only [bs_zero, add_zero] at h0
        rw [h0, sigma_zero (t_letter 0)] at this
        omega
    · -- t k = N (j + k) = N (s1 + 3 + k), so t has period s1 + 3 - j
      have hNN : ∀ k, N (j + k) = N (s1 + 3 + k) := by
        intro k
        rw [hNt k, ← hM k]
        ring_nf
      exact aperiodic ht (s1 + 3 - j) (by omega) ⟨0, fun i => by
        rw [zero_add, zero_add, ← hNt i, ← hNt (s1 + 3 - j + i), hNN i,
          show j + (s1 + 3 - j + i) = s1 + 3 + i by omega]⟩

end OMA.S_oeis_a107793

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a107793.main) :=
  OMA.S_oeis_a107793.disproof
