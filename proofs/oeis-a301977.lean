import OMAStatements.S_oeis_a301977

namespace OMA.OeisA301977

open OMA.S_oeis_a301977

/-! Right-hand side: parity of Stirling numbers of the second kind. -/

/-- Parity of `S(m, 2j+1)`. -/
def f (m j : Nat) : Nat := Nat.stirlingSecond m (2*j+1) % 2

theorem f_lt (m j : Nat) : f m j < 2 := Nat.mod_lt _ (by omega)

theorem st_odd (m k : Nat) :
    Nat.stirlingSecond (m+1) (2*k+1) % 2
      = (Nat.stirlingSecond m (2*k+1) + Nat.stirlingSecond m (2*k)) % 2 := by
  rw [Nat.stirlingSecond_succ_succ]
  have h : (2*k+1) * Nat.stirlingSecond m (2*k+1)
      = 2 * (k * Nat.stirlingSecond m (2*k+1)) + Nat.stirlingSecond m (2*k+1) := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  rw [h]
  omega

theorem st_even (m j : Nat) :
    Nat.stirlingSecond (m+1) (2*j+1+1) % 2 = Nat.stirlingSecond m (2*j+1) % 2 := by
  rw [Nat.stirlingSecond_succ_succ]
  have h : (2*j+1+1) * Nat.stirlingSecond m (2*j+1+1)
      = 2 * ((j+1) * Nat.stirlingSecond m (2*j+1+1)) := by
    rw [← Nat.mul_assoc, show 2*(j+1) = 2*j+1+1 by omega]
  rw [h]
  omega

theorem f_vanish {m j : Nat} (h : m < 2*j+1) : f m j = 0 := by
  unfold f
  have := Nat.stirlingSecond_eq_zero_of_lt h
  omega

theorem f_one (n : Nat) {a b : Nat} (ha : a = n+1) (hb : b = 0) : f a b = 1 := by
  subst ha hb
  show Nat.stirlingSecond (n+1) 1 % 2 = 1
  have := Nat.stirlingSecond_one_right n
  omega

theorem f_rec (n j : Nat) : f (n+2) (j+1) = (f (n+1) (j+1) + f n j) % 2 := by
  unfold f
  show Nat.stirlingSecond (n+1+1) (2*(j+1)+1) % 2
    = (Nat.stirlingSecond (n+1) (2*(j+1)+1) % 2 + Nat.stirlingSecond n (2*j+1) % 2) % 2
  have h1 := st_odd (n+1) (j+1)
  have h2 := st_even n j
  have e : 2*(j+1) = 2*j+1+1 := by omega
  rw [e] at h1 ⊢
  omega

theorem f_rec' {a b c n j : Nat} (ha : a = n+2) (hc : c = n+1) (hb : b = j+1) :
    f a b = (f c b + f n j) % 2 := by
  subst ha hc hb
  exact f_rec n j

theorem dbl (m : Nat) :
    (∀ j, f (2*m) (2*j) = f m j) ∧ (∀ j, f (2*m) (2*j+1) = 0) ∧
    (∀ j, f (2*m+1) (2*j) = f (m+1) j) ∧ (∀ j, f (2*m+1) (2*j+1) = f m j) := by
  induction m with
  | zero =>
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_⟩
    · have h1 : f (2*0) (2*j) = 0 := f_vanish (by omega)
      have h2 : f 0 j = 0 := f_vanish (by omega)
      omega
    · exact f_vanish (by omega)
    · cases j with
      | zero =>
        have h1 : f (2*0+1) (2*0) = 1 := f_one 0 (by omega) (by omega)
        have h2 : f (0+1) 0 = 1 := f_one 0 rfl rfl
        omega
      | succ i =>
        have h1 : f (2*0+1) (2*(i+1)) = 0 := f_vanish (by omega)
        have h2 : f (0+1) (i+1) = 0 := f_vanish (by omega)
        omega
    · have h1 : f (2*0+1) (2*j+1) = 0 := f_vanish (by omega)
      have h2 : f 0 j = 0 := f_vanish (by omega)
      omega
  | succ m ih =>
    obtain ⟨d1, d2, d3, d4⟩ := ih
    have e1 : ∀ j, f (2*(m+1)) (2*j) = f (m+1) j := by
      intro j
      cases j with
      | zero =>
        have h1 : f (2*(m+1)) (2*0) = 1 := f_one (2*m+1) (by omega) (by omega)
        have h2 : f (m+1) 0 = 1 := f_one m rfl rfl
        omega
      | succ i =>
        have h1 : f (2*(m+1)) (2*(i+1))
            = (f (2*m+1) (2*(i+1)) + f (2*m) (2*i+1)) % 2 :=
          f_rec' (n := 2*m) (j := 2*i+1) (by omega) (by omega) (by omega)
        have h2 := d3 (i+1)
        have h3 := d2 i
        have h4 := f_lt (m+1) (i+1)
        omega
    have e2 : ∀ j, f (2*(m+1)) (2*j+1) = 0 := by
      intro j
      have h1 : f (2*(m+1)) (2*j+1) = (f (2*m+1) (2*j+1) + f (2*m) (2*j)) % 2 :=
        f_rec' (n := 2*m) (j := 2*j) (by omega) (by omega) (by omega)
      have h2 := d4 j
      have h3 := d1 j
      omega
    refine ⟨e1, e2, fun j => ?_, fun j => ?_⟩
    · cases j with
      | zero =>
        have h1 : f (2*(m+1)+1) (2*0) = 1 := f_one (2*(m+1)) (by omega) (by omega)
        have h2 : f (m+1+1) 0 = 1 := f_one (m+1) rfl rfl
        omega
      | succ i =>
        have h1 : f (2*(m+1)+1) (2*(i+1))
            = (f (2*(m+1)) (2*(i+1)) + f (2*m+1) (2*i+1)) % 2 :=
          f_rec' (n := 2*m+1) (j := 2*i+1) (by omega) (by omega) (by omega)
        have h2 := e1 (i+1)
        have h3 := d4 i
        have h4 : f (m+1+1) (i+1) = (f (m+1) (i+1) + f m i) % 2 :=
          f_rec' (n := m) (j := i) (by omega) (by omega) (by omega)
        omega
    · have h1 : f (2*(m+1)+1) (2*j+1) = (f (2*(m+1)) (2*j+1) + f (2*m+1) (2*j)) % 2 :=
        f_rec' (n := 2*m+1) (j := 2*j) (by omega) (by omega) (by omega)
      have h2 := e2 j
      have h3 := d3 j
      have h4 := f_lt (m+1) j
      omega

/-- Stern's diatomic sequence, as the number of odd `S(m, 2j+1)`. -/
def s (m : Nat) : Nat := ∑ j ∈ Finset.range m, f m j

theorem sum_range_double (g : Nat → Nat) (t : Nat) :
    ∑ j ∈ Finset.range (2*t), g j = ∑ i ∈ Finset.range t, (g (2*i) + g (2*i+1)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show 2*(t+1) = 2*t+1+1 by omega, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    omega

theorem s_even (t : Nat) : s (2*t) = s t := by
  obtain ⟨d1, d2, -, -⟩ := dbl t
  unfold s
  rw [sum_range_double]
  exact Finset.sum_congr rfl (fun i _ => by rw [d1 i, d2 i, Nat.add_zero])

theorem s_odd (t : Nat) : s (2*t+1) = s t + s (t+1) := by
  obtain ⟨-, -, d3, d4⟩ := dbl t
  have h1 : s (2*t+1)
      = ∑ i ∈ Finset.range t, (f (2*t+1) (2*i) + f (2*t+1) (2*i+1)) + f (2*t+1) (2*t) := by
    unfold s
    rw [Finset.sum_range_succ, sum_range_double]
  have h2 : ∑ i ∈ Finset.range t, (f (2*t+1) (2*i) + f (2*t+1) (2*i+1))
      = ∑ i ∈ Finset.range t, f (t+1) i + ∑ i ∈ Finset.range t, f t i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [d3 i, d4 i])
  have h3 : s (t+1) = ∑ i ∈ Finset.range t, f (t+1) i + f (t+1) t := by
    unfold s
    rw [Finset.sum_range_succ]
  have h4 : s t = ∑ i ∈ Finset.range t, f t i := rfl
  have h5 := d3 t
  omega

theorem rhs (n : Nat) :
    (∑ k ∈ Finset.range n, Nat.stirlingSecond (n+1) (k+1) % 2) + 1 = s n + s (n+1) := by
  have tail : ∀ d, ∑ k ∈ Finset.range (n+1+d), Nat.stirlingSecond (n+1) (k+1) % 2
      = ∑ k ∈ Finset.range (n+1), Nat.stirlingSecond (n+1) (k+1) % 2 := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
      rw [show n+1+(d+1) = n+1+d+1 by omega, Finset.sum_range_succ, ih]
      have : Nat.stirlingSecond (n+1) (n+1+d+1) = 0 :=
        Nat.stirlingSecond_eq_zero_of_lt (by omega)
      omega
  have h1 : ∑ k ∈ Finset.range (n+1), Nat.stirlingSecond (n+1) (k+1) % 2
      = ∑ k ∈ Finset.range n, Nat.stirlingSecond (n+1) (k+1) % 2 + 1 := by
    rw [Finset.sum_range_succ]
    have := Nat.stirlingSecond_self (n+1)
    omega
  have h2 := tail (n+1)
  have h3 : ∑ k ∈ Finset.range (n+1+(n+1)), Nat.stirlingSecond (n+1) (k+1) % 2
      = ∑ i ∈ Finset.range (n+1), (f (n+1) i + f n i) := by
    rw [show n+1+(n+1) = 2*(n+1) by omega, sum_range_double]
    apply Finset.sum_congr rfl
    intro i _
    show Nat.stirlingSecond (n+1) (2*i+1) % 2 + Nat.stirlingSecond (n+1) (2*i+1+1) % 2
      = Nat.stirlingSecond (n+1) (2*i+1) % 2 + Nat.stirlingSecond n (2*i+1) % 2
    rw [st_even]
  have h4 : ∑ i ∈ Finset.range (n+1), (f (n+1) i + f n i) = s (n+1) + s n + f n n := by
    rw [Finset.sum_add_distrib, Finset.sum_range_succ (fun i => f n i)]
    unfold s
    omega
  have h5 : f n n = 0 := f_vanish (by omega)
  omega

/-! Left-hand side: counting even and odd elements of `subseqs n`. -/

theorem subseqs_zero : subseqs 0 = {0} := by
  rw [subseqs, if_pos rfl]

theorem subseqs_ne (n : Nat) (h : n ≠ 0) :
    subseqs n = appendDigit (subseqs (n/2)) (n%2) := by
  rw [subseqs, if_neg h]

theorem half_mem (n : Nat) : ∀ x ∈ subseqs n, x / 2 ∈ subseqs n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro x hx
    by_cases h : n = 0
    · subst h
      rw [subseqs_zero] at hx ⊢
      rw [Finset.mem_singleton] at hx ⊢
      omega
    · rw [subseqs_ne n h] at hx ⊢
      unfold appendDigit at hx ⊢
      rw [Finset.mem_union, Finset.mem_image] at hx
      rw [Finset.mem_union]
      rcases hx with hx | ⟨y, hy, hyx⟩
      · left
        exact ih (n/2) (by omega) x hx
      · left
        have : x / 2 = y := by omega
        rw [this]
        exact hy

theorem filt_same (T : Finset Nat) (b : Nat) (hb : b < 2) (hT : ∀ x ∈ T, x / 2 ∈ T) :
    (appendDigit T b).filter (fun x => x % 2 = b) = T.image (fun x => 2*x+b) := by
  ext x
  simp only [Finset.mem_filter, appendDigit, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hx | ⟨y, hy, hyx⟩, hp⟩
    · exact ⟨x/2, hT x hx, by omega⟩
    · exact ⟨y, hy, hyx⟩
  · rintro ⟨y, hy, hyx⟩
    exact ⟨Or.inr ⟨y, hy, hyx⟩, by omega⟩

theorem filt_other (T : Finset Nat) (b c : Nat) (hb : b < 2) (hc : c ≠ b) :
    (appendDigit T b).filter (fun x => x % 2 = c) = T.filter (fun x => x % 2 = c) := by
  ext x
  simp only [Finset.mem_filter, appendDigit, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hx | ⟨y, hy, hyx⟩, hp⟩
    · exact ⟨hx, hp⟩
    · exact absurd hp (by omega)
  · rintro ⟨hx, hp⟩
    exact ⟨Or.inl hx, hp⟩

theorem card_img (T : Finset Nat) (b : Nat) : (T.image (fun x => 2*x+b)).card = T.card := by
  apply Finset.card_image_of_injective
  intro x y h
  have h' : 2*x+b = 2*y+b := h
  omega

def N (b n : Nat) : Nat := ((subseqs n).filter (fun x => x % 2 = b)).card

theorem card_split (n : Nat) : (subseqs n).card = N 0 n + N 1 n := by
  have hs := Finset.card_filter_add_card_filter_not (s := subseqs n) (fun x => x % 2 = 0)
  have h2 : (subseqs n).filter (fun x => ¬ x % 2 = 0)
      = (subseqs n).filter (fun x => x % 2 = 1) :=
    Finset.filter_congr (fun x _ => by constructor <;> intro h <;> omega)
  unfold N
  rw [← h2]
  omega

theorem sub_even (m : Nat) (hm : 0 < m) : subseqs (2*m) = appendDigit (subseqs m) 0 := by
  rw [subseqs_ne (2*m) (by omega), show 2*m/2 = m by omega, show 2*m%2 = 0 by omega]

theorem sub_odd (m : Nat) : subseqs (2*m+1) = appendDigit (subseqs m) 1 := by
  rw [subseqs_ne (2*m+1) (by omega), show (2*m+1)/2 = m by omega,
    show (2*m+1)%2 = 1 by omega]

theorem N_even0 (m : Nat) (hm : 0 < m) : N 0 (2*m) = (subseqs m).card := by
  unfold N
  rw [sub_even m hm, filt_same _ 0 (by omega) (half_mem m), card_img]

theorem N_even1 (m : Nat) (hm : 0 < m) : N 1 (2*m) = N 1 m := by
  unfold N
  rw [sub_even m hm, filt_other _ 0 1 (by omega) (by omega)]

theorem N_odd1 (m : Nat) : N 1 (2*m+1) = (subseqs m).card := by
  unfold N
  rw [sub_odd, filt_same _ 1 (by omega) (half_mem m), card_img]

theorem N_odd0 (m : Nat) : N 0 (2*m+1) = N 0 m := by
  unfold N
  rw [sub_odd, filt_other _ 1 0 (by omega) (by omega)]

theorem s_one : s 1 = 1 := by
  unfold s
  rw [Finset.sum_range_one]
  exact f_one 0 rfl rfl

theorem main_LR (n : Nat) : N 1 n = s n ∧ N 0 n = s (n+1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [s_one]
      refine ⟨?_, ?_⟩
      · simp [N, s, subseqs_zero]
      · simp only [N, subseqs_zero]
        rw [Finset.filter_singleton, if_pos rfl, Finset.card_singleton]
    · obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2*m ∨ n = 2*m+1 := ⟨n/2, by omega⟩
      · have hm : 0 < m := by omega
        obtain ⟨a1, a0⟩ := ih m (by omega)
        have c := card_split m
        refine ⟨?_, ?_⟩
        · rw [N_even1 m hm, a1, s_even]
        · rw [N_even0 m hm, s_odd]
          omega
      · obtain ⟨a1, a0⟩ := ih m (by omega)
        have c := card_split m
        refine ⟨?_, ?_⟩
        · rw [N_odd1, s_odd]
          omega
        · rw [N_odd0, a0, show 2*m+1+1 = 2*(m+1) by omega, s_even]

theorem card_eq (n : Nat) : (subseqs n).card = s n + s (n+1) := by
  have h1 := main_LR n
  have h2 := card_split n
  omega

end OMA.OeisA301977

theorem OMA.solution : type_of% @OMA.S_oeis_a301977.main := by
  intro n _
  have h1 := OMA.OeisA301977.card_eq n
  have h2 := OMA.OeisA301977.rhs n
  omega
