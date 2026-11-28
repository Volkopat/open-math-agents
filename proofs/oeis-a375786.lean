import OMAStatements.S_oeis_a375786
import Mathlib

-- Same shortest edge: a smaller second edge gives a smaller volume.
theorem a375786_same (a b c y z : ℕ) (ha : 0 < a) (hbc : b ≤ c) (hby : b ≤ y) (hyz : y ≤ z)
    (hS : a*b+a*c+b*c = a*y+a*z+y*z) : b*c ≤ y*z := by
  have hzc : z ≤ c := by
    by_contra h
    have h' : c < z := Nat.lt_of_not_le h
    have h1 : a*c < a*z := Nat.mul_lt_mul_of_pos_left h' ha
    have h2 : a*b ≤ a*y := Nat.mul_le_mul_left a hby
    have h3 : b*c ≤ y*z := Nat.mul_le_mul hby (Nat.le_of_lt h')
    omega
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hby
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hzc
  have h1 : a*e + b*e = a*d + d*z := by nlinarith [hS]
  have hbz : b ≤ z := by omega
  have hde : d ≤ e := by
    by_contra h
    have h' : e < d := Nat.lt_of_not_le h
    have h2 : a*e < a*d := Nat.mul_lt_mul_of_pos_left h' ha
    have h3 : b*e ≤ z*d := Nat.mul_le_mul hbz (Nat.le_of_lt h')
    have h4 : z*d = d*z := Nat.mul_comm z d
    omega
  have h5 : a*d ≤ a*e := Nat.mul_le_mul_left a hde
  have h6 : b*e ≤ d*z := by omega
  nlinarith [h6]

theorem a375786_two (x y z : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y) (hz : 2 ≤ z) :
    x*y+x*z+y*z ≤ x*y*z + 4 := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hx
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hy
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hz
  nlinarith [Nat.zero_le (p*q*r), Nat.zero_le (p*q), Nat.zero_le (p*r), Nat.zero_le (q*r)]

theorem a375786_one (x y z : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    x*y+x*z+y*z ≤ 2*(x*y*z) + 1 := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hx
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hy
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hz
  nlinarith [Nat.zero_le (p*q*r), Nat.zero_le (p*q), Nat.zero_le (p*r), Nat.zero_le (q*r)]

theorem OMA.solution : type_of% @OMA.S_oeis_a375786.main := by
  intro n hn
  constructor
  · classical
    have hne : ∃ a, ∃ b c, OMA.S_oeis_a375786.admissible n a b c :=
      ⟨n, n, n, hn, le_refl _, le_refl _, by ring⟩
    have h1 : ∃ a, (∃ b c, OMA.S_oeis_a375786.admissible n a b c) ∧
        ∀ a', (∃ b c, OMA.S_oeis_a375786.admissible n a' b c) → a ≤ a' :=
      ⟨Nat.find hne, Nat.find_spec hne, fun a' h => Nat.find_min' hne h⟩
    obtain ⟨a, ⟨b0, c0, h0⟩, hamin⟩ := h1
    have hne2 : ∃ b, ∃ c, OMA.S_oeis_a375786.admissible n a b c := ⟨b0, c0, h0⟩
    have h2 : ∃ b, (∃ c, OMA.S_oeis_a375786.admissible n a b c) ∧
        ∀ b', (∃ c, OMA.S_oeis_a375786.admissible n a b' c) → b ≤ b' :=
      ⟨Nat.find hne2, Nat.find_spec hne2, fun b' h => Nat.find_min' hne2 h⟩
    obtain ⟨b, ⟨c, hc⟩, hbmin⟩ := h2
    refine ⟨a, b, c, hc, ?_⟩
    intro x y z hxyz
    have hax : a ≤ x := hamin x ⟨y, z, hxyz⟩
    rcases Nat.lt_or_eq_of_le hax with h | h
    · left; exact h
    · right
      subst h
      exact ⟨rfl, hbmin y ⟨z, hxyz⟩⟩
  · intro a b c habc hleast x y z hxyz
    have hxyz' := hxyz
    obtain ⟨ha, hab, hbc, he⟩ := habc
    obtain ⟨hx, hxy, hyz, he'⟩ := hxyz
    have hS : a*b+a*c+b*c = x*y+x*z+y*z := by omega
    rcases hleast x y z hxyz' with hlt | ⟨hax, hby⟩
    · have h2 := a375786_two x y z (by omega) (by omega) (by omega)
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨k, hk⟩
      · obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
        have hadm : OMA.S_oeis_a375786.admissible n 2 2 (3*j^2+6*j+2) := by
          refine ⟨by omega, le_refl _, by omega, ?_⟩
          rw [hm, hj]; ring
        have hn2 : n^2 = 4*(m*m) := by rw [hm]; ring
        rcases hleast 2 2 _ hadm with h | ⟨h, hb2⟩
        · have ha1 : a = 1 := by omega
          subst ha1
          simp only [one_mul] at he hS ⊢
          have hb : 2 ≤ b := by
            by_contra hb
            have hb1 : b = 1 := by omega
            subst hb1
            simp only [one_mul] at he
            omega
          omega
        · have hb : b = 2 := by omega
          subst h
          subst hb
          omega
      · have hadm : OMA.S_oeis_a375786.admissible n 1 1 (6*k^2+6*k+1) := by
          refine ⟨by omega, le_refl _, by omega, ?_⟩
          rw [hk]; ring
        have h1 := a375786_one x y z (by omega) (by omega) (by omega)
        rcases hleast 1 1 _ hadm with h | ⟨h, hb1⟩
        · omega
        · have hb : b = 1 := by omega
          subst h
          subst hb
          simp only [one_mul] at hS ⊢
          omega
    · rw [← hax] at hS ⊢
      have h := a375786_same a b c y z ha hbc hby hyz hS
      calc a*b*c = a*(b*c) := by ring
        _ ≤ a*(y*z) := Nat.mul_le_mul_left a h
        _ = a*y*z := by ring
