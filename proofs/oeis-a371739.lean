import OMAStatements.S_oeis_a371739
import Mathlib

open OMA.S_oeis_a371739

namespace OMA.P_oeis_a371739

def T (N r : ℕ) : ℚ := ∑ k ∈ Finset.range (r + 1), ((N.choose k : ℕ) : ℚ)

theorem T_succ (N r : ℕ) : T (N + 1) r = 2 * T N r - (N.choose r : ℚ) := by
  induction r with
  | zero => simp [T]; norm_num
  | succ r ih =>
    have e1 : T (N + 1) (r + 1) = T (N + 1) r + ((N + 1).choose (r + 1) : ℚ) := by
      simp [T, Finset.sum_range_succ]
    have e2 : T N (r + 1) = T N r + (N.choose (r + 1) : ℚ) := by
      simp [T, Finset.sum_range_succ]
    rw [e1, e2, ih, Nat.choose_succ_succ']
    push_cast; ring

def S (p : ℕ) : ℚ := T (5 * p) p

def b (p : ℕ) : ℚ := ((5 * p).choose p : ℚ)

theorem cR (N k : ℕ) : ((N + 1).choose (k + 1) : ℚ) = (N.choose k : ℚ) * (N + 1) / (k + 1) := by
  have h := Nat.add_one_mul_choose_eq N k
  have h2 : ((N : ℚ) + 1) * (N.choose k : ℚ) = ((N + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1) := by
    exact_mod_cast h
  have : ((k : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

theorem cL (N k : ℕ) (hk : k ≤ N) : ((N + 1).choose k : ℚ) = (N.choose k : ℚ) * (N + 1) / ((N : ℚ) + 1 - k) := by
  have h := Nat.choose_mul_succ_eq N k
  have hc : ((N + 1 - k : ℕ) : ℚ) = (N : ℚ) + 1 - k := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have h2 : (N.choose k : ℚ) * ((N : ℚ) + 1) = ((N + 1).choose k : ℚ) * ((N : ℚ) + 1 - k) := by
    rw [← hc]; exact_mod_cast h
  have : ((N : ℚ) + 1 - k) ≠ 0 := by
    have : (k : ℚ) ≤ N := by exact_mod_cast hk
    linarith
  field_simp; linarith

theorem c0 (p : ℕ) : ((5 * p).choose (p + 1) : ℚ) = b p * (4 * p) / (p + 1) := by
  have h := Nat.choose_succ_right_eq (5 * p) p
  rw [show 5 * p - p = 4 * p by omega] at h
  have h' : ((5 * p).choose (p + 1) : ℚ) * ((p : ℚ) + 1) = b p * (4 * p) := by
    unfold b; exact_mod_cast h
  have : ((p : ℚ) + 1) ≠ 0 := by positivity
  field_simp; linarith

def q2 (x : ℚ) : ℚ := (5 * x + 1) / (x + 1)
def q3 (x : ℚ) : ℚ := q2 x * (5 * x + 2) / (4 * x + 1)
def q4 (x : ℚ) : ℚ := q3 x * (5 * x + 3) / (4 * x + 2)
def q5 (x : ℚ) : ℚ := q4 x * (5 * x + 4) / (4 * x + 3)
def rb (x : ℚ) : ℚ := q5 x * (5 * x + 5) / (4 * x + 4)
def rho (x : ℚ) : ℚ := 16 * (4 * x / (x + 1)) - 8 * q2 x - 4 * q3 x - 2 * q4 x - q5 x

theorem d2 (p : ℕ) : ((5 * p + 1).choose (p + 1) : ℚ) = b p * q2 p := by
  rw [cR]; unfold b q2; push_cast; ring

theorem d3 (p : ℕ) : ((5 * p + 2).choose (p + 1) : ℚ) = b p * q3 p := by
  rw [show 5 * p + 2 = 5 * p + 1 + 1 by ring, cL _ _ (by omega), d2]; unfold q3; push_cast; ring_nf

theorem d4 (p : ℕ) : ((5 * p + 3).choose (p + 1) : ℚ) = b p * q4 p := by
  rw [show 5 * p + 3 = 5 * p + 2 + 1 by ring, cL _ _ (by omega), d3]; unfold q4; push_cast; ring_nf

theorem d5 (p : ℕ) : ((5 * p + 4).choose (p + 1) : ℚ) = b p * q5 p := by
  rw [show 5 * p + 4 = 5 * p + 3 + 1 by ring, cL _ _ (by omega), d4]; unfold q5; push_cast; ring_nf

theorem hb (p : ℕ) : b (p + 1) = b p * rb p := by
  have : b (p + 1) = ((5 * p + 4 + 1).choose (p + 1) : ℚ) := by
    unfold b; rw [show 5 * (p + 1) = 5 * p + 4 + 1 by ring]
  rw [this, cL _ _ (by omega), d5]; unfold rb; push_cast; ring_nf

theorem hS (p : ℕ) : S (p + 1) = 32 * S p + b p * rho p := by
  have e0 : S (p + 1) = T (5 * p + 4 + 1) (p + 1) := by
    unfold S; rw [show 5 * (p + 1) = 5 * p + 4 + 1 by ring]
  have e1 : T (5 * p) (p + 1) = S p + ((5 * p).choose (p + 1) : ℚ) := by
    unfold S T; rw [Finset.sum_range_succ]
  rw [e0, T_succ, show 5 * p + 4 = 5 * p + 3 + 1 by ring, T_succ,
    show 5 * p + 3 = 5 * p + 2 + 1 by ring, T_succ, show 5 * p + 2 = 5 * p + 1 + 1 by ring, T_succ,
    T_succ, e1, c0, show 5 * p + 1 + 1 = 5 * p + 2 by ring, show 5 * p + 2 + 1 = 5 * p + 3 by ring,
    show 5 * p + 3 + 1 = 5 * p + 4 by ring, d2, d3, d4, d5]
  unfold rho
  ring

end OMA.P_oeis_a371739

open OMA.P_oeis_a371739 in
set_option maxRecDepth 100000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a371739.main := by
  intro n hn
  obtain ⟨p, rfl⟩ : ∃ p, n = p + 4 := ⟨n - 4, by omega⟩
  rw [show p + 4 - 1 = p + 3 by omega, show p + 4 - 2 = p + 2 by omega,
    show p + 4 - 3 = p + 1 by omega, show p + 4 - 4 = p by omega]
  have ha : ∀ m, (a m : ℚ) = S m := by
    intro m; unfold a S T; push_cast; rfl
  have key : (2103902836252421940480 * ((p + 4 : ℕ) : ℚ) ^ 5 - 37021748321251963214976 * ((p + 4 : ℕ) : ℚ) ^ 4 + 52245274300233535540464 * ((p + 4 : ℕ) : ℚ) ^ 3 - 23480043061874079141096 * ((p + 4 : ℕ) : ℚ) ^ 2 + 3174927568769374716024 * ((p + 4 : ℕ) : ℚ)) * (a (p + 4) : ℚ)
      + (-18694351328600379422933225 * ((p + 4 : ℕ) : ℚ) ^ 5 + 155058981032814103617032667 * ((p + 4 : ℕ) : ℚ) ^ 4 - 487454816965768347396098663 * ((p + 4 : ℕ) : ℚ) ^ 3 + 737682691899943302169777257 * ((p + 4 : ℕ) : ℚ) ^ 2 - 538092692618460873974733368 * ((p + 4 : ℕ) : ℚ) + 151498699136733259651875780) * (a (p + 3) : ℚ)
      + (2103902836252421940480 * ((p + 4 : ℕ) : ℚ) ^ 5 + 5745608524777638524903431905 * ((p + 4 : ℕ) : ℚ) ^ 4 - 54890001539029046821562285520 * ((p + 4 : ℕ) : ℚ) ^ 3 + 197802684270055615532009522805 * ((p + 4 : ℕ) : ℚ) ^ 2 - 319136595964975834652573838450 * ((p + 4 : ℕ) : ℚ) + 194221027036373854968686122440) * (a (p + 2) : ℚ)
      + (29121980525489377192516581525 * ((p + 4 : ℕ) : ℚ) ^ 5 - 500940400263989908126698094650 * ((p + 4 : ℕ) : ℚ) ^ 4 + 3255231579681848369885366227575 * ((p + 4 : ℕ) : ℚ) ^ 3 - 10183503113297841846553931238450 * ((p + 4 : ℕ) : ℚ) ^ 2 + 15477018686648501749331821423800 * ((p + 4 : ℕ) : ℚ) - 9174626716168568285504095516800) * (a (p + 1) : ℚ)
      + (-321535128897013379298582500000 * ((p + 4 : ℕ) : ℚ) ^ 5 + 5104437105359827761810405000000 * ((p + 4 : ℕ) : ℚ) ^ 4 - 32041912672263748363339455500000 * ((p + 4 : ℕ) : ℚ) ^ 3 + 99174385094450294333858241000000 * ((p + 4 : ℕ) : ℚ) ^ 2 - 150839831505745425291840841568000 * ((p + 4 : ℕ) : ℚ) + 89741413858834882195923801600000) * (a p : ℚ) = 0 := by
    rw [ha, ha, ha, ha, ha]
    have s4 := hS (p + 3)
    have s3 := hS (p + 2)
    have s2 := hS (p + 1)
    have s1 := hS p
    have b3 := hb (p + 2)
    have b2 := hb (p + 1)
    have b1 := hb p
    rw [show p + 3 + 1 = p + 4 from rfl] at s4
    rw [show p + 2 + 1 = p + 3 from rfl] at s3 b3
    rw [show p + 1 + 1 = p + 2 from rfl] at s2 b2
    rw [s4, s3, s2, s1, b3, b2, b1]
    unfold rho rb q5 q4 q3 q2
    push_cast
    have hp : (0 : ℚ) ≤ p := by positivity
    field_simp
    ring
  generalize hq : ((p + 4 : ℕ) : ℤ) = q
  have hq' : ((p + 4 : ℕ) : ℚ) = (q : ℚ) := by rw [← hq]; push_cast; ring
  rw [hq'] at key
  have : (((2103902836252421940480 * q ^ 5 - 37021748321251963214976 * q ^ 4 + 52245274300233535540464 * q ^ 3 - 23480043061874079141096 * q ^ 2 + 3174927568769374716024 * q) * a (p + 4)
      + (-18694351328600379422933225 * q ^ 5 + 155058981032814103617032667 * q ^ 4 - 487454816965768347396098663 * q ^ 3 + 737682691899943302169777257 * q ^ 2 - 538092692618460873974733368 * q + 151498699136733259651875780) * a (p + 3)
      + (2103902836252421940480 * q ^ 5 + 5745608524777638524903431905 * q ^ 4 - 54890001539029046821562285520 * q ^ 3 + 197802684270055615532009522805 * q ^ 2 - 319136595964975834652573838450 * q + 194221027036373854968686122440) * a (p + 2)
      + (29121980525489377192516581525 * q ^ 5 - 500940400263989908126698094650 * q ^ 4 + 3255231579681848369885366227575 * q ^ 3 - 10183503113297841846553931238450 * q ^ 2 + 15477018686648501749331821423800 * q - 9174626716168568285504095516800) * a (p + 1)
      + (-321535128897013379298582500000 * q ^ 5 + 5104437105359827761810405000000 * q ^ 4 - 32041912672263748363339455500000 * q ^ 3 + 99174385094450294333858241000000 * q ^ 2 - 150839831505745425291840841568000 * q + 89741413858834882195923801600000) * a p   : ℤ) : ℚ) = 0 := by
    push_cast
    exact key
  exact_mod_cast this
