import OMAReductions.R_Buchi_buchi_problem_M5_R1

/-!
# Proof of `Buchi.buchi_problem_M5.R1.H1`

Proves that no nontrivial Büchi sequence of length 5 exists with `1 ≤ x ≤ 10^6`, `a < 0`, and
`100800 ∣ a`.

Given nonnegative integer roots `y₀, y₁, y₂, y₃, y₄` with `y_n^2 = (x + n)^2 + a`, we factor
`2 * x + 1 = y₁^2 - y₀^2 = d * e` with `d = y₁ - y₀` and `e = y₁ + y₀`. Then `d` and `e` are
odd, `3 ≤ d ≤ e`, `d ≤ 1413`, and `4 * (-a) = (d^2 - 1) * (e^2 - 1)`. From `100800 ∣ a` we
deduce `403200 ∣ (d^2 - 1) * (e^2 - 1)`, so `M = 403200 / gcd(403200, d^2 - 1)` divides
`e^2 - 1`. Using a precomputed Chinese Remainder Theorem lift for `50400 = 32 * 9 * 25 * 7`,
we enumerate every surviving arithmetic progression of `(d, e)` and verify by kernel reduction
that at least one of `y₂^2, y₃^2, y₄^2` fails a quadratic residue check modulo one of the
12 small moduli `16, 9, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37`.
-/

namespace BuchiM5R1H1Proof

private def nonSqMask (m mask v : ℕ) : Bool :=
  (mask / 2 ^ (v % m)) % 2 == 0

private def notSq3 (m mask a b c : ℕ) : Bool :=
  nonSqMask m mask a || nonSqMask m mask b || nonSqMask m mask c

private def checkCandidate (d e : ℕ) : Bool :=
  let x := (d * e - 1) / 2
  let y0 := (e - d) / 2
  let y0sq := y0 * y0
  let y2 := y0sq + 4 * x + 4
  let y3 := y0sq + 6 * x + 9
  let y4 := y0sq + 8 * x + 16
  notSq3 16 531 y2 y3 y4 ||
  notSq3 9 147 y2 y3 y4 ||
  notSq3 5 19 y2 y3 y4 ||
  notSq3 7 23 y2 y3 y4 ||
  notSq3 11 571 y2 y3 y4 ||
  notSq3 13 5659 y2 y3 y4 ||
  notSq3 17 107287 y2 y3 y4 ||
  notSq3 19 199411 y2 y3 y4 ||
  notSq3 23 340831 y2 y3 y4 ||
  notSq3 29 332473075 y2 y3 y4 ||
  notSq3 31 303908791 y2 y3 y4 ||
  notSq3 37 96068509339 y2 y3 y4

private def roots2 : ℕ → List ℕ
  | 1 => [0]
  | 2 => [1]
  | 4 => [1, 3]
  | 8 => [1, 3, 5, 7]
  | 16 => [1, 7, 9, 15]
  | 32 => [1, 15, 17, 31]
  | _ => []

private def roots3 : ℕ → List ℕ
  | 1 => [0]
  | 3 => [1, 2]
  | 9 => [1, 8]
  | _ => []

private def roots5 : ℕ → List ℕ
  | 1 => [0]
  | 5 => [1, 4]
  | 25 => [1, 24]
  | _ => []

private def roots7 : ℕ → List ℕ
  | 1 => [0]
  | 7 => [1, 6]
  | _ => []

private def crtLift (M a2 a3 a5 a7 : ℕ) : ℕ :=
  (a2 * 36225 + a3 * 28000 + a5 * 22176 + a7 * 14400) % M

private def crtRoots (M : ℕ) : List ℕ :=
  let r2 := roots2 (Nat.gcd M 32)
  let r3 := roots3 (Nat.gcd M 9)
  let r5 := roots5 (Nat.gcd M 25)
  let r7 := roots7 (Nat.gcd M 7)
  r2.flatMap fun a2 =>
    r3.flatMap fun a3 =>
      r5.flatMap fun a5 =>
        r7.map fun a7 => crtLift M a2 a3 a5 a7


private def checkAP (d M e : ℕ) : ℕ → Bool
  | 0 => true
  | steps + 1 =>
    (if e % 2 == 1 then checkCandidate d e else true) && checkAP d M (e + M) steps

private def firstE (d M r : ℕ) : ℕ :=
  if d ≤ r then r else r + ((d - r + M - 1) / M) * M

private def checkForRoot (d M emax r : ℕ) : Bool :=
  if firstE d M r ≤ emax then
    checkAP d M (firstE d M r) ((emax - firstE d M r) / M + 1)
  else
    true

private def bigM (d : ℕ) : ℕ := 403200 / Nat.gcd 403200 (d * d - 1)

private def checkD (d : ℕ) : Bool :=
  (crtRoots (bigM d)).all (checkForRoot d (bigM d) (2000001 / d))

private def checkRange (start : ℕ) : ℕ → Bool
  | 0 => true
  | count + 1 => checkD (2 * start + 3) && checkRange (start + 1) count

private lemma nonSqMask_sound {m mask : ℕ} (hm : 0 < m)
    (hmask : ∀ r : Fin m, nonSqMask m mask ((r.val * r.val) % m) = false)
    {v : ℕ} (hv : nonSqMask m mask v = true) (y : ℕ) : y * y ≠ v := by
  intro hy
  subst hy
  have h1 : (y * y) % m = ((y % m) * (y % m)) % m := Nat.mul_mod y y m
  have h2 := hmask ⟨y % m, Nat.mod_lt y hm⟩
  unfold nonSqMask at hv h2
  rw [h1] at hv
  rw [Nat.mod_mod] at h2
  exact Bool.false_ne_true (h2.symm.trans hv)

private lemma notSq3_sound {m mask : ℕ} (hm : 0 < m)
    (hmask : ∀ r : Fin m, nonSqMask m mask ((r.val * r.val) % m) = false)
    {a b c : ℕ} (h : notSq3 m mask a b c = true) (ya yb yc : ℕ) :
    ¬ (ya * ya = a ∧ yb * yb = b ∧ yc * yc = c) := by
  rintro ⟨ha, hb, hc⟩
  unfold notSq3 at h
  simp only [Bool.or_eq_true] at h
  rcases h with (h1 | h2) | h3
  · exact nonSqMask_sound hm hmask h1 ya ha
  · exact nonSqMask_sound hm hmask h2 yb hb
  · exact nonSqMask_sound hm hmask h3 yc hc

private lemma mask16_ok : ∀ r : Fin 16, nonSqMask 16 531 ((r.val * r.val) % 16) = false := by
  decide
private lemma mask9_ok : ∀ r : Fin 9, nonSqMask 9 147 ((r.val * r.val) % 9) = false := by
  decide
private lemma mask5_ok : ∀ r : Fin 5, nonSqMask 5 19 ((r.val * r.val) % 5) = false := by
  decide
private lemma mask7_ok : ∀ r : Fin 7, nonSqMask 7 23 ((r.val * r.val) % 7) = false := by
  decide
private lemma mask11_ok : ∀ r : Fin 11, nonSqMask 11 571 ((r.val * r.val) % 11) = false := by
  decide
private lemma mask13_ok : ∀ r : Fin 13, nonSqMask 13 5659 ((r.val * r.val) % 13) = false := by
  decide
private lemma mask17_ok : ∀ r : Fin 17, nonSqMask 17 107287 ((r.val * r.val) % 17) = false := by
  decide
private lemma mask19_ok : ∀ r : Fin 19, nonSqMask 19 199411 ((r.val * r.val) % 19) = false := by
  decide
private lemma mask23_ok : ∀ r : Fin 23, nonSqMask 23 340831 ((r.val * r.val) % 23) = false := by
  decide
private lemma mask29_ok :
    ∀ r : Fin 29, nonSqMask 29 332473075 ((r.val * r.val) % 29) = false := by
  decide
private lemma mask31_ok :
    ∀ r : Fin 31, nonSqMask 31 303908791 ((r.val * r.val) % 31) = false := by
  decide
private lemma mask37_ok :
    ∀ r : Fin 37, nonSqMask 37 96068509339 ((r.val * r.val) % 37) = false := by
  decide

private lemma checkCandidate_sound {d e y2 y3 y4 : ℕ}
    (hcheck : checkCandidate d e = true)
    (h2 : y2 * y2 = ((e - d) / 2) * ((e - d) / 2) + 4 * ((d * e - 1) / 2) + 4)
    (h3 : y3 * y3 = ((e - d) / 2) * ((e - d) / 2) + 6 * ((d * e - 1) / 2) + 9)
    (h4 : y4 * y4 = ((e - d) / 2) * ((e - d) / 2) + 8 * ((d * e - 1) / 2) + 16) :
    False := by
  unfold checkCandidate at hcheck
  dsimp only at hcheck
  simp only [Bool.or_eq_true] at hcheck
  have htriple := And.intro h2 (And.intro h3 h4)
  rcases hcheck with (((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · exact notSq3_sound (by decide) mask16_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask9_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask5_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask7_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask11_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask13_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask17_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask19_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask23_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask29_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask31_ok h y2 y3 y4 htriple
  · exact notSq3_sound (by decide) mask37_ok h y2 y3 y4 htriple

private lemma dvd_32_mem : ∀ m : Fin 33, m.val ∣ 32 → m.val ∈ ([1, 2, 4, 8, 16, 32] : List ℕ) := by
  decide
private lemma dvd_9_mem : ∀ m : Fin 10, m.val ∣ 9 → m.val ∈ ([1, 3, 9] : List ℕ) := by
  decide
private lemma dvd_25_mem : ∀ m : Fin 26, m.val ∣ 25 → m.val ∈ ([1, 5, 25] : List ℕ) := by
  decide
private lemma dvd_7_mem : ∀ m : Fin 8, m.val ∣ 7 → m.val ∈ ([1, 7] : List ℕ) := by
  decide

private lemma roots2_complete :
    ∀ m ∈ ([1, 2, 4, 8, 16, 32] : List ℕ), ∀ r : Fin m,
      (r.val * r.val) % m = 1 % m → r.val ∈ roots2 m := by
  decide
private lemma roots3_complete :
    ∀ m ∈ ([1, 3, 9] : List ℕ), ∀ r : Fin m,
      (r.val * r.val) % m = 1 % m → r.val ∈ roots3 m := by
  decide
private lemma roots5_complete :
    ∀ m ∈ ([1, 5, 25] : List ℕ), ∀ r : Fin m,
      (r.val * r.val) % m = 1 % m → r.val ∈ roots5 m := by
  decide
private lemma roots7_complete :
    ∀ m ∈ ([1, 7] : List ℕ), ∀ r : Fin m,
      (r.val * r.val) % m = 1 % m → r.val ∈ roots7 m := by
  decide

set_option maxHeartbeats 0 in
private lemma M_decomp :
    ∀ j : Fin 706, 0 < bigM (2 * j.val + 3) ∧
      Nat.gcd (bigM (2 * j.val + 3)) 32 * Nat.gcd (bigM (2 * j.val + 3)) 9 *
        Nat.gcd (bigM (2 * j.val + 3)) 25 * Nat.gcd (bigM (2 * j.val + 3)) 7 =
          bigM (2 * j.val + 3) := by
  decide +kernel

private lemma mod_sq_eq_one_of_dvd {m e : ℕ} (he : 1 ≤ e) (hdvd : m ∣ e * e - 1) :
    ((e % m) * (e % m)) % m = 1 % m := by
  have h1 : 1 ≤ e * e := Nat.mul_le_mul he he
  have h2 : e * e % m = 1 % m := by
    obtain ⟨k, hk⟩ := hdvd
    have heq : e * e = 1 + m * k := by omega
    rw [heq, Nat.add_mul_mod_self_left]
  rw [← Nat.mul_mod, h2]

private lemma crtLift_eq_mod {M e : ℕ}
    (hM : Nat.gcd M 32 * Nat.gcd M 9 * Nat.gcd M 25 * Nat.gcd M 7 = M) :
    crtLift M (e % Nat.gcd M 32) (e % Nat.gcd M 9) (e % Nat.gcd M 25) (e % Nat.gcd M 7) =
      e % M := by
  set m2 := Nat.gcd M 32
  set m3 := Nat.gcd M 9
  set m5 := Nat.gcd M 25
  set m7 := Nat.gcd M 7
  have hm2 : m2 ∣ 32 := Nat.gcd_dvd_right M 32
  have hm3 : m3 ∣ 9 := Nat.gcd_dvd_right M 9
  have hm5 : m5 ∣ 25 := Nat.gcd_dvd_right M 25
  have hm7 : m7 ∣ 7 := Nat.gcd_dvd_right M 7
  change (e % m2 * 36225 + e % m3 * 28000 + e % m5 * 22176 + e % m7 * 14400) ≡ e [MOD M]
  set L := e % m2 * 36225 + e % m3 * 28000 + e % m5 * 22176 + e % m7 * 14400
  have hL2 : L ≡ e [MOD m2] := by
    have c1 : 36225 ≡ 1 [MOD m2] := Nat.ModEq.of_dvd hm2 (by decide)
    have c2 : 28000 ≡ 0 [MOD m2] := Nat.ModEq.of_dvd hm2 (by decide)
    have c3 : 22176 ≡ 0 [MOD m2] := Nat.ModEq.of_dvd hm2 (by decide)
    have c4 : 14400 ≡ 0 [MOD m2] := Nat.ModEq.of_dvd hm2 (by decide)
    have hsum : L ≡ e % m2 * 1 + e % m3 * 0 + e % m5 * 0 + e % m7 * 0 [MOD m2] :=
      (((Nat.ModEq.mul_left _ c1).add (Nat.ModEq.mul_left _ c2)).add
        (Nat.ModEq.mul_left _ c3)).add (Nat.ModEq.mul_left _ c4)
    have hrhs : e % m2 * 1 + e % m3 * 0 + e % m5 * 0 + e % m7 * 0 = e % m2 := by ring
    rw [hrhs] at hsum
    exact hsum.trans (Nat.mod_modEq e m2)
  have hL3 : L ≡ e [MOD m3] := by
    have c1 : 36225 ≡ 0 [MOD m3] := Nat.ModEq.of_dvd hm3 (by decide)
    have c2 : 28000 ≡ 1 [MOD m3] := Nat.ModEq.of_dvd hm3 (by decide)
    have c3 : 22176 ≡ 0 [MOD m3] := Nat.ModEq.of_dvd hm3 (by decide)
    have c4 : 14400 ≡ 0 [MOD m3] := Nat.ModEq.of_dvd hm3 (by decide)
    have hsum : L ≡ e % m2 * 0 + e % m3 * 1 + e % m5 * 0 + e % m7 * 0 [MOD m3] :=
      (((Nat.ModEq.mul_left _ c1).add (Nat.ModEq.mul_left _ c2)).add
        (Nat.ModEq.mul_left _ c3)).add (Nat.ModEq.mul_left _ c4)
    have hrhs : e % m2 * 0 + e % m3 * 1 + e % m5 * 0 + e % m7 * 0 = e % m3 := by ring
    rw [hrhs] at hsum
    exact hsum.trans (Nat.mod_modEq e m3)
  have hL5 : L ≡ e [MOD m5] := by
    have c1 : 36225 ≡ 0 [MOD m5] := Nat.ModEq.of_dvd hm5 (by decide)
    have c2 : 28000 ≡ 0 [MOD m5] := Nat.ModEq.of_dvd hm5 (by decide)
    have c3 : 22176 ≡ 1 [MOD m5] := Nat.ModEq.of_dvd hm5 (by decide)
    have c4 : 14400 ≡ 0 [MOD m5] := Nat.ModEq.of_dvd hm5 (by decide)
    have hsum : L ≡ e % m2 * 0 + e % m3 * 0 + e % m5 * 1 + e % m7 * 0 [MOD m5] :=
      (((Nat.ModEq.mul_left _ c1).add (Nat.ModEq.mul_left _ c2)).add
        (Nat.ModEq.mul_left _ c3)).add (Nat.ModEq.mul_left _ c4)
    have hrhs : e % m2 * 0 + e % m3 * 0 + e % m5 * 1 + e % m7 * 0 = e % m5 := by ring
    rw [hrhs] at hsum
    exact hsum.trans (Nat.mod_modEq e m5)
  have hL7 : L ≡ e [MOD m7] := by
    have c1 : 36225 ≡ 0 [MOD m7] := Nat.ModEq.of_dvd hm7 (by decide)
    have c2 : 28000 ≡ 0 [MOD m7] := Nat.ModEq.of_dvd hm7 (by decide)
    have c3 : 22176 ≡ 0 [MOD m7] := Nat.ModEq.of_dvd hm7 (by decide)
    have c4 : 14400 ≡ 1 [MOD m7] := Nat.ModEq.of_dvd hm7 (by decide)
    have hsum : L ≡ e % m2 * 0 + e % m3 * 0 + e % m5 * 0 + e % m7 * 1 [MOD m7] :=
      (((Nat.ModEq.mul_left _ c1).add (Nat.ModEq.mul_left _ c2)).add
        (Nat.ModEq.mul_left _ c3)).add (Nat.ModEq.mul_left _ c4)
    have hrhs : e % m2 * 0 + e % m3 * 0 + e % m5 * 0 + e % m7 * 1 = e % m7 := by ring
    rw [hrhs] at hsum
    exact hsum.trans (Nat.mod_modEq e m7)
  have hcop23 : Nat.Coprime m2 m3 :=
    (by decide : Nat.Coprime 32 9).coprime_dvd_left hm2 |>.coprime_dvd_right hm3
  have hcop23_5 : Nat.Coprime (m2 * m3) m5 :=
    ((by decide : Nat.Coprime (32 * 9) 25).coprime_dvd_left (mul_dvd_mul hm2 hm3)).coprime_dvd_right
      hm5
  have hcop235_7 : Nat.Coprime (m2 * m3 * m5) m7 :=
    ((by decide : Nat.Coprime (32 * 9 * 25) 7).coprime_dvd_left
      (mul_dvd_mul (mul_dvd_mul hm2 hm3) hm5)).coprime_dvd_right hm7
  have hL23 : L ≡ e [MOD m2 * m3] := (Nat.modEq_and_modEq_iff_modEq_mul hcop23).mp ⟨hL2, hL3⟩
  have hL235 : L ≡ e [MOD m2 * m3 * m5] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop23_5).mp ⟨hL23, hL5⟩
  have hL2357 : L ≡ e [MOD m2 * m3 * m5 * m7] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop235_7).mp ⟨hL235, hL7⟩
  rwa [hM] at hL2357

private lemma mod_mem_crtRoots {M e : ℕ} (hM_pos : 0 < M) (he : 1 ≤ e)
    (hM_eq : Nat.gcd M 32 * Nat.gcd M 9 * Nat.gcd M 25 * Nat.gcd M 7 = M)
    (hdvd : M ∣ e * e - 1) : e % M ∈ crtRoots M := by
  set m2 := Nat.gcd M 32
  set m3 := Nat.gcd M 9
  set m5 := Nat.gcd M 25
  set m7 := Nat.gcd M 7
  have hm2_pos : 0 < m2 := Nat.gcd_pos_of_pos_left 32 hM_pos
  have hm3_pos : 0 < m3 := Nat.gcd_pos_of_pos_left 9 hM_pos
  have hm5_pos : 0 < m5 := Nat.gcd_pos_of_pos_left 25 hM_pos
  have hm7_pos : 0 < m7 := Nat.gcd_pos_of_pos_left 7 hM_pos
  have hm2_le : m2 ≤ 32 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right M 32)
  have hm3_le : m3 ≤ 9 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right M 9)
  have hm5_le : m5 ≤ 25 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right M 25)
  have hm7_le : m7 ≤ 7 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right M 7)
  have hm2_mem : m2 ∈ ([1, 2, 4, 8, 16, 32] : List ℕ) :=
    dvd_32_mem ⟨m2, by omega⟩ (Nat.gcd_dvd_right M 32)
  have hm3_mem : m3 ∈ ([1, 3, 9] : List ℕ) :=
    dvd_9_mem ⟨m3, by omega⟩ (Nat.gcd_dvd_right M 9)
  have hm5_mem : m5 ∈ ([1, 5, 25] : List ℕ) :=
    dvd_25_mem ⟨m5, by omega⟩ (Nat.gcd_dvd_right M 25)
  have hm7_mem : m7 ∈ ([1, 7] : List ℕ) :=
    dvd_7_mem ⟨m7, by omega⟩ (Nat.gcd_dvd_right M 7)
  have hr2 : e % m2 ∈ roots2 m2 :=
    roots2_complete m2 hm2_mem ⟨e % m2, Nat.mod_lt e hm2_pos⟩
      (mod_sq_eq_one_of_dvd he ((Nat.gcd_dvd_left M 32).trans hdvd))
  have hr3 : e % m3 ∈ roots3 m3 :=
    roots3_complete m3 hm3_mem ⟨e % m3, Nat.mod_lt e hm3_pos⟩
      (mod_sq_eq_one_of_dvd he ((Nat.gcd_dvd_left M 9).trans hdvd))
  have hr5 : e % m5 ∈ roots5 m5 :=
    roots5_complete m5 hm5_mem ⟨e % m5, Nat.mod_lt e hm5_pos⟩
      (mod_sq_eq_one_of_dvd he ((Nat.gcd_dvd_left M 25).trans hdvd))
  have hr7 : e % m7 ∈ roots7 m7 :=
    roots7_complete m7 hm7_mem ⟨e % m7, Nat.mod_lt e hm7_pos⟩
      (mod_sq_eq_one_of_dvd he ((Nat.gcd_dvd_left M 7).trans hdvd))
  rw [← crtLift_eq_mod hM_eq]
  unfold crtRoots
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨e % m2, hr2, e % m3, hr3, e % m5, hr5, e % m7, hr7, rfl⟩


private lemma checkAP_sound (d M : ℕ) :
    ∀ (steps e t : ℕ), checkAP d M e steps = true → t < steps →
      (e + t * M) % 2 = 1 → checkCandidate d (e + t * M) = true
  | 0, _, _, _, ht, _ => (Nat.not_lt_zero _ ht).elim
  | steps + 1, e, 0, h, _, hodd => by
    simp only [checkAP, Bool.and_eq_true] at h
    have hodd' : (e % 2 == 1) = true := by simpa using hodd
    have h1 := h.1
    rw [if_pos hodd'] at h1
    simpa using h1
  | steps + 1, e, t + 1, h, ht, hodd => by
    simp only [checkAP, Bool.and_eq_true] at h
    have hrec := checkAP_sound d M steps (e + M) t h.2 (by omega)
    have heq : e + M + t * M = e + (t + 1) * M := by ring
    rw [heq] at hrec
    exact hrec hodd

private lemma firstE_spec {d M r q : ℕ} (hM : 0 < M) (hde : d ≤ r + q * M) :
    ∃ t : ℕ, firstE d M r + t * M = r + q * M := by
  unfold firstE
  split_ifs with hdr
  · exact ⟨q, rfl⟩
  · have hlt : (d - r + M - 1) / M < q + 1 := by
      rw [Nat.div_lt_iff_lt_mul hM, Nat.add_mul, Nat.one_mul]
      omega
    refine ⟨q - (d - r + M - 1) / M, ?_⟩
    rw [Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_of_le (Nat.lt_succ_iff.mp hlt)]

private lemma checkForRoot_sound {d M emax e : ℕ} (hM : 0 < M)
    (hcheck : checkForRoot d M emax (e % M) = true)
    (hde : d ≤ e) (hemax : e ≤ emax) (hodd : e % 2 = 1) :
    checkCandidate d e = true := by
  have he : e % M + e / M * M = e := by
    rw [Nat.mul_comm]
    exact Nat.mod_add_div e M
  obtain ⟨t, ht⟩ := firstE_spec (d := d) hM (by rw [he]; exact hde)
  rw [he] at ht
  unfold checkForRoot at hcheck
  generalize firstE d M (e % M) = e0 at hcheck ht
  have he0 : e0 ≤ emax := by omega
  rw [if_pos he0] at hcheck
  have ht_lt : t < (emax - e0) / M + 1 := by
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hM]
    omega
  have hcand := checkAP_sound d M _ e0 t hcheck ht_lt (by rw [ht]; exact hodd)
  rwa [ht] at hcand

private lemma checkRange_sound :
    ∀ (count start j : ℕ), checkRange start count = true →
      start ≤ j → j < start + count → checkD (2 * j + 3) = true
  | 0, _, _, _, h1, h2 => by omega
  | count + 1, start, j, h, h1, h2 => by
    simp only [checkRange, Bool.and_eq_true] at h
    by_cases hj : j = start
    · subst hj
      exact h.1
    · exact checkRange_sound count (start + 1) j h.2 (by omega) (by omega)

private lemma checkRange_append {s a b : ℕ} (h1 : checkRange s a = true)
    (h2 : checkRange (s + a) b = true) : checkRange s (a + b) = true := by
  induction a generalizing s with
  | zero => simpa using h2
  | succ n ih =>
    rw [show n + 1 + b = (n + b) + 1 by omega]
    simp only [checkRange, Bool.and_eq_true] at h1 ⊢
    exact ⟨h1.1, ih h1.2 (by rw [show s + 1 + n = s + (n + 1) by omega]; exact h2)⟩

set_option maxHeartbeats 0 in
private lemma chunk1 : checkRange 0 10 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma chunk2 : checkRange 10 20 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma chunk3 : checkRange 30 30 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma chunk4 : checkRange 60 40 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma chunk5 : checkRange 100 80 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma chunk6 : checkRange 180 120 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma chunk7 : checkRange 300 150 = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private lemma chunk8 : checkRange 450 256 = true := by
  decide +kernel

private lemma checkAll_ok : checkRange 0 706 = true :=
  checkRange_append (a := 10) (b := 696) chunk1 <|
    checkRange_append (a := 20) (b := 676) chunk2 <|
      checkRange_append (a := 30) (b := 646) chunk3 <|
        checkRange_append (a := 40) (b := 606) chunk4 <|
          checkRange_append (a := 80) (b := 526) chunk5 <|
            checkRange_append (a := 120) (b := 406) chunk6 <|
              checkRange_append (a := 150) (b := 256) chunk7 chunk8

/-- The arithmetic core: every admissible factor pair `(d, e)` passes `checkCandidate`. -/
private lemma key {d e : ℕ} (hd3 : 3 ≤ d) (hd1413 : d ≤ 1413) (hde : d ≤ e)
    (he_odd : e % 2 = 1) (hemax : e ≤ 2000001 / d)
    (hdvd : 403200 ∣ (d * d - 1) * (e * e - 1)) (hd_odd : d % 2 = 1) :
    checkCandidate d e = true := by
  obtain ⟨j, rfl⟩ : ∃ j, d = 2 * j + 3 := ⟨(d - 3) / 2, by omega⟩
  have hj_lt : j < 706 := by omega
  have hMd := M_decomp ⟨j, hj_lt⟩
  have hM_pos : 0 < bigM (2 * j + 3) := hMd.1
  have hM_decomp : Nat.gcd (bigM (2 * j + 3)) 32 * Nat.gcd (bigM (2 * j + 3)) 9 *
      Nat.gcd (bigM (2 * j + 3)) 25 * Nat.gcd (bigM (2 * j + 3)) 7 = bigM (2 * j + 3) := hMd.2
  have hM_dvd_e : bigM (2 * j + 3) ∣ e * e - 1 := by
    have hg_pos : 0 < Nat.gcd 403200 ((2 * j + 3) * (2 * j + 3) - 1) :=
      Nat.gcd_pos_of_pos_left _ (by decide)
    have hg1 := Nat.gcd_dvd_left 403200 ((2 * j + 3) * (2 * j + 3) - 1)
    have hg2 := Nat.gcd_dvd_right 403200 ((2 * j + 3) * (2 * j + 3) - 1)
    have hcop := Nat.coprime_div_gcd_div_gcd hg_pos
    unfold bigM
    set g := Nat.gcd 403200 ((2 * j + 3) * (2 * j + 3) - 1)
    have hmul_dvd : g * (403200 / g) ∣ g * (((2 * j + 3) * (2 * j + 3) - 1) / g * (e * e - 1)) := by
      rw [Nat.mul_div_cancel' hg1, ← mul_assoc, Nat.mul_div_cancel' hg2]
      exact hdvd
    have hM_dvd_mul := (mul_dvd_mul_iff_left (Nat.ne_of_gt hg_pos)).mp hmul_dvd
    exact hcop.dvd_of_dvd_mul_left hM_dvd_mul
  have hcheckD : checkD (2 * j + 3) = true :=
    checkRange_sound 706 0 j checkAll_ok (Nat.zero_le j) (by omega)
  have hmem := mod_mem_crtRoots hM_pos (by omega) hM_decomp hM_dvd_e
  unfold checkD at hcheckD
  exact checkForRoot_sound hM_pos (List.all_eq_true.mp hcheckD _ hmem) hde hemax he_odd

end BuchiM5R1H1Proof

open BuchiM5R1H1Proof in
theorem OMA.solution : OMA.R_Buchi_buchi_problem_M5_R1.H1 := by
  intro x a hx1 hx2 ha_neg ha_dvd _ hsq
  have hx2' : x ≤ 1000000 := by norm_num at hx2; exact hx2
  have get_root : ∀ n ∈ Finset.range 5, ∃ y : ℕ, (y : ℤ) ^ 2 = ((x : ℤ) + n) ^ 2 + a := by
    intro n hn
    obtain ⟨r, hr⟩ := hsq n hn
    exact ⟨r.natAbs, by rw [Int.natAbs_sq, sq]; exact hr.symm⟩
  obtain ⟨y0, hy0⟩ := get_root 0 (by simp)
  obtain ⟨y1, hy1⟩ := get_root 1 (by simp)
  obtain ⟨y2, hy2⟩ := get_root 2 (by simp)
  obtain ⟨y3, hy3⟩ := get_root 3 (by simp)
  obtain ⟨y4, hy4⟩ := get_root 4 (by simp)
  simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at hy0 hy1 hy2 hy3 hy4
  have hlt : y0 < y1 := by
    by_contra h
    have h' : (y1 : ℤ) ≤ y0 := by exact_mod_cast not_lt.mp h
    have h'' : (y1 : ℤ) * y1 ≤ y0 * y0 := mul_self_le_mul_self (by positivity) h'
    nlinarith
  obtain ⟨d, rfl⟩ : ∃ d, y1 = y0 + d := ⟨y1 - y0, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, e = 2 * y0 + d := ⟨_, rfl⟩
  have heZ : (e : ℤ) = 2 * y0 + d := by rw [he]; push_cast; ring
  push_cast at hy1
  have hZ : (d : ℤ) * e = 2 * x + 1 := by
    rw [heZ]
    linear_combination hy1 - hy0
  have hN : d * e = 2 * x + 1 := by exact_mod_cast hZ
  have hodd : Odd (d * e) := ⟨x, hN⟩
  obtain ⟨hdo, heo⟩ := Nat.odd_mul.mp hodd
  have hd_odd : d % 2 = 1 := Nat.odd_iff.mp hdo
  have he_odd : e % 2 = 1 := Nat.odd_iff.mp heo
  have hd1 : d ≠ 1 := by
    rintro rfl
    have hyx : y0 = x := by omega
    subst hyx
    linarith
  have hd3 : 3 ≤ d := by omega
  have hde : d ≤ e := by omega
  have hd1413 : d ≤ 1413 := by
    by_contra hgt
    have h1 : 1415 ≤ d := by omega
    have h2 : 1415 * 1415 ≤ d * d := Nat.mul_le_mul h1 h1
    have h3 : d * d ≤ d * e := Nat.mul_le_mul_left d hde
    omega
  have hemax : e ≤ 2000001 / d := by
    refine (Nat.le_div_iff_mul_le (by omega)).mpr ?_
    rw [Nat.mul_comm]
    omega
  have hdvd : 403200 ∣ (d * d - 1) * (e * e - 1) := by
    have h4a : 4 * (-a) = ((d : ℤ) ^ 2 - 1) * ((e : ℤ) ^ 2 - 1) := by
      rw [heZ]
      have hZ' : (d : ℤ) * (2 * y0 + d) = 2 * x + 1 := by rw [← heZ]; exact hZ
      linear_combination 4 * hy0 - ((d : ℤ) * (2 * y0 + d) + 2 * x - 1) * hZ'
    have hd1' : 1 ≤ d * d := Nat.mul_le_mul (by omega : 1 ≤ d) (by omega : 1 ≤ d)
    have he1' : 1 ≤ e * e := Nat.mul_le_mul (by omega : 1 ≤ e) (by omega : 1 ≤ e)
    have hcast : (((d * d - 1) * (e * e - 1) : ℕ) : ℤ) =
        ((d : ℤ) ^ 2 - 1) * ((e : ℤ) ^ 2 - 1) := by
      rw [Nat.cast_mul, Nat.cast_sub hd1', Nat.cast_sub he1', Nat.cast_mul, Nat.cast_mul,
        Nat.cast_one]
      ring
    have hdvdZ : ((403200 : ℕ) : ℤ) ∣ (((d * d - 1) * (e * e - 1) : ℕ) : ℤ) := by
      obtain ⟨k, hk⟩ := ha_dvd
      refine ⟨-k, ?_⟩
      rw [hcast, ← h4a, hk]
      push_cast
      ring
    exact Int.natCast_dvd_natCast.mp hdvdZ
  have hcand := key hd3 hd1413 hde he_odd hemax hdvd hd_odd
  have hx_eq : (d * e - 1) / 2 = x := by omega
  have hy0_eq : (e - d) / 2 = y0 := by omega
  have h2 : y2 * y2 = y0 * y0 + 4 * x + 4 := by
    have h : (y2 : ℤ) * y2 = y0 * y0 + 4 * x + 4 := by linear_combination hy2 - hy0
    exact_mod_cast h
  have h3 : y3 * y3 = y0 * y0 + 6 * x + 9 := by
    have h : (y3 : ℤ) * y3 = y0 * y0 + 6 * x + 9 := by linear_combination hy3 - hy0
    exact_mod_cast h
  have h4 : y4 * y4 = y0 * y0 + 8 * x + 16 := by
    have h : (y4 : ℤ) * y4 = y0 * y0 + 8 * x + 16 := by linear_combination hy4 - hy0
    exact_mod_cast h
  exact checkCandidate_sound hcand (by rw [hy0_eq, hx_eq]; exact h2)
    (by rw [hy0_eq, hx_eq]; exact h3) (by rw [hy0_eq, hx_eq]; exact h4)
