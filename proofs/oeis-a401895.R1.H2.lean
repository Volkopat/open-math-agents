import OMAReductions.R_oeis_a401895_R1

namespace OMA.H2A401895

open OMA.S_oeis_a401895

/-- Reverse the low `k` decimal digits of `x` (zero padded to `k` digits). -/
def revK : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x => (x % 10) * 10 ^ k + revK k (x / 10)

/-- The `k` digit number consisting only of fives. -/
def rep5 (k : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate k 5)

/-- Necessary conditions for a pair of a high block and a low block of a witness. -/
def okState (k : ℕ) (p : ℕ × ℕ) : Bool :=
  let nt := p.1
  let nb := p.2
  let rt := revK k nb
  let rb := revK k nt
  ((nb * rb) % 10 ^ k == rep5 k) && decide (nt * rt ≤ rep5 (2 * k)) &&
    decide (rep5 (2 * k) < (nt + 1) * (rt + 1))

/-- One layer of the digit branch and bound. -/
def expand (k : ℕ) (S : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (S.flatMap fun p =>
    (List.range 10).flatMap fun c =>
      (List.range 10).map fun e =>
        (10 * p.1 + c, e * 10 ^ k + p.2)).filter (okState (k + 1))

/-- All surviving prefix pairs after `k` digits. -/
def states : ℕ → List (ℕ × ℕ)
  | 0 => []
  | 1 => [(9, 5), (5, 9)]
  | k + 2 => expand (k + 1) (states (k + 1))

lemma rep5_succ (k : ℕ) : rep5 (k + 1) = 5 + 10 * rep5 k := by
  simp [rep5, List.replicate_succ, Nat.ofDigits_cons]

lemma rep5_lt (k : ℕ) : rep5 k < 10 ^ k := by
  induction k with
  | zero => simp [rep5]
  | succ k ih =>
      rw [rep5_succ, pow_succ]
      nlinarith

lemma rep5_shift (a b : ℕ) : rep5 (a + b) = rep5 a * 10 ^ b + rep5 b := by
  induction b with
  | zero => simp [rep5]
  | succ b ih =>
      rw [show a + (b + 1) = a + b + 1 by omega, rep5_succ, ih, rep5_succ, pow_succ]
      ring

lemma rep5_mod (m k : ℕ) : rep5 (m + k) % 10 ^ k = rep5 k := by
  rw [rep5_shift]
  rw [add_comm (rep5 m * 10 ^ k) (rep5 k)]
  rw [Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt (rep5_lt k)

lemma rep5_div (a b : ℕ) : rep5 (a + b) / 10 ^ b = rep5 a := by
  rw [rep5_shift]
  rw [add_comm (rep5 a * 10 ^ b) (rep5 b)]
  rw [mul_comm (rep5 a) (10 ^ b)]
  rw [Nat.add_mul_div_left _ _ (pow_pos (by decide : (0:ℕ) < 10) b)]
  rw [Nat.div_eq_of_lt (rep5_lt b)]
  omega

lemma revK_lt (k x : ℕ) : revK k x < 10 ^ k := by
  induction k generalizing x with
  | zero => simp [revK]
  | succ k ih =>
      simp only [revK, pow_succ]
      have h1 : x % 10 < 10 := Nat.mod_lt _ (by decide)
      have h2 : revK k (x / 10) < 10 ^ k := ih (x / 10)
      nlinarith

lemma revK_ofDigits (u : List ℕ) (h : ∀ x ∈ u, x < 10) :
    revK u.length (Nat.ofDigits 10 u) = Nat.ofDigits 10 u.reverse := by
  induction u with
  | nil => simp [revK]
  | cons d t ih =>
      have hd : d < 10 := h d (List.mem_cons_self ..)
      have ht : ∀ x ∈ t, x < 10 := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have ih' := ih ht
      rw [List.length_cons, Nat.ofDigits_cons]
      have hmod : (d + 10 * Nat.ofDigits 10 t) % 10 = d := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
      have hdiv : (d + 10 * Nat.ofDigits 10 t) / 10 = Nat.ofDigits 10 t := by
        rw [Nat.add_mul_div_left _ _ (by decide : 0 < 10)]
        rw [Nat.div_eq_of_lt hd]
        omega
      simp only [revK, hmod, hdiv, ih']
      rw [Nat.ofDigits_reverse_cons]
      ring

lemma ofDigits_take_lt (ds : List ℕ) (hds : ∀ x ∈ ds, x < 10) (k : ℕ) (hk : k ≤ ds.length) :
    Nat.ofDigits 10 (ds.take k) < 10 ^ k := by
  have hlen : (ds.take k).length = k := List.length_take_of_le hk
  calc
    Nat.ofDigits 10 (ds.take k) < 10 ^ (ds.take k).length :=
      Nat.ofDigits_lt_base_pow_length (by decide) fun x hx => hds x (List.mem_of_mem_take hx)
    _ = 10 ^ k := by rw [hlen]

lemma ofDigits_drop_div (ds : List ℕ) (hds : ∀ x ∈ ds, x < 10) (k : ℕ) (hk : k ≤ ds.length) :
    Nat.ofDigits 10 ds / 10 ^ k = Nat.ofDigits 10 (ds.drop k) := by
  conv_lhs => rw [← List.take_append_drop k ds]
  rw [Nat.ofDigits_append]
  have hlen : (ds.take k).length = k := List.length_take_of_le hk
  have hlt := ofDigits_take_lt ds hds k hk
  rw [hlen]
  rw [Nat.add_mul_div_left _ _ (pow_pos (by decide : (0 : ℕ) < 10) k)]
  rw [Nat.div_eq_of_lt hlt]
  simp

lemma ofDigits_take_mod (ds : List ℕ) (hds : ∀ x ∈ ds, x < 10) (k : ℕ) (hk : k ≤ ds.length) :
    Nat.ofDigits 10 ds % 10 ^ k = Nat.ofDigits 10 (ds.take k) := by
  conv_lhs => rw [← List.take_append_drop k ds]
  rw [Nat.ofDigits_append]
  have hlen : (ds.take k).length = k := List.length_take_of_le hk
  have hlt := ofDigits_take_lt ds hds k hk
  rw [hlen]
  rw [Nat.add_mul_mod_self_left]
  rw [Nat.mod_eq_of_lt hlt]

lemma revK_digits_low (n l k : ℕ) (hl : l = (Nat.digits 10 n).length) (hk : k ≤ l) :
    R n % 10 ^ k = revK k (n / 10 ^ (l - k)) := by
  let ds := Nat.digits 10 n
  let u := ds.drop (l - k)
  have hds : ∀ x ∈ ds, x < 10 := fun x hx => Nat.digits_lt_base (by decide) hx
  have hlen : ds.length = l := hl.symm
  have hmod := ofDigits_take_mod ds.reverse (fun x hx => hds x (List.mem_reverse.mp hx)) k
    (by rw [List.length_reverse]; omega)
  have htake : (ds.reverse).take k = u.reverse := by
    rw [List.take_reverse, hlen]
  have hdiv : n / 10 ^ (l - k) = Nat.ofDigits 10 u := by
    rw [← Nat.ofDigits_digits 10 n]
    exact ofDigits_drop_div ds hds (l - k) (by omega)
  have hul : u.length = k := by
    rw [List.length_drop, hlen]
    omega
  have hrev : revK k (Nat.ofDigits 10 u) = Nat.ofDigits 10 u.reverse := by
    rw [← hul]
    exact revK_ofDigits u fun x hx => hds x (List.mem_of_mem_drop hx)
  calc
    R n % 10 ^ k = Nat.ofDigits 10 (ds.reverse) % 10 ^ k := rfl
    _ = Nat.ofDigits 10 ((ds.reverse).take k) := hmod
    _ = Nat.ofDigits 10 u.reverse := by rw [htake]
    _ = revK k (Nat.ofDigits 10 u) := hrev.symm
    _ = revK k (n / 10 ^ (l - k)) := by rw [hdiv]

lemma revK_digits_high (n l k : ℕ) (hl : l = (Nat.digits 10 n).length) (hk : k ≤ l) :
    R n / 10 ^ (l - k) = revK k (n % 10 ^ k) := by
  let ds := Nat.digits 10 n
  let u := ds.take k
  have hds : ∀ x ∈ ds, x < 10 := fun x hx => Nat.digits_lt_base (by decide) hx
  have hlen : ds.length = l := hl.symm
  have hkds : k ≤ ds.length := by omega
  have hdiv := ofDigits_drop_div ds.reverse (fun x hx => hds x (List.mem_reverse.mp hx)) (l - k)
    (by rw [List.length_reverse]; omega)
  have hdrop : (ds.reverse).drop (l - k) = u.reverse := by
    rw [List.drop_reverse, hlen]
    rw [show l - (l - k) = k by omega]
  have hmod : n % 10 ^ k = Nat.ofDigits 10 u := by
    rw [← Nat.ofDigits_digits 10 n]
    exact ofDigits_take_mod ds hds k hkds
  have hul : u.length = k := List.length_take_of_le hkds
  have hrev : revK k (Nat.ofDigits 10 u) = Nat.ofDigits 10 u.reverse := by
    rw [← hul]
    exact revK_ofDigits u fun x hx => hds x (List.mem_of_mem_take hx)
  calc
    R n / 10 ^ (l - k) = Nat.ofDigits 10 (ds.reverse) / 10 ^ (l - k) := rfl
    _ = Nat.ofDigits 10 ((ds.reverse).drop (l - k)) := hdiv
    _ = Nat.ofDigits 10 u.reverse := by rw [hdrop]
    _ = revK k (Nat.ofDigits 10 u) := hrev.symm
    _ = revK k (n % 10 ^ k) := by rw [hmod]

lemma okState_eq_true_iff (k nt nb : ℕ) :
    okState k (nt, nb) = true ↔
      (nb * revK k nt) % 10 ^ k = rep5 k ∧
      nt * revK k nb ≤ rep5 (2 * k) ∧
      rep5 (2 * k) < (nt + 1) * (revK k nb + 1) := by
  simp only [okState, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  tauto

lemma okState_true (n l k : ℕ) (hl : l = (Nat.digits 10 n).length)
    (hM : n * R n = rep5 (2 * l)) (hk1 : 1 ≤ k) (hkl : k ≤ l) :
    okState k (n / 10 ^ (l - k), n % 10 ^ k) = true := by
  rw [okState_eq_true_iff]
  have hlow := revK_digits_low n l k hl hkl
  have hhigh := revK_digits_high n l k hl hkl
  have hPpos : 0 < 10 ^ (l - k) := pow_pos (by decide : (0 : ℕ) < 10) _
  have hmodn : n % 10 ^ (l - k) < 10 ^ (l - k) := Nat.mod_lt _ hPpos
  have hmodr : R n % 10 ^ (l - k) < 10 ^ (l - k) := Nat.mod_lt _ hPpos
  have h2l : 2 * l = 2 * k + 2 * (l - k) := by omega
  have hMdecomp : n * R n = rep5 (2 * k) * (10 ^ (l - k)) ^ 2 + rep5 (2 * (l - k)) := by
    rw [hM, h2l, rep5_shift]
    ring
  have hrem : rep5 (2 * (l - k)) < (10 ^ (l - k)) ^ 2 := by
    rw [← pow_mul, show (l - k) * 2 = 2 * (l - k) by omega]
    exact rep5_lt _
  refine ⟨?_, ?_, ?_⟩
  · rw [← hlow, ← Nat.mul_mod n (R n) (10 ^ k), hM]
    have hmod := rep5_mod (2 * l - k) k
    rwa [show 2 * l - k + k = 2 * l by omega] at hmod
  · rw [← hhigh]
    have hdivn : 10 ^ (l - k) * (n / 10 ^ (l - k)) + n % 10 ^ (l - k) = n :=
      Nat.div_add_mod n (10 ^ (l - k))
    have hdivr : 10 ^ (l - k) * (R n / 10 ^ (l - k)) + R n % 10 ^ (l - k) = R n :=
      Nat.div_add_mod (R n) (10 ^ (l - k))
    have hle_n : 10 ^ (l - k) * (n / 10 ^ (l - k)) ≤ n := by
      calc
        10 ^ (l - k) * (n / 10 ^ (l - k)) ≤
            10 ^ (l - k) * (n / 10 ^ (l - k)) + n % 10 ^ (l - k) := Nat.le_add_right _ _
        _ = n := hdivn
    have hle_r : 10 ^ (l - k) * (R n / 10 ^ (l - k)) ≤ R n := by
      calc
        10 ^ (l - k) * (R n / 10 ^ (l - k)) ≤
            10 ^ (l - k) * (R n / 10 ^ (l - k)) + R n % 10 ^ (l - k) := Nat.le_add_right _ _
        _ = R n := hdivr
    have hmul : (10 ^ (l - k) * (n / 10 ^ (l - k))) *
        (10 ^ (l - k) * (R n / 10 ^ (l - k))) ≤ n * R n := Nat.mul_le_mul hle_n hle_r
    have hkey : (n / 10 ^ (l - k)) * (R n / 10 ^ (l - k)) * (10 ^ (l - k)) ^ 2 ≤
        rep5 (2 * k) * (10 ^ (l - k)) ^ 2 + rep5 (2 * (l - k)) := by
      calc
        (n / 10 ^ (l - k)) * (R n / 10 ^ (l - k)) * (10 ^ (l - k)) ^ 2 =
            (10 ^ (l - k) * (n / 10 ^ (l - k))) *
              (10 ^ (l - k) * (R n / 10 ^ (l - k))) := by ring
        _ ≤ n * R n := hmul
        _ = rep5 (2 * k) * (10 ^ (l - k)) ^ 2 + rep5 (2 * (l - k)) := hMdecomp
    have hkey2 : (n / 10 ^ (l - k)) * (R n / 10 ^ (l - k)) * (10 ^ (l - k)) ^ 2 <
        (rep5 (2 * k) + 1) * (10 ^ (l - k)) ^ 2 := by
      calc
        _ ≤ rep5 (2 * k) * (10 ^ (l - k)) ^ 2 + rep5 (2 * (l - k)) := hkey
        _ < rep5 (2 * k) * (10 ^ (l - k)) ^ 2 + (10 ^ (l - k)) ^ 2 :=
              Nat.add_lt_add_left hrem _
        _ = (rep5 (2 * k) + 1) * (10 ^ (l - k)) ^ 2 := by ring
    have := Nat.lt_of_mul_lt_mul_right hkey2
    omega
  · rw [← hhigh]
    have hlt_n : n < (n / 10 ^ (l - k) + 1) * 10 ^ (l - k) := by
      calc
        n = 10 ^ (l - k) * (n / 10 ^ (l - k)) + n % 10 ^ (l - k) :=
              (Nat.div_add_mod n (10 ^ (l - k))).symm
        _ < 10 ^ (l - k) * (n / 10 ^ (l - k)) + 10 ^ (l - k) :=
              Nat.add_lt_add_left hmodn _
        _ = (n / 10 ^ (l - k) + 1) * 10 ^ (l - k) := by ring
    have hlt_r : R n < (R n / 10 ^ (l - k) + 1) * 10 ^ (l - k) := by
      calc
        R n = 10 ^ (l - k) * (R n / 10 ^ (l - k)) + R n % 10 ^ (l - k) :=
              (Nat.div_add_mod (R n) (10 ^ (l - k))).symm
        _ < 10 ^ (l - k) * (R n / 10 ^ (l - k)) + 10 ^ (l - k) :=
              Nat.add_lt_add_left hmodr _
        _ = (R n / 10 ^ (l - k) + 1) * 10 ^ (l - k) := by ring
    have hmul2 : n * R n <
        ((n / 10 ^ (l - k) + 1) * (R n / 10 ^ (l - k) + 1)) * (10 ^ (l - k)) ^ 2 := by
      calc
        n * R n < ((n / 10 ^ (l - k) + 1) * 10 ^ (l - k)) *
            ((R n / 10 ^ (l - k) + 1) * 10 ^ (l - k)) :=
              Nat.mul_lt_mul_of_lt_of_lt hlt_n hlt_r
        _ = ((n / 10 ^ (l - k) + 1) * (R n / 10 ^ (l - k) + 1)) *
              (10 ^ (l - k)) ^ 2 := by ring
    have hbase : rep5 (2 * k) * (10 ^ (l - k)) ^ 2 ≤ n * R n := by
      rw [hMdecomp]
      exact Nat.le_add_right _ _
    have hlt : rep5 (2 * k) * (10 ^ (l - k)) ^ 2 <
        ((n / 10 ^ (l - k) + 1) * (R n / 10 ^ (l - k) + 1)) * (10 ^ (l - k)) ^ 2 :=
      lt_of_le_of_lt hbase hmul2
    exact Nat.lt_of_mul_lt_mul_right hlt

lemma mem_expand {k : ℕ} {S : List (ℕ × ℕ)} {nt nb : ℕ} (hp : (nt, nb) ∈ S)
    {c e : ℕ} (hc : c < 10) (he : e < 10)
    (hok : okState (k + 1) (10 * nt + c, e * 10 ^ k + nb) = true) :
    (10 * nt + c, e * 10 ^ k + nb) ∈ expand k S := by
  simp only [expand, List.mem_filter, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨⟨(nt, nb), hp, c, hc, e, he, rfl⟩, hok⟩

lemma mem_states (n l : ℕ) (hl : l = (Nat.digits 10 n).length)
    (hM : n * R n = rep5 (2 * l))
    (hcase : (n % 10 = 5 ∧ R n % 10 = 9) ∨ (n % 10 = 9 ∧ R n % 10 = 5)) :
    ∀ k, 1 ≤ k → k ≤ l → (n / 10 ^ (l - k), n % 10 ^ k) ∈ states k := by
  intro k
  induction k with
  | zero => intro h1 _; omega
  | succ k ih =>
      intro hk1 hkl
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        have hl1 : 1 ≤ l := by omega
        have hnlt : n < 10 ^ l := by
          rw [hl]
          exact Nat.lt_base_pow_length_digits (by decide)
        have hntlt : n / 10 ^ (l - 1) < 10 := by
          rw [Nat.div_lt_iff_lt_mul (pow_pos (by decide : (0 : ℕ) < 10) _)]
          calc
            n < 10 ^ l := hnlt
            _ = 10 * 10 ^ (l - 1) := by
                  conv_lhs => rw [show l = l - 1 + 1 by omega]
                  rw [pow_succ]
                  ring
        have hrev1 : revK 1 (n / 10 ^ (l - 1)) = n / 10 ^ (l - 1) := by
          simp [revK, Nat.mod_eq_of_lt hntlt]
        have hlow := revK_digits_low n l 1 hl hl1
        have hnt : n / 10 ^ (l - 1) = R n % 10 := by
          rw [← hrev1]
          simpa using hlow.symm
        have hnb : n % 10 ^ 1 = n % 10 := by norm_num
        rw [hnt, hnb]
        rcases hcase with ⟨h5, h9⟩ | ⟨h9, h5⟩
        · rw [h5, h9]
          simp [states]
        · rw [h9, h5]
          simp [states]
      · have hk1' : 1 ≤ k := hkpos
        have hkl' : k ≤ l := by omega
        have hp := ih hk1' hkl'
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hstates : states (j + 1 + 1) = expand (j + 1) (states (j + 1)) := rfl
        have hnt' : n / 10 ^ (l - (j + 1 + 1)) =
            10 * (n / 10 ^ (l - (j + 1))) + (n / 10 ^ (l - (j + 1 + 1))) % 10 := by
          have h1 : n / 10 ^ (l - (j + 1)) = (n / 10 ^ (l - (j + 1 + 1))) / 10 := by
            rw [show l - (j + 1) = l - (j + 1 + 1) + 1 by omega, pow_succ,
              Nat.div_div_eq_div_mul]
          rw [h1]
          exact (Nat.div_add_mod (n / 10 ^ (l - (j + 1 + 1))) 10).symm
        have hnb' : n % 10 ^ (j + 1 + 1) =
            (n / 10 ^ (j + 1) % 10) * 10 ^ (j + 1) + n % 10 ^ (j + 1) := by
          rw [show j + 1 + 1 = (j + 1) + 1 by omega, Nat.mod_pow_succ]
          ring
        have hok : okState (j + 1 + 1)
            (n / 10 ^ (l - (j + 1 + 1)), n % 10 ^ (j + 1 + 1)) = true :=
          okState_true n l (j + 1 + 1) hl hM (by omega) (by omega)
        have hok2 : okState (j + 1 + 1)
            (10 * (n / 10 ^ (l - (j + 1))) + (n / 10 ^ (l - (j + 1 + 1))) % 10,
             (n / 10 ^ (j + 1) % 10) * 10 ^ (j + 1) + n % 10 ^ (j + 1)) = true := by
          rw [← hnt', ← hnb']
          exact hok
        rw [hstates, hnt', hnb']
        exact mem_expand hp (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) hok2

end OMA.H2A401895

open OMA.H2A401895

open OMA.S_oeis_a401895

theorem OMA.solution : OMA.R_oeis_a401895_R1.H2 := by
  intro n
  dsimp only
  intro hn h11 hcase hdigits
  set l := (Nat.digits 10 n).length with hl
  have hn0 : n ≠ 0 := by omega
  have hne : Nat.digits 10 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn0
  have hlpos : 0 < l := by
    rw [hl]
    exact Nat.pos_of_ne_zero fun h => hne (List.eq_nil_of_length_eq_zero h)
  have h11' : 11 ∣ l := by
    rw [hl]
    exact h11
  have h11le : 11 ≤ l := Nat.le_of_dvd hlpos h11'
  have hM : n * R n = rep5 (2 * l) := by
    have h := congrArg (Nat.ofDigits 10) hdigits
    simpa [rep5, Nat.ofDigits_digits, hl] using h
  have hmem := mem_states n l hl hM hcase
  rcases Nat.eq_or_lt_of_le h11le with hle | hlt
  · have hl11 : l = 11 := hle.symm
    have hnlt : n < 10 ^ 11 := by
      have hlen11 : (Nat.digits 10 n).length = 11 := by rw [← hl, hl11]
      rw [← hlen11]
      exact Nat.lt_base_pow_length_digits (by decide)
    have hp : (n, n) ∈ states 11 := by
      have h := hmem 11 (by decide) h11le
      rw [hl11] at h
      have hmod11 : n % 10 ^ 11 = n := Nat.mod_eq_of_lt hnlt
      rw [hmod11] at h
      simpa using h
    have hall : (states 11).all (fun p => p.1 != p.2) = true := by decide +kernel
    have hbad := (List.all_eq_true.mp hall) (n, n) hp
    simp at hbad
  · obtain ⟨m, hm⟩ := h11'
    have h14 : 14 ≤ l := by omega
    have h := hmem 14 (by decide) h14
    have hempty : states 14 = [] := by decide +kernel
    rw [hempty] at h
    exact List.not_mem_nil h

