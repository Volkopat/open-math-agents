import OMAReductions.R_Erdos398_erdos_398_R1_H3_R1

-- Brocard's equation n! + 1 = m^2 has no solution with 128 <= n < 10000.
-- Original proof by a kernel-checked certificate. For each n the kernel finds a prime p among 14 fixed primes
-- above 10000 with (n! + 1)^((p-1)/2) = -1 modulo p (Euler's criterion), so n! + 1 is not a square modulo p.
-- The residues n! mod p are carried along a loop over n; the range is cut into blocks of 2000 values of n
-- so that no single kernel computation is large.
-- The method is the classical one (Berndt and Galway verified n up to 10^9 this way). This is a verified
-- range of an open problem, not progress on the general statement.

namespace OMA.Brocard398

/-- The test primes. -/
def primes : List ℕ := [10007, 10009, 10037, 10039, 10061, 10067, 10069, 10079, 10091, 10093, 10099, 10103, 10111, 10133]

/-- Multiplies each residue by `n + 1`. -/
def step (n : ℕ) : List ℕ → List ℕ → List ℕ
  | p :: ps, r :: rs => (r * (n + 1)) % p :: step n ps rs
  | _, _ => []

/-- Some prime `p` in the list has `(r + 1)^((p-1)/2) = p - 1` modulo `p`. -/
def cert : List ℕ → List ℕ → Bool
  | p :: ps, r :: rs => ((r + 1) ^ ((p - 1) / 2) % p == p - 1) || cert ps rs
  | _, _ => false

/-- Runs `f` values of `n` from `n` on; returns the final residues if every `n ≥ 128` is certified. -/
def run : ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, R => some R
  | f + 1, n, R =>
      if (decide (n < 128) || cert primes R) = true then run f (n + 1) (step n primes R) else none

/-- The residues of `n!` modulo the primes of a list. -/
def resid (ps : List ℕ) (n : ℕ) : List ℕ := ps.map (fun p => n.factorial % p)

lemma step_resid (n : ℕ) : ∀ ps : List ℕ, step n ps (resid ps n) = resid ps (n + 1) := by
  intro ps
  induction ps with
  | nil => simp [resid, step]
  | cons p ps ih =>
    have ih' : step n ps (List.map (fun p => n.factorial % p) ps) =
        List.map (fun p => (n + 1).factorial % p) ps := ih
    simp only [resid, List.map_cons, step]
    rw [ih']
    congr 1
    rw [Nat.factorial_succ, Nat.mod_mul_mod, Nat.mul_comm]

lemma cert_sound (n : ℕ) : ∀ ps : List ℕ, cert ps (resid ps n) = true →
    ∃ p ∈ ps, (n.factorial % p + 1) ^ ((p - 1) / 2) % p = p - 1 := by
  intro ps
  induction ps with
  | nil => intro h; simp [cert] at h
  | cons p ps ih =>
    intro h
    simp only [resid, List.map_cons, cert, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨p, List.mem_cons_self, h⟩
    · obtain ⟨q, hq, hq'⟩ := ih h
      exact ⟨q, List.mem_cons_of_mem _ hq, hq'⟩

lemma run_spec : ∀ (f n : ℕ) (R' : List ℕ), run f n (resid primes n) = some R' →
    (∀ j, j < f → 128 ≤ n + j →
      ∃ p ∈ primes, ((n + j).factorial % p + 1) ^ ((p - 1) / 2) % p = p - 1) ∧
    R' = resid primes (n + f) := by
  intro f
  induction f with
  | zero =>
    intro n R' h
    simp only [run, Option.some.injEq] at h
    exact ⟨by intro j hj; omega, h.symm⟩
  | succ f ih =>
    intro n R' h
    rw [run] at h
    split_ifs at h with hc
    rw [step_resid] at h
    obtain ⟨h1, h2⟩ := ih (n + 1) R' h
    refine ⟨?_, by rw [h2]; congr 1; omega⟩
    intro j hj hge
    cases j with
    | zero =>
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · omega
      · exact cert_sound n primes hc
    | succ j =>
      have h3 := h1 j (by omega) (by omega)
      rw [show n + 1 + j = n + (j + 1) by omega] at h3
      exact h3

lemma chunk_spec {f n e : ℕ} {R R' : List ℕ} (he : n + f = e) (hR : R = resid primes n)
    (h : run f n R = some R') :
    (∀ m, n ≤ m → m < e → 128 ≤ m →
      ∃ p ∈ primes, (m.factorial % p + 1) ^ ((p - 1) / 2) % p = p - 1) ∧
    R' = resid primes e := by
  subst hR
  subst he
  obtain ⟨h1, h2⟩ := run_spec f n R' h
  refine ⟨?_, h2⟩
  intro m hm1 hm2 hm3
  have h3 := h1 (m - n) (by omega) (by omega)
  rw [show n + (m - n) = m by omega] at h3
  exact h3

/-- Euler's criterion, in the direction needed. -/
lemma not_square_of_cert {p N m : ℕ} (hp : p.Prime) (hp2 : 2 < p) (h : N + 1 = m ^ 2)
    (hc : (N % p + 1) ^ ((p - 1) / 2) % p = p - 1) : False := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hodd : 2 * ((p - 1) / 2) = p - 1 := by
    rcases hp.eq_two_or_odd' with h2 | ⟨k, hk⟩
    · omega
    · omega
  have hcast : ((N % p + 1 : ℕ) : ZMod p) = (m : ZMod p) ^ 2 := by
    rw [Nat.cast_add, ZMod.natCast_mod, Nat.cast_one]
    have h' := congrArg (Nat.cast : ℕ → ZMod p) h
    push_cast at h'
    exact h'
  have e : (((N % p + 1) ^ ((p - 1) / 2) % p : ℕ) : ZMod p) = (m : ZMod p) ^ (p - 1) := by
    rw [ZMod.natCast_mod, Nat.cast_pow, hcast, ← pow_mul, hodd]
  rw [hc] at e
  have e' : ((p - 1 : ℕ) : ZMod p) = -1 := by
    rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  rw [e'] at e
  by_cases hm : (m : ZMod p) = 0
  · rw [hm, zero_pow (by omega)] at e
    have h10 : (1 : ZMod p) = 0 := by linear_combination -e
    exact one_ne_zero h10
  · rw [ZMod.pow_card_sub_one_eq_one hm] at e
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination -e
    rw [ZMod.natCast_eq_zero_iff] at h2
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega

lemma primes_ok : ∀ p ∈ primes, p.Prime ∧ 2 < p := by
  intro p hp
  simp only [primes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

def r0 : List ℕ := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def r1 : List ℕ := [4780, 7743, 8800, 117, 2956, 3748, 2168, 5490, 3206, 5187, 1595, 6207, 2708, 7866]

def r2 : List ℕ := [9738, 2737, 5552, 8673, 2122, 6540, 2984, 5791, 3277, 2953, 4597, 4382, 2933, 4431]

def r3 : List ℕ := [8517, 4306, 9915, 4107, 316, 2086, 3931, 8387, 4706, 5044, 7366, 6124, 4348, 8701]

def r4 : List ℕ := [9992, 1658, 3464, 7277, 1480, 6729, 3207, 4651, 3105, 754, 3389, 7733, 6535, 406]

def r5 : List ℕ := [6991, 6238, 9409, 7079, 1263, 2858, 4410, 1780, 4110, 9921, 2136, 4184, 3247, 4682]

lemma s0 : r0 = resid primes 0 := by decide

set_option maxRecDepth 100000 in
theorem c0 : run 2000 0 r0 = some r1 := by decide +kernel

lemma s1 : r1 = resid primes 2000 := (chunk_spec (by norm_num) s0 c0).2

set_option maxRecDepth 100000 in
theorem c1 : run 2000 2000 r1 = some r2 := by decide +kernel

lemma s2 : r2 = resid primes 4000 := (chunk_spec (by norm_num) s1 c1).2

set_option maxRecDepth 100000 in
theorem c2 : run 2000 4000 r2 = some r3 := by decide +kernel

lemma s3 : r3 = resid primes 6000 := (chunk_spec (by norm_num) s2 c2).2

set_option maxRecDepth 100000 in
theorem c3 : run 2000 6000 r3 = some r4 := by decide +kernel

lemma s4 : r4 = resid primes 8000 := (chunk_spec (by norm_num) s3 c3).2

set_option maxRecDepth 100000 in
theorem c4 : run 2000 8000 r4 = some r5 := by decide +kernel

lemma s5 : r5 = resid primes 10000 := (chunk_spec (by norm_num) s4 c4).2

lemma all_cert (n : ℕ) (h1 : 128 ≤ n) (h2 : n < 10000) :
    ∃ p ∈ primes, (n.factorial % p + 1) ^ ((p - 1) / 2) % p = p - 1 := by
  by_cases g0 : n < 2000
  · exact (chunk_spec (e := 2000) (by norm_num) s0 c0).1 n (by omega) (by omega) h1
  by_cases g1 : n < 4000
  · exact (chunk_spec (e := 4000) (by norm_num) s1 c1).1 n (by omega) (by omega) h1
  by_cases g2 : n < 6000
  · exact (chunk_spec (e := 6000) (by norm_num) s2 c2).1 n (by omega) (by omega) h1
  by_cases g3 : n < 8000
  · exact (chunk_spec (e := 8000) (by norm_num) s3 c3).1 n (by omega) (by omega) h1
  exact (chunk_spec (e := 10000) (by norm_num) s4 c4).1 n (by omega) (by omega) h1

theorem brocard_range (n : ℕ) (h1 : 128 ≤ n) (h2 : n < 10000) (x : ℕ) :
    n.factorial / 4 ≠ x * (x + 1) := by
  intro hx
  have h4 : 4 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hsq : n.factorial + 1 = (2 * x + 1) ^ 2 := by
    obtain ⟨c, hc⟩ := h4
    rw [hc, Nat.mul_div_cancel_left _ (by norm_num)] at hx
    rw [hc, hx]
    ring
  obtain ⟨p, hp, hc⟩ := all_cert n h1 h2
  exact not_square_of_cert (primes_ok p hp).1 (primes_ok p hp).2 hsq hc

end OMA.Brocard398

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1_H3_R1.H1 := by
  intro n h1 h2 x
  exact OMA.Brocard398.brocard_range n h1 h2 x
