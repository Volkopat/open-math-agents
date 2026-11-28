import FormalConjectures.OEIS.«100478»

/-! Shorter proof of `OeisA100478.conjecture`. -/

open scoped Nat.Prime
open OeisA100478

private def cpts : List (ℕ × ℕ) :=
  [(73, 72), (74, 73), (75, 74), (76, 75), (77, 76), (79, 77), (81, 79), (84, 81), (87, 84),
   (91, 87), (95, 91), (100, 95), (109, 100), (120, 109), (132, 120), (150, 132), (175, 150),
   (209, 175), (258, 209), (327, 258), (440, 327), (616, 440), (909, 615), (1420, 909),
   (2367, 1420), (2400, 1438)]

private def tdivs : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59,
   61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109]

private def surv (n : ℕ) : Bool :=
  decide (2 ≤ n) && tdivs.all fun d => decide (d = n ∨ ¬d ∣ n)

private def cert (s cap : ℕ) : List (ℕ × ℕ) → Bool
  | [] => true
  | p :: ps => decide (cap + Nat.count (fun j => surv (s + j) = true) (5 * p.1 + 1 - s) ≤ p.2) &&
      cert (5 * p.1 + 1) p.2 ps

private lemma psurv {n : ℕ} (hn : n.Prime) : surv n = true := by
  have hD : tdivs.all (fun d => decide (2 ≤ d)) = true := by decide +kernel
  simp only [surv, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨hn.two_le, fun d hd => by
    have := of_decide_eq_true (List.all_eq_true.mp hD d hd)
    by_cases h : d ∣ n
    · exact Or.inl (((Nat.dvd_prime hn).mp h).resolve_left (by omega))
    · exact Or.inr h⟩

private lemma cert_ok (ps : List (ℕ × ℕ)) (s cap : ℕ) (hc : Nat.count Nat.Prime s ≤ cap)
    (h : cert s cap ps = true) : ∀ p ∈ ps, π (5 * p.1) ≤ p.2 := by
  induction ps generalizing s cap with
  | nil => simp
  | cons p ps ih =>
    simp only [cert, Bool.and_eq_true, decide_eq_true_eq] at h
    have hpc : π (5 * p.1) ≤ p.2 :=
      ((Nat.count_monotone _ (by omega)).trans_eq (Nat.count_add _ _ _)).trans <|
        (Nat.add_le_add hc (Nat.count_mono_left fun _ _ hp => psurv hp)).trans h.1
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hpc
    · exact ih _ _ hpc h.2 _ hq

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 30000 in
private lemma cpts_ok : ∀ p ∈ cpts, π (5 * p.1) ≤ p.2 :=
  cert_ok cpts 0 0 (by simp) (by decide +kernel)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
private lemma fsmall : ∀ i : Fin 73, 0 < i.val → π (5 * i.val) = i.val →
    i.val ∈ ({66, 67, 68, 70, 71, 72} : Finset ℕ) := by decide +kernel

private lemma upper (m : ℕ) (hm : 73 ≤ m) : π (5 * m) < m := by
  have phi1 : Nat.totient 2310 = 480 := by
    have f (p n : ℕ) (hp : p.Prime) (hc : p.Coprime n) : (p * n).totient = (p - 1) * n.totient := by
      rw [Nat.totient_mul hc, Nat.totient_prime hp]
    change (2 * (3 * (5 * (7 * 11)))).totient = 480
    repeat rw [f _ _ (by decide) (by decide)]
    rw [Nat.totient_prime (by decide : Nat.Prime 11)]
  have phi2 : Nat.totient 30030 = 5760 := by
    change (13 * 2310).totient = 5760
    rw [Nat.totient_mul (by decide : Nat.Coprime 13 2310), Nat.totient_prime (by decide), phi1]
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hs : m ≤ 2400
    · obtain ⟨p, hp, h1, h2⟩ : ∃ p ∈ cpts, m ≤ p.1 ∧ p.2 < m := by simp [cpts]; omega
      exact (Nat.monotone_primeCounting (Nat.mul_le_mul_left 5 h1)).trans_lt ((cpts_ok p hp).trans_lt h2)
    by_cases hmid : m ≤ 12010
    · have h := Nat.primeCounting_add_le (a := 2310) (k := 12000) (by decide) (by decide) (5 * m - 12000)
      rw [phi1, show 12000 + (5 * m - 12000) = 5 * m by omega] at h
      have : π 12000 ≤ 1438 := cpts_ok (2400, 1438) (by decide)
      omega
    · have := ih (m - 6005) (by omega) (by omega)
      have h := Nat.primeCounting_add_le (a := 30030) (k := 5 * (m - 6005)) (by decide) (by omega) 30025
      rw [phi2, show 5 * (m - 6005) + 30025 = 5 * m by omega] at h
      omega

theorem OMA.solution : type_of% @OeisA100478.conjecture := by
  classical
  intro v hv
  have step (i : ℕ) : aGeneral v (i + 5) = π (aGeneral v (i + 4) + aGeneral v (i + 3) +
      aGeneral v (i + 2) + aGeneral v (i + 1) + aGeneral v i) := by rw [aGeneral]
  let M := 73 + v 0 + v 1 + v 2 + v 3 + v 4
  have hM : ∀ n, aGeneral v n ≤ M := fun n => by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < 5
      · interval_cases n <;> simp [aGeneral, M] <;> omega
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 5 := ⟨n - 5, by omega⟩
        rw [step]
        refine (Nat.monotone_primeCounting ?_).trans (upper M (by omega)).le
        have := ih i (by omega); have := ih (i + 1) (by omega); have := ih (i + 2) (by omega)
        have := ih (i + 3) (by omega); have := ih (i + 4) (by omega); omega
  let B (m : ℕ) := ∃ k, ∀ n ≥ k, aGeneral v n ≤ m
  have hex : ∃ m, B m := ⟨M, 0, fun n _ => hM n⟩
  let c := Nat.find hex
  obtain ⟨k, hk⟩ := Nat.find_spec hex
  have hhit : ∃ t ≥ k + 5, aGeneral v t = c := by
    by_contra! h
    have hd : B (c - 1) := ⟨k + 5, fun n hn => by
      have : aGeneral v n ≤ c := hk n (by omega); have := h n hn; omega⟩
    have hc : c ≤ c - 1 := Nat.find_min' hex hd
    have : aGeneral v (k + 5) ≤ c := hk (k + 5) (by omega); have := h (k + 5) le_rfl; omega
  obtain ⟨t, ht, htc⟩ := hhit
  have hc (n : ℕ) : aGeneral v (t + n) = c := by
    induction n with
    | zero => simpa using htc
    | succ n ih =>
      let i := t + n - 5
      have hle : aGeneral v i ≤ c := hk i (by omega)
      have hprev : aGeneral v i ≤ aGeneral v (i + 5) := by rw [show i + 5 = t + n by omega, ih]; exact hle
      have hge := Nat.monotone_primeCounting (show aGeneral v (i + 4) + aGeneral v (i + 3) +
          aGeneral v (i + 2) + aGeneral v (i + 1) + aGeneral v i ≤
          aGeneral v (i + 5) + aGeneral v (i + 4) + aGeneral v (i + 3) + aGeneral v (i + 2) +
          aGeneral v (i + 1) by omega)
      have hstep1 : aGeneral v (i + 6) = π (aGeneral v (i + 5) + aGeneral v (i + 4) +
          aGeneral v (i + 3) + aGeneral v (i + 2) + aGeneral v (i + 1)) := by
        simpa only [Nat.add_assoc, Nat.reduceAdd] using step (i + 1)
      rw [← step i, ← hstep1, show i + 5 = t + n by omega, show i + 6 = t + (n + 1) by omega, ih] at hge
      exact le_antisymm (hk _ (by omega)) hge
  have hfix := step t
  rw [hc 5, hc 4, hc 3, hc 2, hc 1, show aGeneral v t = c by simpa using hc 0] at hfix
  have hfix' : π (5 * c) = c := by rw [show 5 * c = c + c + c + c + c by omega]; exact hfix.symm
  have hpos (n : ℕ) : 0 < aGeneral v n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < 5
      · interval_cases n <;> simp [aGeneral] <;> apply hv
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 5 := ⟨n - 5, by omega⟩
        rw [step]; have := ih i (by omega); have := ih (i + 1) (by omega)
        exact Nat.pos_of_ne_zero (by rw [Ne, Nat.primeCounting_eq_zero_iff]; omega)
  have hsmall : c < 73 := by by_contra! h; have := upper c h; omega
  exact ⟨c, fsmall ⟨c, hsmall⟩ (by simpa [show aGeneral v t = c by simpa using hc 0] using hpos t) hfix',
    Filter.eventually_atTop.2 ⟨t, fun n hn => by simpa only [Nat.add_sub_of_le hn] using hc (n - t)⟩⟩
