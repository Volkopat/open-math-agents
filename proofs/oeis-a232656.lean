import OMAStatements.S_oeis_a232656

-- Problem: A232656: The number of pairs of numbers below n that, when generating a Fibonacci-like sequence modulo n, contain zeros.
-- Upstream: formal-conjectures statements/oeis-a232656.lean:0 (declaration OMA.S_oeis_a232656.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: The Fibonacci step (u, v) |-> (v, u + v) is a bijection on (ZMod n)^2.
-- Every pair whose orbit hits 0 is uniquely of the form step^k (0, c) with c in ZMod n
-- and 0 <= k < entryPoint (n / gcd(n, c.val)). Grouping c by d = n / gcd(n, c.val)
-- gives Sum_{d | n} phi(d) * entryPoint(d).

open OMA.S_oeis_a232656 in
theorem OMA.solution : type_of% @OMA.S_oeis_a232656.main := by
  have entry_exists : ∀ d : ℕ, 1 ≤ d → ∃ k : ℕ, 1 ≤ k ∧ d ∣ Nat.fib k := by
    intro d hd
    have : NeZero d := ⟨by omega⟩
    let T : ZMod d × ZMod d → ZMod d × ZMod d := fun p => (p.2, p.1 + p.2)
    let Tinv : ZMod d × ZMod d → ZMod d × ZMod d := fun p => (p.2 - p.1, p.1)
    have hT_left : Function.LeftInverse Tinv T := by
      intro ⟨x, y⟩
      dsimp [T, Tinv]
      congr 1
      ring
    have hT_inj : Function.Injective T := hT_left.injective
    have hT_iter : ∀ k : ℕ, T^[k] (0, 1) = ((Nat.fib k : ZMod d), (Nat.fib (k + 1) : ZMod d)) := by
      intro k
      induction k with
      | zero => simp [Nat.fib_zero, Nat.fib_one]
      | succ k ih =>
        rw [Function.iterate_succ_apply', ih]
        dsimp [T]
        rw [Nat.fib_add_two]
        push_cast
        rfl
    obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => T^[k] (0, 1))
    have hpos_period : ∀ a b : ℕ, a < b → T^[a] (0, 1) = T^[b] (0, 1) →
        ∃ k : ℕ, 1 ≤ k ∧ d ∣ Nat.fib k := by
      intro a b hab h
      rw [show b = a + (b - a) by omega, Function.iterate_add_apply] at h
      have h0 : (0, 1) = T^[b - a] (0, 1) := (hT_inj.iterate a) h
      have h1 : (0 : ZMod d) = (Nat.fib (b - a) : ZMod d) := by
        have := congrArg Prod.fst h0
        rw [hT_iter (b - a)] at this
        exact this
      exact ⟨b - a, by omega, (ZMod.natCast_eq_zero_iff (Nat.fib (b - a)) d).mp h1.symm⟩
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hpos_period i j hlt heq
    · exact hpos_period j i hgt heq.symm
  have entryPoint_spec : ∀ d : ℕ, 1 ≤ d → 1 ≤ entryPoint d ∧ d ∣ Nat.fib (entryPoint d) := by
    intro d hd
    classical
    have hex := entry_exists d hd
    unfold entryPoint
    rw [dif_pos hex]
    exact Nat.find_spec hex
  have entryPoint_min : ∀ d k : ℕ, 1 ≤ d → 1 ≤ k → k < entryPoint d → ¬ (d ∣ Nat.fib k) := by
    intro d k hd hk1 hklt
    classical
    have hex := entry_exists d hd
    unfold entryPoint at hklt
    rw [dif_pos hex] at hklt
    have hmin := Nat.find_min hex hklt
    intro hdvd
    exact hmin ⟨hk1, hdvd⟩
  intro n hn
  have : NeZero n := ⟨by omega⟩
  let step : ZMod n × ZMod n → ZMod n × ZMod n := fun p => (p.2, p.1 + p.2)
  let invStep : ZMod n × ZMod n → ZMod n × ZMod n := fun p => (p.2 - p.1, p.1)
  have hLeft : Function.LeftInverse invStep step := by
    intro ⟨x, y⟩
    dsimp [step, invStep]
    congr 1
    ring
  have hRight : Function.RightInverse invStep step := by
    intro ⟨x, y⟩
    dsimp [step, invStep]
    congr 1
    ring
  have hstep_inj : Function.Injective step := hLeft.injective
  have hstep_inv : ∀ k p, step^[k] (invStep^[k] p) = p := by
    intro k
    induction k with
    | zero => intro p; rfl
    | succ k ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih, hRight]
  have hinv_step : ∀ k p, invStep^[k] (step^[k] p) = p := by
    intro k
    induction k with
    | zero => intro p; rfl
    | succ k ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ih, hLeft]
  have hstep_fibLike : ∀ x y k : ℕ,
      step^[k] ((x : ZMod n), (y : ZMod n)) = ((fibLike x y k : ZMod n), (fibLike x y (k + 1) : ZMod n)) := by
    intro x y k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      dsimp [step]
      simp only [fibLike, Nat.cast_add]
  have hstep_zero : ∀ (c : ZMod n) (k : ℕ),
      step^[k] (0, c) = (c * (Nat.fib k : ZMod n), c * (Nat.fib (k + 1) : ZMod n)) := by
    intro c k
    induction k with
    | zero => simp [Nat.fib_zero, Nat.fib_one]
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      dsimp [step]
      rw [Nat.fib_add_two]
      push_cast
      congr 1
      ring
  have hperiodic : ∀ p : ZMod n × ZMod n, ∃ L : ℕ, 1 ≤ L ∧ step^[L] p = p := by
    intro p
    obtain ⟨i, j, hij, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun k : ℕ => step^[k] p)
    have haux : ∀ a b : ℕ, a < b → step^[a] p = step^[b] p → ∃ L : ℕ, 1 ≤ L ∧ step^[L] p = p := by
      intro a b hab h
      rw [show b = a + (b - a) by omega, Function.iterate_add_apply] at h
      exact ⟨b - a, by omega, ((hstep_inj.iterate a) h).symm⟩
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact haux i j hlt heq
    · exact haux j i hgt heq.symm
  have hperiod_mul : ∀ (p : ZMod n × ZMod n) (L : ℕ), step^[L] p = p → ∀ q : ℕ, step^[q * L] p = p := by
    intro p L hL q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Nat.add_comm, Function.iterate_add_apply, ih, hL]
  let dFun : ZMod n → ℕ := fun c => n / Nat.gcd n c.val
  have hdFun_pos : ∀ c : ZMod n, 1 ≤ dFun c := by
    intro c
    dsimp [dFun]
    have hg_pos : 0 < Nat.gcd n c.val := Nat.gcd_pos_of_pos_left c.val (by omega)
    have hg_le : Nat.gcd n c.val ≤ n := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left n c.val)
    exact Nat.div_pos hg_le hg_pos
  have hmul_fib_zero : ∀ (c : ZMod n) (k : ℕ),
      c * (Nat.fib k : ZMod n) = 0 ↔ dFun c ∣ Nat.fib k := by
    intro c k
    have hcast : c * (Nat.fib k : ZMod n) = ((c.val * Nat.fib k : ℕ) : ZMod n) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    rw [hcast, ZMod.natCast_eq_zero_iff]
    have key : ∀ N V F : ℕ, 0 < N → (N ∣ V * F ↔ N / Nat.gcd N V ∣ F) := by
      intro N V F hN
      have hg_pos : 0 < Nat.gcd N V := Nat.gcd_pos_of_pos_left V hN
      have hn_eq : N = Nat.gcd N V * (N / Nat.gcd N V) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left N V)).symm
      have hv_eq : V = Nat.gcd N V * (V / Nat.gcd N V) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right N V)).symm
      have hcop : Nat.Coprime (N / Nat.gcd N V) (V / Nat.gcd N V) :=
        Nat.coprime_div_gcd_div_gcd hg_pos
      obtain ⟨G, A, B, hG0, hNA, hVB, hAB, hA⟩ : ∃ G A B : ℕ, 0 < G ∧ N = G * A ∧ V = G * B ∧
          Nat.Coprime A B ∧ N / Nat.gcd N V = A :=
        ⟨Nat.gcd N V, N / Nat.gcd N V, V / Nat.gcd N V, hg_pos, hn_eq, hv_eq, hcop, rfl⟩
      rw [hA, hNA, hVB, mul_assoc, mul_dvd_mul_iff_left (by omega : G ≠ 0)]
      exact ⟨fun h => hAB.dvd_of_dvd_mul_left h, fun h => dvd_mul_of_dvd_right h B⟩
    exact key n c.val (Nat.fib k) (by omega)
  classical
  let S : Finset (ℕ × ℕ) :=
    (Finset.range n ×ˢ Finset.range n).filter (fun p => ∃ k : ℕ, n ∣ fibLike p.1 p.2 k)
  let T : Finset (Σ c : ZMod n, ℕ) :=
    Finset.univ.sigma (fun c : ZMod n => Finset.range (entryPoint (dFun c)))
  have ha_eq : a n = S.card := rfl
  have hcard_bij : T.card = S.card := by
    refine Finset.card_bij (fun ck _ => ((step^[ck.2] (0, ck.1)).1.val, (step^[ck.2] (0, ck.1)).2.val)) ?_ ?_ ?_
    · intro ⟨c, k⟩ hck
      simp only [T, Finset.mem_sigma, Finset.mem_univ, Finset.mem_range, true_and] at hck
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      refine ⟨⟨ZMod.val_lt _, ZMod.val_lt _⟩, ?_⟩
      refine ⟨entryPoint (dFun c) - k, ?_⟩
      apply (ZMod.natCast_eq_zero_iff _ n).mp
      have hst := hstep_fibLike (step^[k] (0, c)).1.val (step^[k] (0, c)).2.val (entryPoint (dFun c) - k)
      have hfst := congrArg Prod.fst hst
      simp only [ZMod.natCast_zmod_val, Prod.mk.eta] at hfst
      rw [← hfst, ← Function.iterate_add_apply, show entryPoint (dFun c) - k + k = entryPoint (dFun c) by omega,
        hstep_zero]
      exact (hmul_fib_zero c (entryPoint (dFun c))).mpr (entryPoint_spec (dFun c) (hdFun_pos c)).2
    · intro ⟨c1, k1⟩ h1 ⟨c2, k2⟩ h2 hfeq
      simp only [T, Finset.mem_sigma, Finset.mem_univ, Finset.mem_range, true_and] at h1 h2
      have hst : step^[k1] (0, c1) = step^[k2] (0, c2) := by
        have h1' := congrArg (fun x : ℕ => (x : ZMod n)) (congrArg Prod.fst hfeq)
        have h2' := congrArg (fun x : ℕ => (x : ZMod n)) (congrArg Prod.snd hfeq)
        simp only [ZMod.natCast_zmod_val] at h1' h2'
        exact Prod.ext h1' h2'
      have hle_case : ∀ (a1 a2 : ZMod n) (j1 j2 : ℕ),
          j1 < entryPoint (dFun a1) → j2 < entryPoint (dFun a2) → j1 ≤ j2 →
          step^[j1] (0, a1) = step^[j2] (0, a2) → a1 = a2 ∧ j1 = j2 := by
        intro a1 a2 j1 j2 _ hj2 hle heq
        rw [show j2 = j1 + (j2 - j1) by omega, Function.iterate_add_apply] at heq
        have h0 : (0, a1) = step^[j2 - j1] (0, a2) := (hstep_inj.iterate j1) heq
        have hfst : a2 * (Nat.fib (j2 - j1) : ZMod n) = 0 := by
          have := congrArg Prod.fst h0
          rw [hstep_zero] at this
          exact this.symm
        have hdvd : dFun a2 ∣ Nat.fib (j2 - j1) := (hmul_fib_zero a2 (j2 - j1)).mp hfst
        have hj_eq : j1 = j2 := by
          by_contra hne
          exact entryPoint_min (dFun a2) (j2 - j1) (hdFun_pos a2) (by omega) (by omega) hdvd
        subst hj_eq
        simp only [Nat.sub_self, Function.iterate_zero, id_eq] at h0
        exact ⟨congrArg Prod.snd h0, rfl⟩
      rcases le_total k1 k2 with hle | hle
      · obtain ⟨hc, hk⟩ := hle_case c1 c2 k1 k2 h1 h2 hle hst
        subst hc; subst hk; rfl
      · obtain ⟨hc, hk⟩ := hle_case c2 c1 k2 k1 h2 h1 hle hst.symm
        subst hc; subst hk; rfl
    · intro ⟨x, y⟩ hxy
      simp only [S, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hxy
      obtain ⟨⟨hx, hy⟩, ⟨m, hm⟩⟩ := hxy
      let q : ZMod n × ZMod n := ((x : ZMod n), (y : ZMod n))
      have hqm : (step^[m] q).1 = 0 := by
        dsimp [q]
        rw [hstep_fibLike]
        exact (ZMod.natCast_eq_zero_iff (fibLike x y m) n).mpr hm
      obtain ⟨L, hL1, hLp⟩ := hperiodic q
      have hex_inv : ∃ j : ℕ, (invStep^[j] q).1 = 0 := by
        refine ⟨(m + 1) * L - m, ?_⟩
        have hml : m ≤ (m + 1) * L := by nlinarith
        have hstep_eq : step^[(m + 1) * L - m] (step^[m] q) = q := by
          rw [← Function.iterate_add_apply, show (m + 1) * L - m + m = (m + 1) * L by omega]
          exact hperiod_mul q L hLp (m + 1)
        have hinv_eq : invStep^[(m + 1) * L - m] q = step^[m] q :=
          (congrArg (invStep^[(m + 1) * L - m]) hstep_eq).symm.trans (hinv_step _ _)
        rw [hinv_eq]
        exact hqm
      let k := Nat.find hex_inv
      have hk_spec : (invStep^[k] q).1 = 0 := Nat.find_spec hex_inv
      let c : ZMod n := (invStep^[k] q).2
      have hinv_eq : invStep^[k] q = (0, c) := Prod.ext hk_spec rfl
      have hq_eq : step^[k] (0, c) = q := by
        rw [← hinv_eq, hstep_inv]
      have hk_lt : k < entryPoint (dFun c) := by
        by_contra hge
        have hle : entryPoint (dFun c) ≤ k := Nat.le_of_not_lt hge
        set r := entryPoint (dFun c)
        have hr1 : 1 ≤ r := (entryPoint_spec (dFun c) (hdFun_pos c)).1
        have hrdvd : dFun c ∣ Nat.fib r := (entryPoint_spec (dFun c) (hdFun_pos c)).2
        have hkr_lt : k - r < k := by omega
        have hinv_kr : invStep^[k - r] q = step^[r] (0, c) := by
          have h1 : q = step^[k - r] (step^[r] (0, c)) := by
            rw [← Function.iterate_add_apply, show k - r + r = k by omega]
            exact hq_eq.symm
          rw [h1, hinv_step]
        have hzero : (invStep^[k - r] q).1 = 0 := by
          rw [hinv_kr, hstep_zero]
          exact (hmul_fib_zero c r).mpr hrdvd
        exact Nat.find_min hex_inv hkr_lt hzero
      refine ⟨⟨c, k⟩, ?_, ?_⟩
      · simp only [T, Finset.mem_sigma, Finset.mem_univ, Finset.mem_range, true_and]
        exact hk_lt
      · rw [hq_eq]
        dsimp [q]
        rw [ZMod.val_natCast_of_lt hx, ZMod.val_natCast_of_lt hy]
  rw [ha_eq, ← hcard_bij]
  simp only [T, Finset.card_sigma, Finset.card_range]
  have hmaps : ∀ c ∈ (Finset.univ : Finset (ZMod n)), dFun c ∈ n.divisors := by
    intro c _
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n c.val), by omega⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun c => entryPoint (dFun c))]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hd_dvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd_dvd (by omega)
  have hinner : ∑ c ∈ Finset.univ.filter (fun c : ZMod n => dFun c = d), entryPoint (dFun c) =
      (Finset.univ.filter (fun c : ZMod n => dFun c = d)).card * entryPoint d := by
    rw [Finset.sum_congr rfl (fun c hc => by rw [(Finset.mem_filter.mp hc).2]), Finset.sum_const, smul_eq_mul]
  rw [hinner]
  congr 1
  set q := n / d
  have hqd : q * d = n := Nat.div_mul_cancel hd_dvd
  have hq_pos : 1 ≤ q := Nat.div_pos (Nat.le_of_dvd (by omega) hd_dvd) hd_pos
  have htot : Nat.totient d = ((Finset.range d).filter d.Coprime).card := rfl
  rw [htot]
  refine (Finset.card_bij (fun r _ => ((q * r : ℕ) : ZMod n)) ?_ ?_ ?_).symm
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hr_lt, hcop⟩ := hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hqr_lt : q * r < n := by nlinarith
    dsimp [dFun]
    rw [ZMod.val_natCast_of_lt hqr_lt, ← hqd, Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one,
      Nat.mul_div_cancel_left d (by omega : 0 < q)]
  · intro r1 hr1 r2 hr2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
    have h1 : q * r1 < n := by nlinarith
    have h2 : q * r2 < n := by nlinarith
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at hval
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hval
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
    dsimp [dFun] at hc
    have hgcd_eq : Nat.gcd n c.val = q := by
      have h1 : Nat.gcd n c.val * (n / Nat.gcd n c.val) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_left n c.val)
      rw [hc] at h1
      have h2 : q * d = n := hqd
      nlinarith
    have hq_dvd_c : q ∣ c.val := hgcd_eq ▸ Nat.gcd_dvd_right n c.val
    refine ⟨c.val / q, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      have hmul : q * (c.val / q) = c.val := Nat.mul_div_cancel' hq_dvd_c
      have hlt : c.val / q < d := by
        have hc_lt : c.val < q * d := hqd.symm ▸ ZMod.val_lt c
        nlinarith
      have hcop : d.Coprime (c.val / q) := by
        have h1 : q * Nat.gcd d (c.val / q) = q := by
          rw [← Nat.gcd_mul_left, hqd, hmul, hgcd_eq]
        have h2 : Nat.gcd d (c.val / q) = 1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) (by linarith)
        exact h2
      exact ⟨hlt, hcop⟩
    · rw [Nat.mul_div_cancel' hq_dvd_c, ZMod.natCast_zmod_val]
