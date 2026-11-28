import OMAStatements.S_oeis_a183767

namespace OMA.A183767Proof

open OMA.S_oeis_a183767

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

private def reconAux (n : ℕ) (r : Fin 5 → ZMod 2) (c : Fin n → ZMod 2)
    (D : Fin n × Fin 4 → ZMod 2) : ∀ i j : ℕ, i < n + 1 → j < 5 → ZMod 2
  | 0, j, _, hj => r ⟨j, hj⟩
  | i + 1, 0, hi, _ => c ⟨i, by omega⟩
  | i + 1, j + 1, hi, hj =>
    D (⟨i, by omega⟩, ⟨j, by omega⟩) +
      reconAux n r c D i j (by omega) (by omega) +
      reconAux n r c D (i + 1) j hi (by omega) +
      reconAux n r c D i (j + 1) (by omega) hj

private def recon (n : ℕ) (r : Fin 5 → ZMod 2) (c : Fin n → ZMod 2)
    (D : Fin n × Fin 4 → ZMod 2) : Fin (n + 1) → Fin 5 → ZMod 2 :=
  fun i j => reconAux n r c D i.1 j.1 i.2 j.2

private lemma recon_left (n : ℕ) (B : Fin (n + 1) → Fin 5 → ZMod 2) :
    recon n (B 0) (fun i => B i.succ 0) (subblockParity n B) = B := by
  funext i j
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  change reconAux n (B 0) (fun i => B i.succ 0) (subblockParity n B) i j hi hj = B ⟨i, hi⟩ ⟨j, hj⟩
  induction i generalizing j with
  | zero =>
    simp only [reconAux]
    rfl
  | succ i ihi =>
    induction j with
    | zero =>
      simp only [reconAux]
      rfl
    | succ j ihj =>
      unfold reconAux
      rw [ihi (by omega) j (by omega), ihj (by omega), ihi (by omega) (j + 1) hj]
      simp only [subblockParity]
      have h1 : B ⟨i, by omega⟩ ⟨j, by omega⟩ + B ⟨i, by omega⟩ ⟨j, by omega⟩ = 0 := zmod2_add_self _
      have h2 : B ⟨i + 1, hi⟩ ⟨j, by omega⟩ + B ⟨i + 1, hi⟩ ⟨j, by omega⟩ = 0 := zmod2_add_self _
      have h3 : B ⟨i, by omega⟩ ⟨j + 1, hj⟩ + B ⟨i, by omega⟩ ⟨j + 1, hj⟩ = 0 := zmod2_add_self _
      calc
        B ⟨i, by omega⟩ ⟨j, by omega⟩ + B ⟨i + 1, hi⟩ ⟨j, by omega⟩ +
            B ⟨i, by omega⟩ ⟨j + 1, hj⟩ + B ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ +
            B ⟨i, by omega⟩ ⟨j, by omega⟩ + B ⟨i + 1, hi⟩ ⟨j, by omega⟩ +
            B ⟨i, by omega⟩ ⟨j + 1, hj⟩
          = (B ⟨i, by omega⟩ ⟨j, by omega⟩ + B ⟨i, by omega⟩ ⟨j, by omega⟩) +
            (B ⟨i + 1, hi⟩ ⟨j, by omega⟩ + B ⟨i + 1, hi⟩ ⟨j, by omega⟩) +
            (B ⟨i, by omega⟩ ⟨j + 1, hj⟩ + B ⟨i, by omega⟩ ⟨j + 1, hj⟩) +
            B ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ := by ring
        _ = B ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ := by rw [h1, h2, h3]; simp

private lemma subblockParity_recon (n : ℕ) (r : Fin 5 → ZMod 2) (c : Fin n → ZMod 2)
    (D : Fin n × Fin 4 → ZMod 2) :
    subblockParity n (recon n r c D) = D := by
  funext ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  simp only [subblockParity, recon, reconAux]
  set x00 := reconAux n r c D i j (by omega) (by omega)
  set x10 := reconAux n r c D (i + 1) j (by omega) (by omega)
  set x01 := reconAux n r c D i (j + 1) (by omega) (by omega)
  calc
    x00 + x10 + x01 + (D (⟨i, hi⟩, ⟨j, hj⟩) + x00 + x10 + x01)
      = (x00 + x00) + (x10 + x10) + (x01 + x01) + D (⟨i, hi⟩, ⟨j, hj⟩) := by ring
    _ = D (⟨i, hi⟩, ⟨j, hj⟩) := by
      rw [zmod2_add_self x00, zmod2_add_self x10, zmod2_add_self x01]; simp

private lemma count_balanced_D (n : ℕ) :
    (Finset.univ.filter fun D : Fin n × Fin 4 → ZMod 2 =>
      (Finset.univ.filter fun p : Fin n × Fin 4 => D p = 0).card =
      (Finset.univ.filter fun p : Fin n × Fin 4 => D p = 1).card).card =
      (4 * n).choose (2 * n) := by
  have hbij :
      (Finset.univ.filter fun D : Fin n × Fin 4 → ZMod 2 =>
        (Finset.univ.filter fun p : Fin n × Fin 4 => D p = 0).card =
        (Finset.univ.filter fun p : Fin n × Fin 4 => D p = 1).card).card =
      ((Finset.univ : Finset (Fin n × Fin 4)).powersetCard (2 * n)).card := by
    refine Finset.card_bij
      (fun D _ => Finset.univ.filter fun p : Fin n × Fin 4 => D p = 1) ?_ ?_ ?_
    · intro D hD
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      have htot : (Finset.univ.filter fun p : Fin n × Fin 4 => D p = 0).card +
          (Finset.univ.filter fun p : Fin n × Fin 4 => D p = 1).card =
          (Finset.univ : Finset (Fin n × Fin 4)).card := by
        have hnot : (Finset.univ.filter fun p : Fin n × Fin 4 => D p = 1) =
            (Finset.univ.filter fun p : Fin n × Fin 4 => ¬ (D p = 0)) := by
          ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rcases zmod2_eq_zero_or_one (D p) with h | h <;> simp [h]
        rw [hnot]
        exact Finset.card_filter_add_card_filter_not _
      have hcard : (Finset.univ : Finset (Fin n × Fin 4)).card = 4 * n := by
        simp [Fintype.card_prod]; ring
      omega
    · intro D1 _ D2 _ hEq
      funext p
      have hp : (D1 p = 1) ↔ (D2 p = 1) := by
        have := Finset.ext_iff.mp hEq p
        simpa using this
      rcases zmod2_eq_zero_or_one (D1 p) with h1 | h1 <;>
        rcases zmod2_eq_zero_or_one (D2 p) with h2 | h2 <;> simp_all
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      refine ⟨fun p => if p ∈ S then 1 else 0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have h1 : (Finset.univ.filter fun p : Fin n × Fin 4 =>
            (if p ∈ S then (1 : ZMod 2) else 0) = 1) = S := by
          ext p; simp
        have h0 : (Finset.univ.filter fun p : Fin n × Fin 4 =>
            (if p ∈ S then (1 : ZMod 2) else 0) = 0) =
            Finset.univ.filter (fun p => p ∉ S) := by
          ext p; simp
        rw [h1, h0, hS.2]
        have htot : (Finset.univ.filter fun p : Fin n × Fin 4 => p ∈ S).card +
            (Finset.univ.filter fun p : Fin n × Fin 4 => p ∉ S).card =
            (Finset.univ : Finset (Fin n × Fin 4)).card :=
          Finset.card_filter_add_card_filter_not _
        have hS' : (Finset.univ.filter fun p : Fin n × Fin 4 => p ∈ S) = S := by ext p; simp
        have hcard : (Finset.univ : Finset (Fin n × Fin 4)).card = 4 * n := by
          simp [Fintype.card_prod]; ring
        rw [hS', hS.2, hcard] at htot
        omega
      · ext p; simp
  rw [hbij, Finset.card_powersetCard]
  have hcard : (Finset.univ : Finset (Fin n × Fin 4)).card = 4 * n := by
    simp [Fintype.card_prod]; ring
  rw [hcard]

end OMA.A183767Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a183767.main := by
  intro n _
  unfold OMA.S_oeis_a183767.a OMA.S_oeis_a183767.rawCount
  let balD := Finset.univ.filter fun D : Fin n × Fin 4 → ZMod 2 =>
    (Finset.univ.filter fun p : Fin n × Fin 4 => D p = 0).card =
    (Finset.univ.filter fun p : Fin n × Fin 4 => D p = 1).card
  have hbij :
      (Finset.univ.filter fun B : Fin (n + 1) → Fin 5 → ZMod 2 =>
        (Finset.univ.filter fun p : Fin n × Fin 4 =>
          OMA.S_oeis_a183767.subblockParity n B p = 0).card =
        (Finset.univ.filter fun p : Fin n × Fin 4 =>
          OMA.S_oeis_a183767.subblockParity n B p = 1).card).card =
      ((Finset.univ : Finset (Fin 5 → ZMod 2)) ×ˢ
        (Finset.univ : Finset (Fin n → ZMod 2)) ×ˢ balD).card := by
    refine Finset.card_bij
      (fun B _ => (B 0, fun i : Fin n => B i.succ 0, OMA.S_oeis_a183767.subblockParity n B))
      ?_ ?_ ?_
    · intro B hB
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hB
      simp only [Finset.mem_product, Finset.mem_univ, true_and, balD, Finset.mem_filter]
      exact hB
    · intro B1 _ B2 _ hEq
      have hr : B1 0 = B2 0 := congrArg Prod.fst hEq
      have hc : (fun i : Fin n => B1 i.succ 0) = (fun i : Fin n => B2 i.succ 0) :=
        congrArg (fun x => x.2.1) hEq
      have hD : OMA.S_oeis_a183767.subblockParity n B1 =
          OMA.S_oeis_a183767.subblockParity n B2 := congrArg (fun x => x.2.2) hEq
      rw [← OMA.A183767Proof.recon_left n B1, ← OMA.A183767Proof.recon_left n B2, hr, hc, hD]
    · rintro ⟨r, c, D⟩ hmem
      simp only [Finset.mem_product, Finset.mem_univ, true_and, balD, Finset.mem_filter] at hmem
      refine ⟨OMA.A183767Proof.recon n r c D, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          OMA.A183767Proof.subblockParity_recon]
        exact hmem
      · refine Prod.ext ?_ (Prod.ext ?_ (OMA.A183767Proof.subblockParity_recon n r c D))
        · funext j; simp [OMA.A183767Proof.recon, OMA.A183767Proof.reconAux]
        · funext i; simp [OMA.A183767Proof.recon, OMA.A183767Proof.reconAux]
  rw [hbij, Finset.card_product, Finset.card_product, OMA.A183767Proof.count_balanced_D n]
  have h5 : (Finset.univ : Finset (Fin 5 → ZMod 2)).card = 32 := by simp [Fintype.card_pi]
  have hn : (Finset.univ : Finset (Fin n → ZMod 2)).card = 2 ^ n := by simp [Fintype.card_pi]
  rw [h5, hn]
  exact Nat.mul_div_right _ (by decide)
