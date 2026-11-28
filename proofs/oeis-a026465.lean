import OMAStatements.S_oeis_a026465

namespace OMA.S_oeis_a026465

/-- Expand a list of lengths into alternating runs of the two bits. -/
private def encode (b : Bool) : List ℕ → List Bool
  | [] => []
  | l::r => List.replicate l b ++ encode (!b) r

private theorem runAux_eq (n m : ℕ) (b : Bool) (t : List Bool) :
    runAux b m (List.replicate n b ++ t) = runAux b (m+n) t := by
  induction n generalizing m with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,runAux,ih,Nat.add_right_comm,Nat.add_assoc]

private theorem runAux_tail (r : List ℕ) (hr : ∀ l ∈ r, 0<l) (b : Bool) (m : ℕ) :
    runAux b m (encode (!b) r) = m::r := by
  induction r generalizing b m with
  | nil => simp [encode,runAux]
  | cons l r ih =>
    have hl := hr l (by simp)
    have htail : ∀ l ∈ r, 0<l := fun l h => hr l (by simp [h])
    obtain _|l := l
    · omega
    · cases b
      · simpa [encode,List.replicate_succ,runAux,runAux_eq,Nat.add_comm] using ih htail true (l+1)
      · simpa [encode,List.replicate_succ,runAux,runAux_eq,Nat.add_comm] using ih htail false (l+1)

private theorem lengths_encode (r : List ℕ) (hr : ∀ l ∈ r, 0<l) (b : Bool) :
    runLengths (encode b r) = r := by
  cases r with
  | nil => rfl
  | cons l r =>
    have hl := hr l (by simp)
    have htail : ∀ l ∈ r, 0<l := fun l h => hr l (by simp [h])
    obtain _|l := l
    · omega
    · simp [encode,List.replicate_succ,runLengths,runAux_eq,runAux_tail r htail,Nat.add_comm]

private theorem small_lengths (k : ℕ) : ∀ l ∈ runStage k, l=1 ∨ l=2 := by
  induction k with
  | zero => simp [runStage]
  | succ k ih =>
    intro l hl
    obtain ⟨a,ha,hl⟩ := List.mem_flatMap.mp hl
    rcases ih a ha with rfl|rfl <;> simp [alpha] at hl <;> tauto

private theorem tau_twice (r : List ℕ) (hr : ∀ l ∈ r, l=1 ∨ l=2) (b : Bool) :
    tau (tau (encode b r)) = encode b (r.flatMap alpha) := by
  induction r generalizing b with
  | nil => rfl
  | cons l r ih =>
    have hl := hr l (by simp)
    have htail : ∀ l ∈ r, l=1 ∨ l=2 := fun l h => hr l (by simp [h])
    have hrec := ih htail (!b)
    rcases hl with rfl|rfl <;> cases b <;>
      simpa [tau,encode,alpha] using hrec

private theorem stage_encoding (k : ℕ) : thueStage (2*k) = encode false (runStage k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, show 2*k+2=(2*k+1)+1 by omega, thueStage, thueStage, ih]
    exact tau_twice _ (small_lengths k) _

private theorem finite_runs (k : ℕ) : runLengths (thueStage (2*k)) = runStage k := by
  rw [stage_encoding]
  exact lengths_encode _ (fun l h => by rcases small_lengths k l h with rfl|rfl <;> decide) _

/-- Every iterate has a proper extension ending in another complete run. -/
private theorem extends_stage (k : ℕ) : ∃ t, runStage (k+1) = (runStage k ++ t) ++ [1] := by
  induction k with
  | zero => exact ⟨[2],rfl⟩
  | succ k ih =>
    obtain ⟨t,ht⟩ := ih
    refine ⟨t.flatMap alpha ++ [1,2],?_⟩
    change (runStage (k+1)).flatMap alpha = ((runStage k).flatMap alpha ++ _) ++ [1]
    rw [ht]
    simp [List.flatMap_append,alpha,List.append_assoc]

private theorem prefix_iff (r : List ℕ) : runPrefix r ↔ ∃ k : ℕ, r <+: runStage k := by
  constructor
  · rintro ⟨k,h⟩
    rw [finite_runs] at h
    exact ⟨k,h.trans (List.dropLast_prefix _)⟩
  · rintro ⟨k,h⟩
    obtain ⟨t,ht⟩ := extends_stage k
    refine ⟨k+1,?_⟩
    rw [finite_runs,ht]
    simpa using h.trans (List.prefix_append (runStage k) t)

private theorem alpha_pal (l : ℕ) : (alpha l).reverse = alpha l := by
  rcases l with _|_|_|l <;> rfl

private theorem reverse_flat (r : List ℕ) : (r.flatMap alpha).reverse = r.reverse.flatMap alpha := by
  induction r with
  | nil => rfl
  | cons l r ih => simp [List.reverse_append,ih,alpha_pal,List.flatMap_append]

private theorem pal_stage (k : ℕ) : (runStage k).reverse = runStage k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [runStage,reverse_flat,ih]

private theorem long_stage (k : ℕ) : k ≤ (runStage k).length := by
  induction k with
  | zero => omega
  | succ k ih =>
    obtain ⟨t,ht⟩ := extends_stage k
    rw [ht]
    simp
    omega

end OMA.S_oeis_a026465

open OMA.S_oeis_a026465 in
theorem OMA.solution : type_of% @OMA.S_oeis_a026465.main := by
  refine ⟨prefix_iff, fun m => ?_⟩
  exact ⟨runStage m, runStage m, long_stage m, pal_stage m, (prefix_iff _).mpr ⟨m, by simp⟩, .refl _⟩
