import A393317.Defs

/-!
# Stage 1: exact halting times of machines 378, 1351 and 1447
-/

namespace A393317

/-! ## Infrastructure -/

/-- Run `k` steps; `none` if the machine halts within these steps. -/
def run (m : ℕ) : ℕ → Config → Option Config
  | 0, c => some c
  | k + 1, c => (step m c).bind (run m k)

/-- Result of a right move from position `p` (state `s`, tape `T` after the move). -/
def exitR (s : Bool) (p : ℕ) (T : ℕ → Bool) : Option Config :=
  if p = 0 then none else some ⟨s, p - 1, T⟩

@[simp] theorem exitR_succ (s : Bool) (p : ℕ) (T : ℕ → Bool) :
    exitR s (p + 1) T = some ⟨s, p, T⟩ := by simp [exitR]

@[simp] theorem exitR_zero (s : Bool) (T : ℕ → Bool) : exitR s 0 T = none := by simp [exitR]

theorem run_step {m : ℕ} {c c' : Config} (h : step m c = some c') (k : ℕ) :
    run m (k + 1) c = run m k c' := by simp [run, h]

theorem run_add (m j k : ℕ) (c : Config) : run m (j + k) c = (run m j c).bind (run m k) := by
  induction j generalizing c with
  | zero => simp [run]
  | succ j ih =>
    rw [Nat.add_right_comm]
    simp only [run]
    cases step m c with
    | none => simp
    | some c' => simpa using ih c'

theorem run_trans {m j k : ℕ} {a b c : Config} (h1 : run m j a = some b)
    (h2 : run m k b = some c) : run m (j + k) a = some c := by
  rw [run_add, h1]; simpa using h2

theorem halts_of_run {m : ℕ} : ∀ {k : ℕ} {c c' : Config}, run m k c = some c' →
    step m c' = none → HaltsAfter m c (k + 1)
  | 0, c, c', h, h' => by
    simp only [run, Option.some.injEq] at h
    subst h; exact HaltsAfter.halt h'
  | k + 1, c, c', h, h' => by
    simp only [run] at h
    cases hs : step m c with
    | none => simp [hs] at h
    | some c1 =>
      rw [hs] at h
      exact HaltsAfter.next hs (halts_of_run (by simpa using h) h')

theorem halts_trans {m j t : ℕ} {a b : Config} (h1 : run m j a = some b)
    (h2 : HaltsAfter m b t) : HaltsAfter m a (j + t) := by
  induction j generalizing a with
  | zero =>
    simp only [run, Option.some.injEq] at h1
    subst h1; simpa using h2
  | succ j ih =>
    simp only [run] at h1
    cases hs : step m a with
    | none => simp [hs] at h1
    | some c1 =>
      rw [hs] at h1
      have := HaltsAfter.next hs (ih (by simpa using h1))
      rwa [Nat.add_right_comm]

/-- `Exits m c τ s p T`: started in `c`, the machine performs `τ` steps and then one more step,
which is a right move from position `p` into state `s`, leaving the tape as `T`. -/
def Exits (m : ℕ) (c : Config) (τ : ℕ) (s : Bool) (p : ℕ) (T : ℕ → Bool) : Prop :=
  ∃ c', run m τ c = some c' ∧ step m c' = exitR s p T

theorem Exits.of_step {m : ℕ} {c : Config} {s : Bool} {p : ℕ} {T : ℕ → Bool}
    (h : step m c = exitR s p T) : Exits m c 0 s p T := ⟨c, rfl, h⟩

theorem Exits.run_eq {m : ℕ} {c : Config} {τ : ℕ} {s : Bool} {p : ℕ} {T : ℕ → Bool}
    (h : Exits m c τ s (p + 1) T) : A393317.run m (τ + 1) c = some ⟨s, p, T⟩ := by
  obtain ⟨c', h1, h2⟩ := h
  rw [run_add, h1]
  simpa [A393317.run] using h2

theorem Exits.halts {m : ℕ} {c : Config} {τ : ℕ} {s : Bool} {T : ℕ → Bool}
    (h : Exits m c τ s 0 T) : HaltsAfter m c (τ + 1) := by
  obtain ⟨c', h1, h2⟩ := h
  exact halts_of_run h1 (by simpa using h2)

theorem Exits.of_run {m j τ : ℕ} {a b : Config} {s : Bool} {p : ℕ} {T : ℕ → Bool}
    (h1 : run m j a = some b) (h2 : Exits m b τ s p T) : Exits m a (j + τ) s p T := by
  obtain ⟨c', h3, h4⟩ := h2
  exact ⟨c', run_trans h1 h3, h4⟩

theorem run_one {m : ℕ} {c c' : Config} (h : step m c = some c') : run m 1 c = some c' := by
  simp [run, h]

/-- Unfolding of `step` for a left move. -/
theorem step_left {m x : ℕ} {s b : Bool} {p : ℕ} {T : ℕ → Bool} (hb : T p = b)
    (hd : digit m s b = x) (hx : x % 2 = 0) :
    step m ⟨s, p, T⟩ = some ⟨decide (x < 4), p + 1, Function.update T p (decide (x / 2 % 2 = 1))⟩ := by
  simp [step, hb, hd, hx]

/-- Unfolding of `step` for a right move. -/
theorem step_right {m x : ℕ} {s b : Bool} {p : ℕ} {T : ℕ → Bool} (hb : T p = b)
    (hd : digit m s b = x) (hx : x % 2 = 1) :
    step m ⟨s, p, T⟩ = exitR (decide (x < 4)) p (Function.update T p (decide (x / 2 % 2 = 1))) := by
  simp [step, hb, hd, hx, exitR]

theorem update_same_val {T : ℕ → Bool} {p : ℕ} {b : Bool} (h : T p = b) :
    Function.update T p b = T := by
  subst h; exact Function.update_eq_self p T

/-! ## Machine 378 -/

section M378

theorem s378_U1 {p : ℕ} {T : ℕ → Bool} (h : T p = true) :
    step 378 ⟨true, p, T⟩ = some ⟨true, p + 1, Function.update T p false⟩ := by
  have := step_left (m := 378) (x := 0) (s := true) h (by decide) (by decide)
  simpa using this

theorem s378_U0 {p : ℕ} {T : ℕ → Bool} (h : T p = false) :
    step 378 ⟨true, p, T⟩ = exitR false p T := by
  have := step_right (m := 378) (x := 5) (s := true) h (by decide) (by decide)
  simpa [update_same_val h] using this

theorem s378_D1 {p : ℕ} {T : ℕ → Bool} (h : T p = true) :
    step 378 ⟨false, p, T⟩ = exitR false p T := by
  have := step_right (m := 378) (x := 7) (s := false) h (by decide) (by decide)
  simpa [update_same_val h] using this

theorem s378_D0 {p : ℕ} {T : ℕ → Bool} (h : T p = false) :
    step 378 ⟨false, p, T⟩ = some ⟨true, p + 1, Function.update T p true⟩ := by
  have := step_left (m := 378) (x := 2) (s := false) h (by decide) (by decide)
  simpa using this

/-- Machine 378, state `U` on a block of `k` ones followed by a zero: after `τ + 1` steps with
`τ + 4 = 2^(k+2)` the head leaves the block on the right in state `D`, tape unchanged. -/
theorem exits378 : ∀ (k p : ℕ) (T : ℕ → Bool), (∀ i < k, T (p + i) = true) → T (p + k) = false →
    ∃ τ, τ + 4 = 2 ^ (k + 2) ∧ Exits 378 ⟨true, p, T⟩ τ false p T
  | 0, p, T, _, h0 => ⟨0, by norm_num, Exits.of_step (s378_U0 (by simpa using h0))⟩
  | k + 1, p, T, h1, h0 => by
    have hp : T p = true := by simpa using h1 0 (by omega)
    have hT1 : ∀ i < k, Function.update T p false (p + 1 + i) = true := fun i hi => by
      rw [Function.update_of_ne (by omega)]
      have := h1 (i + 1) (by omega)
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this
    have hT1' : Function.update T p false (p + 1 + k) = false := by
      rw [Function.update_of_ne (by omega)]
      rwa [Nat.add_right_comm, Nat.add_assoc]
    obtain ⟨τ1, e1, x1⟩ := exits378 k (p + 1) _ hT1 hT1'
    have hT : ∀ i < k, T (p + 1 + i) = true := fun i hi => by
      have := h1 (i + 1) (by omega)
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this
    have hT' : T (p + 1 + k) = false := by rwa [Nat.add_right_comm, Nat.add_assoc]
    obtain ⟨τ2, e2, x2⟩ := exits378 k (p + 1) T hT hT'
    have a1 := run_one (s378_U1 hp)
    have a2 := x1.run_eq
    have a3 : step 378 ⟨false, p, Function.update T p false⟩ = some ⟨true, p + 1, T⟩ := by
      rw [s378_D0 (by simp)]
      simp [update_same_val hp]
    have a4 := x2.run_eq
    have r := run_trans (run_trans (run_trans a1 a2) (run_one a3)) a4
    refine ⟨1 + (τ1 + 1) + 1 + (τ2 + 1), ?_, ⟨_, r, s378_D1 hp⟩⟩
    rw [show k + 1 + 2 = (k + 2) + 1 from rfl, pow_succ]
    omega

/-- **Machine 378**: on every input `x` whose binary expansion ends in exactly `k` ones,
the machine halts after exactly `2^(k+2) - 3` steps. -/
theorem machine378 (x k : ℕ) (h1 : ∀ i < k, x.testBit i = true) (h0 : x.testBit k = false) :
    HaltsAfter 378 (init x) (2 ^ (k + 2) - 3) := by
  obtain ⟨τ, e, h⟩ := exits378 k 0 (fun i => x.testBit i) (by simpa using h1) (by simpa using h0)
  have := h.halts
  have e' : 2 ^ (k + 2) - 3 = τ + 1 := by omega
  rw [e']; exact this

end M378


/-! ## Machine 1351 -/

section M1351

theorem s1351_U1 {p : ℕ} {T : ℕ → Bool} (h : T p = true) :
    step 1351 ⟨true, p, T⟩ = some ⟨true, p + 1, T⟩ := by
  have := step_left (m := 1351) (x := 2) (s := true) h (by decide) (by decide)
  simpa [update_same_val h] using this

theorem s1351_U0 {p : ℕ} {T : ℕ → Bool} (h : T p = false) :
    step 1351 ⟨true, p, T⟩ = exitR false p T := by
  have := step_right (m := 1351) (x := 5) (s := true) h (by decide) (by decide)
  simpa [update_same_val h] using this

theorem s1351_D1 {p : ℕ} {T : ℕ → Bool} (h : T p = true) :
    step 1351 ⟨false, p, T⟩ = some ⟨true, p + 1, Function.update T p false⟩ := by
  have := step_left (m := 1351) (x := 0) (s := false) h (by decide) (by decide)
  simpa using this

theorem s1351_D0 {p : ℕ} {T : ℕ → Bool} (h : T p = false) :
    step 1351 ⟨false, p, T⟩ = exitR false p (Function.update T p true) := by
  have := step_right (m := 1351) (x := 7) (s := false) h (by decide) (by decide)
  simpa using this

/-- State `U` walks left over a block of ones without changing the tape. -/
theorem scan1351 : ∀ (a p : ℕ) (T : ℕ → Bool), (∀ i < a, T (p + i) = true) →
    run 1351 a ⟨true, p, T⟩ = some ⟨true, p + a, T⟩
  | 0, p, T, _ => rfl
  | a + 1, p, T, h => by
    have hp : T p = true := by simpa using h 0 (by omega)
    rw [run_step (s1351_U1 hp), scan1351 a (p + 1) T (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this)]
    simp [Nat.add_assoc, Nat.add_comm 1 a]

/-- Machine 1351, state `D` at offset `i` inside a block of `i + 1 + a` ones (based at `r`)
that is followed by a zero: after `τ + 1` steps, `τ + 2^(a+2) + i + 2 = 2^(i+a+3)`, the head
leaves the block on the right in state `D`, tape unchanged. -/
theorem exits1351 (i a r : ℕ) (T : ℕ → Bool) (h1 : ∀ k < i + 1 + a, T (r + k) = true)
    (h0 : T (r + (i + 1 + a)) = false) :
    ∃ τ, τ + 2 ^ (a + 2) + i + 2 = 2 ^ (i + a + 3) ∧ Exits 1351 ⟨false, r + i, T⟩ τ false r T := by
  have hp : T (r + i) = true := h1 i (by omega)
  set T1 := Function.update T (r + i) false with hT1
  -- step 1: turn around, clearing the cell
  have a1 : run 1351 1 ⟨false, r + i, T⟩ = some ⟨true, r + i + 1, T1⟩ := run_one (s1351_D1 hp)
  -- scan over the `a` ones above
  have a2 : run 1351 a ⟨true, r + i + 1, T1⟩ = some ⟨true, r + i + 1 + a, T1⟩ :=
    scan1351 a _ T1 (fun k hk => by
      rw [hT1, Function.update_of_ne (by omega)]
      have := h1 (i + 1 + k) (by omega)
      rwa [← Nat.add_assoc, ← Nat.add_assoc] at this)
  have hz : T1 (r + i + 1 + a) = false := by
    rw [hT1, Function.update_of_ne (by omega)]
    rwa [← Nat.add_assoc, ← Nat.add_assoc] at h0
  -- turn at the zero
  have a3 : run 1351 1 ⟨true, r + i + 1 + a, T1⟩ = some ⟨false, r + i + a, T1⟩ := by
    apply run_one
    rw [s1351_U0 hz, show r + i + 1 + a = (r + i + a) + 1 by omega, exitR_succ]
  -- walk back through the block above (recursive call), arriving at `r + i`
  have a4 : ∃ X, X + a + 4 = 2 ^ (a + 2) ∧
      run 1351 X ⟨false, r + i + a, T1⟩ = some ⟨false, r + i, T1⟩ := by
    cases a with
    | zero => exact ⟨0, by norm_num, rfl⟩
    | succ a' =>
      obtain ⟨σ, eσ, xσ⟩ := exits1351 a' 0 (r + i + 1) T1 (fun k hk => by
        rw [hT1, Function.update_of_ne (by omega)]
        have := h1 (i + 1 + k) (by omega)
        rwa [← Nat.add_assoc, ← Nat.add_assoc] at this) (by
        have : r + i + 1 + (a' + 1 + 0) = r + i + 1 + (a' + 1) := by omega
        rw [this]; exact hz)
      refine ⟨σ + 1, ?_, ?_⟩
      · have e2 : (2 : ℕ) ^ (a' + 0 + 3) = 2 ^ (a' + 1 + 2) := by congr 1
        have e3 : (2 : ℕ) ^ (0 + 2) = 4 := by norm_num
        rw [e2, e3] at eσ; omega
      · have := xσ.run_eq
        rwa [show r + i + 1 + a' = r + i + (a' + 1) by omega] at this
  obtain ⟨X, eX, a4⟩ := a4
  have hT1p : T1 (r + i) = false := by simp [hT1]
  have a5 : step 1351 ⟨false, r + i, T1⟩ = exitR false (r + i) T := by
    rw [s1351_D0 hT1p, hT1, Function.update_idem, update_same_val hp]
  have pre := run_trans (run_trans (run_trans a1 a2) a3) a4
  cases i with
  | zero =>
    refine ⟨1 + a + 1 + X, ?_, ⟨_, pre, by simpa using a5⟩⟩
    have e : (2 : ℕ) ^ (0 + a + 3) = 2 * 2 ^ (a + 2) := by
      rw [show 0 + a + 3 = (a + 2) + 1 by omega, pow_succ]; ring
    rw [e]; generalize (2 : ℕ) ^ (a + 2) = P at eX ⊢; omega
  | succ i' =>
    have a5' : run 1351 1 ⟨false, r + (i' + 1), T1⟩ = some ⟨false, r + i', T⟩ := by
      apply run_one
      rw [a5, show r + (i' + 1) = (r + i') + 1 by omega, exitR_succ]
    obtain ⟨τ', eτ', xτ'⟩ := exits1351 i' (a + 1) r T (fun k hk => h1 k (by omega)) (by
      rw [show i' + 1 + (a + 1) = i' + 1 + 1 + a by omega]; exact h0)
    refine ⟨1 + a + 1 + X + 1 + τ', ?_, Exits.of_run (run_trans pre a5') xτ'⟩
    have e1 : (2 : ℕ) ^ (a + 1 + 2) = 2 * 2 ^ (a + 2) := by rw [pow_succ]; ring
    have e2 : (2 : ℕ) ^ (i' + (a + 1) + 3) = 2 ^ (i' + 1 + a + 3) := by congr 1; omega
    rw [e1, e2] at eτ'
    omega
termination_by (i + a, i)
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- **Machine 1351**: on every input `x` whose binary expansion ends in exactly `k` ones,
the machine halts after exactly `2^(k+2) - 3` steps. -/
theorem machine1351 (x k : ℕ) (h1 : ∀ i < k, x.testBit i = true) (h0 : x.testBit k = false) :
    HaltsAfter 1351 (init x) (2 ^ (k + 2) - 3) := by
  set T : ℕ → Bool := fun i => x.testBit i with hT
  have sc : run 1351 k ⟨true, 0, T⟩ = some ⟨true, 0 + k, T⟩ :=
    scan1351 k 0 T (by simpa [hT] using h1)
  have st : step 1351 ⟨true, 0 + k, T⟩ = exitR false (0 + k) T := s1351_U0 (by simpa [hT] using h0)
  cases k with
  | zero =>
    have := halts_of_run sc (by simpa using st)
    simpa [init] using this
  | succ k' =>
    have st' : run 1351 1 ⟨true, 0 + (k' + 1), T⟩ = some ⟨false, 0 + k', T⟩ := by
      apply run_one; rw [st, show 0 + (k' + 1) = (0 + k') + 1 by omega, exitR_succ]
    obtain ⟨τ, eτ, xτ⟩ := exits1351 k' 0 0 T (fun i hi => by simpa [hT] using h1 i (by omega))
      (by simpa [hT] using h0)
    have := halts_trans (run_trans sc st') xτ.halts
    have e : 2 ^ (k' + 1 + 2) - 3 = k' + 1 + 1 + (τ + 1) := by
      have e2 : (2 : ℕ) ^ (k' + 0 + 3) = 2 ^ (k' + 1 + 2) := by congr 1
      have e3 : (2 : ℕ) ^ (0 + 2) = 4 := by norm_num
      rw [e2, e3] at eτ; omega
    rw [e]; exact this

end M1351

/-! ## Machine 1447 -/

section M1447

theorem s1447_U1 {p : ℕ} {T : ℕ → Bool} (h : T p = true) :
    step 1447 ⟨true, p, T⟩ = some ⟨true, p + 1, T⟩ := by
  have := step_left (m := 1447) (x := 2) (s := true) h (by decide) (by decide)
  simpa [update_same_val h] using this

theorem s1447_U0 {p : ℕ} {T : ℕ → Bool} (h : T p = false) :
    step 1447 ⟨true, p, T⟩ = some ⟨false, p + 1, Function.update T p true⟩ := by
  have := step_left (m := 1447) (x := 6) (s := true) h (by decide) (by decide)
  simpa using this

theorem s1447_D1 {p : ℕ} {T : ℕ → Bool} (h : T p = true) :
    step 1447 ⟨false, p, T⟩ = some ⟨false, p + 1, Function.update T p false⟩ := by
  have := step_left (m := 1447) (x := 4) (s := false) h (by decide) (by decide)
  simpa using this

theorem s1447_D0 {p : ℕ} {T : ℕ → Bool} (h : T p = false) :
    step 1447 ⟨false, p, T⟩ = exitR false p (Function.update T p true) := by
  have := step_right (m := 1447) (x := 7) (s := false) h (by decide) (by decide)
  simpa using this

/-- The tape with ones exactly on the cells `0, …, N-1`. -/
def ones (N : ℕ) : ℕ → Bool := fun i => decide (i < N)

/-- Overwrite the cells `q, …, q+len-1` with `b`. -/
def fill (T : ℕ → Bool) (q len : ℕ) (b : Bool) : ℕ → Bool :=
  fun i => if q ≤ i ∧ i < q + len then b else T i

theorem scan1447 : ∀ (a p : ℕ) (T : ℕ → Bool), (∀ i < a, T (p + i) = true) →
    run 1447 a ⟨true, p, T⟩ = some ⟨true, p + a, T⟩
  | 0, p, T, _ => rfl
  | a + 1, p, T, h => by
    have hp : T p = true := by simpa using h 0 (by omega)
    rw [run_step (s1447_U1 hp), scan1447 a (p + 1) T (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this)]
    simp [Nat.add_assoc, Nat.add_comm 1 a]

/-- State `D` moving left over `j` ones turns them into zeros. -/
theorem left1447 : ∀ (j q : ℕ) (T : ℕ → Bool), (∀ i < j, T (q + i) = true) →
    run 1447 j ⟨false, q, T⟩ = some ⟨false, q + j, fill T q j false⟩
  | 0, q, T, _ => by
    simp only [run, Nat.add_zero, Option.some.injEq, Config.mk.injEq, true_and]
    funext i; simp only [fill]; rw [if_neg (by omega)]
  | j + 1, q, T, h => by
    have hq : T q = true := by simpa using h 0 (by omega)
    rw [run_step (s1447_D1 hq), left1447 j (q + 1) _ (fun i hi => by
      rw [Function.update_of_ne (by omega)]
      have := h (i + 1) (by omega)
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this)]
    simp only [Option.some.injEq, Config.mk.injEq, true_and]
    refine ⟨by omega, ?_⟩
    funext i
    by_cases hi : i = q
    · subst hi; simp [fill]
    · simp only [fill, Function.update_of_ne hi]
      by_cases h1 : q + 1 ≤ i ∧ i < q + 1 + j
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1, if_neg (by omega)]

/-- State `D` moving right over `j + 1` zeros turns them into ones and leaves on the right. -/
theorem right1447 : ∀ (j q : ℕ) (T : ℕ → Bool), (∀ i < j + 1, T (q + i) = false) →
    Exits 1447 ⟨false, q + j, T⟩ j false q (fill T q (j + 1) true)
  | 0, q, T, h => by
    have hq : T q = false := by simpa using h 0 (by omega)
    apply Exits.of_step
    rw [Nat.add_zero, s1447_D0 hq]
    congr 1
    funext i
    by_cases hi : i = q
    · subst hi; simp [fill]
    · rw [Function.update_of_ne hi]; simp only [fill]; rw [if_neg (by omega)]
  | j + 1, q, T, h => by
    have hq : T (q + (j + 1)) = false := h (j + 1) (by omega)
    have a1 : run 1447 1 ⟨false, q + (j + 1), T⟩ =
        some ⟨false, q + j, Function.update T (q + (j + 1)) true⟩ := by
      apply run_one
      rw [s1447_D0 hq, show q + (j + 1) = (q + j) + 1 by omega, exitR_succ]
    have ih := right1447 j q (Function.update T (q + (j + 1)) true) (fun i hi => by
      rw [Function.update_of_ne (by omega)]; exact h i (by omega))
    have e : fill (Function.update T (q + (j + 1)) true) q (j + 1) true = fill T q (j + 1 + 1) true := by
      funext i
      by_cases hi : i = q + (j + 1)
      · subst hi; simp [fill]
      · simp only [fill, Function.update_of_ne hi]
        by_cases h1 : q ≤ i ∧ i < q + (j + 1)
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    rw [e] at ih
    have := Exits.of_run a1 ih
    rwa [Nat.add_comm 1 j] at this

/-- One sweep: state `D` on cell `q`, ones exactly on `0, …, q+m`: after `2m+3` steps the head
leaves cell `q` on the right, ones now exactly on `0, …, q+m+1`. -/
theorem sweep1447 (q m : ℕ) :
    Exits 1447 ⟨false, q, ones (q + m + 1)⟩ (2 * m + 2) false q (ones (q + m + 2)) := by
  have a1 := left1447 (m + 1) q (ones (q + m + 1)) (fun i hi => by simp [ones]; omega)
  set T2 := fill (ones (q + m + 1)) q (m + 1) false with hT2
  have hz : T2 (q + (m + 1)) = false := by simp [hT2, fill, ones]
  have a2 : run 1447 1 ⟨false, q + (m + 1), T2⟩ =
      some ⟨false, q + m, Function.update T2 (q + (m + 1)) true⟩ := by
    apply run_one
    rw [s1447_D0 hz, show q + (m + 1) = (q + m) + 1 by omega, exitR_succ]
  have a3 := right1447 m q (Function.update T2 (q + (m + 1)) true) (fun i hi => by
    rw [Function.update_of_ne (by omega)]
    simp only [hT2, fill]; rw [if_pos (by omega)])
  have e : fill (Function.update T2 (q + (m + 1)) true) q (m + 1) true = ones (q + m + 2) := by
    funext i
    simp only [fill]
    by_cases h1 : q ≤ i ∧ i < q + (m + 1)
    · rw [if_pos h1]; simp [ones]; omega
    · rw [if_neg h1]
      by_cases hi : i = q + (m + 1)
      · subst hi; simp [ones]; omega
      · rw [Function.update_of_ne hi]
        simp only [hT2, fill]; rw [if_neg h1]
        simp only [ones]
        congr 1
        apply propext
        constructor <;> intro <;> omega
  rw [e] at a3
  have := Exits.of_run (run_trans a1 a2) a3
  rwa [show m + 1 + 1 + m = 2 * m + 2 by omega] at this

/-- The sweeps `q, q-1, …, 0` together. -/
theorem loop1447 : ∀ (q m : ℕ),
    HaltsAfter 1447 ⟨false, q, ones (q + m + 1)⟩ ((q + 1) * (2 * m + 2 * q + 3))
  | 0, m => by
    have := (sweep1447 0 m).halts
    rwa [show 2 * m + 2 + 1 = (0 + 1) * (2 * m + 2 * 0 + 3) by ring] at this
  | q + 1, m => by
    have h1 := (sweep1447 (q + 1) m).run_eq
    have h2 := loop1447 q (m + 2)
    rw [show q + (m + 2) + 1 = q + 1 + m + 2 by omega] at h2
    have := halts_trans h1 h2
    rwa [show 2 * m + 2 + 1 + (q + 1) * (2 * (m + 2) + 2 * q + 3) =
      (q + 1 + 1) * (2 * m + 2 * (q + 1) + 3) by ring] at this

/-- **Machine 1447**: on the input `2^n - 1` (`n` ones) the machine halts after exactly
`2 (n+2)^2 - 1` steps. -/
theorem machine1447 (n : ℕ) : HaltsAfter 1447 (init (2 ^ n - 1)) (2 * (n + 2) ^ 2 - 1) := by
  have hi : init (2 ^ n - 1) = ⟨true, 0, ones n⟩ := by
    simp only [init, Config.mk.injEq, true_and]
    funext i; simp [ones, Nat.testBit_two_pow_sub_one]
  have a1 : run 1447 n ⟨true, 0, ones n⟩ = some ⟨true, 0 + n, ones n⟩ :=
    scan1447 n 0 (ones n) (fun i hi => by simp [ones]; omega)
  have e1 : Function.update (ones n) n true = ones (n + 1) := by
    funext i
    by_cases hi : i = n
    · subst hi; simp [ones]
    · rw [Function.update_of_ne hi]; simp only [ones]; congr 1; apply propext
      constructor <;> intro <;> omega
  have a2 : run 1447 1 ⟨true, 0 + n, ones n⟩ = some ⟨false, n + 1, ones (n + 1)⟩ := by
    apply run_one
    rw [Nat.zero_add, s1447_U0 (by simp [ones]), e1]
  have e2 : Function.update (ones (n + 1)) (n + 1) true = ones (n + 1 + 1) := by
    funext i
    by_cases hi : i = n + 1
    · subst hi; simp [ones]
    · rw [Function.update_of_ne hi]; simp only [ones]; congr 1; apply propext
      constructor <;> intro <;> omega
  have a3 : run 1447 1 ⟨false, n + 1, ones (n + 1)⟩ = some ⟨false, n, ones (n + 1 + 1)⟩ := by
    apply run_one
    rw [s1447_D0 (by simp [ones]), e2, exitR_succ]
  have h := halts_trans (run_trans (run_trans a1 a2) a3) (loop1447 n 1)
  rw [hi]
  have e : 2 * (n + 2) ^ 2 - 1 = n + 1 + 1 + (n + 1) * (2 * 1 + 2 * n + 3) := by
    have : 2 * (n + 2) ^ 2 = n + 1 + 1 + (n + 1) * (2 * 1 + 2 * n + 3) + 1 := by ring
    omega
  rw [e]; exact h

end M1447

/-! ## Consequences for A393317 -/

/-- Machines 378 and 1351 on the input `2^n - 1`. -/
theorem machine378_ones (n : ℕ) : HaltsAfter 378 (init (2 ^ n - 1)) (2 ^ (n + 2) - 3) :=
  machine378 _ n (fun i hi => by simp [Nat.testBit_two_pow_sub_one, hi])
    (by simp [Nat.testBit_two_pow_sub_one])

theorem machine1351_ones (n : ℕ) : HaltsAfter 1351 (init (2 ^ n - 1)) (2 ^ (n + 2) - 3) :=
  machine1351 _ n (fun i hi => by simp [Nat.testBit_two_pow_sub_one, hi])
    (by simp [Nat.testBit_two_pow_sub_one])

theorem ones_mem_range (n : ℕ) (hn : 1 ≤ n) : 2 ^ (n - 1) ≤ 2 ^ n - 1 ∧ 2 ^ n - 1 < 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have : 0 < 2 ^ k := by positivity
  rw [Nat.add_sub_cancel, pow_succ]; omega

/-- **Lower bound for A393317**: both `2^(n+2) - 3` and `2 (n+2)^2 - 1` occur as halting times
of some machine on some `n`-bit input (`n ≥ 1`). -/
theorem lower_bound (n : ℕ) (hn : 1 ≤ n) :
    2 ^ (n + 2) - 3 ∈ haltingTimes n ∧ 2 * (n + 2) ^ 2 - 1 ∈ haltingTimes n := by
  obtain ⟨h1, h2⟩ := ones_mem_range n hn
  exact ⟨⟨378, by norm_num, 2 ^ n - 1, h1, h2, machine378_ones n⟩,
    ⟨1447, by norm_num, 2 ^ n - 1, h1, h2, machine1447 n⟩⟩

end A393317
