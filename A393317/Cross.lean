import A393317.Defs

/-!
# Crossing sequences

A halting run is decomposed along the cell boundaries.  For the boundary to the right of cell `i`
we record the *history* `h_i`: the list of pairs (state in which the head enters cell `i` from the
right, state in which it leaves cell `i` to the right again).  Neighbouring histories are coupled
by a purely local relation `Compat` that only involves the initial content of the cell between
them, and the halting time is `|h_0| + 2 (|h_1| + |h_2| + ...)` with `h_0 = [(U, r)]`.
-/

namespace A393317

/-! ## Components of a transition -/

/-- New state (`true` = `U`). -/
def nxt (m : ℕ) (s b : Bool) : Bool := decide (digit m s b < 4)
/-- Symbol written. -/
def wrt (m : ℕ) (s b : Bool) : Bool := decide (digit m s b / 2 % 2 = 1)
/-- Does the head move right? -/
def rgt (m : ℕ) (s b : Bool) : Bool := decide (digit m s b % 2 = 1)

theorem step_of_rgt {m : ℕ} {s : Bool} {p : ℕ} {T : ℕ → Bool} (h : rgt m s (T p) = true) :
    step m ⟨s, p, T⟩ = if p = 0 then none else
      some ⟨nxt m s (T p), p - 1, Function.update T p (wrt m s (T p))⟩ := by
  have h' : digit m s (T p) % 2 = 1 := by simpa [rgt] using h
  simp [step, nxt, wrt, h']

theorem step_of_lft {m : ℕ} {s : Bool} {p : ℕ} {T : ℕ → Bool} (h : rgt m s (T p) = false) :
    step m ⟨s, p, T⟩ = some ⟨nxt m s (T p), p + 1, Function.update T p (wrt m s (T p))⟩ := by
  have h' : ¬ digit m s (T p) % 2 = 1 := by simpa [rgt] using h
  simp [step, nxt, wrt, h']

/-! ## Tapes as streams -/

/-- Drop the first cell. -/
def tl (W : ℕ → Bool) : ℕ → Bool := fun i => W (i + 1)

/-- Put a cell in front. -/
def cons (b : Bool) (W : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | i + 1 => W i

@[simp] theorem tl_cons (b : Bool) (W : ℕ → Bool) : tl (cons b W) = W := rfl
@[simp] theorem cons_zero (b : Bool) (W : ℕ → Bool) : cons b W 0 = b := rfl
@[simp] theorem cons_succ (b : Bool) (W : ℕ → Bool) (i : ℕ) : cons b W (i + 1) = W i := rfl

/-- A history: list of pairs (entry state, exit state). -/
abbrev Hist := List (Bool × Bool)

/-- `Call m s W r W' τ`: the head enters the first cell of the tape part `W` (the cells from some
position on, to the left) in state `s`; it stays inside this part for `τ` steps and with the last
of them leaves it to the right in state `r`, the tape part now being `W'`. -/
inductive Call (m : ℕ) : Bool → (ℕ → Bool) → Bool → (ℕ → Bool) → ℕ → Prop
  | right {s : Bool} {W : ℕ → Bool} : rgt m s (W 0) = true →
      Call m s W (nxt m s (W 0)) (cons (wrt m s (W 0)) (tl W)) 1
  | left {s : Bool} {W : ℕ → Bool} {r1 : Bool} {W1 : ℕ → Bool} {r : Bool} {W' : ℕ → Bool}
      {τ1 τ2 : ℕ} : rgt m s (W 0) = false →
      Call m (nxt m s (W 0)) (tl W) r1 W1 τ1 →
      Call m r1 (cons (wrt m s (W 0)) W1) r W' τ2 →
      Call m s W r W' (1 + τ1 + τ2)

/-- `Sess m W h W' c`: a sequence of calls on the tape part `W` with the entry and exit states
listed in `h`, total number of steps `c`. -/
inductive Sess (m : ℕ) : (ℕ → Bool) → Hist → (ℕ → Bool) → ℕ → Prop
  | nil {W : ℕ → Bool} : Sess m W [] W 0
  | cons {W : ℕ → Bool} {e r : Bool} {W1 : ℕ → Bool} {τ : ℕ} {h : Hist} {W' : ℕ → Bool} {c : ℕ} :
      Call m e W r W1 τ → Sess m W1 h W' c → Sess m W ((e, r) :: h) W' (τ + c)

/-- `Chain m s b hc r b'`: a cell with symbol `b`, entered in state `s`; the head goes left as
often as `hc` has entries (entered with / returning in the listed states), then leaves the cell to
the right in state `r`; the cell then holds `b'`. -/
inductive Chain (m : ℕ) : Bool → Bool → Hist → Bool → Bool → Prop
  | right {s b : Bool} : rgt m s b = true → Chain m s b [] (nxt m s b) (wrt m s b)
  | left {s b r1 : Bool} {hc : Hist} {r b' : Bool} : rgt m s b = false →
      Chain m r1 (wrt m s b) hc r b' → Chain m s b ((nxt m s b, r1) :: hc) r b'

/-- `Compat m b h h' b'`: a cell with initial symbol `b` turns the history `h` on its right
boundary into the history `h'` on its left boundary; finally it holds `b'`. -/
inductive Compat (m : ℕ) : Bool → Hist → Hist → Bool → Prop
  | nil {b : Bool} : Compat m b [] [] b
  | cons {b e r : Bool} {hc : Hist} {b1 : Bool} {h h' : Hist} {b' : Bool} :
      Chain m e b hc r b1 → Compat m b1 h h' b' → Compat m b ((e, r) :: h) (hc ++ h') b'

/-! ## From a halting run to a call -/

/-- The part of the tape from position `p` on. -/
def shift (p : ℕ) (T : ℕ → Bool) : ℕ → Bool := fun i => T (p + i)

/-- The tape that agrees with `T` below `p` and with the stream `W` from `p` on. -/
def glue (p : ℕ) (T W : ℕ → Bool) : ℕ → Bool := fun i => if i < p then T i else W (i - p)

theorem shift_update_succ (p : ℕ) (T : ℕ → Bool) (b : Bool) :
    shift (p + 1) (Function.update T p b) = tl (shift p T) := by
  funext i
  simp only [shift, tl]
  rw [Function.update_of_ne (by omega)]
  congr 1; omega

theorem shift_glue (p : ℕ) (T W1 : ℕ → Bool) (b : Bool) :
    shift p (glue (p + 1) (Function.update T p b) W1) = cons b W1 := by
  funext i
  cases i with
  | zero => simp [shift, glue]
  | succ k =>
    simp only [shift, glue, cons_succ]
    rw [if_neg (by omega)]
    congr 1; omega

theorem update_eq_glue (q : ℕ) (T : ℕ → Bool) (b : Bool) :
    Function.update T (q + 1) b = glue (q + 1) T (cons b (tl (shift (q + 1) T))) := by
  funext i
  by_cases h : i < q + 1
  · simp only [glue, if_pos h]
    rw [Function.update_of_ne (by omega)]
  · simp only [glue, if_neg h]
    obtain ⟨k, rfl⟩ : ∃ k, i = q + 1 + k := ⟨i - (q + 1), by omega⟩
    rw [Nat.add_sub_cancel_left]
    cases k with
    | zero => simp
    | succ k =>
      rw [Function.update_of_ne (by omega)]
      simp only [cons_succ, tl, shift]

theorem glue_glue (p : ℕ) (T W1 W' : ℕ → Bool) (b : Bool) :
    glue p (glue (p + 1) (Function.update T p b) W1) W' = glue p T W' := by
  funext i
  by_cases h : i < p
  · simp only [glue, if_pos h]
    rw [if_pos (by omega), Function.update_of_ne (by omega)]
  · simp only [glue, if_neg h]

theorem call_of_halts (m : ℕ) : ∀ (t : ℕ) (s : Bool) (p : ℕ) (T : ℕ → Bool),
    HaltsAfter m ⟨s, p, T⟩ t →
    ∃ r W' τ, Call m s (shift p T) r W' τ ∧ (p = 0 → τ = t) ∧
      (∀ q, p = q + 1 → ∃ t', t = τ + t' ∧ HaltsAfter m ⟨r, q, glue p T W'⟩ t') := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro s p T h
    by_cases hr : rgt m s (T p) = true
    · refine ⟨nxt m s (T p), cons (wrt m s (T p)) (tl (shift p T)), 1, ?_, ?_, ?_⟩
      · exact Call.right (m := m) (s := s) (W := shift p T) hr
      · intro hp
        subst hp
        cases h with
        | halt _ => rfl
        | next hs _ => simp [step_of_rgt hr] at hs
      · intro q hq
        subst hq
        cases h with
        | halt hs => simp [step_of_rgt hr] at hs
        | @next _ c' t0 hs h' =>
          refine ⟨t0, by omega, ?_⟩
          have hc : c' = ⟨nxt m s (T (q + 1)), q, Function.update T (q + 1) (wrt m s (T (q + 1)))⟩ := by
            have := hs
            rw [step_of_rgt hr] at this
            simpa using this.symm
          rw [hc, update_eq_glue] at h'
          exact h'
    · have hl : rgt m s (T p) = false := by simpa using hr
      cases h with
      | halt hs => simp [step_of_lft hl] at hs
      | @next _ c' t0 hs h' =>
        have hc : c' = ⟨nxt m s (T p), p + 1, Function.update T p (wrt m s (T p))⟩ := by
          have := hs
          rw [step_of_lft hl] at this
          simpa using this.symm
        rw [hc] at h'
        obtain ⟨r1, W1, τ1, c1, _, k1⟩ := ih t0 (by omega) _ _ _ h'
        obtain ⟨t', e1, h1⟩ := k1 p rfl
        obtain ⟨r, W', τ2, c2, z2, k2⟩ := ih t' (by omega) _ _ _ h1
        rw [shift_update_succ] at c1
        rw [shift_glue] at c2
        refine ⟨r, W', 1 + τ1 + τ2, Call.left (s := s) (W := shift p T) hl c1 c2, ?_, ?_⟩
        · intro hp
          have := z2 hp
          omega
        · intro q hq
          obtain ⟨t'', e2, h2⟩ := k2 q hq
          rw [glue_glue] at h2
          exact ⟨t'', by omega, h2⟩

/-- A halting run from the initial configuration is a single call on the whole tape. -/
theorem sess_of_halts {m x t : ℕ} (h : HaltsAfter m (init x) t) :
    ∃ r W', Sess m (fun i => x.testBit i) [(true, r)] W' t := by
  obtain ⟨r, W', τ, c, z, _⟩ := call_of_halts m t true 0 (fun i => x.testBit i) h
  have e : shift 0 (fun i => x.testBit i) = fun i => x.testBit i := by
    funext i; simp [shift]
  rw [e] at c
  have := Sess.cons c (Sess.nil (m := m))
  rw [z rfl] at this
  exact ⟨r, W', this⟩

/-! ## Decomposition of a session at one cell -/

theorem Sess.append {m : ℕ} {W : ℕ → Bool} {h1 : Hist} {W1 : ℕ → Bool} {c1 : ℕ} {h2 : Hist}
    {W2 : ℕ → Bool} {c2 : ℕ} (s1 : Sess m W h1 W1 c1) (s2 : Sess m W1 h2 W2 c2) :
    Sess m W (h1 ++ h2) W2 (c1 + c2) := by
  induction s1 with
  | nil => simpa using s2
  | cons hc _ ih =>
    have := Sess.cons hc (ih s2)
    simpa [Nat.add_assoc] using this

theorem call_decomp {m : ℕ} {s : Bool} {W : ℕ → Bool} {r : Bool} {W' : ℕ → Bool} {τ : ℕ}
    (h : Call m s W r W' τ) :
    ∃ hc c1, Sess m (tl W) hc (tl W') c1 ∧ Chain m s (W 0) hc r (W' 0) ∧
      τ = 1 + hc.length + c1 := by
  induction h with
  | right hr => exact ⟨[], 0, Sess.nil, Chain.right hr, rfl⟩
  | @left s W r1 W1 r W' τ1 τ2 hl c1 _ _ ih2 =>
    obtain ⟨hc2, k2, s2, ch2, e2⟩ := ih2
    simp only [tl_cons, cons_zero] at s2 ch2
    refine ⟨(nxt m s (W 0), r1) :: hc2, τ1 + k2, Sess.cons c1 s2, Chain.left hl ch2, ?_⟩
    simp only [List.length_cons]
    omega

/-- **Decomposition at one cell.**  A session with history `h` on a tape part `W` induces a
session on the rest `tl W` whose history `h'` is compatible with `h` via the first cell, and the
costs add up. -/
theorem sess_decomp {m : ℕ} {W : ℕ → Bool} {h : Hist} {W' : ℕ → Bool} {c : ℕ}
    (s : Sess m W h W' c) :
    ∃ h' c', Sess m (tl W) h' (tl W') c' ∧ Compat m (W 0) h h' (W' 0) ∧
      c = h.length + h'.length + c' := by
  induction s with
  | nil => exact ⟨[], 0, Sess.nil, Compat.nil, rfl⟩
  | @cons W e r W1 τ h W' c hc _ ih =>
    obtain ⟨h', c', s', cp, e'⟩ := ih
    obtain ⟨hc1, k1, s1, ch1, e1⟩ := call_decomp hc
    refine ⟨hc1 ++ h', k1 + c', s1.append s', Compat.cons ch1 cp, ?_⟩
    simp only [List.length_cons, List.length_append]
    omega

end A393317
