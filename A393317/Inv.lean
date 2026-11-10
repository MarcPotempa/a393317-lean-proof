import A393317.Cross

/-!
# Invariants on crossing sequences

Histories are read by a finite automaton with transition function `dl` (states are natural
numbers, `0` is the initial state, letters are the codes `pc` of pairs).  Two kinds of invariants
are established with the help of finite, locally checkable product invariants:

* **forward** (`FwdInv`): every history that a tape part can produce at all is accepted by an
  automaton `A` (i.e. uses allowed transitions only);
* **top-down** (`TdInv`): if the history `h` on the right boundary of a cell is accepted by `AG`
  and the history `h'` on its left boundary is accepted by `AD`, then `h'` is accepted by `AG'`
  and `|h'| ≤ c |h| + Δ`, where `Δ` only depends on the automaton states reached by `h` and `h'`.
-/

namespace A393317

/-- Code of a pair (entry state, exit state): `UU = 0`, `UD = 1`, `DU = 2`, `DD = 3`. -/
def pc (a : Bool × Bool) : ℕ := (if a.1 then 0 else 2) + (if a.2 then 0 else 1)

theorem pc_lt (a : Bool × Bool) : pc a < 4 := by
  rcases a with ⟨_ | _, _ | _⟩ <;> decide

section Auto

variable (dl : ℕ → ℕ → ℕ)

/-- State reached from `q` by reading the history. -/
def stRun : ℕ → Hist → ℕ
  | q, [] => q
  | q, a :: h => stRun (dl q (pc a)) h

/-- All transitions taken from `q` on reading the history are allowed by `A`. -/
def acc (A : ℕ → ℕ → Bool) : ℕ → Hist → Bool
  | _, [] => true
  | q, a :: h => A q (pc a) && acc A (dl q (pc a)) h

theorem stRun_append (q : ℕ) (h1 h2 : Hist) :
    stRun dl q (h1 ++ h2) = stRun dl (stRun dl q h1) h2 := by
  induction h1 generalizing q with
  | nil => rfl
  | cons a h1 ih => simpa [stRun] using ih _

theorem acc_append (A : ℕ → ℕ → Bool) (q : ℕ) (h1 h2 : Hist) :
    acc dl A q (h1 ++ h2) = (acc dl A q h1 && acc dl A (stRun dl q h1) h2) := by
  induction h1 generalizing q with
  | nil => simp [acc, stRun]
  | cons a h1 ih => simp [acc, stRun, ih, Bool.and_assoc]

end Auto

/-! ## Forward invariant -/

/-- A product invariant for "a cell in front of a tape part": `I sym qa qt` for the idle cell
(current symbol `sym`, automaton state `qa` of the history of the cell-with-rest so far, state
`qt` of the history of the rest so far), `Bz e s sym qa qt` while a call that started in state
`e` is being processed and the head is on the cell in state `s`. -/
structure FwdInv (m : ℕ) (dl : ℕ → ℕ → ℕ) (A : ℕ → ℕ → Bool) (bits : Bool → Bool)
    (I : Bool → ℕ → ℕ → Bool) (Bz : Bool → Bool → Bool → ℕ → ℕ → Bool) : Prop where
  start : ∀ b, bits b = true → I b 0 0 = true
  enter : ∀ sym qa qt, I sym qa qt = true → ∀ e, Bz e e sym qa qt = true
  stepR : ∀ e s sym qa qt, Bz e s sym qa qt = true → rgt m s sym = true →
    A qa (pc (e, nxt m s sym)) = true ∧
      I (wrt m s sym) (dl qa (pc (e, nxt m s sym))) qt = true
  stepL : ∀ e s sym qa qt, Bz e s sym qa qt = true → rgt m s sym = false → ∀ rr,
    A qt (pc (nxt m s sym, rr)) = true →
      Bz e rr (wrt m s sym) qa (dl qt (pc (nxt m s sym, rr))) = true

namespace FwdInv

variable {m : ℕ} {dl : ℕ → ℕ → ℕ} {A : ℕ → ℕ → Bool} {bits : Bool → Bool}
  {I : Bool → ℕ → ℕ → Bool} {Bz : Bool → Bool → Bool → ℕ → ℕ → Bool}

theorem chain (inv : FwdInv m dl A bits I Bz) {s b : Bool} {hc : Hist} {r b' : Bool}
    (ch : Chain m s b hc r b') : ∀ {e : Bool} {qa qt : ℕ}, Bz e s b qa qt = true →
    acc dl A qt hc = true →
    A qa (pc (e, r)) = true ∧ I b' (dl qa (pc (e, r))) (stRun dl qt hc) = true := by
  induction ch with
  | right hr => intro e qa qt hB _; exact inv.stepR _ _ _ _ _ hB hr
  | @left s b r1 hc r b' hl _ ih =>
    intro e qa qt hB ha
    simp only [acc, Bool.and_eq_true] at ha
    exact ih (inv.stepL _ _ _ _ _ hB hl r1 ha.1) ha.2

theorem compat (inv : FwdInv m dl A bits I Bz) {b : Bool} {h h' : Hist} {b' : Bool}
    (cp : Compat m b h h' b') : ∀ {qa qt : ℕ}, I b qa qt = true → acc dl A qt h' = true →
    acc dl A qa h = true ∧ I b' (stRun dl qa h) (stRun dl qt h') = true := by
  induction cp with
  | nil => intro qa qt hI _; exact ⟨rfl, hI⟩
  | @cons b e r hc b1 h h' b' ch _ ih =>
    intro qa qt hI ha
    rw [acc_append, Bool.and_eq_true] at ha
    obtain ⟨a1, i1⟩ := inv.chain ch (inv.enter _ _ _ hI e) ha.1
    obtain ⟨a2, i2⟩ := ih i1 ha.2
    refine ⟨by simp [acc, a1, a2], ?_⟩
    rw [stRun_append]
    exact i2

/-- **Soundness of the forward invariant**: every history produced by a tape part of the region
`R` is accepted by `A`. -/
theorem sound (inv : FwdInv m dl A bits I Bz) {R : (ℕ → Bool) → Prop}
    (hR : ∀ W, R W → bits (W 0) = true ∧ R (tl W)) :
    ∀ (c : ℕ) (W : ℕ → Bool) (h : Hist) (W' : ℕ → Bool), R W → Sess m W h W' c →
      acc dl A 0 h = true := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro W h W' hW s
    cases h with
    | nil => rfl
    | cons a h =>
      obtain ⟨h', c', s', cp, e⟩ := sess_decomp s
      have hc : c' < c := by simp only [List.length_cons] at e; omega
      have a' := ih c' hc _ _ _ (hR W hW).2 s'
      exact (inv.compat cp (inv.start _ (hR W hW).1) a').1

end FwdInv

/-! ## Top-down invariant with weights -/

/-- Product invariant with integer potentials for the top-down direction.  `PI b0 sym g qt`
(idle) and `PB b0 r s sym g qt` (busy, the current call has to leave in state `r`) give the
potential of a product state if it belongs to the invariant; `Dd` marks busy states from which
the cell can never be left in the required way.  Along every step
"(number of pairs of `h'` consumed) − c · (number of entries of `h` started)" grows at most as
much as the potential. -/
structure TdInv (m : ℕ) (dl : ℕ → ℕ → ℕ) (AG AD AG' : ℕ → ℕ → Bool) (bits : Bool → Bool) (c : ℕ)
    (PI : Bool → Bool → ℕ → ℕ → Option ℤ)
    (PB : Bool → Bool → Bool → Bool → ℕ → ℕ → Option ℤ)
    (Dd : Bool → Bool → Bool → Bool → ℕ → ℕ → Bool)
    (E : Bool → ℕ → ℕ → Option ℤ) : Prop where
  start : ∀ b, bits b = true → ∃ π, PI b b 0 0 = some π ∧ 0 ≤ π
  enter : ∀ b0 sym g qt π, PI b0 sym g qt = some π → ∀ e r, AG g (pc (e, r)) = true →
    Dd b0 r e sym (dl g (pc (e, r))) qt = true ∨
      ∃ π', PB b0 r e sym (dl g (pc (e, r))) qt = some π' ∧ π - c ≤ π'
  stepR : ∀ b0 r s sym g qt π, PB b0 r s sym g qt = some π → rgt m s sym = true →
    nxt m s sym = r → ∃ π', PI b0 (wrt m s sym) g qt = some π' ∧ π ≤ π'
  stepL : ∀ b0 r s sym g qt π, PB b0 r s sym g qt = some π → rgt m s sym = false → ∀ rr,
    AD qt (pc (nxt m s sym, rr)) = true →
      Dd b0 r rr (wrt m s sym) g (dl qt (pc (nxt m s sym, rr))) = true ∨
        (AG' qt (pc (nxt m s sym, rr)) = true ∧
          ∃ π', PB b0 r rr (wrt m s sym) g (dl qt (pc (nxt m s sym, rr))) = some π' ∧ π + 1 ≤ π')
  deadR : ∀ b0 r s sym g qt, Dd b0 r s sym g qt = true → rgt m s sym = true → nxt m s sym ≠ r
  deadL : ∀ b0 r s sym g qt, Dd b0 r s sym g qt = true → rgt m s sym = false → ∀ rr,
    AD qt (pc (nxt m s sym, rr)) = true →
      Dd b0 r rr (wrt m s sym) g (dl qt (pc (nxt m s sym, rr))) = true
  edge : ∀ b0 sym g qt π, PI b0 sym g qt = some π → ∃ Δ, E b0 g qt = some Δ ∧ π ≤ Δ

namespace TdInv

variable {m : ℕ} {dl : ℕ → ℕ → ℕ} {AG AD AG' : ℕ → ℕ → Bool} {bits : Bool → Bool} {c : ℕ}
  {PI : Bool → Bool → ℕ → ℕ → Option ℤ} {PB : Bool → Bool → Bool → Bool → ℕ → ℕ → Option ℤ}
  {Dd : Bool → Bool → Bool → Bool → ℕ → ℕ → Bool} {E : Bool → ℕ → ℕ → Option ℤ}

theorem not_dead (inv : TdInv m dl AG AD AG' bits c PI PB Dd E) {s b : Bool} {hc : Hist}
    {r b' : Bool} (ch : Chain m s b hc r b') : ∀ {b0 : Bool} {g qt : ℕ},
    acc dl AD qt hc = true → Dd b0 r s b g qt = true → False := by
  induction ch with
  | right hr => intro b0 g qt _ hd; exact inv.deadR _ _ _ _ _ _ hd hr rfl
  | @left s b r1 hc r b' hl _ ih =>
    intro b0 g qt ha hd
    simp only [acc, Bool.and_eq_true] at ha
    exact ih ha.2 (inv.deadL _ _ _ _ _ _ hd hl r1 ha.1)

theorem chain (inv : TdInv m dl AG AD AG' bits c PI PB Dd E) {s b : Bool} {hc : Hist}
    {r b' : Bool} (ch : Chain m s b hc r b') : ∀ {b0 : Bool} {g qt : ℕ} {π : ℤ},
    PB b0 r s b g qt = some π → acc dl AD qt hc = true →
    acc dl AG' qt hc = true ∧
      ∃ π', PI b0 b' g (stRun dl qt hc) = some π' ∧ π + hc.length ≤ π' := by
  induction ch with
  | right hr =>
    intro b0 g qt π hB _
    obtain ⟨π', h1, h2⟩ := inv.stepR _ _ _ _ _ _ _ hB hr rfl
    exact ⟨rfl, π', h1, by simpa using h2⟩
  | @left s b r1 hc r b' hl ch' ih =>
    intro b0 g qt π hB ha
    simp only [acc, Bool.and_eq_true] at ha
    rcases inv.stepL _ _ _ _ _ _ _ hB hl r1 ha.1 with hd | ⟨hg, π1, h1, h2⟩
    · exact (inv.not_dead ch' ha.2 hd).elim
    · obtain ⟨a3, π', h3, h4⟩ := ih h1 ha.2
      refine ⟨by simp [acc, hg, a3], π', h3, ?_⟩
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      omega

theorem compat (inv : TdInv m dl AG AD AG' bits c PI PB Dd E) {b : Bool} {h h' : Hist}
    {b' : Bool} (cp : Compat m b h h' b') : ∀ {b0 : Bool} {g qt : ℕ} {π : ℤ},
    PI b0 b g qt = some π → acc dl AG g h = true → acc dl AD qt h' = true →
    acc dl AG' qt h' = true ∧
      ∃ π', PI b0 b' (stRun dl g h) (stRun dl qt h') = some π' ∧
        π + h'.length - c * h.length ≤ π' := by
  induction cp with
  | nil =>
    intro b0 g qt π hI _ _
    exact ⟨rfl, π, hI, by simp⟩
  | @cons b e r hc b1 h h' b' ch _ ih =>
    intro b0 g qt π hI hg ha
    simp only [acc, Bool.and_eq_true] at hg
    rw [acc_append, Bool.and_eq_true] at ha
    rcases inv.enter _ _ _ _ _ hI e r hg.1 with hd | ⟨π1, h1, h2⟩
    · exact (inv.not_dead ch ha.1 hd).elim
    · obtain ⟨a2, π2, h3, h4⟩ := inv.chain ch h1 ha.1
      obtain ⟨a3, π3, h5, h6⟩ := ih h3 hg.2 ha.2
      refine ⟨by rw [acc_append, a2]; simpa using a3, π3, ?_, ?_⟩
      · rw [stRun_append]; exact h5
      · simp only [List.length_cons, List.length_append, Nat.cast_add, Nat.cast_one]
        have : (c : ℤ) * ((h.length : ℤ) + 1) = c * h.length + c := by ring
        omega

/-- **Soundness of the top-down invariant.** -/
theorem sound (inv : TdInv m dl AG AD AG' bits c PI PB Dd E) {b : Bool} {h h' : Hist}
    {b' : Bool} (hb : bits b = true) (cp : Compat m b h h' b') (hg : acc dl AG 0 h = true)
    (ha : acc dl AD 0 h' = true) :
    acc dl AG' 0 h' = true ∧
      ∃ Δ, E b (stRun dl 0 h) (stRun dl 0 h') = some Δ ∧ (h'.length : ℤ) ≤ c * h.length + Δ := by
  obtain ⟨π, h1, h2⟩ := inv.start b hb
  obtain ⟨a1, π', h3, h4⟩ := inv.compat cp h1 hg ha
  obtain ⟨Δ, h5, h6⟩ := inv.edge _ _ _ _ _ h3
  exact ⟨a1, Δ, h5, by omega⟩

end TdInv

end A393317
