import A393317.Inv

/-!
# From the invariants to a bound on the halting time

`AbsSys` collects what the invariants give for one machine: a "one-counter system" on pairs
(automaton state of a history, length of the history), together with potential functions
`Wi` (input region, depending on the number `k` of remaining input cells) and `Wb` (blank
region) that dominate the cost.  The cost of a session with history `h` and `c` steps is
measured by `c + |h|`, which equals twice the sum of the lengths of all histories to the left.
-/

namespace A393317

/-- Length information for the automaton: `lo q` is a lower bound for the length of every history
ending in state `q`, and the exact length if `ex q`. -/
structure LenInfo (dl : ℕ → ℕ → ℕ) (N : ℕ) (lo : ℕ → ℕ) (ex : ℕ → Bool) : Prop where
  pos : 0 < N
  closed : ∀ q, q < N → ∀ a, a < 4 → dl q a < N
  lo0 : lo 0 = 0
  ex0 : ex 0 = true
  step : ∀ q, q < N → ∀ a, a < 4 →
    lo (dl q a) ≤ lo q + 1 ∧ (ex (dl q a) = true → ex q = true ∧ lo (dl q a) = lo q + 1)

/-- The length `ℓ` is possible for a history ending in state `g`. -/
def LenOK (lo : ℕ → ℕ) (ex : ℕ → Bool) (g ℓ : ℕ) : Prop := lo g ≤ ℓ ∧ (ex g = true → ℓ = lo g)

theorem LenInfo.ok {dl : ℕ → ℕ → ℕ} {N : ℕ} {lo : ℕ → ℕ} {ex : ℕ → Bool}
    (li : LenInfo dl N lo ex) (h : Hist) :
    stRun dl 0 h < N ∧ LenOK lo ex (stRun dl 0 h) h.length := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨li.pos, by simp [stRun, LenOK, li.lo0]⟩
  | append_singleton l a ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have hs : stRun dl 0 (l ++ [a]) = dl (stRun dl 0 l) (pc a) := by
      rw [stRun_append]; rfl
    obtain ⟨s1, s2⟩ := li.step _ h1 _ (pc_lt a)
    rw [hs]
    refine ⟨li.closed _ h1 _ (pc_lt a), ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton]; omega
    · intro he
      obtain ⟨e1, e2⟩ := s2 he
      simp only [List.length_append, List.length_singleton]
      rw [e2, h3 e1]

theorem Sess.cost_nil {m : ℕ} {W W' : ℕ → Bool} {c : ℕ} (s : Sess m W [] W' c) : c = 0 := by
  cases s; rfl

/-- Everything the certificate of one machine provides. -/
structure AbsSys (m : ℕ) (dl : ℕ → ℕ → ℕ) (lo : ℕ → ℕ) (ex : ℕ → Bool) (c D : ℕ)
    (ADi ADb AGi AGb : ℕ → ℕ → Bool) (Ei : Bool → ℕ → ℕ → Option ℤ)
    (Eb : Bool → ℕ → ℕ → Option ℤ) (Wi : ℕ → ℕ → ℕ → ℤ) (Wb : ℕ → ℕ → ℤ) : Prop where
  fwdI : ∀ (c : ℕ) (W : ℕ → Bool) (h : Hist) (W' : ℕ → Bool), Sess m W h W' c →
    acc dl ADi 0 h = true
  fwdB : ∀ (c : ℕ) (W : ℕ → Bool) (h : Hist) (W' : ℕ → Bool), (∀ i, W i = false) →
    Sess m W h W' c → acc dl ADb 0 h = true
  tdI : ∀ (b : Bool) (h h' : Hist) (b' : Bool), Compat m b h h' b' → acc dl AGi 0 h = true →
    acc dl ADi 0 h' = true → acc dl AGi 0 h' = true ∧
      ∃ Δ, Ei b (stRun dl 0 h) (stRun dl 0 h') = some Δ ∧ (h'.length : ℤ) ≤ c * h.length + Δ
  tdB : ∀ (h h' : Hist) (b' : Bool), Compat m false h h' b' → acc dl AGb 0 h = true →
    acc dl ADb 0 h' = true → acc dl AGb 0 h' = true ∧
      ∃ Δ, Eb false (stRun dl 0 h) (stRun dl 0 h') = some Δ ∧
        (h'.length : ℤ) ≤ c * h.length + Δ
  gb : ∀ h : Hist, acc dl AGi 0 h = true → acc dl ADb 0 h = true → acc dl AGb 0 h = true
  startG : ∀ r : Bool, acc dl ADi 0 [(true, r)] = true → acc dl AGi 0 [(true, r)] = true
  len : ∀ h : Hist, LenOK lo ex (stRun dl 0 h) h.length
  potB : ∀ (g g' : ℕ) (Δ : ℤ) (ℓ ℓ' : ℕ), Eb false g g' = some Δ → 1 ≤ ℓ → LenOK lo ex g ℓ →
    LenOK lo ex g' ℓ' → (ℓ' : ℤ) ≤ c * ℓ + Δ → (D : ℤ) * (2 * ℓ) + Wb g' ℓ' ≤ Wb g ℓ
  potI : ∀ (b : Bool) (g g' : ℕ) (Δ : ℤ) (ℓ ℓ' k : ℕ), Ei b g g' = some Δ → 1 ≤ ℓ →
    LenOK lo ex g ℓ → LenOK lo ex g' ℓ' → (ℓ' : ℤ) ≤ c * ℓ + Δ →
    (D : ℤ) * (2 * ℓ) + Wi g' ℓ' k ≤ Wi g ℓ (k + 1)
  pot0 : ∀ g ℓ : ℕ, LenOK lo ex g ℓ → Wb g ℓ ≤ Wi g ℓ 0
  potE : 0 ≤ Wb 0 0
  potE' : ∀ k : ℕ, 0 ≤ Wi 0 0 k

namespace AbsSys

variable {m : ℕ} {dl : ℕ → ℕ → ℕ} {lo : ℕ → ℕ} {ex : ℕ → Bool} {c D : ℕ}
  {ADi ADb AGi AGb : ℕ → ℕ → Bool} {Ei : Bool → ℕ → ℕ → Option ℤ}
  {Eb : Bool → ℕ → ℕ → Option ℤ} {Wi : ℕ → ℕ → ℕ → ℤ} {Wb : ℕ → ℕ → ℤ}

theorem boundB (S : AbsSys m dl lo ex c D ADi ADb AGi AGb Ei Eb Wi Wb) :
    ∀ (cst : ℕ) (W : ℕ → Bool) (h : Hist) (W' : ℕ → Bool), (∀ i, W i = false) →
      Sess m W h W' cst → acc dl AGb 0 h = true →
      (D : ℤ) * ((cst : ℤ) + h.length) ≤ Wb (stRun dl 0 h) h.length := by
  intro cst
  induction cst using Nat.strong_induction_on with
  | _ cst ih =>
    intro W h W' hW s hg
    cases h with
    | nil =>
      have := s.cost_nil
      subst this
      simpa [stRun] using S.potE
    | cons a h0 =>
      obtain ⟨h', c', s', cp, e⟩ := sess_decomp s
      have hc : c' < cst := by simp only [List.length_cons] at e; omega
      have hW' : ∀ i, tl W i = false := fun i => hW (i + 1)
      rw [hW 0] at cp
      have ha := S.fwdB c' _ _ _ hW' s'
      obtain ⟨hg', Δ, hE, hl⟩ := S.tdB _ _ _ cp hg ha
      have i1 := ih c' hc _ _ _ hW' s' hg'
      have i2 := S.potB _ _ Δ (a :: h0).length h'.length hE (by simp) (S.len _) (S.len _) hl
      have e' : (cst : ℤ) = ((a :: h0).length : ℤ) + h'.length + c' := by exact_mod_cast e
      have : (D : ℤ) * ((cst : ℤ) + (a :: h0).length) =
          D * (2 * ((a :: h0).length : ℤ)) + D * ((c' : ℤ) + h'.length) := by rw [e']; ring
      rw [this]
      linarith

theorem boundI (S : AbsSys m dl lo ex c D ADi ADb AGi AGb Ei Eb Wi Wb) :
    ∀ (k cst : ℕ) (W : ℕ → Bool) (h : Hist) (W' : ℕ → Bool), (∀ i, k ≤ i → W i = false) →
      Sess m W h W' cst → acc dl AGi 0 h = true →
      (D : ℤ) * ((cst : ℤ) + h.length) ≤ Wi (stRun dl 0 h) h.length k := by
  intro k
  induction k with
  | zero =>
    intro cst W h W' hW s hg
    have hW0 : ∀ i, W i = false := fun i => hW i (Nat.zero_le i)
    have ha := S.fwdB cst _ _ _ hW0 s
    have := S.boundB cst W h W' hW0 s (S.gb h hg ha)
    exact le_trans this (S.pot0 _ _ (S.len h))
  | succ k ih =>
    intro cst W h W' hW s hg
    cases h with
    | nil =>
      have := s.cost_nil
      subst this
      simpa [stRun] using S.potE' (k + 1)
    | cons a h0 =>
      obtain ⟨h', c', s', cp, e⟩ := sess_decomp s
      have hW' : ∀ i, k ≤ i → tl W i = false := fun i hi => hW (i + 1) (by omega)
      have ha := S.fwdI c' _ _ _ s'
      obtain ⟨hg', Δ, hE, hl⟩ := S.tdI _ _ _ _ cp hg ha
      have i1 := ih c' _ _ _ hW' s' hg'
      have i2 := S.potI _ _ _ Δ (a :: h0).length h'.length k hE (by simp) (S.len _) (S.len _) hl
      have e' : (cst : ℤ) = ((a :: h0).length : ℤ) + h'.length + c' := by exact_mod_cast e
      have : (D : ℤ) * ((cst : ℤ) + (a :: h0).length) =
          D * (2 * ((a :: h0).length : ℤ)) + D * ((c' : ℤ) + h'.length) := by rw [e']; ring
      rw [this]
      linarith

/-- **Bound on the halting time** in terms of the potential of the initial history. -/
theorem halting_bound (S : AbsSys m dl lo ex c D ADi ADb AGi AGb Ei Eb Wi Wb) {n x t : ℕ}
    (hx : x < 2 ^ n) (h : HaltsAfter m (init x) t) :
    ∃ r : Bool, acc dl ADi 0 [(true, r)] = true ∧
      (D : ℤ) * ((t : ℤ) + 1) ≤ Wi (dl 0 (pc (true, r))) 1 n := by
  obtain ⟨r, W', s⟩ := sess_of_halts h
  have ha := S.fwdI _ _ _ _ s
  have hW : ∀ i, n ≤ i → (fun i => x.testBit i) i = false := by
    intro i hi
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))
  have := S.boundI n t _ _ _ hW s (S.startG r ha)
  exact ⟨r, ha, by simpa [stRun] using this⟩

end AbsSys

end A393317
