import A393317.Poly

/-!
# Certificates and their checker

A certificate consists of finite tables.  `Cert.check m C` is a computable Boolean test, and
`Cert.sound` shows that a certificate that passes the test for machine `m` proves
`t + 1 ≤ 2 (n+2)²` for every halting time `t` of `m` on an input `x < 2^n`, `n ≥ 1`.
-/

namespace A393317

/-- Lookup in an association list. -/
def look {α β : Type} [DecidableEq α] (k : α) : List (α × β) → Option β
  | [] => none
  | (k', v) :: L => if k = k' then some v else look k L

theorem look_mem {α β : Type} [DecidableEq α] {k : α} {v : β} :
    ∀ {L : List (α × β)}, look k L = some v → (k, v) ∈ L
  | [], h => by simp [look] at h
  | (k', v') :: L, h => by
    simp only [look] at h
    by_cases hk : k = k'
    · simp only [hk, if_true, Option.some.injEq] at h
      subst h; subst hk; exact List.mem_cons_self
    · simp only [hk, if_false] at h
      exact List.mem_cons_of_mem _ (look_mem h)

/-- `o` is defined and at least `x`. -/
def geI (o : Option ℤ) (x : ℤ) : Bool :=
  match o with
  | some π => decide (x ≤ π)
  | none => false

theorem geI_iff {o : Option ℤ} {x : ℤ} : geI o x = true ↔ ∃ π, o = some π ∧ x ≤ π := by
  cases o with
  | none => simp [geI]
  | some π => simp [geI]

def tab (T : List (List ℕ)) (q a : ℕ) : ℕ := (T.getD q []).getD a 0
def tabB (T : List (List Bool)) (q a : ℕ) : Bool := (T.getD q []).getD a false

/-! ## The individual checks -/

def lenCheck (N : ℕ) (dl : ℕ → ℕ → ℕ) (lo : ℕ → ℕ) (ex : ℕ → Bool) : Bool :=
  decide (0 < N) && decide (lo 0 = 0) && ex 0 &&
    (List.range N).all fun q => (List.range 4).all fun a =>
      decide (dl q a < N) && decide (lo (dl q a) ≤ lo q + 1) &&
        (!ex (dl q a) || (ex q && decide (lo (dl q a) = lo q + 1)))

theorem lenCheck_sound {N : ℕ} {dl : ℕ → ℕ → ℕ} {lo : ℕ → ℕ} {ex : ℕ → Bool}
    (h : lenCheck N dl lo ex = true) : LenInfo dl N lo ex := by
  simp only [lenCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun q hq a ha => (h4 q hq a ha).1.1, h2, h3, fun q hq a ha => ?_⟩
  obtain ⟨⟨_, k2⟩, k3⟩ := h4 q hq a ha
  refine ⟨k2, fun he => ?_⟩
  rcases k3 with k | k
  · rw [k] at he; exact absurd he (by simp)
  · exact k

def fwdCheck (m : ℕ) (dl : ℕ → ℕ → ℕ) (A : ℕ → ℕ → Bool) (bits : List Bool)
    (I : List (Bool × ℕ × ℕ)) (B : List (Bool × Bool × Bool × ℕ × ℕ)) : Bool :=
  bits.all (fun b => decide ((b, 0, 0) ∈ I)) &&
  I.all (fun x => decide ((true, true, x) ∈ B) && decide ((false, false, x) ∈ B)) &&
  B.all (fun x =>
    if rgt m x.2.1 x.2.2.1 then
      A x.2.2.2.1 (pc (x.1, nxt m x.2.1 x.2.2.1)) &&
        decide ((wrt m x.2.1 x.2.2.1, dl x.2.2.2.1 (pc (x.1, nxt m x.2.1 x.2.2.1)), x.2.2.2.2) ∈ I)
    else
      (!A x.2.2.2.2 (pc (nxt m x.2.1 x.2.2.1, true)) ||
        decide ((x.1, true, wrt m x.2.1 x.2.2.1, x.2.2.2.1,
          dl x.2.2.2.2 (pc (nxt m x.2.1 x.2.2.1, true))) ∈ B)) &&
      (!A x.2.2.2.2 (pc (nxt m x.2.1 x.2.2.1, false)) ||
        decide ((x.1, false, wrt m x.2.1 x.2.2.1, x.2.2.2.1,
          dl x.2.2.2.2 (pc (nxt m x.2.1 x.2.2.1, false))) ∈ B)))

theorem fwdCheck_sound {m : ℕ} {dl : ℕ → ℕ → ℕ} {A : ℕ → ℕ → Bool} {bits : List Bool}
    {I : List (Bool × ℕ × ℕ)} {B : List (Bool × Bool × Bool × ℕ × ℕ)}
    (h : fwdCheck m dl A bits I B = true) :
    FwdInv m dl A (fun b => decide (b ∈ bits)) (fun sym qa qt => decide ((sym, qa, qt) ∈ I))
      (fun e s sym qa qt => decide ((e, s, sym, qa, qt) ∈ B)) := by
  simp only [fwdCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    simp only [decide_eq_true_eq] at hb ⊢
    exact h1 b hb
  · intro sym qa qt hI e
    simp only [decide_eq_true_eq] at hI ⊢
    cases e
    · exact (h2 _ hI).2
    · exact (h2 _ hI).1
  · intro e s sym qa qt hB hr
    simp only [decide_eq_true_eq] at hB ⊢
    have := h3 _ hB
    simp only [hr, if_true, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · intro e s sym qa qt hB hl rr hA
    simp only [decide_eq_true_eq] at hB ⊢
    have := h3 _ hB
    simp only [hl, Bool.false_eq_true, if_false, Bool.and_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_true_eq] at this
    cases rr
    · rcases this.2 with k | k
      · rw [k] at hA; exact absurd hA (by simp)
      · exact k
    · rcases this.1 with k | k
      · rw [k] at hA; exact absurd hA (by simp)
      · exact k

def tdCheck (m : ℕ) (dl : ℕ → ℕ → ℕ) (AG AD AG' : ℕ → ℕ → Bool) (bits : List Bool) (c : ℕ)
    (tI : List ((Bool × Bool × ℕ × ℕ) × ℤ))
    (tB : List ((Bool × Bool × Bool × Bool × ℕ × ℕ) × ℤ))
    (tD : List (Bool × Bool × Bool × Bool × ℕ × ℕ))
    (E : List ((Bool × ℕ × ℕ) × ℤ)) : Bool :=
  bits.all (fun b => geI (look (b, b, 0, 0) tI) 0) &&
  tI.all (fun x =>
    [(true, true), (true, false), (false, true), (false, false)].all (fun a =>
      !AG x.1.2.2.1 (pc a) ||
        (decide ((x.1.1, a.2, a.1, x.1.2.1, dl x.1.2.2.1 (pc a), x.1.2.2.2) ∈ tD) ||
          geI (look (x.1.1, a.2, a.1, x.1.2.1, dl x.1.2.2.1 (pc a), x.1.2.2.2) tB) (x.2 - c)))) &&
  tB.all (fun x =>
    -- x.1 = (b0, r, s, sym, g, qt)
    if rgt m x.1.2.2.1 x.1.2.2.2.1 then
      !(nxt m x.1.2.2.1 x.1.2.2.2.1 == x.1.2.1) ||
        geI (look (x.1.1, wrt m x.1.2.2.1 x.1.2.2.2.1, x.1.2.2.2.2.1, x.1.2.2.2.2.2) tI) x.2
    else
      [true, false].all (fun rr =>
        !AD x.1.2.2.2.2.2 (pc (nxt m x.1.2.2.1 x.1.2.2.2.1, rr)) ||
          (decide ((x.1.1, x.1.2.1, rr, wrt m x.1.2.2.1 x.1.2.2.2.1, x.1.2.2.2.2.1,
              dl x.1.2.2.2.2.2 (pc (nxt m x.1.2.2.1 x.1.2.2.2.1, rr))) ∈ tD) ||
            (AG' x.1.2.2.2.2.2 (pc (nxt m x.1.2.2.1 x.1.2.2.2.1, rr)) &&
              geI (look (x.1.1, x.1.2.1, rr, wrt m x.1.2.2.1 x.1.2.2.2.1, x.1.2.2.2.2.1,
                dl x.1.2.2.2.2.2 (pc (nxt m x.1.2.2.1 x.1.2.2.2.1, rr))) tB) (x.2 + 1))))) &&
  tD.all (fun x =>
    -- x = (b0, r, s, sym, g, qt)
    if rgt m x.2.2.1 x.2.2.2.1 then !(nxt m x.2.2.1 x.2.2.2.1 == x.2.1)
    else
      [true, false].all (fun rr =>
        !AD x.2.2.2.2.2 (pc (nxt m x.2.2.1 x.2.2.2.1, rr)) ||
          decide ((x.1, x.2.1, rr, wrt m x.2.2.1 x.2.2.2.1, x.2.2.2.2.1,
            dl x.2.2.2.2.2 (pc (nxt m x.2.2.1 x.2.2.2.1, rr))) ∈ tD))) &&
  tI.all (fun x => geI (look (x.1.1, x.1.2.2.1, x.1.2.2.2) E) x.2)

theorem tdCheck_sound {m : ℕ} {dl : ℕ → ℕ → ℕ} {AG AD AG' : ℕ → ℕ → Bool} {bits : List Bool}
    {c : ℕ} {tI : List ((Bool × Bool × ℕ × ℕ) × ℤ)}
    {tB : List ((Bool × Bool × Bool × Bool × ℕ × ℕ) × ℤ)}
    {tD : List (Bool × Bool × Bool × Bool × ℕ × ℕ)} {E : List ((Bool × ℕ × ℕ) × ℤ)}
    (h : tdCheck m dl AG AD AG' bits c tI tB tD E = true) :
    TdInv m dl AG AD AG' (fun b => decide (b ∈ bits)) c
      (fun b0 sym g qt => look (b0, sym, g, qt) tI)
      (fun b0 r s sym g qt => look (b0, r, s, sym, g, qt) tB)
      (fun b0 r s sym g qt => decide ((b0, r, s, sym, g, qt) ∈ tD))
      (fun b0 g qt => look (b0, g, qt) E) := by
  simp only [tdCheck, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    simp only [decide_eq_true_eq] at hb
    exact geI_iff.1 (h1 b hb)
  · intro b0 sym g qt π hI e r hA
    have := h2 _ (look_mem hI) (e, r) (by cases e <;> cases r <;> simp)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
    rcases this with k | k | k
    · rw [k] at hA; exact absurd hA (by simp)
    · exact Or.inl (by simpa using k)
    · exact Or.inr (geI_iff.1 k)
  · intro b0 r s sym g qt π hB hr hn
    have := h3 _ (look_mem hB)
    simp only [hr, if_true, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at this
    rcases this with k | k
    · exact absurd hn k
    · exact geI_iff.1 k
  · intro b0 r s sym g qt π hB hl rr hA
    have := h3 _ (look_mem hB)
    simp only [hl, Bool.false_eq_true, if_false, List.all_eq_true] at this
    have := this rr (by cases rr <;> simp)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, Bool.and_eq_true] at this
    rcases this with k | k | ⟨k1, k2⟩
    · rw [k] at hA; exact absurd hA (by simp)
    · exact Or.inl (by simpa using k)
    · exact Or.inr ⟨k1, geI_iff.1 k2⟩
  · intro b0 r s sym g qt hd hr
    simp only [decide_eq_true_eq] at hd
    have := h4 _ hd
    simp only [hr, if_true, Bool.not_eq_true', beq_eq_false_iff_ne] at this
    exact this
  · intro b0 r s sym g qt hd hl rr hA
    simp only [decide_eq_true_eq] at hd ⊢
    have := h4 _ hd
    simp only [hl, Bool.false_eq_true, if_false, List.all_eq_true] at this
    have := this rr (by cases rr <;> simp)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at this
    rcases this with k | k
    · rw [k] at hA; exact absurd hA (by simp)
    · exact k
  · intro b0 sym g qt π hI
    exact geI_iff.1 (h5 _ (look_mem hI))

def gbCheck (N : ℕ) (AGi ADb AGb : ℕ → ℕ → Bool) : Bool :=
  (List.range N).all fun q => (List.range 4).all fun a => !(AGi q a && ADb q a) || AGb q a

theorem gbCheck_sound {N : ℕ} {dl : ℕ → ℕ → ℕ} {lo : ℕ → ℕ} {ex : ℕ → Bool}
    {AGi ADb AGb : ℕ → ℕ → Bool} (li : LenInfo dl N lo ex) (h : gbCheck N AGi ADb AGb = true) :
    ∀ (hs : Hist) (q : ℕ), q < N → acc dl AGi q hs = true → acc dl ADb q hs = true →
      acc dl AGb q hs = true := by
  simp only [gbCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff] at h
  intro hs
  induction hs with
  | nil => intro q _ _ _; rfl
  | cons a hs ih =>
    intro q hq h1 h2
    simp only [acc, Bool.and_eq_true] at h1 h2 ⊢
    refine ⟨?_, ih _ (li.closed q hq _ (pc_lt a)) h1.2 h2.2⟩
    rcases h q hq (pc a) (pc_lt a) with (k | k) | k
    · rw [k] at h1; exact absurd h1.1 (by simp)
    · rw [k] at h2; exact absurd h2.1 (by simp)
    · exact k

/-! ## Certificates -/

/-- The tables shared by all kinds of certificates: automaton, allowed transitions and the
product invariants for the input region (`f*`, `t*`, `eI`) and the blank region
(`g*`, `u*`, `eB`). -/
structure Core where
  N : ℕ
  dl : List (List ℕ)
  lo : List ℕ
  ex : List Bool
  adI : List (List Bool)
  adB : List (List Bool)
  agI : List (List Bool)
  agB : List (List Bool)
  fI : List (Bool × ℕ × ℕ)
  fB : List (Bool × Bool × Bool × ℕ × ℕ)
  gI : List (Bool × ℕ × ℕ)
  gB : List (Bool × Bool × Bool × ℕ × ℕ)
  tI : List ((Bool × Bool × ℕ × ℕ) × ℤ)
  tB : List ((Bool × Bool × Bool × Bool × ℕ × ℕ) × ℤ)
  tD : List (Bool × Bool × Bool × Bool × ℕ × ℕ)
  eI : List ((Bool × ℕ × ℕ) × ℤ)
  uI : List ((Bool × Bool × ℕ × ℕ) × ℤ)
  uB : List ((Bool × Bool × Bool × Bool × ℕ × ℕ) × ℤ)
  uD : List (Bool × Bool × Bool × Bool × ℕ × ℕ)
  eB : List ((Bool × ℕ × ℕ) × ℤ)

namespace Core

def dlF (C : Core) : ℕ → ℕ → ℕ := tab C.dl
def loF (C : Core) (q : ℕ) : ℕ := C.lo.getD q 0
def exF (C : Core) (q : ℕ) : Bool := C.ex.getD q false

/-- The test of the invariants for machine `m` with growth factor `c`. -/
def check (m c : ℕ) (C : Core) : Bool :=
  lenCheck C.N C.dlF C.loF C.exF &&
  fwdCheck m C.dlF (tabB C.adI) [true, false] C.fI C.fB &&
  fwdCheck m C.dlF (tabB C.adB) [false] C.gI C.gB &&
  tdCheck m C.dlF (tabB C.agI) (tabB C.adI) (tabB C.agI) [true, false] c C.tI C.tB C.tD C.eI &&
  tdCheck m C.dlF (tabB C.agB) (tabB C.adB) (tabB C.agB) [false] c C.uI C.uB C.uD C.eB &&
  gbCheck C.N (tabB C.agI) (tabB C.adB) (tabB C.agB) &&
  [true, false].all (fun r => !tabB C.adI 0 (pc (true, r)) || tabB C.agI 0 (pc (true, r)))

theorem lenInfo {m c : ℕ} {C : Core} (h : C.check m c = true) :
    LenInfo C.dlF C.N C.loF C.exF := by
  simp only [check, Bool.and_eq_true] at h
  exact lenCheck_sound h.1.1.1.1.1.1

/-- The invariants give an `AbsSys` for every choice of potentials that satisfy the potential
inequalities. -/
theorem absSys {m c : ℕ} {C : Core} (h : C.check m c = true) {D : ℕ} {Wi : ℕ → ℕ → ℕ → ℤ}
    {Wb : ℕ → ℕ → ℤ}
    (potB : ∀ (g g' : ℕ) (Δ : ℤ) (ℓ ℓ' : ℕ), look (false, g, g') C.eB = some Δ → 1 ≤ ℓ →
      LenOK C.loF C.exF g ℓ → LenOK C.loF C.exF g' ℓ' → (ℓ' : ℤ) ≤ c * ℓ + Δ →
      (D : ℤ) * (2 * ℓ) + Wb g' ℓ' ≤ Wb g ℓ)
    (potI : ∀ (b : Bool) (g g' : ℕ) (Δ : ℤ) (ℓ ℓ' k : ℕ), look (b, g, g') C.eI = some Δ → 1 ≤ ℓ →
      LenOK C.loF C.exF g ℓ → LenOK C.loF C.exF g' ℓ' → (ℓ' : ℤ) ≤ c * ℓ + Δ →
      (D : ℤ) * (2 * ℓ) + Wi g' ℓ' k ≤ Wi g ℓ (k + 1))
    (pot0 : ∀ g ℓ : ℕ, LenOK C.loF C.exF g ℓ → Wb g ℓ ≤ Wi g ℓ 0)
    (potE : 0 ≤ Wb 0 0) (potE' : ∀ k : ℕ, 0 ≤ Wi 0 0 k) :
    AbsSys m C.dlF C.loF C.exF c D (tabB C.adI) (tabB C.adB) (tabB C.agI) (tabB C.agB)
      (fun b g g' => look (b, g, g') C.eI) (fun b g g' => look (b, g, g') C.eB) Wi Wb := by
  have li := lenInfo h
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨_, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩ := h
  have fI := fwdCheck_sound c2
  have fB := fwdCheck_sound c3
  have tI := tdCheck_sound c4
  have tB := tdCheck_sound c5
  refine
    { fwdI := ?_, fwdB := ?_, tdI := ?_, tdB := ?_, gb := ?_, startG := ?_, len := ?_,
      potB := potB, potI := potI, pot0 := pot0, potE := potE, potE' := potE' }
  · intro c W hs W' s
    exact fI.sound (R := fun _ => True) (fun W _ => ⟨by cases W 0 <;> simp, trivial⟩) c W hs W'
      trivial s
  · intro c W hs W' hW s
    exact fB.sound (R := fun W => ∀ i, W i = false)
      (fun W hW => ⟨by simp [hW 0], fun i => hW (i + 1)⟩) c W hs W' hW s
  · intro b hs hs' b' cp hg ha
    exact tI.sound (by cases b <;> simp) cp hg ha
  · intro hs hs' b' cp hg ha
    exact tB.sound (by simp) cp hg ha
  · intro hs hg ha
    exact gbCheck_sound li c6 hs 0 li.pos hg ha
  · intro r ha
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at c7
    simp only [acc, Bool.and_true] at ha ⊢
    rcases c7 r (by cases r <;> simp) with k | k
    · rw [k] at ha; exact absurd ha (by simp)
    · exact k
  · intro hs
    exact (li.ok hs).2

end Core

/-- A certificate with quadratic potentials (scaled by `D`). -/
structure Cert extends Core where
  D : ℕ
  wi : List Q2
  wb : List Q2

namespace Cert

def wiF (C : Cert) (g : ℕ) : Q2 := C.wi.getD g Q2.zero
def wbF (C : Cert) (g : ℕ) : Q2 := C.wb.getD g Q2.zero

/-- The complete test for machine `m`. -/
def check (m : ℕ) (C : Cert) : Bool :=
  C.toCore.check m 1 &&
  decide (1 ≤ C.D) && decide (C.wi.length = C.N) && decide (C.wb.length = C.N) &&
  C.eI.all (fun x => edgeOK C.D (C.wiF x.1.2.1) (C.wiF x.1.2.2) (C.loF x.1.2.1) (C.exF x.1.2.1)
    (C.loF x.1.2.2) (C.exF x.1.2.2) x.2 1) &&
  C.eB.all (fun x => edgeOK C.D (C.wbF x.1.2.1) (C.wbF x.1.2.2) (C.loF x.1.2.1) (C.exF x.1.2.1)
    (C.loF x.1.2.2) (C.exF x.1.2.2) x.2 0) &&
  (List.range C.N).all (fun g => zeroOK (C.wiF g) (C.wbF g) (C.loF g) (C.exF g)) &&
  decide (C.wiF 0 = Q2.zero) && decide (C.wbF 0 = Q2.zero) &&
  [true, false].all (fun r => !tabB C.adI 0 (pc (true, r)) ||
    tgtOK C.D (C.wiF (C.dlF 0 (pc (true, r)))))

theorem absSys {m : ℕ} {C : Cert} (h : C.check m = true) :
    AbsSys m C.dlF C.loF C.exF 1 C.D (tabB C.adI) (tabB C.adB) (tabB C.agI) (tabB C.agB)
      (fun b g g' => look (b, g, g') C.eI) (fun b g g' => look (b, g, g') C.eB)
      (fun g ℓ k => (C.wiF g).eval ℓ k) (fun g ℓ => (C.wbF g).eval ℓ 0) := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, _⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩, c15⟩, _⟩ := h
  simp only [decide_eq_true_eq] at c9 c10 c14 c15
  refine Core.absSys c0 ?_ ?_ ?_ ?_ ?_
  · intro g g' Δ ℓ ℓ' hE hℓ hl hl' hΔ
    simp only [List.all_eq_true] at c12
    have := c12 _ (look_mem hE)
    have := edgeOK_sound this (ℓ := ℓ) (ℓ' := ℓ') (k := 0) (le_refl 0) (by exact_mod_cast hl.1)
      (fun he => by exact_mod_cast hl.2 he) (by exact_mod_cast hl'.1)
      (fun he => by exact_mod_cast hl'.2 he) (by simpa using hΔ)
    simpa using this
  · intro b g g' Δ ℓ ℓ' k hE hℓ hl hl' hΔ
    simp only [List.all_eq_true] at c11
    have := c11 _ (look_mem hE)
    have := edgeOK_sound this (ℓ := ℓ) (ℓ' := ℓ') (k := k) (by positivity)
      (by exact_mod_cast hl.1) (fun he => by exact_mod_cast hl.2 he) (by exact_mod_cast hl'.1)
      (fun he => by exact_mod_cast hl'.2 he) (by simpa using hΔ)
    simpa using this
  · intro g ℓ hl
    by_cases hg : g < C.N
    · simp only [List.all_eq_true, List.mem_range] at c13
      exact zeroOK_sound (c13 g hg) (by exact_mod_cast hl.1) (fun he => by exact_mod_cast hl.2 he)
    · have e1 : C.wiF g = Q2.zero := by
        simp only [wiF]; rw [List.getD_eq_default _ _ (by omega)]
      have e2 : C.wbF g = Q2.zero := by
        simp only [wbF]; rw [List.getD_eq_default _ _ (by omega)]
      simp [e1, e2]
  · simp [c15]
  · intro k
    simp [c14]

/-- **Soundness of the checker** (quadratic potentials). -/
theorem sound {m : ℕ} {C : Cert} (h : C.check m = true) {n x t : ℕ} (hn : 1 ≤ n)
    (hx : x < 2 ^ n) (ht : HaltsAfter m (init x) t) : t + 1 ≤ 2 * (n + 2) ^ 2 := by
  obtain ⟨r, ha, hb⟩ := (absSys h).halting_bound hx ht
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, c8⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, c16⟩ := h
  simp only [decide_eq_true_eq] at c8
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at c16
  simp only [acc, Bool.and_true] at ha
  have ht' : tgtOK C.D (C.wiF (C.dlF 0 (pc (true, r)))) = true := by
    rcases c16 r (by cases r <;> simp) with k | k
    · rw [k] at ha; exact absurd ha (by simp)
    · exact k
  have h2 := tgtOK_sound ht' hn
  have hD : (0 : ℤ) < C.D := by exact_mod_cast c8
  have h3 : (C.D : ℤ) * ((t : ℤ) + 1) ≤ C.D * (2 * ((n : ℤ) + 2) ^ 2) := by
    refine le_trans hb ?_
    simpa using h2
  have h4 : (t : ℤ) + 1 ≤ 2 * ((n : ℤ) + 2) ^ 2 := le_of_mul_le_mul_left h3 hD
  exact_mod_cast h4

end Cert

end A393317
