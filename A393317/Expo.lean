import A393317.Checker

/-!
# Certificates with exponential potentials

For the few machines whose histories can double from cell to cell (`c = 2`), the potentials have
the form `(al·ℓ + ga)·2^k + be·ℓ + de`.
-/

namespace A393317

/-- `(al·ℓ + ga)·2^k + be·ℓ + de`. -/
structure E2 where
  al : ℤ
  ga : ℤ
  be : ℤ
  de : ℤ
deriving DecidableEq, Repr

namespace E2

def zero : E2 := ⟨0, 0, 0, 0⟩

def eval (q : E2) (ℓ : ℤ) (k : ℕ) : ℤ := (q.al * ℓ + q.ga) * 2 ^ k + q.be * ℓ + q.de

@[simp] theorem eval_zero (ℓ : ℤ) (k : ℕ) : zero.eval ℓ k = 0 := by simp [eval, zero]

end E2

/-- Decidable sufficient condition for `D·2ℓ + q'(ℓ', k) ≤ q(ℓ, k + sh)` for all admissible
`ℓ, ℓ', k` with `ℓ' ≤ 2ℓ + Δ`. -/
def edgeOK2 (D : ℤ) (q q' : E2) (lo : ℤ) (ex : Bool) (lo' : ℤ) (ex' : Bool) (Δ : ℤ) (sh : ℕ) :
    Bool :=
  let ℓ₀ : ℤ := if ex then lo else max lo ((lo' - Δ + 1) / 2)
  let uc : ℤ := if ex then 0 else 1
  let ℓ₁ : ℤ := if ex' then lo' else 2 * ℓ₀ + Δ
  let uc' : ℤ := if ex' then 0 else 2 * uc
  let A0 : ℤ := 2 ^ sh * (q.al * ℓ₀ + q.ga) - (q'.al * ℓ₁ + q'.ga)
  let A1 : ℤ := 2 ^ sh * q.al * uc - q'.al * uc'
  let B0 : ℤ := q.be * ℓ₀ + q.de - (q'.be * ℓ₁ + q'.de) - 2 * D * ℓ₀
  let B1 : ℤ := q.be * uc - q'.be * uc' - 2 * D * uc
  (ex && decide (2 * lo + Δ < lo')) ||
    ((ex' || (decide (0 ≤ q'.al) && decide (0 ≤ q'.al + q'.be))) &&
      decide (0 ≤ A0) && decide (0 ≤ A1) && decide (0 ≤ A0 + B0) && decide (0 ≤ A1 + B1))

/-- The arithmetic core: if `A0, A1, A0+B0, A1+B1 ≥ 0`, `u ≥ 0` and `P ≥ 1`, then
`(A0 + A1 u) P + B0 + B1 u ≥ 0`. -/
theorem expo_core {A0 A1 B0 B1 u P : ℤ} (h0 : 0 ≤ A0) (h1 : 0 ≤ A1) (h2 : 0 ≤ A0 + B0)
    (h3 : 0 ≤ A1 + B1) (hu : 0 ≤ u) (hP : 1 ≤ P) : 0 ≤ (A0 + A1 * u) * P + (B0 + B1 * u) := by
  have hA : 0 ≤ A0 + A1 * u := add_nonneg h0 (mul_nonneg h1 hu)
  have t1 : 0 ≤ (A0 + A1 * u) * (P - 1) := mul_nonneg hA (by omega)
  have t2 : 0 ≤ (A1 + B1) * u := mul_nonneg h3 hu
  nlinarith [t1, t2]

theorem E2.mono_eval {q : E2} (ha : 0 ≤ q.al) (hb : 0 ≤ q.al + q.be) {ℓ ℓ' : ℤ} (h : ℓ ≤ ℓ')
    (k : ℕ) : q.eval ℓ k ≤ q.eval ℓ' k := by
  have hP : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have e : q.eval ℓ' k - q.eval ℓ k = (ℓ' - ℓ) * (q.al * 2 ^ k + q.be) := by
    simp only [E2.eval]; ring
  have t1 : 0 ≤ q.al * (2 ^ k - 1) := mul_nonneg ha (by omega)
  have t2 : 0 ≤ (ℓ' - ℓ) * (q.al * 2 ^ k + q.be) := mul_nonneg (by omega) (by nlinarith [t1])
  linarith

theorem edgeOK2_sound {D : ℤ} {q q' : E2} {lo : ℤ} {ex : Bool} {lo' : ℤ} {ex' : Bool} {Δ : ℤ}
    {sh : ℕ} (h : edgeOK2 D q q' lo ex lo' ex' Δ sh = true) {ℓ ℓ' : ℤ} (k : ℕ)
    (h1 : lo ≤ ℓ) (h2 : ex = true → ℓ = lo) (h1' : lo' ≤ ℓ') (h2' : ex' = true → ℓ' = lo')
    (hΔ : ℓ' ≤ 2 * ℓ + Δ) : D * (2 * ℓ) + q'.eval ℓ' k ≤ q.eval ℓ (k + sh) := by
  have hP : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hpow : (2 : ℤ) ^ (k + sh) = 2 ^ sh * 2 ^ k := by rw [pow_add]; ring
  cases ex with
  | true =>
    have hℓ : ℓ = lo := h2 rfl
    cases ex' with
    | true =>
      have hℓ' : ℓ' = lo' := h2' rfl
      simp only [edgeOK2, if_true, Bool.true_and, Bool.true_or, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with hv | ⟨⟨⟨hA0, hA1⟩, hAB0⟩, hAB1⟩
      · omega
      · have := expo_core hA0 hA1 hAB0 hAB1 (le_refl 0) hP
        simp only [E2.eval, hℓ, hℓ', hpow]
        nlinarith [this]
    | false =>
      simp only [edgeOK2, if_true, Bool.true_and, Bool.false_or, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, if_false] at h
      rcases h with hv | ⟨⟨⟨⟨⟨ma, mb⟩, hA0⟩, hA1⟩, hAB0⟩, hAB1⟩
      · omega
      · have hmono := E2.mono_eval ma mb (ℓ := ℓ') (ℓ' := 2 * lo + Δ) (by omega) k
        have := expo_core hA0 hA1 hAB0 hAB1 (le_refl 0) hP
        simp only [E2.eval, hℓ, hpow] at hmono ⊢
        nlinarith [this, hmono]
  | false =>
    have hu : 0 ≤ ℓ - max lo ((lo' - Δ + 1) / 2) := by
      have : max lo ((lo' - Δ + 1) / 2) ≤ ℓ := max_le h1 (by omega)
      omega
    cases ex' with
    | true =>
      have hℓ' : ℓ' = lo' := h2' rfl
      simp only [edgeOK2, if_true, Bool.false_and, Bool.true_or, Bool.true_and, Bool.false_or,
        Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hA0, hA1⟩, hAB0⟩, hAB1⟩ := h
      have := expo_core hA0 hA1 hAB0 hAB1 hu hP
      simp only [E2.eval, hℓ', hpow]
      nlinarith [this]
    | false =>
      simp only [edgeOK2, Bool.false_and, Bool.false_or, Bool.and_eq_true, Bool.false_eq_true,
        if_false, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨ma, mb⟩, hA0⟩, hA1⟩, hAB0⟩, hAB1⟩ := h
      have hmono := E2.mono_eval ma mb (ℓ := ℓ') (ℓ' := 2 * ℓ + Δ) hΔ k
      have := expo_core hA0 hA1 hAB0 hAB1 hu hP
      simp only [E2.eval, hpow] at hmono ⊢
      nlinarith [this, hmono]

/-- Decidable sufficient condition for `qb(ℓ, 0) ≤ q(ℓ, 0)` for all admissible `ℓ`. -/
def zeroOK2 (q qb : E2) (lo : ℤ) (ex : Bool) : Bool :=
  let R1 : ℤ := (q.al + q.be) - (qb.al + qb.be)
  let R0 : ℤ := (q.ga + q.de) - (qb.ga + qb.de)
  (ex || decide (0 ≤ R1)) && decide (0 ≤ R1 * lo + R0)

theorem zeroOK2_sound {q qb : E2} {lo : ℤ} {ex : Bool} (h : zeroOK2 q qb lo ex = true) {ℓ : ℤ}
    (h1 : lo ≤ ℓ) (h2 : ex = true → ℓ = lo) : qb.eval ℓ 0 ≤ q.eval ℓ 0 := by
  cases ex with
  | true =>
    have := h2 rfl
    subst this
    simp only [zeroOK2, Bool.true_or, Bool.true_and, decide_eq_true_eq] at h
    simp only [E2.eval, pow_zero, mul_one]
    linarith
  | false =>
    simp only [zeroOK2, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨r1, r2⟩ := h
    have t := mul_nonneg r1 (show (0 : ℤ) ≤ ℓ - lo by omega)
    simp only [E2.eval, pow_zero, mul_one]
    nlinarith [t, r2]

/-- Decidable sufficient condition for `q(1, n) ≤ D (2^(n+2) − 2)` for all `n ≥ 1`. -/
def tgtOK2 (D : ℤ) (q : E2) : Bool :=
  decide (q.al + q.ga ≤ 4 * D) && decide (2 * (q.al + q.ga) + q.be + q.de ≤ 6 * D)

theorem tgtOK2_sound {D : ℤ} {q : E2} (h : tgtOK2 D q = true) {n : ℕ} (hn : 1 ≤ n) :
    q.eval 1 n ≤ D * (2 ^ (n + 2) - 2) := by
  simp only [tgtOK2, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨r1, r2⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hP : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have e1 : (2 : ℤ) ^ (k + 1 + 2) = 8 * 2 ^ k := by rw [pow_add, pow_add]; ring
  have e2 : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_add]; ring
  have t : 0 ≤ (4 * D - (q.al + q.ga)) * (2 ^ k - 1) := mul_nonneg (by omega) (by omega)
  simp only [E2.eval, e1, e2]
  nlinarith [t]

/-- A certificate with exponential potentials (growth factor 2). -/
structure CertE extends Core where
  D : ℕ
  we : List E2
  wbE : List E2

namespace CertE

def weF (C : CertE) (g : ℕ) : E2 := C.we.getD g E2.zero
def wbF (C : CertE) (g : ℕ) : E2 := C.wbE.getD g E2.zero

def check (m : ℕ) (C : CertE) : Bool :=
  C.toCore.check m 2 &&
  decide (1 ≤ C.D) && decide (C.we.length = C.N) && decide (C.wbE.length = C.N) &&
  C.eI.all (fun x => edgeOK2 C.D (C.weF x.1.2.1) (C.weF x.1.2.2) (C.loF x.1.2.1) (C.exF x.1.2.1)
    (C.loF x.1.2.2) (C.exF x.1.2.2) x.2 1) &&
  C.eB.all (fun x => edgeOK2 C.D (C.wbF x.1.2.1) (C.wbF x.1.2.2) (C.loF x.1.2.1) (C.exF x.1.2.1)
    (C.loF x.1.2.2) (C.exF x.1.2.2) x.2 0) &&
  (List.range C.N).all (fun g => zeroOK2 (C.weF g) (C.wbF g) (C.loF g) (C.exF g)) &&
  decide (C.weF 0 = E2.zero) && decide (C.wbF 0 = E2.zero) &&
  [true, false].all (fun r => !tabB C.adI 0 (pc (true, r)) ||
    tgtOK2 C.D (C.weF (C.dlF 0 (pc (true, r)))))

theorem absSys {m : ℕ} {C : CertE} (h : C.check m = true) :
    AbsSys m C.dlF C.loF C.exF 2 C.D (tabB C.adI) (tabB C.adB) (tabB C.agI) (tabB C.agB)
      (fun b g g' => look (b, g, g') C.eI) (fun b g g' => look (b, g, g') C.eB)
      (fun g ℓ k => (C.weF g).eval ℓ k) (fun g ℓ => (C.wbF g).eval ℓ 0) := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨c0, _⟩, c9⟩, c10⟩, c11⟩, c12⟩, c13⟩, c14⟩, c15⟩, _⟩ := h
  simp only [decide_eq_true_eq] at c9 c10 c14 c15
  refine Core.absSys c0 ?_ ?_ ?_ ?_ ?_
  · intro g g' Δ ℓ ℓ' hE hℓ hl hl' hΔ
    simp only [List.all_eq_true] at c12
    have := c12 _ (look_mem hE)
    have := edgeOK2_sound this (ℓ := ℓ) (ℓ' := ℓ') 0 (by exact_mod_cast hl.1)
      (fun he => by exact_mod_cast hl.2 he) (by exact_mod_cast hl'.1)
      (fun he => by exact_mod_cast hl'.2 he) (by simpa using hΔ)
    simpa using this
  · intro b g g' Δ ℓ ℓ' k hE hℓ hl hl' hΔ
    simp only [List.all_eq_true] at c11
    have := c11 _ (look_mem hE)
    exact edgeOK2_sound this (ℓ := ℓ) (ℓ' := ℓ') k (by exact_mod_cast hl.1)
      (fun he => by exact_mod_cast hl.2 he) (by exact_mod_cast hl'.1)
      (fun he => by exact_mod_cast hl'.2 he) (by simpa using hΔ)
  · intro g ℓ hl
    by_cases hg : g < C.N
    · simp only [List.all_eq_true, List.mem_range] at c13
      exact zeroOK2_sound (c13 g hg) (by exact_mod_cast hl.1) (fun he => by exact_mod_cast hl.2 he)
    · have e1 : C.weF g = E2.zero := by
        simp only [weF]; rw [List.getD_eq_default _ _ (by omega)]
      have e2 : C.wbF g = E2.zero := by
        simp only [wbF]; rw [List.getD_eq_default _ _ (by omega)]
      simp [e1, e2]
  · simp [c15]
  · intro k
    simp [c14]

/-- **Soundness of the checker** (exponential potentials). -/
theorem sound {m : ℕ} {C : CertE} (h : C.check m = true) {n x t : ℕ} (hn : 1 ≤ n)
    (hx : x < 2 ^ n) (ht : HaltsAfter m (init x) t) : t + 3 ≤ 2 ^ (n + 2) := by
  obtain ⟨r, ha, hb⟩ := (absSys h).halting_bound hx ht
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, c8⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, c16⟩ := h
  simp only [decide_eq_true_eq] at c8
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at c16
  simp only [acc, Bool.and_true] at ha
  have ht' : tgtOK2 C.D (C.weF (C.dlF 0 (pc (true, r)))) = true := by
    rcases c16 r (by cases r <;> simp) with k | k
    · rw [k] at ha; exact absurd ha (by simp)
    · exact k
  have h2 := tgtOK2_sound ht' hn
  have hD : (0 : ℤ) < C.D := by exact_mod_cast c8
  have h3 : (C.D : ℤ) * ((t : ℤ) + 1) ≤ C.D * (2 ^ (n + 2) - 2) := by
    refine le_trans hb ?_
    simpa using h2
  have h4 : (t : ℤ) + 1 ≤ 2 ^ (n + 2) - 2 := le_of_mul_le_mul_left h3 hD
  have h5 : (t : ℤ) + 3 ≤ 2 ^ (n + 2) := by omega
  exact_mod_cast h5

end CertE

end A393317
