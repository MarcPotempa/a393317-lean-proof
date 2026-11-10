import A393317.Bound

/-!
# Quadratic potentials

Potentials are polynomials of degree at most two in the length `ℓ` of a history and the number
`k` of remaining input cells.  The inequalities needed for `AbsSys` are reduced to the
non-negativity of all coefficients of a difference polynomial after a shift of the variables,
which is a decidable condition.
-/

namespace A393317

/-- `a20 ℓ² + a11 ℓ k + a02 k² + a10 ℓ + a01 k + a00`. -/
structure Q2 where
  a20 : ℤ
  a11 : ℤ
  a02 : ℤ
  a10 : ℤ
  a01 : ℤ
  a00 : ℤ
deriving DecidableEq, Repr

namespace Q2

def zero : Q2 := ⟨0, 0, 0, 0, 0, 0⟩

def eval (q : Q2) (ℓ k : ℤ) : ℤ :=
  q.a20 * ℓ ^ 2 + q.a11 * ℓ * k + q.a02 * k ^ 2 + q.a10 * ℓ + q.a01 * k + q.a00

@[simp] theorem eval_zero (ℓ k : ℤ) : zero.eval ℓ k = 0 := by simp [eval, zero]

/-- Coefficients of `q (ℓ₀ + uc·u, k + sh)` as a polynomial in `(u, k)`. -/
def expand (q : Q2) (ℓ₀ uc sh : ℤ) : Q2 where
  a20 := q.a20 * uc ^ 2
  a11 := q.a11 * uc
  a02 := q.a02
  a10 := (2 * q.a20 * ℓ₀ + q.a11 * sh + q.a10) * uc
  a01 := q.a11 * ℓ₀ + 2 * q.a02 * sh + q.a01
  a00 := q.a20 * ℓ₀ ^ 2 + q.a11 * ℓ₀ * sh + q.a02 * sh ^ 2 + q.a10 * ℓ₀ + q.a01 * sh + q.a00

theorem expand_eval (q : Q2) (ℓ₀ uc sh u k : ℤ) :
    (q.expand ℓ₀ uc sh).eval u k = q.eval (ℓ₀ + uc * u) (k + sh) := by
  simp only [eval, expand]; ring

def sub (p q : Q2) : Q2 :=
  ⟨p.a20 - q.a20, p.a11 - q.a11, p.a02 - q.a02, p.a10 - q.a10, p.a01 - q.a01, p.a00 - q.a00⟩

theorem sub_eval (p q : Q2) (ℓ k : ℤ) : (p.sub q).eval ℓ k = p.eval ℓ k - q.eval ℓ k := by
  simp only [eval, sub]; ring

def nonneg (q : Q2) : Bool :=
  decide (0 ≤ q.a20) && decide (0 ≤ q.a11) && decide (0 ≤ q.a02) && decide (0 ≤ q.a10) &&
    decide (0 ≤ q.a01) && decide (0 ≤ q.a00)

theorem nonneg_eval {q : Q2} (h : q.nonneg = true) {u k : ℤ} (hu : 0 ≤ u) (hk : 0 ≤ k) :
    0 ≤ q.eval u k := by
  simp only [nonneg, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  simp only [eval]
  positivity

/-- `q` is non-decreasing in `ℓ` on `ℓ ≥ lo` (for every `k ≥ 0`). -/
def mono (q : Q2) (lo : ℤ) : Bool :=
  decide (0 ≤ q.a20) && decide (0 ≤ q.a11) && decide (0 ≤ q.a20 * (2 * lo) + q.a10)

theorem mono_eval {q : Q2} {lo : ℤ} (h : q.mono lo = true) {ℓ ℓ' k : ℤ} (h1 : lo ≤ ℓ)
    (h2 : ℓ ≤ ℓ') (hk : 0 ≤ k) : q.eval ℓ k ≤ q.eval ℓ' k := by
  simp only [mono, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨m1, m2⟩, m3⟩ := h
  have e : q.eval ℓ' k - q.eval ℓ k = (ℓ' - ℓ) * (q.a20 * (ℓ' + ℓ) + q.a11 * k + q.a10) := by
    simp only [eval]; ring
  have t1 : q.a20 * (2 * lo) ≤ q.a20 * (ℓ' + ℓ) := mul_le_mul_of_nonneg_left (by omega) m1
  have t2 : 0 ≤ q.a11 * k := mul_nonneg m2 hk
  have t3 : 0 ≤ (ℓ' - ℓ) * (q.a20 * (ℓ' + ℓ) + q.a11 * k + q.a10) :=
    mul_nonneg (by omega) (by linarith)
  linarith

end Q2

/-- Decidable sufficient condition for
`D · 2ℓ + q'(ℓ', k) ≤ q(ℓ, k + sh)` for all admissible `ℓ, ℓ', k` with `ℓ' ≤ ℓ + Δ`. -/
def edgeOK (D : ℤ) (q q' : Q2) (lo : ℤ) (ex : Bool) (lo' : ℤ) (ex' : Bool) (Δ sh : ℤ) : Bool :=
  let ℓ₀ : ℤ := if ex then lo else max lo (lo' - Δ)
  let uc : ℤ := if ex then 0 else 1
  let ℓ₁ : ℤ := if ex' then lo' else ℓ₀ + Δ
  let uc' : ℤ := if ex' then 0 else uc
  let R : Q2 := (q.expand ℓ₀ uc sh).sub (q'.expand ℓ₁ uc' 0)
  let R' : Q2 := { R with a10 := R.a10 - 2 * D * uc, a00 := R.a00 - 2 * D * ℓ₀ }
  (ex && decide (lo + Δ < lo')) || ((ex' || q'.mono lo') && R'.nonneg)

theorem edgeOK_sound {D : ℤ} {q q' : Q2} {lo : ℤ} {ex : Bool} {lo' : ℤ} {ex' : Bool} {Δ sh : ℤ}
    (h : edgeOK D q q' lo ex lo' ex' Δ sh = true) {ℓ ℓ' k : ℤ} (hk : 0 ≤ k)
    (h1 : lo ≤ ℓ) (h2 : ex = true → ℓ = lo) (h1' : lo' ≤ ℓ') (h2' : ex' = true → ℓ' = lo')
    (hΔ : ℓ' ≤ ℓ + Δ) : D * (2 * ℓ) + q'.eval ℓ' k ≤ q.eval ℓ (k + sh) := by
  cases ex with
  | true =>
    have hℓ : ℓ = lo := h2 rfl
    cases ex' with
    | true =>
      have hℓ' : ℓ' = lo' := h2' rfl
      simp only [edgeOK, if_true, Bool.true_and, Bool.true_or, Bool.or_eq_true,
        decide_eq_true_eq] at h
      rcases h with hv | hn
      · omega
      · have := Q2.nonneg_eval hn (le_refl 0) hk
        simp only [Q2.eval, Q2.sub, Q2.expand] at this
        simp only [Q2.eval, hℓ, hℓ']
        linarith
    | false =>
      simp only [edgeOK, if_true, Bool.true_and, Bool.false_or, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true, if_false] at h
      rcases h with hv | ⟨hm, hn⟩
      · omega
      · have hmono := Q2.mono_eval hm (ℓ := ℓ') (ℓ' := lo + Δ) (k := k) h1' (by omega) hk
        have := Q2.nonneg_eval hn (le_refl 0) hk
        simp only [Q2.eval, Q2.sub, Q2.expand] at this
        simp only [Q2.eval, hℓ] at hmono ⊢
        linarith
  | false =>
    have hu : 0 ≤ ℓ - max lo (lo' - Δ) := by
      have : max lo (lo' - Δ) ≤ ℓ := max_le h1 (by omega)
      omega
    cases ex' with
    | true =>
      have hℓ' : ℓ' = lo' := h2' rfl
      simp only [edgeOK, if_true, Bool.false_and, Bool.true_or, Bool.true_and, Bool.false_or,
        Bool.false_eq_true, if_false] at h
      have := Q2.nonneg_eval h hu hk
      simp only [Q2.eval, Q2.sub, Q2.expand] at this
      simp only [Q2.eval, hℓ']
      linarith
    | false =>
      simp only [edgeOK, Bool.false_and, Bool.false_or, Bool.and_eq_true, Bool.false_eq_true,
        if_false] at h
      obtain ⟨hm, hn⟩ := h
      have hmono := Q2.mono_eval hm (ℓ := ℓ') (ℓ' := ℓ + Δ) (k := k) h1' hΔ hk
      have := Q2.nonneg_eval hn hu hk
      simp only [Q2.eval, Q2.sub, Q2.expand] at this
      simp only [Q2.eval] at hmono ⊢
      linarith

/-- Decidable sufficient condition for `qb(ℓ, 0) ≤ q(ℓ, 0)` for all admissible `ℓ`. -/
def zeroOK (q qb : Q2) (lo : ℤ) (ex : Bool) : Bool :=
  let uc : ℤ := if ex then 0 else 1
  let R : Q2 := (q.expand lo uc 0).sub (qb.expand lo uc 0)
  decide (0 ≤ R.a20) && decide (0 ≤ R.a10) && decide (0 ≤ R.a00)

theorem zeroOK_sound {q qb : Q2} {lo : ℤ} {ex : Bool} (h : zeroOK q qb lo ex = true) {ℓ : ℤ}
    (h1 : lo ≤ ℓ) (h2 : ex = true → ℓ = lo) : qb.eval ℓ 0 ≤ q.eval ℓ 0 := by
  cases ex with
  | true =>
    have := h2 rfl
    subst this
    simp only [zeroOK, if_true, Bool.and_eq_true, decide_eq_true_eq, Q2.sub, Q2.expand] at h
    obtain ⟨⟨r1, r2⟩, r3⟩ := h
    simp only [Q2.eval]
    linarith
  | false =>
    simp only [zeroOK, Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq, Q2.sub,
      Q2.expand] at h
    obtain ⟨⟨r1, r2⟩, r3⟩ := h
    have hu : 0 ≤ ℓ - lo := by omega
    have t1 := mul_nonneg r1 (mul_nonneg hu hu)
    have t2 := mul_nonneg r2 hu
    simp only [Q2.eval]
    nlinarith [t1, t2, r3]

/-- Decidable sufficient condition for `q(1, n) ≤ D · 2(n+2)²` for all `n ≥ 1`. -/
def tgtOK (D : ℤ) (q : Q2) : Bool :=
  let R : Q2 := q.expand 1 0 1
  decide (R.a02 ≤ 2 * D) && decide (R.a01 ≤ 12 * D) && decide (R.a00 ≤ 18 * D)

theorem tgtOK_sound {D : ℤ} {q : Q2} (h : tgtOK D q = true) {n : ℕ} (hn : 1 ≤ n) :
    q.eval 1 n ≤ D * (2 * ((n : ℤ) + 2) ^ 2) := by
  simp only [tgtOK, Bool.and_eq_true, decide_eq_true_eq, Q2.expand] at h
  obtain ⟨⟨r1, r2⟩, r3⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : (0 : ℤ) ≤ k := by positivity
  simp only [Q2.eval]
  push_cast
  nlinarith [mul_nonneg hk hk, mul_le_mul_of_nonneg_right r1 (mul_nonneg hk hk),
    mul_le_mul_of_nonneg_right r2 hk]

end A393317
