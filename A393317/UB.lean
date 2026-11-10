import A393317.Expo
import A393317.Special

/-!
# The upper bound for a single machine

`UB m` says that every halting time of machine `m` on an input `x < 2^n` (`n ≥ 1`) is at most the
conjectured value `bnd n` of A393317.
-/

namespace A393317

/-- The value of A393317(n) conjectured by M. F. Hasler. -/
def bnd (n : ℕ) : ℕ := if n < 5 then 2 * (n + 2) ^ 2 - 1 else 2 ^ (n + 2) - 3

/-- Every halting time of machine `m` on inputs below `2^n` is at most `bnd n`. -/
def UB (m : ℕ) : Prop :=
  ∀ n x t : ℕ, 1 ≤ n → x < 2 ^ n → HaltsAfter m (init x) t → t ≤ bnd n

theorem quad_le_exp (n : ℕ) (hn : 5 ≤ n) : 2 * (n + 2) ^ 2 + 2 ≤ 2 ^ (n + 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have e : (2 : ℕ) ^ (n + 1 + 2) = 2 * 2 ^ (n + 2) := by rw [pow_succ]; ring
    have h1 : 2 * (n + 1 + 2) ^ 2 + 2 = 2 * (n + 2) ^ 2 + 2 + (4 * n + 10) := by ring
    have h2 : 4 * n + 10 ≤ 2 * (n + 2) ^ 2 + 2 := by nlinarith
    omega

theorem four_sq_le_exp (n : ℕ) (hn : 5 ≤ n) : 4 * n ^ 2 + 3 ≤ 2 ^ (n + 2) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have e : (2 : ℕ) ^ (n + 1 + 2) = 2 * 2 ^ (n + 2) := by rw [pow_succ]; ring
    have h1 : 4 * (n + 1) ^ 2 + 3 = 4 * n ^ 2 + 3 + (8 * n + 4) := by ring
    have h2 : 8 * n + 4 ≤ 4 * n ^ 2 + 3 := by nlinarith
    omega

theorem le_bnd_of_quad {n t : ℕ} (h : t + 1 ≤ 2 * (n + 2) ^ 2) : t ≤ bnd n := by
  unfold bnd
  split
  · omega
  · have := quad_le_exp n (by omega)
    omega

theorem le_bnd_of_exp {n t : ℕ} (hn : 1 ≤ n) (h : t + 3 ≤ 2 ^ (n + 2)) : t ≤ bnd n := by
  unfold bnd
  split
  · interval_cases n <;> norm_num at h ⊢ <;> omega
  · omega

theorem le_bnd_of_four_sq {n t : ℕ} (hn : 1 ≤ n) (h : t ≤ 4 * n ^ 2) : t ≤ bnd n := by
  unfold bnd
  split
  · interval_cases n <;> norm_num at h ⊢ <;> omega
  · have := four_sq_le_exp n (by omega)
    omega

theorem UB.of_cert {m : ℕ} {C : Cert} (h : C.check m = true) : UB m :=
  fun _ _ _ hn hx ht => le_bnd_of_quad (Cert.sound h hn hx ht)

theorem UB.of_certE {m : ℕ} {C : CertE} (h : C.check m = true) : UB m :=
  fun _ _ _ hn hx ht => le_bnd_of_exp hn (CertE.sound h hn hx ht)

theorem ub3555 : UB 3555 := by
  intro n x t hn hx ht
  have h := m3555 hx ht
  unfold bnd
  split
  · have : 2 * (n + 2) ^ 2 = 2 * n ^ 2 + 8 * n + 8 := by ring
    omega
  · have h1 := quad_le_exp n (by omega)
    have : 2 * (n + 2) ^ 2 = 2 * n ^ 2 + 8 * n + 8 := by ring
    omega

theorem ub1507 : UB 1507 := by
  intro n x t hn hx ht
  rcases Nat.lt_or_ge n 2 with h | h
  · have hn1 : n = 1 := by omega
    subst hn1
    have := m1507_one (by simpa using hx) ht
    simp only [bnd]
    norm_num
    omega
  · exact le_bnd_of_four_sq hn (m1507 h hx ht)

theorem ub2830 : UB 2830 := fun _ _ _ hn hx ht => le_bnd_of_four_sq hn (m2830 hn hx ht)

theorem ub2574 : UB 2574 := fun _ _ _ hn hx ht => le_bnd_of_four_sq hn (m2574 hn hx ht)

end A393317
