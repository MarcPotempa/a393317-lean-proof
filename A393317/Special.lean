import A393317.Stage1

/-!
# The four machines that need an individual argument: 1507, 3555, 2574, 2830

Machines 1507 and 3555 (and, with the roles of the symbols exchanged, 2574 and 2830) work in
"events": in state `D` the head sweeps to the left over a block of equal symbols, changing them,
turns at the first different symbol and comes back like a zip, changing the symbols back and
alternating its state.  Every event consumes one cell (the turning point), which gives quadratic
bounds for the halting time.
-/

namespace A393317

/-! ## General facts about halting -/

theorem halts_unique {m : ℕ} {c : Config} {t t' : ℕ} (h : HaltsAfter m c t)
    (h' : HaltsAfter m c t') : t = t' := by
  induction h generalizing t' with
  | halt hs =>
    cases h' with
    | halt _ => rfl
    | next hs' _ => rw [hs] at hs'; cases hs'
  | next hs _ ih =>
    cases h' with
    | halt hs' => rw [hs] at hs'; cases hs'
    | next hs' h'' =>
      rw [hs] at hs'
      cases hs'
      rw [ih h'']

theorem halts_split {m : ℕ} : ∀ {k : ℕ} {c c' : Config} {t : ℕ}, run m k c = some c' →
    HaltsAfter m c t → ∃ t', t = k + t' ∧ HaltsAfter m c' t'
  | 0, c, c', t, hr, h => by
    simp only [run, Option.some.injEq] at hr
    subst hr
    exact ⟨t, by omega, h⟩
  | k + 1, c, c', t, hr, h => by
    simp only [run] at hr
    cases h with
    | halt hs => simp [hs] at hr
    | @next _ c1 t0 hs h0 =>
      rw [hs] at hr
      obtain ⟨t', e, h'⟩ := halts_split (k := k) (by simpa using hr) h0
      exact ⟨t', by omega, h'⟩

theorem Exits.split {m : ℕ} {c : Config} {τ : ℕ} {s : Bool} {p : ℕ} {T : ℕ → Bool} {t : ℕ}
    (hx : Exits m c τ s (p + 1) T) (h : HaltsAfter m c t) :
    ∃ t', t = τ + 1 + t' ∧ HaltsAfter m ⟨s, p, T⟩ t' :=
  halts_split hx.run_eq h

theorem Exits.time {m : ℕ} {c : Config} {τ : ℕ} {s : Bool} {T : ℕ → Bool} {t : ℕ}
    (hx : Exits m c τ s 0 T) (h : HaltsAfter m c t) : t = τ + 1 :=
  halts_unique h hx.halts

/-- `s` flipped `k` times. -/
def flipn (k : ℕ) (s : Bool) : Bool := if k % 2 = 0 then s else !s

theorem flipn_succ_not (k : ℕ) (s : Bool) : flipn (k + 1) (!s) = flipn (k + 2) s := by
  simp only [flipn]
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · rw [if_neg (by omega), if_pos (by omega)]; simp
  · rw [if_pos (by omega), if_neg (by omega)]

theorem flipn_succ_false (d : ℕ) : flipn (d + 1) false = flipn d true := by
  simp only [flipn]
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · rw [if_neg (by omega), if_pos (by omega)]; rfl
  · rw [if_pos (by omega), if_neg (by omega)]; rfl

theorem fill_in {T : ℕ → Bool} {q len : ℕ} {b : Bool} {i : ℕ} (h1 : q ≤ i) (h2 : i < q + len) :
    fill T q len b i = b := by
  simp only [fill]; rw [if_pos ⟨h1, h2⟩]

theorem fill_out {T : ℕ → Bool} {q len : ℕ} {b : Bool} {i : ℕ} (h : ¬(q ≤ i ∧ i < q + len)) :
    fill T q len b i = T i := by
  simp only [fill]; rw [if_neg h]

theorem next_zero (T : ℕ → Bool) {a n : ℕ} (han : a < n) (hn : T n = false) :
    ∃ z, a < z ∧ z ≤ n ∧ T z = false ∧ ∀ i, a < i → i < z → T i = true := by
  classical
  have hex : ∃ i, a < i ∧ T i = false := ⟨n, han, hn⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, Nat.find_min' hex ⟨han, hn⟩, (Nat.find_spec hex).2,
    fun i hi hiz => ?_⟩
  have := Nat.find_min hex hiz
  simp only [not_and] at this
  simpa using this hi

theorem next_one (T : ℕ → Bool) {a : ℕ} (hex : ∃ i, a < i ∧ T i = true) :
    ∃ y, a < y ∧ T y = true ∧ ∀ i, a < i → i < y → T i = false := by
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun i hi hiy => ?_⟩
  have := Nat.find_min hex hiy
  simp only [not_and] at this
  simpa using this hi

/-! ## Family A: `U0 → D1R`, `D1 → D0L`, `D0 → U1R` (machines 1507 and 3555) -/

structure FamA (m : ℕ) : Prop where
  u0 : digit m true false = 7
  d1 : digit m false true = 4
  d0 : digit m false false = 3

namespace FamA

variable {m : ℕ}

theorem sD1 (f : FamA m) {p : ℕ} {T : ℕ → Bool} (h : T p = true) :
    step m ⟨false, p, T⟩ = some ⟨false, p + 1, Function.update T p false⟩ := by
  have := step_left (m := m) (x := 4) (s := false) h f.d1 (by decide)
  simpa using this

/-- On a zero both states write a one, move right and change the state. -/
theorem sZ (f : FamA m) {s : Bool} {p : ℕ} {T : ℕ → Bool} (h : T p = false) :
    step m ⟨s, p, T⟩ = exitR (!s) p (Function.update T p true) := by
  cases s with
  | true =>
    have := step_right (m := m) (x := 7) (s := true) h f.u0 (by decide)
    simpa using this
  | false =>
    have := step_right (m := m) (x := 3) (s := false) h f.d0 (by decide)
    simpa using this

/-- State `D` sweeps left over `j` ones, erasing them. -/
theorem sweep (f : FamA m) : ∀ (j q : ℕ) (T : ℕ → Bool), (∀ i < j, T (q + i) = true) →
    run m j ⟨false, q, T⟩ = some ⟨false, q + j, fill T q j false⟩
  | 0, q, T, _ => by
    simp only [run, Nat.add_zero, Option.some.injEq, Config.mk.injEq, true_and]
    funext i; rw [fill_out (by omega)]
  | j + 1, q, T, h => by
    have hq : T q = true := by simpa using h 0 (by omega)
    rw [run_step (f.sD1 hq), sweep f j (q + 1) _ (fun i hi => by
      rw [Function.update_of_ne (by omega)]
      have := h (i + 1) (by omega)
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this)]
    simp only [Option.some.injEq, Config.mk.injEq, true_and]
    refine ⟨by omega, ?_⟩
    funext i
    by_cases hi : i = q
    · subst hi; rw [fill_out (by omega), fill_in (by omega) (by omega)]; simp
    · by_cases h1 : q + 1 ≤ i ∧ i < q + 1 + j
      · rw [fill_in h1.1 h1.2, fill_in (by omega) (by omega)]
      · rw [fill_out h1, fill_out (by omega), Function.update_of_ne hi]

/-- The zip: moving right over `j + 1` zeros, writing ones and alternating the state. -/
theorem zip (f : FamA m) : ∀ (j q : ℕ) (s : Bool) (T : ℕ → Bool),
    (∀ i < j + 1, T (q + i) = false) →
    Exits m ⟨s, q + j, T⟩ j (flipn (j + 1) s) q (fill T q (j + 1) true)
  | 0, q, s, T, h => by
    have hq : T q = false := by simpa using h 0 (by omega)
    apply Exits.of_step
    rw [Nat.add_zero, f.sZ hq]
    have e1 : flipn (0 + 1) s = !s := by simp [flipn]
    rw [e1]
    congr 1
    funext i
    by_cases hi : i = q
    · subst hi; rw [fill_in (by omega) (by omega)]; simp
    · rw [Function.update_of_ne hi, fill_out (by omega)]
  | j + 1, q, s, T, h => by
    have hq : T (q + (j + 1)) = false := h (j + 1) (by omega)
    have a1 : run m 1 ⟨s, q + (j + 1), T⟩ =
        some ⟨!s, q + j, Function.update T (q + (j + 1)) true⟩ := by
      apply run_one
      rw [f.sZ hq, show q + (j + 1) = (q + j) + 1 by omega, exitR_succ]
    have ih := zip f j q (!s) (Function.update T (q + (j + 1)) true) (fun i hi => by
      rw [Function.update_of_ne (by omega)]; exact h i (by omega))
    have e : fill (Function.update T (q + (j + 1)) true) q (j + 1) true =
        fill T q (j + 1 + 1) true := by
      funext i
      by_cases hi : i = q + (j + 1)
      · subst hi; rw [fill_out (by omega), fill_in (by omega) (by omega)]; simp
      · by_cases h1 : q ≤ i ∧ i < q + (j + 1)
        · rw [fill_in h1.1 h1.2, fill_in (by omega) (by omega)]
        · rw [fill_out h1, fill_out (by omega), Function.update_of_ne hi]
    rw [e, flipn_succ_not] at ih
    have := Exits.of_run a1 ih
    rwa [Nat.add_comm 1 j] at this

/-- **A `D`-event**: state `D` on cell `r`, ones on `r, …, r+d-1`, a zero on `r+d`.  After
`2d + 1` steps the head leaves cell `r` to the right, in state `U` if `d` is even and in state
`D` otherwise; the only change of the tape is a one on cell `r+d`. -/
theorem dev (f : FamA m) (r d : ℕ) (T : ℕ → Bool) (h1 : ∀ i < d, T (r + i) = true)
    (h0 : T (r + d) = false) :
    Exits m ⟨false, r, T⟩ (2 * d) (flipn d true) r (Function.update T (r + d) true) := by
  have a1 := f.sweep d r T h1
  have a2 := f.zip d r false (fill T r d false) (fun i hi => by
    by_cases hid : i < d
    · rw [fill_in (by omega) (by omega)]
    · have : i = d := by omega
      subst this
      rw [fill_out (by omega)]; exact h0)
  have e : fill (fill T r d false) r (d + 1) true = Function.update T (r + d) true := by
    funext i
    by_cases hi : i = r + d
    · subst hi; rw [fill_in (by omega) (by omega)]; simp
    · rw [Function.update_of_ne hi]
      by_cases h2 : r ≤ i ∧ i < r + d
      · rw [fill_in h2.1 (by omega)]
        obtain ⟨k, rfl⟩ : ∃ k, i = r + k := ⟨i - r, by omega⟩
        exact (h1 k (by omega)).symm
      · rw [fill_out (by omega), fill_out h2]
  rw [e, flipn_succ_false] at a2
  have := Exits.of_run a1 a2
  rwa [show d + d = 2 * d by omega] at this

end FamA

/-! ## Machine 3555 -/

theorem famA3555 : FamA 3555 := ⟨by decide, by decide, by decide⟩

theorem s3555_U1 {p : ℕ} {T : ℕ → Bool} (h : T p = true) :
    step 3555 ⟨true, p, T⟩ = some ⟨false, p + 1, T⟩ := by
  have := step_left (m := 3555) (x := 6) (s := true) h (by decide) (by decide)
  simpa [update_same_val h] using this

/-- One round: `U` on cell 0, ones on `0, …, z-1`, a zero on `z`. -/
theorem ev3555 {z : ℕ} {T : ℕ → Bool} (hz : 1 ≤ z) (h1 : ∀ i < z, T i = true)
    (h0 : T z = false) :
    run 3555 (2 * z) ⟨true, 0, T⟩ = some ⟨flipn (z - 1) true, 0, Function.update T z true⟩ := by
  obtain ⟨d, rfl⟩ : ∃ d, z = d + 1 := ⟨z - 1, by omega⟩
  have a1 : run 3555 1 ⟨true, 0, T⟩ = some ⟨false, 0 + 1, T⟩ := run_one (s3555_U1 (h1 0 (by omega)))
  have a2 := (famA3555.dev (0 + 1) d T (fun i hi => h1 _ (by omega))
    (by rw [show 0 + 1 + d = d + 1 by omega]; exact h0)).run_eq
  have := run_trans a1 a2
  rw [show 0 + 1 + d = d + 1 by omega] at this
  rw [show 2 * (d + 1) = 1 + (2 * d + 1) by omega, Nat.add_sub_cancel]
  exact this

theorem fin3555 {z : ℕ} {T : ℕ → Bool} (h1 : ∀ i < z, T i = true) (h0 : T z = false) :
    HaltsAfter 3555 ⟨false, 0, T⟩ (2 * z + 1) :=
  (famA3555.dev 0 z T (fun i hi => by simpa using h1 i hi) (by simpa using h0)).halts

theorem blank3555 {z : ℕ} {T : ℕ → Bool} {t : ℕ} (hz : 1 ≤ z) (h1 : ∀ i < z, T i = true)
    (h0 : ∀ i, z ≤ i → T i = false) (h : HaltsAfter 3555 ⟨true, 0, T⟩ t) : t ≤ 6 * z + 7 := by
  obtain ⟨t1, e1, k1⟩ := halts_split (ev3555 hz h1 (h0 z (le_refl z))) h
  have o1 : ∀ i < z + 1, Function.update T z true i = true := by
    intro i hi
    by_cases hiz : i = z
    · subst hiz; simp
    · rw [Function.update_of_ne hiz]; exact h1 i (by omega)
  have z1 : ∀ i, z + 1 ≤ i → Function.update T z true i = false := by
    intro i hi
    rw [Function.update_of_ne (by omega)]; exact h0 i (by omega)
  rcases Nat.mod_two_eq_zero_or_one (z - 1) with hp | hp
  · -- back in state U
    have es : flipn (z - 1) true = true := by simp [flipn, hp]
    rw [es] at k1
    obtain ⟨t2, e2, k2⟩ := halts_split (ev3555 (by omega) o1 (z1 (z + 1) (le_refl _))) k1
    have es2 : flipn (z + 1 - 1) true = false := by
      simp only [flipn]; rw [if_neg (by omega)]; rfl
    rw [es2] at k2
    have o2 : ∀ i < z + 2, Function.update (Function.update T z true) (z + 1) true i = true := by
      intro i hi
      by_cases hiz : i = z + 1
      · subst hiz; simp
      · rw [Function.update_of_ne hiz]; exact o1 i (by omega)
    have z2 : Function.update (Function.update T z true) (z + 1) true (z + 2) = false := by
      rw [Function.update_of_ne (by omega)]; exact z1 _ (by omega)
    have := halts_unique k2 (fin3555 o2 z2)
    omega
  · have es : flipn (z - 1) true = false := by
      simp only [flipn]; rw [if_neg (by omega)]; rfl
    rw [es] at k1
    have := halts_unique k1 (fin3555 o1 (z1 (z + 1) (le_refl _)))
    omega

theorem input3555 (n : ℕ) : ∀ (k z : ℕ) (T : ℕ → Bool) (t : ℕ), z + k = n → 1 ≤ z →
    (∀ i < z, T i = true) → T z = false → (∀ i, n ≤ i → T i = false) →
    HaltsAfter 3555 ⟨true, 0, T⟩ t → t ≤ k * (2 * n) + 6 * n + 7 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro z T t hzk hz h1 h0 hb h
    by_cases hk : k = 0
    · subst hk
      have hzn : z = n := by omega
      subst hzn
      have := blank3555 hz h1 hb h
      omega
    · obtain ⟨t1, e1, k1⟩ := halts_split (ev3555 hz h1 h0) h
      have hTn : Function.update T z true n = false := by
        rw [Function.update_of_ne (by omega)]; exact hb n (le_refl n)
      obtain ⟨z', hz1, hz2, hz3, hz4⟩ := next_zero (Function.update T z true) (a := z) (n := n)
        (by omega) hTn
      have o1 : ∀ i < z', Function.update T z true i = true := by
        intro i hi
        by_cases hiz : i = z
        · subst hiz; simp
        · by_cases hlt : i < z
          · rw [Function.update_of_ne hiz]; exact h1 i hlt
          · exact hz4 i (by omega) hi
      have hb' : ∀ i, n ≤ i → Function.update T z true i = false := by
        intro i hi
        rw [Function.update_of_ne (by omega)]; exact hb i hi
      have hzn : z ≤ n := by omega
      rcases Nat.mod_two_eq_zero_or_one (z - 1) with hp | hp
      · have es : flipn (z - 1) true = true := by simp [flipn, hp]
        rw [es] at k1
        have := ih (n - z') (by omega) z' _ t1 (by omega) (by omega) o1 hz3 hb' k1
        have hmul : (n - z') * (2 * n) + 2 * n ≤ k * (2 * n) := by
          have : n - z' + 1 ≤ k := by omega
          calc (n - z') * (2 * n) + 2 * n = (n - z' + 1) * (2 * n) := by ring
            _ ≤ k * (2 * n) := Nat.mul_le_mul_right _ this
        omega
      · have es : flipn (z - 1) true = false := by
          simp only [flipn]; rw [if_neg (by omega)]; rfl
        rw [es] at k1
        have := halts_unique k1 (fin3555 o1 hz3)
        have hmul : 2 * n ≤ k * (2 * n) := Nat.le_mul_of_pos_left _ (by omega)
        omega

/-- **Machine 3555**: every halting time on an input below `2^n` is at most `2n² + 4n + 7`. -/
theorem m3555 {n x t : ℕ} (hx : x < 2 ^ n) (h : HaltsAfter 3555 (init x) t) :
    t ≤ 2 * n ^ 2 + 4 * n + 7 := by
  have hTn : x.testBit n = false := Nat.testBit_lt_two_pow hx
  by_cases h0 : x.testBit 0 = true
  · have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; rw [h0] at hTn; cases hTn
      · exact h
    obtain ⟨z, hz1, hz2, hz3, hz4⟩ := next_zero (fun i => x.testBit i) (a := 0) (n := n) hn hTn
    have o1 : ∀ i < z, (fun i => x.testBit i) i = true := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact h0
      · exact hz4 i h hi
    have hb : ∀ i, n ≤ i → (fun i => x.testBit i) i = false := fun i hi =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))
    have := input3555 n (n - z) z _ t (by omega) hz1 o1 hz3 hb h
    have hmul : (n - z) * (2 * n) ≤ (n - 1) * (2 * n) := Nat.mul_le_mul_right _ (by omega)
    have e : (n - 1) * (2 * n) + 2 * n = 2 * n ^ 2 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [Nat.add_sub_cancel]; ring
    omega
  · have h0' : x.testBit 0 = false := by simpa using h0
    have hs : step 3555 (init x) = none := by
      have := famA3555.sZ (s := true) (p := 0) (T := fun i => x.testBit i) h0'
      simpa [init] using this
    have := halts_unique h (HaltsAfter.halt hs)
    omega

/-! ## Machine 1507 -/

theorem famA1507 : FamA 1507 := ⟨by decide, by decide, by decide⟩

theorem s1507_U1 {p : ℕ} {T : ℕ → Bool} (h : T p = true) :
    step 1507 ⟨true, p, T⟩ = some ⟨true, p + 1, T⟩ := by
  have := step_left (m := 1507) (x := 2) (s := true) h (by decide) (by decide)
  simpa [update_same_val h] using this

theorem scan1507 : ∀ (a p : ℕ) (T : ℕ → Bool), (∀ i < a, T (p + i) = true) →
    run 1507 a ⟨true, p, T⟩ = some ⟨true, p + a, T⟩
  | 0, p, T, _ => rfl
  | a + 1, p, T, h => by
    have hp : T p = true := by simpa using h 0 (by omega)
    rw [run_step (s1507_U1 hp), scan1507 a (p + 1) T (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this)]
    simp [Nat.add_assoc, Nat.add_comm 1 a]

/-- **A `U`-event**: state `U` on cell `r`, ones on `r, …, r+a`, a zero on `r+a+1`: the head
walks to the zero, turns it into a one and comes back one cell in state `D`. -/
theorem uev1507 {r a : ℕ} {T : ℕ → Bool} (h1 : ∀ i < a + 1, T (r + i) = true)
    (h0 : T (r + (a + 1)) = false) :
    run 1507 (a + 2) ⟨true, r, T⟩ =
      some ⟨false, r + a, Function.update T (r + (a + 1)) true⟩ := by
  have a1 := scan1507 (a + 1) r T h1
  have a2 : run 1507 1 ⟨true, r + (a + 1), T⟩ =
      some ⟨false, r + a, Function.update T (r + (a + 1)) true⟩ := by
    apply run_one
    rw [famA1507.sZ h0, show r + (a + 1) = (r + a) + 1 by omega, exitR_succ]; rfl
  have := run_trans a1 a2
  exact this

/-- In the blank region a `U`-event never leads to halting. -/
theorem nh1507 : ∀ (t r top : ℕ) (T : ℕ → Bool), 2 ≤ top → r < top → (∀ i < top, T i = true) →
    (∀ i, top ≤ i → T i = false) → ¬ HaltsAfter 1507 ⟨true, r, T⟩ t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro r top T htop hr h1 h0 h
    obtain ⟨a, rfl⟩ : ∃ a, top = r + (a + 1) := ⟨top - r - 1, by omega⟩
    obtain ⟨t1, e1, k1⟩ := halts_split (uev1507 (fun i hi => h1 _ (by omega)) (h0 _ (le_refl _))) h
    set T1 := Function.update T (r + (a + 1)) true with hT1
    have o1 : ∀ i < r + (a + 1) + 1, T1 i = true := by
      intro i hi
      by_cases hiz : i = r + (a + 1)
      · subst hiz; simp [hT1]
      · rw [hT1, Function.update_of_ne hiz]; exact h1 i (by omega)
    have z1 : ∀ i, r + (a + 1) + 1 ≤ i → T1 i = false := by
      intro i hi
      rw [hT1, Function.update_of_ne (by omega)]; exact h0 i (by omega)
    have dv := famA1507.dev (r + a) 2 T1 (fun i hi => o1 _ (by omega)) (z1 _ (by omega))
    have hra : r + a = (r + a - 1) + 1 := by omega
    rw [hra] at dv
    obtain ⟨t2, e2, k2⟩ := dv.split (by rw [← hra]; exact k1)
    have es : flipn 2 true = true := by simp [flipn]
    rw [es] at k2
    refine ih t2 (by omega) (r + a - 1) (r + (a + 1) + 2) _ (by omega) (by omega) ?_ ?_ k2
    · intro i hi
      by_cases hiz : i = r + a - 1 + 1 + 2
      · rw [hiz]; simp
      · rw [Function.update_of_ne hiz]; exact o1 i (by omega)
    · intro i hi
      rw [Function.update_of_ne (by omega)]; exact z1 i (by omega)

/-- In the blank region a chain of `D`-events takes at most `(r+1)(2·top+1)` steps. -/
theorem chain1507 : ∀ (r top : ℕ) (T : ℕ → Bool) (t : ℕ), r < top → (∀ i < top, T i = true) →
    (∀ i, top ≤ i → T i = false) → HaltsAfter 1507 ⟨false, r, T⟩ t →
    t ≤ (r + 1) * (2 * top + 1) := by
  intro r
  induction r with
  | zero =>
    intro top T t _ h1 h0 h
    have dv := famA1507.dev 0 top T (fun i hi => by simpa using h1 i hi)
      (by simpa using h0 top (le_refl _))
    have := dv.time h
    omega
  | succ r' ih =>
    intro top T t hr h1 h0 h
    obtain ⟨d, rfl⟩ : ∃ d, top = r' + 1 + d := ⟨top - (r' + 1), by omega⟩
    have dv := famA1507.dev (r' + 1) d T (fun i hi => h1 _ (by omega)) (h0 _ (le_refl _))
    obtain ⟨t1, e1, k1⟩ := dv.split h
    set T1 := Function.update T (r' + 1 + d) true with hT1
    have o1 : ∀ i < r' + 1 + d + 1, T1 i = true := by
      intro i hi
      by_cases hiz : i = r' + 1 + d
      · subst hiz; simp [hT1]
      · rw [hT1, Function.update_of_ne hiz]; exact h1 i (by omega)
    have z1 : ∀ i, r' + 1 + d + 1 ≤ i → T1 i = false := by
      intro i hi
      rw [hT1, Function.update_of_ne (by omega)]; exact h0 i (by omega)
    cases hs : flipn d true with
    | true =>
      rw [hs] at k1
      exact (nh1507 t1 r' (r' + 1 + d + 1) T1 (by omega) (by omega) o1 z1 k1).elim
    | false =>
      rw [hs] at k1
      have := ih (r' + 1 + d + 1) T1 t1 (by omega) o1 z1 k1
      have e : (r' + 1 + 1) * (2 * (r' + 1 + d) + 1) + 2 * (r' + 1) =
          (r' + 1) * (2 * (r' + 1 + d + 1) + 1) + (2 * (r' + 1 + d) + 1) := by ring
      generalize (r' + 1 + 1) * (2 * (r' + 1 + d) + 1) = Q at e ⊢
      generalize (r' + 1) * (2 * (r' + 1 + d + 1) + 1) = P at e this
      omega

theorem main1507 (n : ℕ) (hn : 2 ≤ n) : ∀ (t : ℕ) (s : Bool) (r top : ℕ) (T : ℕ → Bool),
    r < top → top ≤ n → (∀ i < top, T i = true) → T top = false → (∀ i, n ≤ i → T i = false) →
    HaltsAfter 1507 ⟨s, r, T⟩ t → t ≤ (2 * n - top) * (2 * n + 1) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro s r top T hr htop h1 h0 hb h
    by_cases hn' : top = n
    · subst hn'
      cases s with
      | true => exact (nh1507 t r top T hn hr h1 hb h).elim
      | false =>
        have := chain1507 r top T t hr h1 hb h
        have h2 : (r + 1) * (2 * top + 1) ≤ top * (2 * top + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [show 2 * top - top = top by omega]
        omega
    · have hlt : top < n := by omega
      set T1 := Function.update T top true with hT1
      have hT1n : T1 n = false := by
        rw [hT1, Function.update_of_ne (by omega)]; exact hb n (le_refl n)
      obtain ⟨top', hz1, hz2, hz3, hz4⟩ := next_zero T1 (a := top) (n := n) hlt hT1n
      have o1 : ∀ i < top', T1 i = true := by
        intro i hi
        by_cases hiz : i = top
        · subst hiz; simp [hT1]
        · by_cases hl : i < top
          · rw [hT1, Function.update_of_ne hiz]; exact h1 i hl
          · exact hz4 i (by omega) hi
      have hb' : ∀ i, n ≤ i → T1 i = false := by
        intro i hi
        rw [hT1, Function.update_of_ne (by omega)]; exact hb i hi
      -- arithmetic: one more event costs at most `2n+1`
      have harith : ∀ cost t1 : ℕ, cost ≤ 2 * n + 1 → t1 ≤ (2 * n - top') * (2 * n + 1) →
          cost + t1 ≤ (2 * n - top) * (2 * n + 1) := by
        intro cost t1 hc ht1
        have h2 : (2 * n - top') * (2 * n + 1) ≤ (2 * n - top - 1) * (2 * n + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h3 : (2 * n - top - 1) * (2 * n + 1) + (2 * n + 1) = (2 * n - top) * (2 * n + 1) := by
          obtain ⟨k, hk⟩ : ∃ k, 2 * n - top = k + 1 := ⟨2 * n - top - 1, by omega⟩
          rw [hk, Nat.add_sub_cancel]; ring
        omega
      cases s with
      | true =>
        obtain ⟨a, rfl⟩ : ∃ a, top = r + (a + 1) := ⟨top - r - 1, by omega⟩
        obtain ⟨t1, e1, k1⟩ := halts_split
          (uev1507 (fun i hi => h1 _ (by omega)) h0) h
        have := ih t1 (by omega) false (r + a) top' T1 (by omega) hz2 o1 hz3 hb' k1
        rw [e1]
        exact harith _ _ (by omega) this
      | false =>
        obtain ⟨d, rfl⟩ : ∃ d, top = r + d := ⟨top - r, by omega⟩
        have dv := famA1507.dev r d T (fun i hi => h1 _ (by omega)) h0
        cases r with
        | zero =>
          have := dv.time h
          have h2 : 1 * (2 * n + 1) ≤ (2 * n - (0 + d)) * (2 * n + 1) :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        | succ r' =>
          obtain ⟨t1, e1, k1⟩ := dv.split h
          have := ih t1 (by omega) _ r' top' T1 (by omega) hz2 o1 hz3 hb' k1
          rw [e1]
          exact harith _ _ (by omega) this

/-- **Machine 1507**, inputs with at least two bits allowed. -/
theorem m1507 {n x t : ℕ} (hn : 2 ≤ n) (hx : x < 2 ^ n) (h : HaltsAfter 1507 (init x) t) :
    t ≤ 4 * n ^ 2 := by
  have hTn : x.testBit n = false := Nat.testBit_lt_two_pow hx
  by_cases h0 : x.testBit 0 = true
  · obtain ⟨z, hz1, hz2, hz3, hz4⟩ := next_zero (fun i => x.testBit i) (a := 0) (n := n)
      (by omega) hTn
    have o1 : ∀ i < z, (fun i => x.testBit i) i = true := by
      intro i hi
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; exact h0
      · exact hz4 i h hi
    have hb : ∀ i, n ≤ i → (fun i => x.testBit i) i = false := fun i hi =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))
    have := main1507 n hn t true 0 z _ hz1 hz2 o1 hz3 hb h
    have h2 : (2 * n - z) * (2 * n + 1) ≤ (2 * n - 1) * (2 * n + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h3 : (2 * n - 1) * (2 * n + 1) + 1 = 4 * n ^ 2 := by
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]; ring
    omega
  · have h0' : x.testBit 0 = false := by simpa using h0
    have hs : step 1507 (init x) = none := by
      have := famA1507.sZ (s := true) (p := 0) (T := fun i => x.testBit i) h0'
      simpa [init] using this
    have := halts_unique h (HaltsAfter.halt hs)
    have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega

/-- **Machine 1507** on the inputs `0` and `1`. -/
theorem m1507_one {x t : ℕ} (hx : x < 2) (h : HaltsAfter 1507 (init x) t) : t ≤ 7 := by
  interval_cases x
  · have hs : step 1507 (init 0) = none := by
      have := famA1507.sZ (s := true) (p := 0) (T := fun i => (0 : ℕ).testBit i) (by simp)
      simpa [init] using this
    have := halts_unique h (HaltsAfter.halt hs)
    omega
  · set T : ℕ → Bool := fun i => (1 : ℕ).testBit i with hT
    have t0 : T 0 = true := by simp [hT]
    have tz : ∀ i, 1 ≤ i → T i = false := by
      intro i hi
      exact Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num : 1 < 2 ^ 1)
        (Nat.pow_le_pow_right (by norm_num) hi))
    have a1 := uev1507 (r := 0) (a := 0) (T := T) (fun i hi => by
      have : i = 0 := by omega
      subst this; simpa using t0) (by simpa using tz 1 (le_refl 1))
    obtain ⟨t1, e1, k1⟩ := halts_split a1 (by simpa [init] using h)
    have dv := famA1507.dev 0 2 (Function.update T (0 + (0 + 1)) true) (fun i hi => by
      rcases Nat.eq_zero_or_pos i with h | h
      · subst h; simp [t0]
      · have : i = 1 := by omega
        subst this; simp) (by
      rw [Function.update_of_ne (by omega)]; exact tz _ (by omega))
    have := dv.time (by simpa using k1)
    omega

/-! ## Family B: `U1 → D0R`, `D1 → U0R`, `D0 → D1L` (machines 2830 and 2574) -/

structure FamB (m : ℕ) : Prop where
  u1 : digit m true true = 5
  d1 : digit m false true = 1
  d0 : digit m false false = 6

namespace FamB

variable {m : ℕ}

theorem sD0 (f : FamB m) {p : ℕ} {T : ℕ → Bool} (h : T p = false) :
    step m ⟨false, p, T⟩ = some ⟨false, p + 1, Function.update T p true⟩ := by
  have := step_left (m := m) (x := 6) (s := false) h f.d0 (by decide)
  simpa using this

/-- On a one both states write a zero, move right and change the state. -/
theorem sO (f : FamB m) {s : Bool} {p : ℕ} {T : ℕ → Bool} (h : T p = true) :
    step m ⟨s, p, T⟩ = exitR (!s) p (Function.update T p false) := by
  cases s with
  | true =>
    have := step_right (m := m) (x := 5) (s := true) h f.u1 (by decide)
    simpa using this
  | false =>
    have := step_right (m := m) (x := 1) (s := false) h f.d1 (by decide)
    simpa using this

theorem sweep (f : FamB m) : ∀ (j q : ℕ) (T : ℕ → Bool), (∀ i < j, T (q + i) = false) →
    run m j ⟨false, q, T⟩ = some ⟨false, q + j, fill T q j true⟩
  | 0, q, T, _ => by
    simp only [run, Nat.add_zero, Option.some.injEq, Config.mk.injEq, true_and]
    funext i; rw [fill_out (by omega)]
  | j + 1, q, T, h => by
    have hq : T q = false := by simpa using h 0 (by omega)
    rw [run_step (f.sD0 hq), sweep f j (q + 1) _ (fun i hi => by
      rw [Function.update_of_ne (by omega)]
      have := h (i + 1) (by omega)
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this)]
    simp only [Option.some.injEq, Config.mk.injEq, true_and]
    refine ⟨by omega, ?_⟩
    funext i
    by_cases hi : i = q
    · subst hi; rw [fill_out (by omega), fill_in (by omega) (by omega)]; simp
    · by_cases h1 : q + 1 ≤ i ∧ i < q + 1 + j
      · rw [fill_in h1.1 h1.2, fill_in (by omega) (by omega)]
      · rw [fill_out h1, fill_out (by omega), Function.update_of_ne hi]

theorem zip (f : FamB m) : ∀ (j q : ℕ) (s : Bool) (T : ℕ → Bool),
    (∀ i < j + 1, T (q + i) = true) →
    Exits m ⟨s, q + j, T⟩ j (flipn (j + 1) s) q (fill T q (j + 1) false)
  | 0, q, s, T, h => by
    have hq : T q = true := by simpa using h 0 (by omega)
    apply Exits.of_step
    rw [Nat.add_zero, f.sO hq]
    have e1 : flipn (0 + 1) s = !s := by simp [flipn]
    rw [e1]
    congr 1
    funext i
    by_cases hi : i = q
    · subst hi; rw [fill_in (by omega) (by omega)]; simp
    · rw [Function.update_of_ne hi, fill_out (by omega)]
  | j + 1, q, s, T, h => by
    have hq : T (q + (j + 1)) = true := h (j + 1) (by omega)
    have a1 : run m 1 ⟨s, q + (j + 1), T⟩ =
        some ⟨!s, q + j, Function.update T (q + (j + 1)) false⟩ := by
      apply run_one
      rw [f.sO hq, show q + (j + 1) = (q + j) + 1 by omega, exitR_succ]
    have ih := zip f j q (!s) (Function.update T (q + (j + 1)) false) (fun i hi => by
      rw [Function.update_of_ne (by omega)]; exact h i (by omega))
    have e : fill (Function.update T (q + (j + 1)) false) q (j + 1) false =
        fill T q (j + 1 + 1) false := by
      funext i
      by_cases hi : i = q + (j + 1)
      · subst hi; rw [fill_out (by omega), fill_in (by omega) (by omega)]; simp
      · by_cases h1 : q ≤ i ∧ i < q + (j + 1)
        · rw [fill_in h1.1 h1.2, fill_in (by omega) (by omega)]
        · rw [fill_out h1, fill_out (by omega), Function.update_of_ne hi]
    rw [e, flipn_succ_not] at ih
    have := Exits.of_run a1 ih
    rwa [Nat.add_comm 1 j] at this

/-- **A `D`-event** (family B): zeros on `r, …, r+d-1`, a one on `r+d`. -/
theorem dev (f : FamB m) (r d : ℕ) (T : ℕ → Bool) (h0 : ∀ i < d, T (r + i) = false)
    (h1 : T (r + d) = true) :
    Exits m ⟨false, r, T⟩ (2 * d) (flipn d true) r (Function.update T (r + d) false) := by
  have a1 := f.sweep d r T h0
  have a2 := f.zip d r false (fill T r d true) (fun i hi => by
    by_cases hid : i < d
    · rw [fill_in (by omega) (by omega)]
    · have : i = d := by omega
      subst this
      rw [fill_out (by omega)]; exact h1)
  have e : fill (fill T r d true) r (d + 1) false = Function.update T (r + d) false := by
    funext i
    by_cases hi : i = r + d
    · subst hi; rw [fill_in (by omega) (by omega)]; simp
    · rw [Function.update_of_ne hi]
      by_cases h2 : r ≤ i ∧ i < r + d
      · rw [fill_in h2.1 (by omega)]
        obtain ⟨k, rfl⟩ : ∃ k, i = r + k := ⟨i - r, by omega⟩
        exact (h0 k (by omega)).symm
      · rw [fill_out (by omega), fill_out h2]
  rw [e, flipn_succ_false] at a2
  have := Exits.of_run a1 a2
  rwa [show d + d = 2 * d by omega] at this

/-- State `D` on a part of the tape without ones never comes back. -/
theorem nhD (f : FamB m) : ∀ (t p : ℕ) (T : ℕ → Bool), (∀ i, p ≤ i → T i = false) →
    ¬ HaltsAfter m ⟨false, p, T⟩ t := by
  intro t
  induction t with
  | zero => intro p T _ h; cases h
  | succ t ih =>
    intro p T hz h
    have hs := f.sD0 (hz p (le_refl p))
    cases h with
    | halt hs' => rw [hs] at hs'; cases hs'
    | next hs' h' =>
      rw [hs] at hs'
      cases hs'
      exact ih (p + 1) _ (fun i hi => by
        rw [Function.update_of_ne (by omega)]; exact hz i (by omega)) h'

end FamB

/-! ## Machine 2830 -/

theorem famB2830 : FamB 2830 := ⟨by decide, by decide, by decide⟩

theorem s2830_U0 {p : ℕ} {T : ℕ → Bool} (h : T p = false) :
    step 2830 ⟨true, p, T⟩ = some ⟨false, p + 1, T⟩ := by
  have := step_left (m := 2830) (x := 4) (s := true) h (by decide) (by decide)
  simpa [update_same_val h] using this

theorem ev2830 {y : ℕ} {T : ℕ → Bool} (hy : 1 ≤ y) (h0 : ∀ i < y, T i = false)
    (h1 : T y = true) :
    run 2830 (2 * y) ⟨true, 0, T⟩ = some ⟨flipn (y - 1) true, 0, Function.update T y false⟩ := by
  obtain ⟨d, rfl⟩ : ∃ d, y = d + 1 := ⟨y - 1, by omega⟩
  have a1 : run 2830 1 ⟨true, 0, T⟩ = some ⟨false, 0 + 1, T⟩ := run_one (s2830_U0 (h0 0 (by omega)))
  have a2 := (famB2830.dev (0 + 1) d T (fun i hi => h0 _ (by omega))
    (by rw [show 0 + 1 + d = d + 1 by omega]; exact h1)).run_eq
  have := run_trans a1 a2
  rw [show 0 + 1 + d = d + 1 by omega] at this
  rw [show 2 * (d + 1) = 1 + (2 * d + 1) by omega, Nat.add_sub_cancel]
  exact this

theorem fin2830 {y : ℕ} {T : ℕ → Bool} (h0 : ∀ i < y, T i = false) (h1 : T y = true) :
    HaltsAfter 2830 ⟨false, 0, T⟩ (2 * y + 1) :=
  (famB2830.dev 0 y T (fun i hi => by simpa using h0 i hi) (by simpa using h1)).halts

theorem nhU2830 {T : ℕ → Bool} {t : ℕ} (hz : ∀ i, T i = false) :
    ¬ HaltsAfter 2830 ⟨true, 0, T⟩ t := by
  intro h
  have hs := s2830_U0 (p := 0) (hz 0)
  cases h with
  | halt hs' => rw [hs] at hs'; cases hs'
  | next hs' h' =>
    rw [hs] at hs'
    cases hs'
    exact famB2830.nhD _ _ _ (fun i _ => hz i) h'

theorem input2830 (n : ℕ) : ∀ (k y : ℕ) (T : ℕ → Bool) (t : ℕ), y + k = n → 1 ≤ y →
    (∀ i < y, T i = false) → T y = true → (∀ i, n ≤ i → T i = false) →
    HaltsAfter 2830 ⟨true, 0, T⟩ t → t ≤ k * (4 * n) + 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro y T t hyk hy h0 h1 hb h
    have hyn : y < n := by
      by_contra hc
      rw [hb y (by omega)] at h1; cases h1
    obtain ⟨t1, e1, k1⟩ := halts_split (ev2830 hy h0 h1) h
    set T1 := Function.update T y false with hT1
    have z1 : ∀ i < y + 1, T1 i = false := by
      intro i hi
      by_cases hiy : i = y
      · subst hiy; simp [hT1]
      · rw [hT1, Function.update_of_ne hiy]; exact h0 i (by omega)
    have hb' : ∀ i, n ≤ i → T1 i = false := by
      intro i hi
      rw [hT1, Function.update_of_ne (by omega)]; exact hb i hi
    by_cases hex : ∃ i, y < i ∧ T1 i = true
    · obtain ⟨y', hy1, hy2, hy3⟩ := next_one T1 hex
      have hy'n : y' < n := by
        by_contra hc
        rw [hb' y' (by omega)] at hy2; cases hy2
      have z1' : ∀ i < y', T1 i = false := by
        intro i hi
        by_cases hl : i < y + 1
        · exact z1 i hl
        · exact hy3 i (by omega) hi
      rcases Nat.mod_two_eq_zero_or_one (y - 1) with hp | hp
      · have es : flipn (y - 1) true = true := by simp [flipn, hp]
        rw [es] at k1
        have := ih (n - y') (by omega) y' T1 t1 (by omega) (by omega) z1' hy2 hb' k1
        have hmul : (n - y') * (4 * n) + 4 * n ≤ k * (4 * n) := by
          have : n - y' + 1 ≤ k := by omega
          calc (n - y') * (4 * n) + 4 * n = (n - y' + 1) * (4 * n) := by ring
            _ ≤ k * (4 * n) := Nat.mul_le_mul_right _ this
        omega
      · have es : flipn (y - 1) true = false := by
          simp only [flipn]; rw [if_neg (by omega)]; rfl
        rw [es] at k1
        have := halts_unique k1 (fin2830 z1' hy2)
        have hmul : 4 * n ≤ k * (4 * n) := Nat.le_mul_of_pos_left _ (by omega)
        omega
    · have hz : ∀ i, T1 i = false := by
        intro i
        by_cases hl : i < y + 1
        · exact z1 i hl
        · by_contra hc
          exact hex ⟨i, by omega, by simpa using hc⟩
      cases hs : flipn (y - 1) true with
      | true => rw [hs] at k1; exact (nhU2830 hz k1).elim
      | false => rw [hs] at k1; exact (famB2830.nhD _ _ _ (fun i _ => hz i) k1).elim

/-- **Machine 2830**. -/
theorem m2830 {n x t : ℕ} (hn : 1 ≤ n) (hx : x < 2 ^ n) (h : HaltsAfter 2830 (init x) t) :
    t ≤ 4 * n ^ 2 := by
  have hpos : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hb : ∀ i, n ≤ i → x.testBit i = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))
  by_cases h0 : x.testBit 0 = true
  · have hs : step 2830 (init x) = none := by
      have := famB2830.sO (s := true) (p := 0) (T := fun i => x.testBit i) h0
      simpa [init] using this
    have := halts_unique h (HaltsAfter.halt hs)
    omega
  · have h0' : x.testBit 0 = false := by simpa using h0
    by_cases hex : ∃ i, 0 < i ∧ (fun i => x.testBit i) i = true
    · obtain ⟨y, hy1, hy2, hy3⟩ := next_one _ hex
      have hyn : y < n := by
        by_contra hc
        rw [hb y (by omega)] at hy2; cases hy2
      have z0 : ∀ i < y, (fun i => x.testBit i) i = false := by
        intro i hi
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; exact h0'
        · exact hy3 i h hi
      have := input2830 n (n - y) y _ t (by omega) hy1 z0 hy2 hb h
      have hmul : (n - y) * (4 * n) ≤ (n - 1) * (4 * n) := Nat.mul_le_mul_right _ (by omega)
      have e : (n - 1) * (4 * n) + 4 * n = 4 * n ^ 2 := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [Nat.add_sub_cancel]; ring
      omega
    · have hz : ∀ i, (fun i => x.testBit i) i = false := by
        intro i
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; exact h0'
        · by_contra hc
          exact hex ⟨i, h, by simpa using hc⟩
      exact (nhU2830 hz h).elim

/-! ## Machine 2574 -/

theorem famB2574 : FamB 2574 := ⟨by decide, by decide, by decide⟩

theorem s2574_U0 {p : ℕ} {T : ℕ → Bool} (h : T p = false) :
    step 2574 ⟨true, p, T⟩ = some ⟨true, p + 1, T⟩ := by
  have := step_left (m := 2574) (x := 0) (s := true) h (by decide) (by decide)
  simpa [update_same_val h] using this

theorem scan2574 : ∀ (a p : ℕ) (T : ℕ → Bool), (∀ i < a, T (p + i) = false) →
    run 2574 a ⟨true, p, T⟩ = some ⟨true, p + a, T⟩
  | 0, p, T, _ => rfl
  | a + 1, p, T, h => by
    have hp : T p = false := by simpa using h 0 (by omega)
    rw [run_step (s2574_U0 hp), scan2574 a (p + 1) T (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [← Nat.add_assoc, Nat.add_right_comm] at this)]
    simp [Nat.add_assoc, Nat.add_comm 1 a]

theorem uev2574 {r a : ℕ} {T : ℕ → Bool} (h0 : ∀ i < a + 1, T (r + i) = false)
    (h1 : T (r + (a + 1)) = true) :
    run 2574 (a + 2) ⟨true, r, T⟩ =
      some ⟨false, r + a, Function.update T (r + (a + 1)) false⟩ := by
  have a1 := scan2574 (a + 1) r T h0
  have a2 : run 2574 1 ⟨true, r + (a + 1), T⟩ =
      some ⟨false, r + a, Function.update T (r + (a + 1)) false⟩ := by
    apply run_one
    rw [famB2574.sO h1, show r + (a + 1) = (r + a) + 1 by omega, exitR_succ]; rfl
  have := run_trans a1 a2
  exact this

theorem nhU2574 : ∀ (t p : ℕ) (T : ℕ → Bool), (∀ i, p ≤ i → T i = false) →
    ¬ HaltsAfter 2574 ⟨true, p, T⟩ t := by
  intro t
  induction t with
  | zero => intro p T _ h; cases h
  | succ t ih =>
    intro p T hz h
    have hs := s2574_U0 (hz p (le_refl p))
    cases h with
    | halt hs' => rw [hs] at hs'; cases hs'
    | next hs' h' =>
      rw [hs] at hs'
      cases hs'
      exact ih (p + 1) _ (fun i hi => hz i (by omega)) h'

theorem main2574 (n : ℕ) : ∀ (t : ℕ) (s : Bool) (r y : ℕ) (T : ℕ → Bool), r < y →
    (∀ i < y, T i = false) → T y = true → (∀ i, n ≤ i → T i = false) →
    HaltsAfter 2574 ⟨s, r, T⟩ t → t ≤ (n - y) * (2 * n + 1) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro s r y T hr h0 h1 hb h
    have hyn : y < n := by
      by_contra hc
      rw [hb y (by omega)] at h1; cases h1
    set T1 := Function.update T y false with hT1
    have z1 : ∀ i < y + 1, T1 i = false := by
      intro i hi
      by_cases hiy : i = y
      · subst hiy; simp [hT1]
      · rw [hT1, Function.update_of_ne hiy]; exact h0 i (by omega)
    have hb' : ∀ i, n ≤ i → T1 i = false := by
      intro i hi
      rw [hT1, Function.update_of_ne (by omega)]; exact hb i hi
    -- what happens in the configuration after the event
    have after : ∀ (s' : Bool) (r' t1 : ℕ), r' < y → t1 < t → HaltsAfter 2574 ⟨s', r', T1⟩ t1 →
        ∀ cost : ℕ, cost ≤ 2 * n + 1 → cost + t1 ≤ (n - y) * (2 * n + 1) := by
      intro s' r' t1 hr' ht1 k1 cost hc
      by_cases hex : ∃ i, y < i ∧ T1 i = true
      · obtain ⟨y', hy1, hy2, hy3⟩ := next_one T1 hex
        have hy'n : y' < n := by
          by_contra hc'
          rw [hb' y' (by omega)] at hy2; cases hy2
        have z1' : ∀ i < y', T1 i = false := by
          intro i hi
          by_cases hl : i < y + 1
          · exact z1 i hl
          · exact hy3 i (by omega) hi
        have := ih t1 ht1 s' r' y' T1 (by omega) z1' hy2 hb' k1
        have h2 : (n - y') * (2 * n + 1) ≤ (n - y - 1) * (2 * n + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h3 : (n - y - 1) * (2 * n + 1) + (2 * n + 1) = (n - y) * (2 * n + 1) := by
          obtain ⟨k, hk⟩ : ∃ k, n - y = k + 1 := ⟨n - y - 1, by omega⟩
          rw [hk, Nat.add_sub_cancel]; ring
        omega
      · have hz : ∀ i, T1 i = false := by
          intro i
          by_cases hl : i < y + 1
          · exact z1 i hl
          · by_contra hc'
            exact hex ⟨i, by omega, by simpa using hc'⟩
        cases s' with
        | true => exact (nhU2574 _ _ _ (fun i _ => hz i) k1).elim
        | false => exact (famB2574.nhD _ _ _ (fun i _ => hz i) k1).elim
    cases s with
    | true =>
      obtain ⟨a, rfl⟩ : ∃ a, y = r + (a + 1) := ⟨y - r - 1, by omega⟩
      obtain ⟨t1, e1, k1⟩ := halts_split (uev2574 (fun i hi => h0 _ (by omega)) h1) h
      rw [e1]
      exact after false (r + a) t1 (by omega) (by omega) k1 _ (by omega)
    | false =>
      obtain ⟨d, rfl⟩ : ∃ d, y = r + d := ⟨y - r, by omega⟩
      have dv := famB2574.dev r d T (fun i hi => h0 _ (by omega)) h1
      cases r with
      | zero =>
        have := dv.time h
        have h2 : 1 * (2 * n + 1) ≤ (n - (0 + d)) * (2 * n + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
      | succ r' =>
        obtain ⟨t1, e1, k1⟩ := dv.split h
        rw [e1]
        exact after _ r' t1 (by omega) (by omega) k1 _ (by omega)

/-- **Machine 2574**. -/
theorem m2574 {n x t : ℕ} (hn : 1 ≤ n) (hx : x < 2 ^ n) (h : HaltsAfter 2574 (init x) t) :
    t ≤ 4 * n ^ 2 := by
  have hpos : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hb : ∀ i, n ≤ i → (fun i => x.testBit i) i = false := fun i hi =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))
  by_cases h0 : x.testBit 0 = true
  · have hs : step 2574 (init x) = none := by
      have := famB2574.sO (s := true) (p := 0) (T := fun i => x.testBit i) h0
      simpa [init] using this
    have := halts_unique h (HaltsAfter.halt hs)
    omega
  · have h0' : x.testBit 0 = false := by simpa using h0
    by_cases hex : ∃ i, 0 < i ∧ (fun i => x.testBit i) i = true
    · obtain ⟨y, hy1, hy2, hy3⟩ := next_one _ hex
      have z0 : ∀ i < y, (fun i => x.testBit i) i = false := by
        intro i hi
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; exact h0'
        · exact hy3 i h hi
      have := main2574 n t true 0 y _ hy1 z0 hy2 hb h
      have hmul : (n - y) * (2 * n + 1) ≤ n * (2 * n + 1) := Nat.mul_le_mul_right _ (by omega)
      have e : n * (2 * n + 1) = 2 * n ^ 2 + n := by ring
      have : n ≤ n ^ 2 := by nlinarith
      omega
    · have hz : ∀ i, 0 ≤ i → (fun i => x.testBit i) i = false := by
        intro i _
        rcases Nat.eq_zero_or_pos i with h | h
        · subst h; exact h0'
        · by_contra hc
          exact hex ⟨i, h, by simpa using hc⟩
      exact (nhU2574 _ _ _ hz h).elim

end A393317
