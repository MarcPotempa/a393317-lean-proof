import A393317.All

/-!
# OEIS A393317: proof of M. F. Hasler's conjecture

`A393317(n)` is the largest halting time of any of the 4096 Wolfram 2-state 2-symbol Turing
machines over all `n`-bit inputs.  Hasler conjectured (OEIS, Feb 12 2026)

* `A393317(n) = 2(n+2)² − 1` for `n < 5` and `A393317(n) = 2^(n+2) − 3` for `n > 4`;
* machines 378 and 1351 have maximal runtime `2^(n+2) − 3`, machine 1447 has maximal runtime
  `2(n+2)² − 1` over the `n`-bit inputs, in each case attained for the input `2^n − 1`.
-/

namespace A393317

/-- **Hasler's conjecture for A393317.**  For every `n ≥ 1` the set of halting times of all 4096
machines over all `n`-bit inputs has the greatest element `2(n+2)² − 1` if `n < 5` and
`2^(n+2) − 3` if `n ≥ 5`. -/
theorem hasler_conjecture (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest (haltingTimes n) (if n < 5 then 2 * (n + 2) ^ 2 - 1 else 2 ^ (n + 2) - 3) := by
  constructor
  · obtain ⟨h1, h2⟩ := lower_bound n hn
    split
    · exact h2
    · exact h1
  · rintro t ⟨m, hm, x, _, hx, ht⟩
    exact ub_all m hm n x t hn hx ht

/-- **Hasler's conjecture, inputs with at most `n` binary digits.**  The maximum does not change
if all inputs `x < 2^n` (including `0`) are admitted. -/
theorem hasler_conjecture_upto (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest (haltingTimesUpTo n) (if n < 5 then 2 * (n + 2) ^ 2 - 1 else 2 ^ (n + 2) - 3) := by
  obtain ⟨⟨m, hm, x, _, hx, ht⟩, _⟩ := hasler_conjecture n hn
  refine ⟨⟨m, hm, x, hx, ht⟩, ?_⟩
  rintro t ⟨m, hm, x, hx, ht⟩
  exact ub_all m hm n x t hn hx ht

/-- The halting times of machine `m` over the `n`-bit inputs. -/
def haltingTimesOf (m n : ℕ) : Set ℕ :=
  {t | ∃ x, 2 ^ (n - 1) ≤ x ∧ x < 2 ^ n ∧ HaltsAfter m (init x) t}

/-- The number of trailing ones of `x` exists and is at most `n` if `x < 2^n`. -/
theorem trailing_ones {n x : ℕ} (hx : x < 2 ^ n) :
    ∃ k, k ≤ n ∧ (∀ i < k, x.testBit i = true) ∧ x.testBit k = false := by
  classical
  have hex : ∃ k, x.testBit k = false := ⟨n, Nat.testBit_lt_two_pow hx⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (Nat.testBit_lt_two_pow hx), fun i hi => ?_,
    Nat.find_spec hex⟩
  simpa using Nat.find_min hex hi

theorem pow_le_pow_exp {k n : ℕ} (h : k ≤ n) : 2 ^ (k + 2) - 3 ≤ 2 ^ (n + 2) - 3 :=
  Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 3

/-- **Machine 378**: the maximal halting time over the `n`-bit inputs is `2^(n+2) − 3`. -/
theorem max378 (n : ℕ) (hn : 1 ≤ n) : IsGreatest (haltingTimesOf 378 n) (2 ^ (n + 2) - 3) := by
  obtain ⟨h1, h2⟩ := ones_mem_range n hn
  refine ⟨⟨2 ^ n - 1, h1, h2, machine378_ones n⟩, ?_⟩
  rintro t ⟨x, _, hx, ht⟩
  obtain ⟨k, hk, o, z⟩ := trailing_ones hx
  rw [halts_unique ht (machine378 x k o z)]
  exact pow_le_pow_exp hk

/-- **Machine 1351**: the maximal halting time over the `n`-bit inputs is `2^(n+2) − 3`. -/
theorem max1351 (n : ℕ) (hn : 1 ≤ n) : IsGreatest (haltingTimesOf 1351 n) (2 ^ (n + 2) - 3) := by
  obtain ⟨h1, h2⟩ := ones_mem_range n hn
  refine ⟨⟨2 ^ n - 1, h1, h2, machine1351_ones n⟩, ?_⟩
  rintro t ⟨x, _, hx, ht⟩
  obtain ⟨k, hk, o, z⟩ := trailing_ones hx
  rw [halts_unique ht (machine1351 x k o z)]
  exact pow_le_pow_exp hk

/-- **Machine 1447**: the maximal halting time over the `n`-bit inputs is `2(n+2)² − 1`. -/
theorem max1447 (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest (haltingTimesOf 1447 n) (2 * (n + 2) ^ 2 - 1) := by
  obtain ⟨h1, h2⟩ := ones_mem_range n hn
  refine ⟨⟨2 ^ n - 1, h1, h2, machine1447 n⟩, ?_⟩
  rintro t ⟨x, _, hx, ht⟩
  have := Cert.sound Certs.ok1447 hn hx ht
  omega

end A393317
