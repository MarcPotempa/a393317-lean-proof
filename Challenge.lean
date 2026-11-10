import Mathlib

/-!
# OEIS A393317 – Wolfram's 2-state 2-symbol Turing machines, halting times

Model (as in OEIS A392245 / A393317, Wolfram's `TuringMachine[m]`, `m = 0..4095`):

* The tape holds the binary digits of the input; cell `i` holds the digit of weight `2^i`,
  all other cells are `0`. "Right" means towards cell `0`, "left" towards higher cells.
* The head starts on cell `0` in state `U`. The machine halts as soon as the head moves
  right from cell `0`. The halting time is the number of steps performed.
* The machine number `m` is read as four base-8 digits, most significant first, for the cases
  `(U,1), (U,0), (D,1), (D,0)`. A digit `x` means: new state `U` if `x < 4`, else `D`;
  symbol written `(x / 2) % 2`; move right if `x` is odd, else left.
-/

namespace A393317

/-- A configuration: state (`true` = `U`, the start state; `false` = `D`),
head position and tape contents. -/
structure Config where
  state : Bool
  pos : ℕ
  tape : ℕ → Bool

/-- The base-8 digit of machine number `m` for state `s` and scanned symbol `b`. -/
def digit (m : ℕ) (s b : Bool) : ℕ := m / 8 ^ (2 * s.toNat + b.toNat) % 8

/-- One step of machine `m`; `none` means that the head has left the tape on the right,
i.e. the machine has halted with this step. -/
def step (m : ℕ) (c : Config) : Option Config :=
  let x := digit m c.state (c.tape c.pos)
  let t := Function.update c.tape c.pos (decide (x / 2 % 2 = 1))
  if x % 2 = 1 then
    if c.pos = 0 then none else some ⟨decide (x < 4), c.pos - 1, t⟩
  else some ⟨decide (x < 4), c.pos + 1, t⟩

/-- `HaltsAfter m c t`: machine `m`, started in configuration `c`, halts after exactly `t` steps. -/
inductive HaltsAfter (m : ℕ) : Config → ℕ → Prop
  | halt {c : Config} : step m c = none → HaltsAfter m c 1
  | next {c c' : Config} {t : ℕ} : step m c = some c' → HaltsAfter m c' t → HaltsAfter m c (t + 1)

/-- Initial configuration for input `x`. -/
def init (x : ℕ) : Config := ⟨true, 0, fun i => x.testBit i⟩

/-- The set of halting times of all 4096 machines over all `n`-bit inputs. -/
def haltingTimes (n : ℕ) : Set ℕ :=
  {t | ∃ m < 4096, ∃ x, 2 ^ (n - 1) ≤ x ∧ x < 2 ^ n ∧ HaltsAfter m (init x) t}

/-- The set of halting times of all 4096 machines over all inputs with at most `n` binary digits
(all `x < 2^n`, including the input `0`).  This is the reading used by the program attached to
the OEIS entry; `hasler_conjecture_upto` shows that it gives the same maximum. -/
def haltingTimesUpTo (n : ℕ) : Set ℕ :=
  {t | ∃ m < 4096, ∃ x, x < 2 ^ n ∧ HaltsAfter m (init x) t}

/-- **Hasler's conjecture for OEIS A393317** (M. F. Hasler, Feb 12 2026): for every `n ≥ 1` the
largest halting time of any of the 4096 machines over all `n`-bit inputs is `2(n+2)² − 1` if
`n < 5` and `2^(n+2) − 3` if `n ≥ 5`. -/
theorem hasler_conjecture (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest (haltingTimes n) (if n < 5 then 2 * (n + 2) ^ 2 - 1 else 2 ^ (n + 2) - 3) := by
  sorry

/-- The same statement for the inputs with at most `n` binary digits (`x < 2^n`). -/
theorem hasler_conjecture_upto (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest (haltingTimesUpTo n) (if n < 5 then 2 * (n + 2) ^ 2 - 1 else 2 ^ (n + 2) - 3) := by
  sorry

end A393317
