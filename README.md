# A machine-checked proof of Hasler's conjecture for OEIS A393317

**Statement.** [OEIS A393317](https://oeis.org/A393317): a(n) is the maximum halting time for any of the 4096
Wolfram 2-state 2-symbol Turing machines across all n-bit inputs (runs that do not halt are excluded). The
sequence comes from S. Wolfram, *P vs. NP and the Difficulty of Computation: A Ruliological Approach* (2026);
it starts 17, 31, 49, 71, 125, 253, 509, 1021, ... M. F. Hasler conjectured in the OEIS entry (12 Feb 2026):

1. the maximal runtime of machines 378 and 1351 is 2^(n+2) - 3 and that of machine 1447 is 2(n+2)^2 - 1,
   in each case for the n-bit input 2^n - 1;
2. a(n) = 2(n+2)^2 - 1 for n < 5 and a(n) = 2^(n+2) - 3 for n > 4.

**Result.** This repository contains a complete Lean 4 / Mathlib proof of both parts (no `sorry`, no
`native_decide`; axioms: `propext`, `Quot.sound`, `Classical.choice`). The main theorem is

```lean
theorem A393317.hasler_conjecture (n : ℕ) (hn : 1 ≤ n) :
    IsGreatest (haltingTimes n) (if n < 5 then 2 * (n + 2) ^ 2 - 1 else 2 ^ (n + 2) - 3)
```

where `haltingTimes n` is the set of halting times of all 4096 machines over all inputs `2^(n-1) ≤ x < 2^n`.
`hasler_conjecture_upto` is the same statement for all inputs `x < 2^n` (the reading used by the program
attached to the OEIS entry; the maximum is the same). Part 1 is `max378`, `max1351`, `max1447`; in fact machines
378 and 1351 halt after exactly 2^(k+2) - 3 steps on every input whose binary expansion ends in exactly k ones
(`machine378`, `machine1351`).

A description of the proof for human readers is in [`paper/a393317.pdf`](paper/a393317.pdf).

## Idea of the proof

* **Lower bound.** Machines 378 and 1351 are binary counters; machine 1447 sweeps back and forth over a growing
  block. Their halting times on 2^n - 1 are computed exactly (`A393317/Stage1.lean`).
* **Upper bound, all 4096 machines.** The tape ends on the right, so a halting run can be cut along the cell
  boundaries. For each boundary we record the list of pairs (state when the head crosses to the left, state when
  it comes back). The halting time is twice the total length of these lists minus one, and neighbouring lists are
  coupled by a relation that involves only the cell between them (`A393317/Cross.lean`). For each machine a small
  certificate bounds the total length: a finite automaton reading the lists, two invariants and a potential
  function (`Inv.lean`, `Bound.lean`, `Poly.lean`, `Expo.lean`). The certificates were found by a search program
  (`gen/`); they are verified by a checker that is proved correct in Lean (`Checker.lean`) and evaluated inside
  the Lean kernel (`A393317/Certs/`, `by decide +kernel`). This covers 4092 machines: 4084 with a quadratic
  bound, 8 with the bound 2^(n+2) - 3.
* **Four machines by hand.** Machines 1507, 3555, 2574 and 2830 are not covered by this scheme and are analysed
  individually (`A393317/Special.lean`).

## Files

| File | Content |
|---|---|
| `Challenge.lean` | the model and the two statements with `sorry` (input for Comparator) |
| `Solution.lean` | imports the proof (input for Comparator) |
| `comparator.json` | Comparator configuration |
| `A393317/Defs.lean` | the model: `Config`, `step`, `HaltsAfter`, `init`, `haltingTimes` |
| `A393317/Stage1.lean` | exact halting times of machines 378, 1351, 1447 |
| `A393317/Cross.lean`, `Inv.lean`, `Bound.lean` | crossing sequences, invariants, bound from potentials |
| `A393317/Poly.lean`, `Checker.lean`, `Expo.lean` | potentials, certificate checker and its soundness |
| `A393317/Special.lean` | machines 1507, 3555, 2574, 2830 |
| `A393317/UB.lean`, `All.lean`, `Certs/C0.lean` ... `C63.lean` | upper bound for every machine (`Certs` and `All.lean` are generated) |
| `A393317/Main.lean` | `hasler_conjecture`, `hasler_conjecture_upto`, `max378`, `max1351`, `max1447` |
| `ModelCheck.lean` | the model against published OEIS data (see below) |
| `Axioms.lean` | prints the axioms used by the main theorems |
| `gen/` | search program for the certificates, a plain simulator, generator of `ModelCheck.lean` |
| `paper/` | description of the proof (LaTeX source and PDF) |

## Checking

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain `leanprover/lean4:v4.27.0` is selected
by `lean-toolchain`; Mathlib `v4.27.0` is pinned in `lake-manifest.json`).

```
lake exe cache get      # downloads the compiled Mathlib
lake build              # builds the proof, ModelCheck and Axioms
```

The build of this project takes about 7 minutes on a 16-core machine (most of it for the 64 certificate files)
and ends with `Build completed successfully`. `Axioms.lean` prints, for each main theorem,
`depends on axioms: [propext, Classical.choice, Quot.sound]`.

**Comparator.** To check that the theorems are proved with exactly the statements and definitions of
`Challenge.lean`, run [Comparator](https://github.com/leanprover/comparator) in this directory:

```
lake env <path to>/comparator comparator.json
```

(with `landrun` and `lean4export` installed as described in the Comparator README). The run ends with
`Lean default kernel accepts the solution` / `Your solution is okay!`.

**Certificates.** `gen/batch.py` regenerates `A393317/Certs/` and `A393317/All.lean`
(`cd gen && python3 batch.py ../A393317/Certs`; needs numpy and scipy). The search program does not have to be
trusted: a wrong certificate is rejected by the Lean checker. With numpy 2.4.4 and scipy 1.18.0 the output is
byte-identical to the files in this repository; other versions of the linear-programming solver may produce
different, equally valid certificates.

## The model and how it was validated

The tape holds the binary digits of the input, cell `i` the digit of weight `2^i`; all other cells are 0. The
head starts on cell 0 in state `U`; "right" means towards cell 0. The machine halts as soon as the head moves
right from cell 0, and the halting time is the number of steps. The machine number `m` (0..4095) is read as four
base-8 digits, most significant first, for the cases (U,1), (U,0), (D,1), (D,0); a digit `x` means: new state `U`
if `x < 4`, else `D`; symbol written `(x / 2) % 2`; move right if `x` is odd, else left.

These definitions (`A393317/Defs.lean`, repeated in `Challenge.lean`, about 40 lines) were written for this
project. They are the part that the Lean kernel cannot check, so they were compared with data computed by
others:

* `ModelCheck.lean` proves in the kernel that the model reproduces **every term listed in the OEIS entry** for
  the ten entries "Halting time for Wolfram's 2-state 2-symbol Turing machine M when started with n on the tape"
  (machines 1285, 261, 3333, 3111, 1511, 3626, 773, 897, 919, 3239; A393103, A393106, A393146, A393190, A393209,
  A393210, A393212, A393232, A393233, A393234; 68 to 86 terms each, 782 in total).
* `gen/simulate.py`, a plain Python simulator of the same model, reproduces a(1..8) of A393317 by exhaustive
  search, and the machines named in the OEIS entry (378, 1351, 1447) attain the stated values on the stated
  inputs.
* The decoding of the machine numbers agrees with the Python program attached to the OEIS entry.

## Status and limitations

* The proof was checked with the standard Lean kernel (via `lake build` and Comparator). No second, independent
  kernel was used.
* No human has read the proof or the description in `paper/`. Where the description and the Lean files differ,
  the Lean files are authoritative.
* The definition of the model was written by the AI model that produced the proof; it does not come from an
  external source and has not been reviewed by a second person. It was tested as described above; a direct
  comparison with Wolfram's `TuringMachine` function was not made. Should the model deviate from Wolfram's set-up
  in a way these tests do not detect, the theorem would still be true, but about a slightly different model.
* Searches on 10 Nov 2026 (OEIS, GitHub, arXiv, Zenodo, web) found no earlier proof of the conjecture. A related
  result for a single machine (halting times of machine 3626, A393210) was formalized in
  [the-omega-institute/trureturing#25879](https://github.com/the-omega-institute/trureturing/pull/25879).

## Credits

The choice of problem, the proof, its Lean formalization and the description were produced by Claude Fable 5
(an AI model by Anthropic; model ID `claude-fable-5-2`, working in Claude Code) on 10 Nov 2026. The work was
commissioned by Dr. Marc Potempa, who set the task and decided to publish it, but did not contribute to the
mathematical content.

## License

Apache License 2.0, see `LICENSE`.
