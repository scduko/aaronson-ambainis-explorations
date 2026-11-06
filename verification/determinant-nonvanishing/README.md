# Verification of the determinant nonvanishing simplification

This change replaces the proof of `DetLow.agMatrix_det_ne_zero` (paper Lemma 3.4)
by specialization to one indeterminate and extraction of the unique top coefficient.
The statement of that theorem and `AaronsonAmbainis/Conjecture.lean` are unchanged.

The repository's pinned Lean 4.33.0 and Mathlib revision are unchanged.
The execution environment exposes `/proc/self/exe`, but not the equivalent
`/proc/<current-process-id>/exe` used by Lean's executable-path lookup. A local
`LD_PRELOAD` shim redirects only that lookup to `/proc/self/exe`. It does not
change the Lean binaries, proof checking, or source files, and is not part of the project.

The accompanying check logs and source digest record this revision's verification.

Proof-source commit on the fork: `572b8a5be10c1f1658d2bfb2006a8a6b168d4d86`.

- `make check`: exit 0; imports and source audit passed; full build passed;
  axiom audit reported 119 declarations with zero errors.
- The three determinant lemmas in `determinant-axioms.txt` use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- `make paper`: successful; extracted text agrees with the existing paper PDF.
  The existing PDF was retained to avoid a change to build metadata alone.
- `LEAN_NUM_THREADS=1 make replay`: exit 0; all 84 project modules replayed.

Both `make check` and `make replay` ran with `LEAN_NUM_THREADS=1` and the
executable-path compatibility shim described above. No proof-checking settings
were disabled. The source digest is in `source-digest.txt`; the raw outputs are
`check.txt`, `axiom-report.txt`, `determinant-axioms.txt`, and `replay.txt`.
