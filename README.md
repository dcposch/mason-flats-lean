# Mason’s flat log-concavity is false

Larson (arXiv:2607.02208, Example 2.2 / Theorem 2.3) exhibited a rank-76
graphic matroid whose Whitney numbers of the second kind fail log-concavity:

\[
W_{74}^2 < W_{73}\,W_{75}.
\]

The matroid is the dual of a rank-3 parallel extension of \(U_{3,4}\) with
parallel classes of sizes \(1,26,26,26\) (the cycle matroid of a generalized
theta graph with path lengths \(26,26,26,1\)). Flats of rank \(76-i\) are
counted as cyclic sets of nullity \(i\) in the dual; the counts are the
binomial identities

\[
\begin{aligned}
W_{75} &= 3\binom{26}{2}+26^3 = 18551,\\
W_{74} &= 3\binom{26}{3}+3\binom{26}{2}^2+3\binom{26}{2}\,26^2 = 983775,\\
W_{73} &= 3\binom{26}{4}+6\binom{26}{3}\binom{26}{2}+\binom{26}{2}^3
  +3\binom{26}{3}\,26^2+3\binom{26}{2}^2\,26 = 52954525.
\end{aligned}
\]

This is a Palomar project. Submissions go to
<https://submit.palomar-registry.org/>.

## Repository map

- `Challenge.lean` — audited statement `MasonFlats.mason_log_concave_false`.
- `Solution.lean` — the same declaration, proved.
- `MasonFlats/` — dual construction, cyclic-set bijection, typed binomial counts.
- `sources/` — Larson arXiv:2607.02208.
- `comparator.json`, `formalization.yaml` — Palomar metadata.

## Verify

```sh
lake build Challenge Solution MasonFlats
printf 'import Solution\n#print axioms MasonFlats.mason_log_concave_false\n' \
  | lake env lean --stdin
```

Lean 4.32.0, Mathlib v4.32.0. Forbidden: `native_decide`, `Lean.ofReduceBool`.
Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`.
