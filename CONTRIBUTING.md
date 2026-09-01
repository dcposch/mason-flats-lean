# Adapting this template

1. Rename the package and namespace throughout the repository.
2. Put the proof development in the library and import it from `Solution.lean`.
3. Rewrite `Challenge.lean` as a small, independently auditable statement
   surface. Keep its advertised declarations statement-only with `sorry`; the
   corresponding proofs belong in `Solution.lean`. Its imports must satisfy the
   current Palomar policy.
4. Update `comparator.json` with every advertised theorem and any definition
   holes. Definition holes require special editorial scrutiny.
5. Replace every `TEMPLATE` value in `formalization.yaml` with honest,
   independently checkable metadata.
