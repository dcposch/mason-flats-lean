/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# Mason’s flat log-concavity conjecture is false

Mason (1972) conjectured that the Whitney numbers of the second kind of a
matroid — the numbers `W_i` of rank-`i` flats — form a log-concave sequence.
Larson (arXiv:2607.02208, Example 2.2 / Theorem 2.3) disproved this by an
explicit rank-76 graphic matroid, the cycle matroid of a generalized theta
graph with path lengths `26, 26, 26, 1`.

The compared statement is the existence of a rank-76 matroid on `79`
elements with `W_74 ^ 2 < W_73 * W_75`. The dual cyclic-set count and the
binomial identities live in `Solution.lean`. White’s conjecture from the
same paper is not compared.
-/

open Set Matroid

namespace MasonFlats

/-- Whitney numbers of the second kind: the number of flats of rank `i`. -/
noncomputable def whitneySecond {α : Type*} (M : Matroid α) (i : ℕ) : ℕ :=
  {F : Set α | M.IsFlat F ∧ M.eRk F = i}.ncard

/-- **Mason (1972) is false.** There is a rank-`76` matroid on `79` elements
whose Whitney numbers of the second kind fail log-concavity at ranks
`73, 74, 75`. -/
theorem mason_log_concave_false :
    ∃ M : Matroid (Fin 79),
      M.E = univ ∧
      M.eRank = 76 ∧
      whitneySecond M 74 ^ 2 < whitneySecond M 73 * whitneySecond M 75 := by
  sorry

end MasonFlats
