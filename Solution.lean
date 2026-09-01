/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import MasonFlats
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-!
# Proved solution

Comparator matches `MasonFlats.mason_log_concave_false` in `Challenge.lean`.
-/

open Set Matroid

namespace MasonFlats

theorem mason_log_concave_false :
    ∃ M : Matroid (Fin 79),
      M.E = univ ∧
      M.eRank = 76 ∧
      whitneySecond M 74 ^ 2 < whitneySecond M 73 * whitneySecond M 75 :=
  ⟨theta, theta_E, theta_eRank, mason_ineq⟩

end MasonFlats
