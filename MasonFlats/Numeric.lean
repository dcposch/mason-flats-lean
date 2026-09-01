/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import MasonFlats.Count2

open Matroid

namespace MasonFlats

lemma choose_26_2 : Nat.choose 26 2 = 325 := by decide
lemma choose_26_3 : Nat.choose 26 3 = 2600 := by decide
lemma choose_26_4 : Nat.choose 26 4 = 14950 := by decide

lemma w75_val : 3 * Nat.choose 26 2 + 26 ^ 3 = 18551 := by
  rw [choose_26_2]; decide

lemma w74_val :
    3 * Nat.choose 26 3 + 3 * Nat.choose 26 2 ^ 2 + 3 * Nat.choose 26 2 * 26 ^ 2 = 983775 := by
  rw [choose_26_2, choose_26_3]; decide

lemma w73_val :
    3 * Nat.choose 26 4 + 6 * Nat.choose 26 3 * Nat.choose 26 2 + Nat.choose 26 2 ^ 3 +
      3 * Nat.choose 26 3 * 26 ^ 2 + 3 * Nat.choose 26 2 ^ 2 * 26 = 52954525 := by
  rw [choose_26_2, choose_26_3, choose_26_4]; decide

lemma w_sq_lt : (983775 : ℕ) ^ 2 < 52954525 * 18551 := by decide

lemma mason_ineq :
    whitneySecond theta 74 ^ 2 < whitneySecond theta 73 * whitneySecond theta 75 := by
  rw [whitney_73, whitney_74, whitney_75, w73_val, w74_val, w75_val]
  exact w_sq_lt

end MasonFlats
