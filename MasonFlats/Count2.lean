/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import MasonFlats.Count

open Set Matroid

namespace MasonFlats

open scoped Classical

lemma ncard_union3 {α : Type*} [Finite α] {s t u : Set α}
    (hst : Disjoint s t) (hsu : Disjoint s u) (htu : Disjoint t u) :
    (s ∪ t ∪ u).ncard = s.ncard + t.ncard + u.ncard := by
  have d : Disjoint (s ∪ t) u := disjoint_union_left.2 ⟨hsu, htu⟩
  rw [ncard_union_eq d, ncard_union_eq hst]

lemma mem_union3_1 {α : Type*} {A B C : Set α} {x : α} (h : x ∈ A) :
    x ∈ A ∪ B ∪ C := Or.inl (Or.inl h)

lemma mem_union3_2 {α : Type*} {A B C : Set α} {x : α} (h : x ∈ B) :
    x ∈ A ∪ B ∪ C := Or.inl (Or.inr h)

lemma mem_union3_3 {α : Type*} {A B C : Set α} {x : α} (h : x ∈ C) :
    x ∈ A ∪ B ∪ C := Or.inr h

lemma mem_union6_1 {α : Type*} {A B C D E F : Set α} {x : α} (h : x ∈ A) :
    x ∈ A ∪ B ∪ C ∪ D ∪ E ∪ F :=
  Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inl h

lemma mem_union6_2 {α : Type*} {A B C D E F : Set α} {x : α} (h : x ∈ B) :
    x ∈ A ∪ B ∪ C ∪ D ∪ E ∪ F :=
  Or.inl <| Or.inl <| Or.inl <| Or.inl <| Or.inr h

lemma mem_union6_3 {α : Type*} {A B C D E F : Set α} {x : α} (h : x ∈ C) :
    x ∈ A ∪ B ∪ C ∪ D ∪ E ∪ F :=
  Or.inl <| Or.inl <| Or.inl <| Or.inr h

lemma mem_union6_4 {α : Type*} {A B C D E F : Set α} {x : α} (h : x ∈ D) :
    x ∈ A ∪ B ∪ C ∪ D ∪ E ∪ F :=
  Or.inl <| Or.inl <| Or.inr h

lemma mem_union6_5 {α : Type*} {A B C D E F : Set α} {x : α} (h : x ∈ E) :
    x ∈ A ∪ B ∪ C ∪ D ∪ E ∪ F :=
  Or.inl <| Or.inr h

lemma mem_union6_6 {α : Type*} {A B C D E F : Set α} {x : α} (h : x ∈ F) :
    x ∈ A ∪ B ∪ C ∪ D ∪ E ∪ F :=
  Or.inr h

lemma ncard_cyclic_null_two :
    {S : Set (Fin 79) | IsCyclic thetaDual S ∧ S.ncard = min 3 (supp S).ncard + 2}.ncard =
      3 * Nat.choose 26 3 + 3 * Nat.choose 26 2 ^ 2 +
        3 * Nat.choose 26 2 * 26 ^ 2 := by
  let A := typed 0 3 0 0 ∪ typed 0 0 3 0 ∪ typed 0 0 0 3
  let B := typed 0 2 2 0 ∪ typed 0 2 0 2 ∪ typed 0 0 2 2
  let C := typed 1 2 1 1 ∪ typed 1 1 2 1 ∪ typed 1 1 1 2
  have hEq : {S : Set (Fin 79) | IsCyclic thetaDual S ∧
      S.ncard = min 3 (supp S).ncard + 2} = A ∪ B ∪ C := by
    ext S
    constructor
    · intro h
      have hty : S ∈ typed (S ∩ para 0).ncard (S ∩ para 1).ncard
          (S ∩ para 2).ncard (S ∩ para 3).ncard := ⟨rfl, rfl, rfl, rfl⟩
      set n0 := (S ∩ para 0).ncard
      set n1 := (S ∩ para 1).ncard
      set n2 := (S ∩ para 2).ncard
      set n3 := (S ∩ para 3).ncard
      have hsum : n0 + n1 + n2 + n3 = min 3 (supp S).ncard + 2 := by
        simpa [typed_ncard hty] using h.2
      have hkn := typed_supp_ncard hty
      have hcyc := (typed_cyclic hty).1 h.1
      have hn0le : n0 ≤ 1 := by
        have : n0 ≤ (para 0).ncard := ncard_le_ncard inter_subset_right
        simpa [ncard_para_zero] using this
      cases Nat.eq_zero_or_pos n0 with
      | inl h0 =>
        have hsing : n0 ≠ 1 ∧ n1 ≠ 1 ∧ n2 ≠ 1 ∧ n3 ≠ 1 := by
          rcases hcyc with hs | hp
          · exact hs
          · exact absurd hp.1 (not_lt.2 (le_of_eq h0))
        have hk : (supp S).ncard =
            (if n1 = 0 then 0 else 1) + (if n2 = 0 then 0 else 1) +
            (if n3 = 0 then 0 else 1) := by simpa [h0] using hkn
        have hsum' : n1 + n2 + n3 = min 3 (supp S).ncard + 2 := by
          rw [h0] at hsum; omega
        have h3 := three_nat_null_two hsing.2.1 hsing.2.2.1 hsing.2.2.2
          (by simpa [hk] using hsum')
        rcases h3 with h' | h' | h' | h' | h' | h'
        · exact Or.inl (Or.inl (Or.inl (Or.inl (by simpa [A, typed, h0, h'] using hty))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr (by simpa [A, typed, h0, h'] using hty))))
        · exact Or.inl (Or.inl (Or.inr (by simpa [A, typed, h0, h'] using hty)))
        · exact Or.inl (Or.inr (Or.inl (Or.inl (by simpa [B, typed, h0, h'] using hty))))
        · exact Or.inl (Or.inr (Or.inl (Or.inr (by simpa [B, typed, h0, h'] using hty))))
        · exact Or.inl (Or.inr (Or.inr (by simpa [B, typed, h0, h'] using hty)))
      | inr _ =>
        have hpos : 0 < n0 ∧ 0 < n1 ∧ 0 < n2 ∧ 0 < n3 := by
          rcases hcyc with hs | hp
          · exact absurd (show n0 = 1 from by omega) hs.1
          · exact hp
        have hn0z : n0 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.1
        have hn1z : n1 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.2.1
        have hn2z : n2 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.2.2.1
        have hn3z : n3 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.2.2.2
        have hk4 : (supp S).ncard = 4 := by simpa [hkn, hn0z, hn1z, hn2z, hn3z]
        have : n0 + n1 + n2 + n3 = 5 := by simp [hk4] at hsum; exact hsum
        have hn01 : n0 = 1 := by omega
        have h123 : n1 + n2 + n3 = 4 := by omega
        have hps := pos_three_sum hpos.2.1 hpos.2.2.1 hpos.2.2.2 h123
        rcases hps with h' | h' | h'
        · exact Or.inr (Or.inl (Or.inl (by simpa [C, typed, hn01, h'] using hty)))
        · exact Or.inr (Or.inl (Or.inr (by simpa [C, typed, hn01, h'] using hty)))
        · exact Or.inr (Or.inr (by simpa [C, typed, hn01, h'] using hty))
    · intro h
      cases h with
      | inl h =>
        cases h with
        | inl h =>
          cases h with
          | inl h =>
            cases h with
            | inl h => exact cyclic_of_typed h (by decide) (by decide)
            | inr h => exact cyclic_of_typed h (by decide) (by decide)
          | inr h => exact cyclic_of_typed h (by decide) (by decide)
        | inr h =>
          cases h with
          | inl h =>
            cases h with
            | inl h => exact cyclic_of_typed h (by decide) (by decide)
            | inr h => exact cyclic_of_typed h (by decide) (by decide)
          | inr h => exact cyclic_of_typed h (by decide) (by decide)
      | inr h =>
        cases h with
        | inl h =>
          cases h with
          | inl h => exact cyclic_of_typed h (by decide) (by decide)
          | inr h => exact cyclic_of_typed h (by decide) (by decide)
        | inr h => exact cyclic_of_typed h (by decide) (by decide)
  have nA : A.ncard = 3 * Nat.choose 26 3 := by
    have h := ncard_union3
      (s := typed 0 3 0 0) (t := typed 0 0 3 0) (u := typed 0 0 0 3)
      (typed_disjoint (by decide)) (typed_disjoint (by decide)) (typed_disjoint (by decide))
    simp [A] at h ⊢
    simp [ncard_typed, Nat.choose_zero_right] at h
    rw [h]; ring
  have nB : B.ncard = 3 * Nat.choose 26 2 ^ 2 := by
    have h := ncard_union3
      (s := typed 0 2 2 0) (t := typed 0 2 0 2) (u := typed 0 0 2 2)
      (typed_disjoint (by decide)) (typed_disjoint (by decide)) (typed_disjoint (by decide))
    simp [B] at h ⊢
    simp [ncard_typed, Nat.choose_zero_right] at h
    rw [h]; ring
  have nC : C.ncard = 3 * Nat.choose 26 2 * 26 ^ 2 := by
    have h := ncard_union3
      (s := typed 1 2 1 1) (t := typed 1 1 2 1) (u := typed 1 1 1 2)
      (typed_disjoint (by decide)) (typed_disjoint (by decide)) (typed_disjoint (by decide))
    simp only [C] at h ⊢
    rw [h, ncard_typed, ncard_typed, ncard_typed]
    rw [Nat.choose_self, Nat.choose_one_right]
    ring
  have dAB : Disjoint A B := by
    dsimp [A, B]
    refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩
    · refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
    · refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
    · refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
  have dAC : Disjoint A C := by
    dsimp [A, C]
    refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩
    · refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
    · refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
    · refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
  have dBC : Disjoint B C := by
    dsimp [B, C]
    refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩
    · refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
    · refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
    · refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
      · exact typed_disjoint (by decide)
  rw [hEq, ncard_union3 dAB dAC dBC, nA, nB, nC]

lemma whitney_74 :
    whitneySecond theta 74 =
      3 * Nat.choose 26 3 + 3 * Nat.choose 26 2 ^ 2 +
        3 * Nat.choose 26 2 * 26 ^ 2 := by
  rw [whitney_eq_cyclic 2 (by decide), ncard_cyclic_null_two]

lemma ncard_cyclic_null_three :
    {S : Set (Fin 79) | IsCyclic thetaDual S ∧ S.ncard = min 3 (supp S).ncard + 3}.ncard =
      3 * Nat.choose 26 4 + 6 * Nat.choose 26 3 * Nat.choose 26 2 +
        Nat.choose 26 2 ^ 3 + 3 * Nat.choose 26 3 * 26 ^ 2 +
        3 * Nat.choose 26 2 ^ 2 * 26 := by
  let A := typed 0 4 0 0 ∪ typed 0 0 4 0 ∪ typed 0 0 0 4
  let B1 := typed 0 3 2 0 ∪ typed 0 3 0 2 ∪ typed 0 2 3 0
  let B2 := typed 0 0 3 2 ∪ typed 0 2 0 3 ∪ typed 0 0 2 3
  let G := typed 0 2 2 2
  let D := typed 1 3 1 1 ∪ typed 1 1 3 1 ∪ typed 1 1 1 3
  let E := typed 1 2 2 1 ∪ typed 1 2 1 2 ∪ typed 1 1 2 2
  have hEq : {S : Set (Fin 79) | IsCyclic thetaDual S ∧
      S.ncard = min 3 (supp S).ncard + 3} = A ∪ B1 ∪ B2 ∪ G ∪ D ∪ E := by
    ext S
    constructor
    · intro h
      have hty : S ∈ typed (S ∩ para 0).ncard (S ∩ para 1).ncard
          (S ∩ para 2).ncard (S ∩ para 3).ncard := ⟨rfl, rfl, rfl, rfl⟩
      set n0 := (S ∩ para 0).ncard
      set n1 := (S ∩ para 1).ncard
      set n2 := (S ∩ para 2).ncard
      set n3 := (S ∩ para 3).ncard
      have hsum : n0 + n1 + n2 + n3 = min 3 (supp S).ncard + 3 := by
        simpa [typed_ncard hty] using h.2
      have hkn := typed_supp_ncard hty
      have hcyc := (typed_cyclic hty).1 h.1
      have hn0le : n0 ≤ 1 := by
        have : n0 ≤ (para 0).ncard := ncard_le_ncard inter_subset_right
        simpa [ncard_para_zero] using this
      cases Nat.eq_zero_or_pos n0 with
      | inl h0 =>
        have hsing : n0 ≠ 1 ∧ n1 ≠ 1 ∧ n2 ≠ 1 ∧ n3 ≠ 1 := by
          rcases hcyc with hs | hp
          · exact hs
          · exact absurd hp.1 (not_lt.2 (le_of_eq h0))
        have hk : (supp S).ncard =
            (if n1 = 0 then 0 else 1) + (if n2 = 0 then 0 else 1) +
            (if n3 = 0 then 0 else 1) := by simpa [h0] using hkn
        have hsum' : n1 + n2 + n3 = min 3 (supp S).ncard + 3 := by
          rw [h0] at hsum; omega
        have h3 := three_nat_null_three hsing.2.1 hsing.2.2.1 hsing.2.2.2
          (by simpa [hk] using hsum')
        rcases h3 with h' | h' | h' | h' | h' | h' | h' | h' | h' | h'
        · exact mem_union6_1 (mem_union3_1 (by simpa [typed, h0, h'] using hty))
        · exact mem_union6_1 (mem_union3_2 (by simpa [typed, h0, h'] using hty))
        · exact mem_union6_1 (mem_union3_3 (by simpa [typed, h0, h'] using hty))
        · exact mem_union6_2 (mem_union3_1 (by simpa [typed, h0, h'] using hty))
        · exact mem_union6_2 (mem_union3_2 (by simpa [typed, h0, h'] using hty))
        · exact mem_union6_2 (mem_union3_3 (by simpa [typed, h0, h'] using hty))
        · exact mem_union6_3 (mem_union3_1 (by simpa [typed, h0, h'] using hty))
        · exact mem_union6_3 (mem_union3_2 (by simpa [typed, h0, h'] using hty))
        · exact mem_union6_3 (mem_union3_3 (by simpa [typed, h0, h'] using hty))
        · exact mem_union6_4 (by simpa [G, h0, h'] using hty)
      | inr _ =>
        have hpos : 0 < n0 ∧ 0 < n1 ∧ 0 < n2 ∧ 0 < n3 := by
          rcases hcyc with hs | hp
          · exact absurd (show n0 = 1 from by omega) hs.1
          · exact hp
        have hn0z : n0 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.1
        have hn1z : n1 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.2.1
        have hn2z : n2 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.2.2.1
        have hn3z : n3 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.2.2.2
        have hk4 : (supp S).ncard = 4 := by simpa [hkn, hn0z, hn1z, hn2z, hn3z]
        have : n0 + n1 + n2 + n3 = 6 := by simp [hk4] at hsum; exact hsum
        have hn01 : n0 = 1 := by omega
        have h123 : n1 + n2 + n3 = 5 := by omega
        have hps := pos_three_sum_five hpos.2.1 hpos.2.2.1 hpos.2.2.2 h123
        rcases hps with h' | h' | h' | h' | h' | h'
        · exact mem_union6_5 (mem_union3_1 (by simpa [typed, hn01, h'] using hty))
        · exact mem_union6_5 (mem_union3_2 (by simpa [typed, hn01, h'] using hty))
        · exact mem_union6_5 (mem_union3_3 (by simpa [typed, hn01, h'] using hty))
        · exact mem_union6_6 (mem_union3_1 (by simpa [typed, hn01, h'] using hty))
        · exact mem_union6_6 (mem_union3_2 (by simpa [typed, hn01, h'] using hty))
        · exact mem_union6_6 (mem_union3_3 (by simpa [typed, hn01, h'] using hty))
    · intro h
      cases h with
      | inl h =>
        cases h with
        | inl h =>
          cases h with
          | inl h =>
            cases h with
            | inl h =>
              cases h with
              | inl h =>
                cases h with
                | inl h =>
                  cases h with
                  | inl h => exact cyclic_of_typed h (by decide) (by decide)
                  | inr h => exact cyclic_of_typed h (by decide) (by decide)
                | inr h => exact cyclic_of_typed h (by decide) (by decide)
              | inr h =>
                cases h with
                | inl h =>
                  cases h with
                  | inl h => exact cyclic_of_typed h (by decide) (by decide)
                  | inr h => exact cyclic_of_typed h (by decide) (by decide)
                | inr h => exact cyclic_of_typed h (by decide) (by decide)
            | inr h =>
              cases h with
              | inl h =>
                cases h with
                | inl h => exact cyclic_of_typed h (by decide) (by decide)
                | inr h => exact cyclic_of_typed h (by decide) (by decide)
              | inr h => exact cyclic_of_typed h (by decide) (by decide)
          | inr h => exact cyclic_of_typed h (by decide) (by decide)
        | inr h =>
          cases h with
          | inl h =>
            cases h with
            | inl h => exact cyclic_of_typed h (by decide) (by decide)
            | inr h => exact cyclic_of_typed h (by decide) (by decide)
          | inr h => exact cyclic_of_typed h (by decide) (by decide)
      | inr h =>
        cases h with
        | inl h =>
          cases h with
          | inl h => exact cyclic_of_typed h (by decide) (by decide)
          | inr h => exact cyclic_of_typed h (by decide) (by decide)
        | inr h => exact cyclic_of_typed h (by decide) (by decide)
  have nA : A.ncard = 3 * Nat.choose 26 4 := by
    have h := ncard_union3 (s := typed 0 4 0 0) (t := typed 0 0 4 0) (u := typed 0 0 0 4)
      (typed_disjoint (by decide)) (typed_disjoint (by decide)) (typed_disjoint (by decide))
    simp [A] at h ⊢
    simp [ncard_typed, Nat.choose_zero_right] at h
    rw [h]; ring
  have nB1 : B1.ncard = 3 * Nat.choose 26 3 * Nat.choose 26 2 := by
    have h := ncard_union3 (s := typed 0 3 2 0) (t := typed 0 3 0 2) (u := typed 0 2 3 0)
      (typed_disjoint (by decide)) (typed_disjoint (by decide)) (typed_disjoint (by decide))
    simp [B1] at h ⊢
    simp [ncard_typed, Nat.choose_zero_right] at h
    rw [h]; ring
  have nB2 : B2.ncard = 3 * Nat.choose 26 3 * Nat.choose 26 2 := by
    have h := ncard_union3 (s := typed 0 0 3 2) (t := typed 0 2 0 3) (u := typed 0 0 2 3)
      (typed_disjoint (by decide)) (typed_disjoint (by decide)) (typed_disjoint (by decide))
    simp [B2] at h ⊢
    simp [ncard_typed, Nat.choose_zero_right] at h
    rw [h]; ring
  have nG : G.ncard = Nat.choose 26 2 ^ 3 := by
    simp only [G]
    rw [ncard_typed, Nat.choose_zero_right]
    ring
  have nD : D.ncard = 3 * Nat.choose 26 3 * 26 ^ 2 := by
    have h := ncard_union3 (s := typed 1 3 1 1) (t := typed 1 1 3 1) (u := typed 1 1 1 3)
      (typed_disjoint (by decide)) (typed_disjoint (by decide)) (typed_disjoint (by decide))
    simp only [D] at h ⊢
    rw [h, ncard_typed, ncard_typed, ncard_typed, Nat.choose_self, Nat.choose_one_right]
    ring
  have nE : E.ncard = 3 * Nat.choose 26 2 ^ 2 * 26 := by
    have h := ncard_union3 (s := typed 1 2 2 1) (t := typed 1 2 1 2) (u := typed 1 1 2 2)
      (typed_disjoint (by decide)) (typed_disjoint (by decide)) (typed_disjoint (by decide))
    simp only [E] at h ⊢
    rw [h, ncard_typed, ncard_typed, ncard_typed, Nat.choose_self, Nat.choose_one_right]
    ring
  have step1 : (A ∪ B1).ncard = A.ncard + B1.ncard := by
    refine ncard_union_eq ?_
    dsimp [A, B1]
    refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
      (refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
        exact typed_disjoint (by decide))
  have step2 : (A ∪ B1 ∪ B2).ncard = (A ∪ B1).ncard + B2.ncard := by
    refine ncard_union_eq ?_
    refine disjoint_union_left.2 ⟨?_, ?_⟩
    · dsimp [A, B2]
      refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        (refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
          exact typed_disjoint (by decide))
    · dsimp [B1, B2]
      refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        (refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
          exact typed_disjoint (by decide))
  have step3 : (A ∪ B1 ∪ B2 ∪ G).ncard = (A ∪ B1 ∪ B2).ncard + G.ncard := by
    refine ncard_union_eq ?_
    refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩
    · dsimp [A, G]; refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        exact typed_disjoint (by decide)
    · dsimp [B1, G]; refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        exact typed_disjoint (by decide)
    · dsimp [B2, G]; refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        exact typed_disjoint (by decide)
  have step4 : (A ∪ B1 ∪ B2 ∪ G ∪ D).ncard = (A ∪ B1 ∪ B2 ∪ G).ncard + D.ncard := by
    refine ncard_union_eq ?_
    refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · dsimp [A, D]; refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        (refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
          exact typed_disjoint (by decide))
    · dsimp [B1, D]; refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        (refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
          exact typed_disjoint (by decide))
    · dsimp [B2, D]; refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        (refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
          exact typed_disjoint (by decide))
    · dsimp [G, D]; refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
        exact typed_disjoint (by decide)
  have step5 : (A ∪ B1 ∪ B2 ∪ G ∪ D ∪ E).ncard =
      (A ∪ B1 ∪ B2 ∪ G ∪ D).ncard + E.ncard := by
    refine ncard_union_eq ?_
    refine disjoint_union_left.2
      ⟨disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · dsimp [A, E]; refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        (refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
          exact typed_disjoint (by decide))
    · dsimp [B1, E]; refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        (refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
          exact typed_disjoint (by decide))
    · dsimp [B2, E]; refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        (refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
          exact typed_disjoint (by decide))
    · dsimp [G, E]; refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
        exact typed_disjoint (by decide)
    · dsimp [D, E]; refine disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨?_, ?_⟩, ?_⟩ <;>
        (refine disjoint_union_right.2 ⟨disjoint_union_right.2 ⟨?_, ?_⟩, ?_⟩ <;>
          exact typed_disjoint (by decide))
  rw [hEq, step5, step4, step3, step2, step1, nA, nB1, nB2, nG, nD, nE]
  ring

lemma whitney_73 :
    whitneySecond theta 73 =
      3 * Nat.choose 26 4 + 6 * Nat.choose 26 3 * Nat.choose 26 2 +
        Nat.choose 26 2 ^ 3 + 3 * Nat.choose 26 3 * 26 ^ 2 +
        3 * Nat.choose 26 2 ^ 2 * 26 := by
  rw [whitney_eq_cyclic 3 (by decide), ncard_cyclic_null_three]

end MasonFlats

