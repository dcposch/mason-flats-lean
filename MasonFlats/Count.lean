/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import MasonFlats.Cyclic
import Mathlib.Data.Set.Card.Arithmetic

/-!
Classification and binomial counts of cyclic sets of given nullity in `thetaDual`.
-/

open Set Matroid

namespace MasonFlats

open scoped Classical

def typed (n0 n1 n2 n3 : ℕ) : Set (Set (Fin 79)) :=
  {S | (S ∩ para 0).ncard = n0 ∧ (S ∩ para 1).ncard = n1 ∧
       (S ∩ para 2).ncard = n2 ∧ (S ∩ para 3).ncard = n3}

lemma ncard_prod4 {α β γ δ : Type*} (s : Set α) (t : Set β) (u : Set γ) (v : Set δ) :
    (s ×ˢ t ×ˢ u ×ˢ v).ncard = s.ncard * t.ncard * u.ncard * v.ncard := by
  rw [ncard_prod, ncard_prod, ncard_prod, mul_assoc, mul_assoc]

lemma inter_union_para
    {t0 t1 t2 t3 : Set (Fin 79)}
    (h0 : t0 ⊆ para 0) (h1 : t1 ⊆ para 1) (h2 : t2 ⊆ para 2) (h3 : t3 ⊆ para 3) (i : Fin 4) :
    (t0 ∪ t1 ∪ t2 ∪ t3) ∩ para i =
      if i = 0 then t0 else if i = 1 then t1 else if i = 2 then t2 else t3 := by
  fin_cases i <;> simp
  · ext e
    constructor
    · intro he
      rcases he.1 with (((h | h) | h) | h)
      · exact h
      · exact (disjoint_left.1 (para_disjoint (by decide : (1 : Fin 4) ≠ 0)) (h1 h) he.2).elim
      · exact (disjoint_left.1 (para_disjoint (by decide : (2 : Fin 4) ≠ 0)) (h2 h) he.2).elim
      · exact (disjoint_left.1 (para_disjoint (by decide : (3 : Fin 4) ≠ 0)) (h3 h) he.2).elim
    · intro he
      exact ⟨Or.inl (Or.inl (Or.inl he)), h0 he⟩
  · ext e
    constructor
    · intro he
      rcases he.1 with (((h | h) | h) | h)
      · exact (disjoint_left.1 (para_disjoint (by decide : (0 : Fin 4) ≠ 1)) (h0 h) he.2).elim
      · exact h
      · exact (disjoint_left.1 (para_disjoint (by decide : (2 : Fin 4) ≠ 1)) (h2 h) he.2).elim
      · exact (disjoint_left.1 (para_disjoint (by decide : (3 : Fin 4) ≠ 1)) (h3 h) he.2).elim
    · intro he
      exact ⟨Or.inl (Or.inl (Or.inr he)), h1 he⟩
  · ext e
    constructor
    · intro he
      rcases he.1 with (((h | h) | h) | h)
      · exact (disjoint_left.1 (para_disjoint (by decide : (0 : Fin 4) ≠ 2)) (h0 h) he.2).elim
      · exact (disjoint_left.1 (para_disjoint (by decide : (1 : Fin 4) ≠ 2)) (h1 h) he.2).elim
      · exact h
      · exact (disjoint_left.1 (para_disjoint (by decide : (3 : Fin 4) ≠ 2)) (h3 h) he.2).elim
    · intro he
      exact ⟨Or.inl (Or.inr he), h2 he⟩
  · ext e
    constructor
    · intro he
      rcases he.1 with (((h | h) | h) | h)
      · exact (disjoint_left.1 (para_disjoint (by decide : (0 : Fin 4) ≠ 3)) (h0 h) he.2).elim
      · exact (disjoint_left.1 (para_disjoint (by decide : (1 : Fin 4) ≠ 3)) (h1 h) he.2).elim
      · exact (disjoint_left.1 (para_disjoint (by decide : (2 : Fin 4) ≠ 3)) (h2 h) he.2).elim
      · exact h
    · intro he
      exact ⟨Or.inr he, h3 he⟩

lemma ncard_typed (n0 n1 n2 n3 : ℕ) :
    (typed n0 n1 n2 n3).ncard =
      Nat.choose 1 n0 * Nat.choose 26 n1 * Nat.choose 26 n2 * Nat.choose 26 n3 := by
  let A0 : Set (Set (Fin 79)) := {t | t ⊆ para 0 ∧ t.ncard = n0}
  let A1 : Set (Set (Fin 79)) := {t | t ⊆ para 1 ∧ t.ncard = n1}
  let A2 : Set (Set (Fin 79)) := {t | t ⊆ para 2 ∧ t.ncard = n2}
  let A3 : Set (Set (Fin 79)) := {t | t ⊆ para 3 ∧ t.ncard = n3}
  have hA0 : A0.ncard = Nat.choose 1 n0 := by
    have := ncard_powerset_ncard (para 0).toFinite n0
    simpa [A0, ncard_para_zero] using this
  have hA1 : A1.ncard = Nat.choose 26 n1 := by
    have := ncard_powerset_ncard (para 1).toFinite n1
    simpa [A1, ncard_para_one] using this
  have hA2 : A2.ncard = Nat.choose 26 n2 := by
    have := ncard_powerset_ncard (para 2).toFinite n2
    simpa [A2, ncard_para_two] using this
  have hA3 : A3.ncard = Nat.choose 26 n3 := by
    have := ncard_powerset_ncard (para 3).toFinite n3
    simpa [A3, ncard_para_three] using this
  refine (ncard_congr (t := A0 ×ˢ A1 ×ˢ A2 ×ˢ A3)
      (fun S _ => (S ∩ para 0, S ∩ para 1, S ∩ para 2, S ∩ para 3))
      (fun S hS => ?mem)
      (fun S₁ S₂ h₁ h₂ heq => ?inj)
      (fun p hp => ?surj)).trans (by rw [ncard_prod4, hA0, hA1, hA2, hA3])
  · exact ⟨⟨inter_subset_right, hS.1⟩,
      ⟨inter_subset_right, hS.2.1⟩,
      ⟨inter_subset_right, hS.2.2.1⟩,
      ⟨inter_subset_right, hS.2.2.2⟩⟩
  · have e0 : S₁ ∩ para 0 = S₂ ∩ para 0 := congrArg (fun p : Set (Fin 79) × _ => p.1) heq
    have e123 := congrArg (fun p : Set (Fin 79) × _ => p.2) heq
    have e1 : S₁ ∩ para 1 = S₂ ∩ para 1 := congrArg (fun p : Set (Fin 79) × _ => p.1) e123
    have e23 := congrArg (fun p : Set (Fin 79) × _ => p.2) e123
    have e2 : S₁ ∩ para 2 = S₂ ∩ para 2 := congrArg (fun p : Set (Fin 79) × _ => p.1) e23
    have e3 : S₁ ∩ para 3 = S₂ ∩ para 3 := congrArg (fun p : Set (Fin 79) × _ => p.2) e23
    rw [eq_union_parts S₁, eq_union_parts S₂, e0, e1, e2, e3]
  · obtain ⟨t0, t123⟩ := p
    obtain ⟨t1, t23⟩ := t123
    obtain ⟨t2, t3⟩ := t23
    have ht0 : t0 ⊆ para 0 ∧ t0.ncard = n0 := hp.1
    have ht1 : t1 ⊆ para 1 ∧ t1.ncard = n1 := hp.2.1
    have ht2 : t2 ⊆ para 2 ∧ t2.ncard = n2 := hp.2.2.1
    have ht3 : t3 ⊆ para 3 ∧ t3.ncard = n3 := hp.2.2.2
    refine ⟨t0 ∪ t1 ∪ t2 ∪ t3, ?_, ?_⟩
    · have h0 := inter_union_para ht0.1 ht1.1 ht2.1 ht3.1 0
      have h1 := inter_union_para ht0.1 ht1.1 ht2.1 ht3.1 1
      have h2 := inter_union_para ht0.1 ht1.1 ht2.1 ht3.1 2
      have h3 := inter_union_para ht0.1 ht1.1 ht2.1 ht3.1 3
      simp at h0 h1 h2 h3
      simp [typed, h0, h1, h2, h3, ht0.2, ht1.2, ht2.2, ht3.2]
    · have h0 := inter_union_para ht0.1 ht1.1 ht2.1 ht3.1 0
      have h1 := inter_union_para ht0.1 ht1.1 ht2.1 ht3.1 1
      have h2 := inter_union_para ht0.1 ht1.1 ht2.1 ht3.1 2
      have h3 := inter_union_para ht0.1 ht1.1 ht2.1 ht3.1 3
      simp at h0 h1 h2 h3
      rw [h0, h1, h2, h3]

lemma typed_ncard {S : Set (Fin 79)} {n0 n1 n2 n3 : ℕ}
    (h : S ∈ typed n0 n1 n2 n3) :
    S.ncard = n0 + n1 + n2 + n3 := by
  rw [ncard_sum_parts, h.1, h.2.1, h.2.2.1, h.2.2.2]

lemma typed_supp {S : Set (Fin 79)} {n0 n1 n2 n3 : ℕ}
    (h : S ∈ typed n0 n1 n2 n3) :
    supp S = {i : Fin 4 | (if i = 0 then n0 else if i = 1 then n1 else if i = 2 then n2 else n3) > 0} := by
  ext i
  simp only [supp, mem_setOf]
  fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]

lemma ncard_fin4_setOf (p : Fin 4 → Prop) [DecidablePred p] :
    {i : Fin 4 | p i}.ncard =
      (if p 0 then 1 else 0) + (if p 1 then 1 else 0) +
      (if p 2 then 1 else 0) + (if p 3 then 1 else 0) := by
  have : {i : Fin 4 | p i} = ((Finset.univ.filter p : Finset (Fin 4)) : Set (Fin 4)) := by
    ext i; simp
  have hU : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  rw [this, ncard_coe_finset, hU]
  simp [Finset.filter_insert, Finset.filter_singleton]
  split_ifs <;> simp

lemma typed_supp_ncard {S : Set (Fin 79)} {n0 n1 n2 n3 : ℕ}
    (h : S ∈ typed n0 n1 n2 n3) :
    (supp S).ncard =
      (if n0 = 0 then 0 else 1) + (if n1 = 0 then 0 else 1) +
      (if n2 = 0 then 0 else 1) + (if n3 = 0 then 0 else 1) := by
  rw [typed_supp h, ncard_fin4_setOf]
  simp [Nat.pos_iff_ne_zero]

lemma typed_cyclic {S : Set (Fin 79)} {n0 n1 n2 n3 : ℕ}
    (h : S ∈ typed n0 n1 n2 n3) :
    IsCyclic thetaDual S ↔
      (n0 ≠ 1 ∧ n1 ≠ 1 ∧ n2 ≠ 1 ∧ n3 ≠ 1) ∨ (0 < n0 ∧ 0 < n1 ∧ 0 < n2 ∧ 0 < n3) := by
  rw [thetaDual_isCyclic_iff]
  constructor
  · intro hc
    rcases hc with hsing | huniv
    · refine Or.inl ⟨?_, ?_, ?_, ?_⟩
      · exact h.1 ▸ hsing 0
      · exact h.2.1 ▸ hsing 1
      · exact h.2.2.1 ▸ hsing 2
      · exact h.2.2.2 ▸ hsing 3
    · have hall : ∀ i, i ∈ supp S := by intro i; simp [huniv]
      refine Or.inr ⟨?_, ?_, ?_, ?_⟩
      · have hne : (S ∩ para 0).Nonempty := mem_supp.1 (hall 0)
        have := (ncard_pos (toFinite _)).2 hne
        simpa [h.1] using this
      · have hne : (S ∩ para 1).Nonempty := mem_supp.1 (hall 1)
        have := (ncard_pos (toFinite _)).2 hne
        simpa [h.2.1] using this
      · have hne : (S ∩ para 2).Nonempty := mem_supp.1 (hall 2)
        have := (ncard_pos (toFinite _)).2 hne
        simpa [h.2.2.1] using this
      · have hne : (S ∩ para 3).Nonempty := mem_supp.1 (hall 3)
        have := (ncard_pos (toFinite _)).2 hne
        simpa [h.2.2.2] using this
  · intro hc
    rcases hc with hsing | hpos
    · exact Or.inl fun i => by
        fin_cases i <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2, hsing]
    · refine Or.inr (eq_univ_iff_forall.2 fun i => ?_)
      fin_cases i <;> simp [supp, h.1, h.2.1, h.2.2.1, h.2.2.2, hpos]

lemma typed_disjoint {n0 n1 n2 n3 m0 m1 m2 m3 : ℕ}
    (h : n0 ≠ m0 ∨ n1 ≠ m1 ∨ n2 ≠ m2 ∨ n3 ≠ m3) :
    Disjoint (typed n0 n1 n2 n3) (typed m0 m1 m2 m3) := by
  rw [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
  intro S hS
  rcases h with h | h | h | h
  · exact h (hS.1.1.symm.trans hS.2.1)
  · exact h (hS.1.2.1.symm.trans hS.2.2.1)
  · exact h (hS.1.2.2.1.symm.trans hS.2.2.2.1)
  · exact h (hS.1.2.2.2.symm.trans hS.2.2.2.2)

lemma ncard_union4 {α : Type*} [Finite α] {s t u v : Set α}
    (hst : Disjoint s t) (hsu : Disjoint s u) (hsv : Disjoint s v)
    (htu : Disjoint t u) (htv : Disjoint t v) (huv : Disjoint u v) :
    (s ∪ t ∪ u ∪ v).ncard = s.ncard + t.ncard + u.ncard + v.ncard := by
  have d1 : Disjoint (s ∪ t) u := disjoint_union_left.2 ⟨hsu, htu⟩
  have d2 : Disjoint (s ∪ t ∪ u) v :=
    disjoint_union_left.2 ⟨disjoint_union_left.2 ⟨hsv, htv⟩, huv⟩
  rw [ncard_union_eq d2, ncard_union_eq d1, ncard_union_eq hst]

lemma three_nat_null_one {n1 n2 n3 : ℕ}
    (hn1 : n1 ≠ 1) (hn2 : n2 ≠ 1) (hn3 : n3 ≠ 1)
    (hs : n1 + n2 + n3 =
      min 3 ((if n1 = 0 then 0 else 1) + (if n2 = 0 then 0 else 1) +
        (if n3 = 0 then 0 else 1)) + 1) :
    (n1 = 2 ∧ n2 = 0 ∧ n3 = 0) ∨ (n1 = 0 ∧ n2 = 2 ∧ n3 = 0) ∨
      (n1 = 0 ∧ n2 = 0 ∧ n3 = 2) := by
  by_cases h1 : n1 = 0 <;> by_cases h2 : n2 = 0 <;> by_cases h3 : n3 = 0 <;>
    simp [h1, h2, h3] at hn1 hn2 hn3 hs ⊢ <;> omega

/-! ### Nullity 1: W_75 -/

lemma cyclic_null_one :
    {S : Set (Fin 79) | IsCyclic thetaDual S ∧ S.ncard = min 3 (supp S).ncard + 1} =
      typed 0 2 0 0 ∪ typed 0 0 2 0 ∪ typed 0 0 0 2 ∪ typed 1 1 1 1 := by
  ext S
  constructor
  · intro h
    have hty : S ∈ typed (S ∩ para 0).ncard (S ∩ para 1).ncard
        (S ∩ para 2).ncard (S ∩ para 3).ncard := ⟨rfl, rfl, rfl, rfl⟩
    set n0 := (S ∩ para 0).ncard with hn0d
    set n1 := (S ∩ para 1).ncard with hn1d
    set n2 := (S ∩ para 2).ncard with hn2d
    set n3 := (S ∩ para 3).ncard with hn3d
    have hsum : n0 + n1 + n2 + n3 = min 3 (supp S).ncard + 1 := by
      simpa [typed_ncard hty] using h.2
    have hkn := typed_supp_ncard hty
    have hcyc := (typed_cyclic hty).1 h.1
    have hn0le : n0 ≤ 1 := by
      have : n0 ≤ (para 0).ncard := ncard_le_ncard inter_subset_right
      simpa [ncard_para_zero] using this
    cases Nat.eq_zero_or_pos n0 with
    | inl h0 =>
      have hsing : n0 ≠ 1 ∧ n1 ≠ 1 ∧ n2 ≠ 1 ∧ n3 ≠ 1 := by
        rcases hcyc with h | hpos
        · exact h
        · exact (Nat.not_lt_zero _ (h0 ▸ hpos.1)).elim
      have hk : (supp S).ncard =
          (if n1 = 0 then 0 else 1) + (if n2 = 0 then 0 else 1) +
          (if n3 = 0 then 0 else 1) := by simpa [h0] using hkn
      have hsum' : n1 + n2 + n3 = min 3 (supp S).ncard + 1 := by
        rw [h0] at hsum; omega
      have : (n1 = 2 ∧ n2 = 0 ∧ n3 = 0) ∨ (n1 = 0 ∧ n2 = 2 ∧ n3 = 0) ∨
          (n1 = 0 ∧ n2 = 0 ∧ n3 = 2) := by
        refine three_nat_null_one hsing.2.1 hsing.2.2.1 hsing.2.2.2 ?_
        simpa [hk] using hsum'
      rcases this with h' | h' | h'
      · exact Or.inl (Or.inl (Or.inl (by simpa [typed, h0, h'] using hty)))
      · exact Or.inl (Or.inl (Or.inr (by simpa [typed, h0, h'] using hty)))
      · exact Or.inl (Or.inr (by simpa [typed, h0, h'] using hty))
    | inr h0 =>
      have hpos : 0 < n0 ∧ 0 < n1 ∧ 0 < n2 ∧ 0 < n3 := by
        rcases hcyc with hsing | hpos
        · have : n0 = 1 := by omega
          exact absurd this hsing.1
        · exact hpos
      have hn0z : n0 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.1
      have hn1z : n1 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.2.1
      have hn2z : n2 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.2.2.1
      have hn3z : n3 ≠ 0 := Nat.pos_iff_ne_zero.1 hpos.2.2.2
      have : (supp S).ncard = 4 := by simpa [hkn, hn0z, hn1z, hn2z, hn3z]
      have : n0 + n1 + n2 + n3 = 4 := by simp [this] at hsum; exact hsum
      have : n0 = 1 ∧ n1 = 1 ∧ n2 = 1 ∧ n3 = 1 := by omega
      exact Or.inr (by simpa [typed, this] using hty)
  · intro h
    cases h with
    | inl h =>
      cases h with
      | inl h =>
        cases h with
        | inl h =>
          have hc := (typed_cyclic h).2 (Or.inl ⟨by decide, by decide, by decide, by decide⟩)
          have hs : (supp S).ncard = 1 := by simpa using typed_supp_ncard h
          have hn : S.ncard = 2 := by simpa using typed_ncard h
          exact ⟨hc, by simp [hn, hs]⟩
        | inr h =>
          have hc := (typed_cyclic h).2 (Or.inl ⟨by decide, by decide, by decide, by decide⟩)
          have hs : (supp S).ncard = 1 := by simpa using typed_supp_ncard h
          have hn : S.ncard = 2 := by simpa using typed_ncard h
          exact ⟨hc, by simp [hn, hs]⟩
      | inr h =>
        have hc := (typed_cyclic h).2 (Or.inl ⟨by decide, by decide, by decide, by decide⟩)
        have hs : (supp S).ncard = 1 := by simpa using typed_supp_ncard h
        have hn : S.ncard = 2 := by simpa using typed_ncard h
        exact ⟨hc, by simp [hn, hs]⟩
    | inr h =>
      have hc := (typed_cyclic h).2 (Or.inr ⟨by decide, by decide, by decide, by decide⟩)
      have hs : (supp S).ncard = 4 := by simpa using typed_supp_ncard h
      have hn : S.ncard = 4 := by simpa using typed_ncard h
      exact ⟨hc, by simp [hn, hs]⟩

lemma ncard_cyclic_null_one :
    {S : Set (Fin 79) | IsCyclic thetaDual S ∧ S.ncard = min 3 (supp S).ncard + 1}.ncard =
      3 * Nat.choose 26 2 + 26 ^ 3 := by
  rw [cyclic_null_one]
  have d01 := typed_disjoint (n0 := 0) (n1 := 2) (n2 := 0) (n3 := 0)
    (m0 := 0) (m1 := 0) (m2 := 2) (m3 := 0) (Or.inr (Or.inl (by decide : (2 : ℕ) ≠ 0)))
  have d02 := typed_disjoint (n0 := 0) (n1 := 2) (n2 := 0) (n3 := 0)
    (m0 := 0) (m1 := 0) (m2 := 0) (m3 := 2) (Or.inr (Or.inl (by decide : (2 : ℕ) ≠ 0)))
  have d03 := typed_disjoint (n0 := 0) (n1 := 2) (n2 := 0) (n3 := 0)
    (m0 := 1) (m1 := 1) (m2 := 1) (m3 := 1) (Or.inl (by decide : (0 : ℕ) ≠ 1))
  have d12 := typed_disjoint (n0 := 0) (n1 := 0) (n2 := 2) (n3 := 0)
    (m0 := 0) (m1 := 0) (m2 := 0) (m3 := 2) (Or.inr (Or.inr (Or.inl (by decide : (2 : ℕ) ≠ 0))))
  have d13 := typed_disjoint (n0 := 0) (n1 := 0) (n2 := 2) (n3 := 0)
    (m0 := 1) (m1 := 1) (m2 := 1) (m3 := 1) (Or.inl (by decide : (0 : ℕ) ≠ 1))
  have d23 := typed_disjoint (n0 := 0) (n1 := 0) (n2 := 0) (n3 := 2)
    (m0 := 1) (m1 := 1) (m2 := 1) (m3 := 1) (Or.inl (by decide : (0 : ℕ) ≠ 1))
  rw [ncard_union4 d01 d02 d03 d12 d13 d23]
  simp [ncard_typed, Nat.choose_one_right, Nat.choose_zero_right]
  ring

lemma cyclic_of_typed {S : Set (Fin 79)} {n0 n1 n2 n3 i : ℕ}
    (h : S ∈ typed n0 n1 n2 n3)
    (hcy : (n0 ≠ 1 ∧ n1 ≠ 1 ∧ n2 ≠ 1 ∧ n3 ≠ 1) ∨
      (0 < n0 ∧ 0 < n1 ∧ 0 < n2 ∧ 0 < n3))
    (hi : n0 + n1 + n2 + n3 =
      min 3 ((if n0 = 0 then 0 else 1) + (if n1 = 0 then 0 else 1) +
        (if n2 = 0 then 0 else 1) + (if n3 = 0 then 0 else 1)) + i) :
    IsCyclic thetaDual S ∧ S.ncard = min 3 (supp S).ncard + i :=
  ⟨(typed_cyclic h).2 hcy, by rw [typed_ncard h, typed_supp_ncard h, hi]⟩

lemma three_nat_null_two {n1 n2 n3 : ℕ}
    (hn1 : n1 ≠ 1) (hn2 : n2 ≠ 1) (hn3 : n3 ≠ 1)
    (hs : n1 + n2 + n3 =
      min 3 ((if n1 = 0 then 0 else 1) + (if n2 = 0 then 0 else 1) +
        (if n3 = 0 then 0 else 1)) + 2) :
    (n1 = 3 ∧ n2 = 0 ∧ n3 = 0) ∨ (n1 = 0 ∧ n2 = 3 ∧ n3 = 0) ∨
      (n1 = 0 ∧ n2 = 0 ∧ n3 = 3) ∨ (n1 = 2 ∧ n2 = 2 ∧ n3 = 0) ∨
      (n1 = 2 ∧ n2 = 0 ∧ n3 = 2) ∨ (n1 = 0 ∧ n2 = 2 ∧ n3 = 2) := by
  by_cases h1 : n1 = 0 <;> by_cases h2 : n2 = 0 <;> by_cases h3 : n3 = 0 <;>
    simp [h1, h2, h3] at hn1 hn2 hn3 hs ⊢ <;> omega

lemma three_nat_null_three {n1 n2 n3 : ℕ}
    (hn1 : n1 ≠ 1) (hn2 : n2 ≠ 1) (hn3 : n3 ≠ 1)
    (hs : n1 + n2 + n3 =
      min 3 ((if n1 = 0 then 0 else 1) + (if n2 = 0 then 0 else 1) +
        (if n3 = 0 then 0 else 1)) + 3) :
    (n1 = 4 ∧ n2 = 0 ∧ n3 = 0) ∨ (n1 = 0 ∧ n2 = 4 ∧ n3 = 0) ∨
      (n1 = 0 ∧ n2 = 0 ∧ n3 = 4) ∨ (n1 = 3 ∧ n2 = 2 ∧ n3 = 0) ∨
      (n1 = 3 ∧ n2 = 0 ∧ n3 = 2) ∨ (n1 = 2 ∧ n2 = 3 ∧ n3 = 0) ∨
      (n1 = 0 ∧ n2 = 3 ∧ n3 = 2) ∨ (n1 = 2 ∧ n2 = 0 ∧ n3 = 3) ∨
      (n1 = 0 ∧ n2 = 2 ∧ n3 = 3) ∨ (n1 = 2 ∧ n2 = 2 ∧ n3 = 2) := by
  by_cases h1 : n1 = 0 <;> by_cases h2 : n2 = 0 <;> by_cases h3 : n3 = 0 <;>
    simp [h1, h2, h3] at hn1 hn2 hn3 hs ⊢ <;> omega

lemma pos_three_sum {n1 n2 n3 : ℕ} (h1 : 0 < n1) (h2 : 0 < n2) (h3 : 0 < n3)
    (hs : n1 + n2 + n3 = 4) :
    (n1 = 2 ∧ n2 = 1 ∧ n3 = 1) ∨ (n1 = 1 ∧ n2 = 2 ∧ n3 = 1) ∨
      (n1 = 1 ∧ n2 = 1 ∧ n3 = 2) := by omega

lemma pos_three_sum_five {n1 n2 n3 : ℕ} (h1 : 0 < n1) (h2 : 0 < n2) (h3 : 0 < n3)
    (hs : n1 + n2 + n3 = 5) :
    (n1 = 3 ∧ n2 = 1 ∧ n3 = 1) ∨ (n1 = 1 ∧ n2 = 3 ∧ n3 = 1) ∨
      (n1 = 1 ∧ n2 = 1 ∧ n3 = 3) ∨ (n1 = 2 ∧ n2 = 2 ∧ n3 = 1) ∨
      (n1 = 2 ∧ n2 = 1 ∧ n3 = 2) ∨ (n1 = 1 ∧ n2 = 2 ∧ n3 = 2) := by omega

lemma whitney_75 :
    whitneySecond theta 75 = 3 * Nat.choose 26 2 + 26 ^ 3 := by
  rw [whitney_eq_cyclic 1 (by decide), ncard_cyclic_null_one]

end MasonFlats
