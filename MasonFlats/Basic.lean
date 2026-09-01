/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Dual
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.FinCases

/-!
The dual `thetaDual` of Larson’s generalized-theta graphic matroid: a rank-3
matroid on `Fin 79` whose simplification is `U_{3,4}`, with parallel classes
of sizes `1, 26, 26, 26`.
-/

open Set Matroid

namespace MasonFlats

open scoped Classical

/-- Parallel-class index: `0` is the singleton class; `1,2,3` have size 26. -/
def cls (e : Fin 79) : Fin 4 :=
  if h : e = 0 then 0
  else ⟨(e.val - 1) / 26 + 1, by
    have hne : e.val ≠ 0 := Fin.val_ne_of_ne h
    have h1 : 1 ≤ e.val := Nat.one_le_iff_ne_zero.mpr hne
    have h78 : e.val ≤ 78 := Nat.lt_succ_iff.mp e.isLt
    have hlt : e.val - 1 < 78 := Nat.sub_lt_left_of_lt_add h1 (Nat.lt_succ_iff.mpr h78)
    have hdiv : (e.val - 1) / 26 < 3 :=
      (Nat.div_lt_iff_lt_mul (by decide : 0 < 26)).2 (by
        simpa [show 3 * 26 = 78 from rfl] using hlt)
    exact Nat.add_lt_add_right hdiv 1⟩

lemma cls_zero : cls 0 = 0 := dif_pos rfl

lemma cls_eq_zero_iff {e : Fin 79} : cls e = 0 ↔ e = 0 := by
  by_cases h : e = 0
  · simp [cls, h]
  · simp [cls, h, Fin.ext_iff]

lemma cls_of_ne_zero {e : Fin 79} (h : e ≠ 0) :
    (cls e).val = (e.val - 1) / 26 + 1 := by
  simp [cls, h]

lemma cls_eq_one_iff {e : Fin 79} : cls e = 1 ↔ 1 ≤ e.val ∧ e.val ≤ 26 := by
  by_cases h : e = 0
  · subst e; simp [cls_zero]
  · have hval := cls_of_ne_zero h
    have hne : e.val ≠ 0 := Fin.val_ne_of_ne h
    constructor
    · intro heq
      have hv : (e.val - 1) / 26 + 1 = 1 := by
        simpa [hval] using congrArg Fin.val heq
      have hdiv : (e.val - 1) / 26 = 0 := Nat.succ_injective hv
      have : e.val - 1 < 26 := (Nat.div_eq_zero_iff.1 hdiv).resolve_left (by decide)
      omega
    · intro hle
      apply Fin.ext
      have hdiv : (e.val - 1) / 26 = 0 := Nat.div_eq_of_lt (by omega)
      simpa [hval, hdiv]

lemma cls_eq_two_iff {e : Fin 79} : cls e = 2 ↔ 27 ≤ e.val ∧ e.val ≤ 52 := by
  by_cases h : e = 0
  · subst e; simp [cls_zero]
  · have hval := cls_of_ne_zero h
    constructor
    · intro heq
      have hv : (e.val - 1) / 26 + 1 = 2 := by
        simpa [hval] using congrArg Fin.val heq
      have hdiv : (e.val - 1) / 26 = 1 := Nat.succ_injective hv
      have hlo : 26 ≤ e.val - 1 :=
        (Nat.le_div_iff_mul_le (by decide : 0 < 26)).1 (le_of_eq hdiv.symm)
      have hhi : e.val - 1 < 52 :=
        (Nat.div_lt_iff_lt_mul (by decide : 0 < 26)).1 (hdiv.symm ▸ (by decide : (1 : ℕ) < 2))
      omega
    · intro hle
      apply Fin.ext
      have hdiv : (e.val - 1) / 26 = 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      simpa [hval, hdiv]

lemma cls_eq_three_iff {e : Fin 79} : cls e = 3 ↔ 53 ≤ e.val ∧ e.val ≤ 78 := by
  by_cases h : e = 0
  · subst e; simp [cls_zero]
  · have hval := cls_of_ne_zero h
    have h78 : e.val ≤ 78 := Nat.lt_succ_iff.mp e.isLt
    constructor
    · intro heq
      have hv : (e.val - 1) / 26 + 1 = 3 := by
        simpa [hval] using congrArg Fin.val heq
      have hdiv : (e.val - 1) / 26 = 2 := Nat.succ_injective hv
      have hlo : 52 ≤ e.val - 1 :=
        (Nat.le_div_iff_mul_le (by decide : 0 < 26)).1 (le_of_eq hdiv.symm)
      have hhi : e.val - 1 < 78 :=
        (Nat.div_lt_iff_lt_mul (by decide : 0 < 26)).1 (hdiv.symm ▸ (by decide : (2 : ℕ) < 3))
      omega
    · intro hle
      apply Fin.ext
      have hdiv : (e.val - 1) / 26 = 2 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      simpa [hval, hdiv]

/-- The four parallel classes. -/
def para (i : Fin 4) : Set (Fin 79) := {e | cls e = i}

lemma mem_para {e : Fin 79} {i : Fin 4} : e ∈ para i ↔ cls e = i := Iff.rfl

lemma para_zero : para 0 = {0} := by
  ext e; simp [para, cls_eq_zero_iff]

lemma ncard_val_Icc {a b : ℕ} (hb : b < 79) (_hab : a ≤ b) :
    {e : Fin 79 | a ≤ e.val ∧ e.val ≤ b}.ncard = b + 1 - a := by
  refine (ncard_congr (t := {n : ℕ | a ≤ n ∧ n ≤ b}) (fun e _ => e.val)
      (fun _ he => he)
      (fun e₁ e₂ _ _ h => Fin.ext h)
      (fun n hn => ⟨⟨n, lt_of_le_of_lt hn.2 hb⟩, hn, rfl⟩)).trans ?_
  simpa [Set.Icc] using ncard_Icc_nat a b

lemma para_one : para 1 = {e : Fin 79 | 1 ≤ e.val ∧ e.val ≤ 26} := by
  ext e; simp [para, cls_eq_one_iff]

lemma para_two : para 2 = {e : Fin 79 | 27 ≤ e.val ∧ e.val ≤ 52} := by
  ext e; simp [para, cls_eq_two_iff]

lemma para_three : para 3 = {e : Fin 79 | 53 ≤ e.val ∧ e.val ≤ 78} := by
  ext e; simp [para, cls_eq_three_iff]

lemma ncard_para_zero : (para 0).ncard = 1 := by
  rw [para_zero, ncard_singleton]

lemma ncard_para_one : (para 1).ncard = 26 := by
  rw [para_one, ncard_val_Icc (by decide) (by decide)]

lemma ncard_para_two : (para 2).ncard = 26 := by
  rw [para_two, ncard_val_Icc (by decide) (by decide)]

lemma ncard_para_three : (para 3).ncard = 26 := by
  rw [para_three, ncard_val_Icc (by decide) (by decide)]

lemma ncard_para (i : Fin 4) : (para i).ncard = if i = 0 then 1 else 26 := by
  fin_cases i <;> simp [ncard_para_zero, ncard_para_one, ncard_para_two, ncard_para_three]

lemma para_disjoint {i j : Fin 4} (h : i ≠ j) : Disjoint (para i) (para j) := by
  rw [Set.disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem]
  intro e he
  exact h ((mem_para.1 he.1).symm.trans (mem_para.1 he.2))

lemma cls_val_cases (e : Fin 79) :
    cls e = 0 ∨ cls e = 1 ∨ cls e = 2 ∨ cls e = 3 := by
  have hlt : (cls e).val < 4 := (cls e).isLt
  have hv : (cls e).val = 0 ∨ (cls e).val = 1 ∨ (cls e).val = 2 ∨ (cls e).val = 3 := by
    omega
  rcases hv with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

lemma eq_union_parts (S : Set (Fin 79)) :
    S = (S ∩ para 0) ∪ (S ∩ para 1) ∪ (S ∩ para 2) ∪ (S ∩ para 3) := by
  ext e
  constructor
  · intro he
    rcases cls_val_cases e with h | h | h | h
    · exact Or.inl <| Or.inl <| Or.inl ⟨he, h⟩
    · exact Or.inl <| Or.inl <| Or.inr ⟨he, h⟩
    · exact Or.inl <| Or.inr ⟨he, h⟩
    · exact Or.inr ⟨he, h⟩
  · intro he
    rcases he with (((h | h) | h) | h) <;> exact h.1

lemma ncard_sum_parts (S : Set (Fin 79)) :
    S.ncard =
      (S ∩ para 0).ncard + (S ∩ para 1).ncard +
      (S ∩ para 2).ncard + (S ∩ para 3).ncard := by
  have d01 : Disjoint (S ∩ para 0) (S ∩ para 1) :=
    (para_disjoint (by decide : (0 : Fin 4) ≠ 1)).mono inter_subset_right inter_subset_right
  have d2 : Disjoint ((S ∩ para 0) ∪ (S ∩ para 1)) (S ∩ para 2) :=
    disjoint_union_left.2
      ⟨(para_disjoint (by decide : (0 : Fin 4) ≠ 2)).mono inter_subset_right inter_subset_right,
        (para_disjoint (by decide : (1 : Fin 4) ≠ 2)).mono inter_subset_right inter_subset_right⟩
  have d3 : Disjoint ((S ∩ para 0) ∪ (S ∩ para 1) ∪ (S ∩ para 2)) (S ∩ para 3) :=
    disjoint_union_left.2
      ⟨disjoint_union_left.2
        ⟨(para_disjoint (by decide : (0 : Fin 4) ≠ 3)).mono inter_subset_right inter_subset_right,
          (para_disjoint (by decide : (1 : Fin 4) ≠ 3)).mono inter_subset_right inter_subset_right⟩,
        (para_disjoint (by decide : (2 : Fin 4) ≠ 3)).mono inter_subset_right inter_subset_right⟩
  nth_rw 1 [eq_union_parts S]
  rw [ncard_union_eq d3, ncard_union_eq d2, ncard_union_eq d01]

/-- Independence in the rank-3 parallel extension of `U_{3,4}`. -/
def thetaIndep (I : Set (Fin 79)) : Prop :=
  I.ncard ≤ 3 ∧ InjOn cls I

lemma thetaIndep_empty : thetaIndep (∅ : Set (Fin 79)) :=
  ⟨by simp, injOn_empty _⟩

lemma thetaIndep_subset {I J : Set (Fin 79)} (hJ : thetaIndep J) (hIJ : I ⊆ J) :
    thetaIndep I :=
  ⟨(ncard_le_ncard hIJ).trans hJ.1, hJ.2.mono hIJ⟩

lemma thetaIndep_aug {I J : Set (Fin 79)} (hI : thetaIndep I) (hJ : thetaIndep J)
    (hlt : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ thetaIndep (insert e I) := by
  have hlt' : (cls '' I).ncard < (cls '' J).ncard := by
    rwa [hI.2.ncard_image, hJ.2.ncard_image]
  have : ¬ cls '' J ⊆ cls '' I := fun hsub => (ncard_le_ncard hsub).not_gt hlt'
  obtain ⟨c, hcJ, hcI⟩ := not_subset.1 this
  obtain ⟨e, heJ, rfl⟩ := hcJ
  have heI : e ∉ I := fun heI => hcI ⟨e, heI, rfl⟩
  refine ⟨e, heJ, heI, ?_⟩
  constructor
  · rw [ncard_insert_of_notMem heI]
    exact (Nat.succ_le_of_lt hlt).trans hJ.1
  · rw [injOn_insert heI]
    exact ⟨hI.2, hcI⟩

/-- Larson’s dual: rank 3 on 79 elements, parallel classes of sizes 1,26,26,26. -/
def thetaDual : Matroid (Fin 79) :=
  (IndepMatroid.ofFinite
    (E := (univ : Set (Fin 79)))
    (hE := finite_univ)
    (Indep := thetaIndep)
    (indep_empty := thetaIndep_empty)
    (indep_subset := fun _ _ => thetaIndep_subset)
    (indep_aug := fun _ _ => thetaIndep_aug)
    (subset_ground := fun _ _ => subset_univ _)).matroid

/-- The rank-76 dual of `thetaDual`. -/
def theta : Matroid (Fin 79) := thetaDual✶

@[simp] lemma thetaDual_indep {I : Set (Fin 79)} :
    thetaDual.Indep I ↔ thetaIndep I := Iff.rfl

@[simp] lemma thetaDual_E : thetaDual.E = univ := rfl

@[simp] lemma theta_E : theta.E = univ := rfl

lemma injOn_ncard_le_four {I : Set (Fin 79)} (h : InjOn cls I) : I.ncard ≤ 4 := by
  rw [← h.ncard_image]
  exact (ncard_le_ncard (subset_univ _)).trans (by simp [ncard_univ])

lemma thetaDual_dep_iff {D : Set (Fin 79)} :
    thetaDual.Dep D ↔ 3 < D.ncard ∨ ¬ InjOn cls D := by
  constructor
  · intro h
    have : ¬ (D.ncard ≤ 3 ∧ InjOn cls D) := by
      simpa [thetaIndep] using h.not_indep
    rcases not_and_or.1 this with h | h
    · exact Or.inl (Nat.not_le.1 h)
    · exact Or.inr h
  · intro h
    refine ⟨fun hI => ?_, subset_univ _⟩
    rcases h with h | h
    · exact h.not_ge hI.1
    · exact h hI.2

lemma exists_ne_of_not_injOn {I : Set (Fin 79)} (h : ¬ InjOn cls I) :
    ∃ e ∈ I, ∃ f ∈ I, e ≠ f ∧ cls e = cls f := by
  simp only [InjOn, not_forall] at h
  obtain ⟨e, he, f, hf, heq, hne⟩ := h
  exact ⟨e, he, f, hf, hne, heq⟩

lemma pair_dep {e f : Fin 79} (hne : e ≠ f) (hcls : cls e = cls f) :
    thetaDual.Dep {e, f} :=
  thetaDual_dep_iff.2 (Or.inr fun h => hne (h (by simp) (by simp) hcls))

lemma thetaDual_isCircuit_iff {C : Set (Fin 79)} :
    thetaDual.IsCircuit C ↔
      (C.ncard = 2 ∧ ∃ i, C ⊆ para i) ∨ (C.ncard = 4 ∧ InjOn cls C) := by
  constructor
  · intro hC
    rcases thetaDual_dep_iff.1 hC.dep with hcard | hinj
    · have hinj : InjOn cls C := by
        by_contra hnot
        obtain ⟨e, he, f, hf, hne, heq⟩ := exists_ne_of_not_injOn hnot
        have heqC := hC.eq_of_dep_subset (pair_dep hne heq) (pair_subset he hf)
        have : C.ncard = 2 := heqC ▸ ncard_pair hne
        omega
      have : C.ncard ≤ 4 := injOn_ncard_le_four hinj
      exact Or.inr ⟨by omega, hinj⟩
    · obtain ⟨e, he, f, hf, hne, heq⟩ := exists_ne_of_not_injOn hinj
      have heqC := hC.eq_of_dep_subset (pair_dep hne heq) (pair_subset he hf)
      refine Or.inl ⟨heqC ▸ ncard_pair hne, ⟨cls e, ?_⟩⟩
      intro x hx
      have hx' : x = e ∨ x = f := by simpa [← heqC] using hx
      rcases hx' with rfl | rfl
      · rfl
      · exact heq.symm
  · rintro (⟨h2, i, hsub⟩ | ⟨h4, hinj⟩)
    · obtain ⟨e, f, hne, rfl⟩ := ncard_eq_two.1 h2
      have hcls : cls e = cls f :=
        (hsub (by simp : e ∈ ({e, f} : Set (Fin 79)))).trans
          (hsub (by simp : f ∈ ({e, f} : Set (Fin 79)))).symm
      refine isCircuit_iff_forall_ssubset.2 ⟨pair_dep hne hcls, fun I hI => ?_⟩
      have hle : I.ncard ≤ 1 := by
        have := ncard_lt_ncard hI
        omega
      exact ⟨hle.trans (by decide),
        fun x hx y hy _ => (ncard_le_one_iff_subsingleton.1 hle) hx hy⟩
    · refine isCircuit_iff_forall_ssubset.2 ⟨?_, fun I hI => ?_⟩
      · exact thetaDual_dep_iff.2 (Or.inl (by omega))
      · have : I.ncard < 4 := h4 ▸ ncard_lt_ncard hI
        exact ⟨Nat.lt_succ_iff.mp this, hinj.mono hI.subset⟩

/-- Classes met by `S`. -/
def supp (S : Set (Fin 79)) : Set (Fin 4) := {i | 0 < (S ∩ para i).ncard}

lemma mem_supp {S : Set (Fin 79)} {i : Fin 4} :
    i ∈ supp S ↔ (S ∩ para i).Nonempty := by
  simp only [supp, mem_setOf_eq]
  exact ncard_pos

lemma supp_eq_image (S : Set (Fin 79)) : supp S = cls '' S := by
  ext i
  constructor
  · intro hi
    obtain ⟨e, he⟩ := mem_supp.1 hi
    exact ⟨e, he.1, he.2⟩
  · intro hi
    obtain ⟨e, heS, rfl⟩ := hi
    exact mem_supp.2 ⟨e, heS, rfl⟩

lemma supp_ncard_le (S : Set (Fin 79)) : (supp S).ncard ≤ 4 :=
  (ncard_le_ncard (subset_univ _)).trans (by simp [ncard_univ])

/-- A representative of class `i` in `S`, junk if the class is empty. -/
noncomputable def chooseIn (S : Set (Fin 79)) (i : Fin 4) : Fin 79 :=
  Classical.epsilon fun e : Fin 79 => e ∈ S ∩ para i

lemma chooseIn_mem {S : Set (Fin 79)} {i : Fin 4} (h : i ∈ supp S) :
    chooseIn S i ∈ S ∩ para i :=
  Classical.epsilon_spec (p := fun e : Fin 79 => e ∈ S ∩ para i) (mem_supp.1 h)

lemma chooseIn_cls {S : Set (Fin 79)} {i : Fin 4} (h : i ∈ supp S) :
    cls (chooseIn S i) = i :=
  (chooseIn_mem h).2

lemma chooseIn_mem_S {S : Set (Fin 79)} {i : Fin 4} (h : i ∈ supp S) :
    chooseIn S i ∈ S :=
  (chooseIn_mem h).1

def p1 : Fin 79 := ⟨1, by decide⟩
def p2 : Fin 79 := ⟨27, by decide⟩
def p3 : Fin 79 := ⟨53, by decide⟩

lemma cls_p1 : cls p1 = 1 := cls_eq_one_iff.2 ⟨by decide, by decide⟩
lemma cls_p2 : cls p2 = 2 := cls_eq_two_iff.2 ⟨by decide, by decide⟩
lemma cls_p3 : cls p3 = 3 := cls_eq_three_iff.2 ⟨by decide, by decide⟩

lemma thetaDual_eRank : thetaDual.eRank = 3 := by
  let I : Set (Fin 79) := {p1, p2, p3}
  have hne12 : p1 ≠ p2 := by decide
  have hne13 : p1 ≠ p3 := by decide
  have hne23 : p2 ≠ p3 := by decide
  have hcard : I.ncard = 3 := by
    simp [I, ncard_insert_of_notMem, ncard_singleton, hne12, hne13, hne23]
  have hI : thetaDual.Indep I := by
    refine ⟨le_of_eq hcard, ?_⟩
    intro x hx y hy hxy
    simp [I] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · rfl
    · exact absurd (cls_p1.symm.trans (hxy.trans cls_p2)) (by decide)
    · exact absurd (cls_p1.symm.trans (hxy.trans cls_p3)) (by decide)
    · exact absurd (cls_p2.symm.trans (hxy.trans cls_p1)) (by decide)
    · rfl
    · exact absurd (cls_p2.symm.trans (hxy.trans cls_p3)) (by decide)
    · exact absurd (cls_p3.symm.trans (hxy.trans cls_p1)) (by decide)
    · exact absurd (cls_p3.symm.trans (hxy.trans cls_p2)) (by decide)
    · rfl
  have hB : thetaDual.IsBase I :=
    hI.isBase_of_maximal fun J hJ hIJ =>
      eq_of_subset_of_ncard_le hIJ (by
        have : J.ncard ≤ 3 := hJ.1
        omega)
  have : I.encard = 3 := by
    rw [← (toFinite I).cast_ncard_eq, hcard]; simp
  simpa [this] using hB.encard_eq_eRank.symm

lemma theta_eRank : theta.eRank = 76 := by
  have h := eRank_add_eRank_dual thetaDual
  have hE : (univ : Set (Fin 79)).encard = 79 := by simp [encard_univ]
  have hr : thetaDual.eRank + theta.eRank = 79 := by
    simpa [theta, hE] using h
  have h3 : thetaDual.eRank = 3 := thetaDual_eRank
  have : (3 : ℕ∞) + theta.eRank = 79 := by simpa [h3] using hr
  have hfin : theta.eRank ≠ ⊤ := by
    intro htop
    simp [htop] at this
  have hnat := congrArg ENat.toNat this
  simp [ENat.toNat_add (by decide : (3 : ℕ∞) ≠ ⊤) hfin] at hnat
  have : theta.eRank.toNat = 76 := by omega
  exact (ENat.coe_toNat_eq_self.2 hfin).symm.trans (congrArg (fun n : ℕ => (n : ℕ∞)) this)

lemma thetaDual_eRk (S : Set (Fin 79)) :
    thetaDual.eRk S = min 3 (supp S).ncard := by
  classical
  let s : Finset (Fin 4) := (supp S).toFinset
  have hs : s.card = (supp S).ncard := by
    simpa [s] using (ncard_eq_toFinset_card' (supp S)).symm
  obtain ⟨t, htt, htc⟩ := Finset.exists_subset_card_eq (min_le_right 3 s.card)
  let T : Set (Fin 4) := t
  have hTsub : T ⊆ supp S := by
    intro i hi
    have : i ∈ s := htt (by simpa [T] using hi)
    simpa [s] using this
  have hTcard : T.ncard = min 3 (supp S).ncard := by
    simpa [T, ncard_coe_finset, hs] using htc
  let I : Set (Fin 79) := (fun i => chooseIn S i) '' T
  have hinjT : InjOn (fun i => chooseIn S i) T := by
    intro i hi j hj hij
    exact (chooseIn_cls (hTsub hi)).symm.trans
      ((congrArg cls hij).trans (chooseIn_cls (hTsub hj)))
  have hIcard : I.ncard = T.ncard := hinjT.ncard_image
  have hIsub : I ⊆ S := by
    rintro _ ⟨i, hi, rfl⟩
    exact chooseIn_mem_S (hTsub hi)
  have hIind : thetaDual.Indep I := by
    refine ⟨?_, ?_⟩
    · rw [hIcard, hTcard]; exact min_le_left _ _
    · rintro x ⟨i, hi, rfl⟩ y ⟨j, hj, rfl⟩ hxy
      have : i = j := (chooseIn_cls (hTsub hi)).symm.trans
        (hxy.trans (chooseIn_cls (hTsub hj)))
      subst this; rfl
  have hB : thetaDual.IsBasis I S := by
    refine hIind.isBasis_of_forall_insert hIsub ?_
    intro e ⟨heS, heI⟩
    rw [thetaDual_dep_iff]
    have hsup : cls e ∈ supp S := mem_supp.2 ⟨e, heS, rfl⟩
    by_cases hmem : cls e ∈ T
    · refine Or.inr ?_
      rw [injOn_insert heI]
      intro h
      exact h.2 ⟨chooseIn S (cls e), ⟨cls e, hmem, rfl⟩, chooseIn_cls (hTsub hmem)⟩
    · have hne : T ≠ supp S := fun h => hmem (h ▸ hsup)
      have hss : T ⊂ supp S := hTsub.ssubset_of_ne hne
      have hlt : T.ncard < (supp S).ncard := ncard_lt_ncard hss
      have hk : min 3 (supp S).ncard < (supp S).ncard := by simpa [hTcard] using hlt
      have h3 : T.ncard = 3 := by
        have : 3 ≤ (supp S).ncard := by
          by_contra h
          have : (supp S).ncard ≤ 2 := Nat.lt_succ_iff.mp (Nat.not_le.mp h)
          have : min 3 (supp S).ncard = (supp S).ncard := Nat.min_eq_right (by omega)
          omega
        simpa [hTcard, Nat.min_eq_left this]
      refine Or.inl ?_
      rw [ncard_insert_of_notMem heI, hIcard, h3]
      decide
  rw [← hB.encard_eq_eRk, ← (toFinite I).cast_ncard_eq, hIcard, hTcard]

/-- Whitney numbers of the second kind: the number of flats of rank `i`. -/
noncomputable def whitneySecond {α : Type*} (M : Matroid α) (i : ℕ) : ℕ :=
  {F : Set α | M.IsFlat F ∧ M.eRk F = i}.ncard

end MasonFlats
