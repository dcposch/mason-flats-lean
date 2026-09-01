/-
Copyright (c) 2026 Dan Clemens Posch. All rights reserved.
Released under the Apache License, Version 2.0; see LICENSE.
Authors: Dan Clemens Posch
-/
import MasonFlats.Basic
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Loop

/-!
Cyclic sets of `thetaDual` and Larson’s identification of Whitney numbers of
`theta` with cyclic-set counts in the dual.
-/

open Set Matroid

namespace MasonFlats

open scoped Classical

/-- A set is cyclic if it is a union of circuits. -/
def IsCyclic {α : Type*} (M : Matroid α) (S : Set α) : Prop :=
  S ⊆ M.E ∧ ∀ e ∈ S, ∃ C, M.IsCircuit C ∧ e ∈ C ∧ C ⊆ S

lemma isFlat_iff_compl_cyclic {α : Type*} {M : Matroid α} {F : Set α}
    (hF : F ⊆ M.E) :
    M.IsFlat F ↔ IsCyclic M✶ (M.E \ F) := by
  constructor
  · intro hFlat
    refine ⟨sdiff_subset, fun e he => ?_⟩
    have hnl : (M ／ F).IsNonloop e := by
      refine ⟨?_, ⟨he.1, he.2⟩⟩
      rw [contract_isLoop_iff_mem_closure]
      intro h
      exact he.2 (by simpa [hFlat.closure] using h.1)
    obtain ⟨K, hK, heK⟩ := hnl.exists_mem_isCocircuit
    have hKE : K ⊆ M.E \ F := hK.subset_ground
    rw [isCocircuit_def, dual_contract, delete_isCircuit_iff] at hK
    exact ⟨K, hK.1, heK, hKE⟩
  · intro hCyc
    rw [isFlat_iff_closure_eq]
    refine (subset_antisymm (M.subset_closure F hF) ?_).symm
    intro e hecl
    by_contra heF
    have heE : e ∈ M.E := mem_ground_of_mem_closure hecl
    obtain ⟨C, hCsub, hC, heC⟩ := (mem_closure_iff_exists_isCircuit heF).1 hecl
    obtain ⟨K, hK, heK, hKsub⟩ := hCyc.2 e ⟨heE, heF⟩
    have hinter : C ∩ K = {e} := by
      refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨heC, heK⟩)
      intro x hx
      have hxK : x ∈ M.E \ F := hKsub hx.2
      have hxC : x ∈ insert e F := hCsub hx.1
      simpa [mem_insert_iff, hxK.2] using hxC
    exact hC.inter_isCocircuit_ne_singleton (isCocircuit_def.2 hK) hinter

lemma thetaDual_isCyclic_iff {S : Set (Fin 79)} :
    IsCyclic thetaDual S ↔
      (∀ i, (S ∩ para i).ncard ≠ 1) ∨ supp S = univ := by
  constructor
  · intro hCyc
    by_cases h4 : supp S = univ
    · exact Or.inr h4
    · refine Or.inl fun i hi => ?_
      obtain ⟨e, heq⟩ := ncard_eq_one.1 hi
      have heS : e ∈ S := ((heq.symm ▸ mem_singleton e : e ∈ S ∩ para i)).1
      obtain ⟨C, hC, heC, hCS⟩ := hCyc.2 e heS
      rcases thetaDual_isCircuit_iff.1 hC with ⟨h2, j, hsub⟩ | ⟨h4c, hinj⟩
      · obtain ⟨x, y, hne, rfl⟩ := ncard_eq_two.1 h2
        have : i = j :=
          ((heq.symm ▸ mem_singleton e : e ∈ S ∩ para i)).2.symm.trans
            (mem_para.1 (hsub heC))
        subst this
        have hx : x ∈ S ∩ para i := ⟨hCS (by simp), hsub (by simp)⟩
        have hy : y ∈ S ∩ para i := ⟨hCS (by simp), hsub (by simp)⟩
        have hss : ({x, y} : Set (Fin 79)) ⊆ {e} := by
          simpa [heq] using pair_subset hx hy
        have hn1 : ({x, y} : Set (Fin 79)).ncard ≤ 1 :=
          (ncard_le_ncard hss).trans (by simp)
        have hn2 : ({x, y} : Set (Fin 79)).ncard = 2 := ncard_pair hne
        omega
      · have himg : (cls '' C).ncard = 4 := by rw [hinj.ncard_image, h4c]
        have hCuniv : cls '' C = univ :=
          eq_of_subset_of_ncard_le (subset_univ _) (by simp [ncard_univ, himg])
        have hsup : supp S = univ := by
          rw [supp_eq_image, eq_univ_iff_forall]
          intro k
          have : k ∈ cls '' C := by simpa [hCuniv]
          obtain ⟨x, hxC, rfl⟩ := this
          exact ⟨x, hCS hxC, rfl⟩
        exact h4 hsup
  · intro h
    refine ⟨subset_univ _, fun e heS => ?_⟩
    rcases h with hsing | huniv
    · have hne : (S ∩ para (cls e)).Nonempty := ⟨e, ⟨heS, rfl⟩⟩
      have hpos : 0 < (S ∩ para (cls e)).ncard :=
        (ncard_pos (toFinite (S ∩ para (cls e)))).2 hne
      have hge : 2 ≤ (S ∩ para (cls e)).ncard := by
        have : (S ∩ para (cls e)).ncard ≠ 1 := hsing _
        omega
      have : ¬ S ∩ para (cls e) ⊆ {e} := by
        intro hsub
        have : (S ∩ para (cls e)).ncard ≤ 1 :=
          (ncard_le_ncard hsub).trans (by simp)
        omega
      obtain ⟨f, hf, hfne⟩ := not_subset.1 this
      have hne : f ≠ e := fun h => hfne (by simp [h])
      have hcls : cls f = cls e := hf.2
      refine ⟨{e, f}, ?_, mem_insert _ _, pair_subset heS hf.1⟩
      refine thetaDual_isCircuit_iff.2 (Or.inl ⟨ncard_pair hne.symm, ⟨cls e, ?_⟩⟩)
      intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · rfl
      · exact hcls
    · set e0 := e
      let T : Set (Fin 4) := univ \ {cls e0}
      have hT : ∀ i ∈ T, i ∈ supp S := by
        intro i hi
        simpa [huniv] using (mem_univ i)
      let C : Set (Fin 79) := insert e0 ((fun i => chooseIn S i) '' T)
      have hinjT : InjOn (fun i => chooseIn S i) T := by
        intro i hi j hj hij
        exact (chooseIn_cls (hT i hi)).symm.trans
          ((congrArg cls hij).trans (chooseIn_cls (hT j hj)))
      have he_not : e0 ∉ (fun i => chooseIn S i) '' T := by
        rintro ⟨i, hi, hch⟩
        have : i = cls e0 := by
          simpa [chooseIn_cls (hT i hi)] using congrArg cls hch
        exact hi.2 (this ▸ mem_singleton _)
      have hTcard : T.ncard = 3 := by
        rw [ncard_sdiff (singleton_subset_iff.2 (mem_univ _))]
        simp [ncard_univ, ncard_singleton]
      have hCcard : C.ncard = 4 := by
        rw [ncard_insert_of_notMem he_not, hinjT.ncard_image, hTcard]
      have hinjC : InjOn cls C := by
        intro x hx y hy hxy
        simp only [C, mem_insert_iff, mem_image] at hx hy
        rcases hx with rfl | ⟨i, hi, rfl⟩ <;> rcases hy with rfl | ⟨j, hj, rfl⟩
        · rfl
        · have : cls e0 = j := by
            simpa [chooseIn_cls (hT _ hj)] using hxy
          exact absurd (this ▸ mem_singleton _) hj.2
        · have : i = cls e0 :=
            (chooseIn_cls (hT _ hi)).symm.trans hxy
          exact absurd (this ▸ mem_singleton _) hi.2
        · have : i = j := (chooseIn_cls (hT i hi)).symm.trans
            (hxy.trans (chooseIn_cls (hT j hj)))
          subst this; rfl
      refine ⟨C, thetaDual_isCircuit_iff.2 (Or.inr ⟨hCcard, hinjC⟩), mem_insert _ _, ?_⟩
      intro x hx
      simp only [C, mem_insert_iff, mem_image] at hx
      rcases hx with rfl | ⟨i, hi, rfl⟩
      · exact heS
      · exact chooseIn_mem_S (hT i hi)

lemma dual_rank_nat (S : Set (Fin 79)) :
    (theta.eRk (univ \ S)).toNat + S.ncard = min 3 (supp S).ncard + 76 := by
  have h := eRk_dual_add_eRank (M := theta) (X := S) (subset_univ _)
  have heq : thetaDual.eRk S + 76 = theta.eRk (univ \ S) + S.encard := by
    simp only [theta_E] at h
    rw [show theta✶ = thetaDual from by simp [theta], theta_eRank] at h
    exact h
  have hrk := thetaDual_eRk S
  have hS : S.encard = (S.ncard : ℕ∞) := (toFinite S).cast_ncard_eq.symm
  have hfin₁ : thetaDual.eRk S ≠ ⊤ := by rw [hrk]; exact ENat.coe_ne_top _
  have hfin₂ : theta.eRk (univ \ S) ≠ ⊤ := by
    have : theta.eRk (univ \ S) ≤ 76 := by
      simpa [theta_eRank] using eRk_le_eRank theta (univ \ S)
    exact ne_of_lt (this.trans_lt (ENat.coe_lt_top 76))
  have hfin₃ : S.encard ≠ ⊤ := by rw [hS]; exact ENat.coe_ne_top _
  have hnat := congrArg ENat.toNat heq
  have h1 : (thetaDual.eRk S + 76).toNat = min 3 (supp S).ncard + 76 := by
    rw [ENat.toNat_add hfin₁ (by simp), hrk]
    simp
  have h2 : (theta.eRk (univ \ S) + S.encard).toNat =
      (theta.eRk (univ \ S)).toNat + S.ncard := by
    rw [ENat.toNat_add hfin₂ hfin₃, hS, ENat.toNat_coe]
  omega

lemma whitney_eq_cyclic (i : ℕ) (hi : i ≤ 76) :
    whitneySecond theta (76 - i) =
      {S : Set (Fin 79) |
        IsCyclic thetaDual S ∧ S.ncard = min 3 (supp S).ncard + i}.ncard := by
  refine ncard_congr (fun F _ => (univ : Set (Fin 79)) \ F) ?_ ?_ ?_
  · intro F hF
    have hFE : F ⊆ univ := hF.1.subset_ground
    have hCyc : IsCyclic thetaDual (univ \ F) := by
      simpa [theta] using (isFlat_iff_compl_cyclic hFE).1 hF.1
    have hnat := dual_rank_nat (univ \ F)
    have hFeq : univ \ (univ \ F) = F := by ext; simp
    rw [hFeq] at hnat
    have hrk : (theta.eRk F).toNat = 76 - i := by
      have hcoe : theta.eRk F = ((76 - i : ℕ) : ℕ∞) := hF.2
      rw [hcoe, ENat.toNat_coe]
    have hnat' : (76 - i) + (univ \ F).ncard = min 3 (supp (univ \ F)).ncard + 76 := by
      rwa [hrk] at hnat
    have : (univ \ F).ncard = min 3 (supp (univ \ F)).ncard + i := by
      have h' := congrArg (· + i) hnat'
      have hcancel : 76 - i + i = 76 := Nat.sub_add_cancel hi
      omega
    exact ⟨hCyc, this⟩
  · intro F₁ F₂ h₁ h₂ h
    have hF₁ : F₁ ⊆ univ := h₁.1.subset_ground
    have hF₂ : F₂ ⊆ univ := h₂.1.subset_ground
    have hF₁c : univ \ (univ \ F₁) = F₁ := by ext; simp
    have hF₂c : univ \ (univ \ F₂) = F₂ := by ext; simp
    rw [← hF₁c, h, hF₂c]
  · intro S hS
    refine ⟨univ \ S, ?_, by ext; simp⟩
    have hFE : univ \ S ⊆ univ := sdiff_subset
    have hCyc' : IsCyclic theta✶ (theta.E \ (univ \ S)) := by
      have : theta.E \ (univ \ S) = S := by
        ext x; simp [theta_E]
      simpa [this, theta] using hS.1
    have hFlat : theta.IsFlat (univ \ S) :=
      (isFlat_iff_compl_cyclic (M := theta) hFE).2 hCyc'
    have hnat := dual_rank_nat S
    have hfin : theta.eRk (univ \ S) ≠ ⊤ := by
      have : theta.eRk (univ \ S) ≤ 76 := by
        simpa [theta_eRank] using eRk_le_eRank theta (univ \ S)
      exact ne_of_lt (this.trans_lt (ENat.coe_lt_top 76))
    have hto : (theta.eRk (univ \ S)).toNat = 76 - i := by
      have hn := hS.2
      have hnat' : (theta.eRk (univ \ S)).toNat + (min 3 (supp S).ncard + i) =
          min 3 (supp S).ncard + 76 := by
        rwa [hn] at hnat
      have hcancel : 76 - i + i = 76 := Nat.sub_add_cancel hi
      omega
    have hRk : theta.eRk (univ \ S) = 76 - i :=
      (ENat.coe_toNat_eq_self.2 hfin).symm.trans
        (congrArg (fun n : ℕ => (n : ℕ∞)) hto)
    exact ⟨hFlat, hRk⟩

end MasonFlats
