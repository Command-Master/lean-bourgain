import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.SetLike.Fintype
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Pseudorandom.Lines
import Pseudorandom.Constants

open Classical Finset

variable {α : Type*} [Field α] [Fintype α]

noncomputable def projective_transform (p q : α × α) (h : p ≠ q) : (α × α × α) ≃ₗ[α] (α × α × α) := by
  let l := Submodule.pair p q
  let inf := Submodule.infinity α
  have b₁ := Submodule.pair_basis p q h
  have b₂ := Submodule.infinity_basis α
  have f : l ≃ₗ[α] inf := b₁.repr.trans b₂.repr.symm
  let l' := Classical.choose (Submodule.exists_isCompl l)
  have l'p : IsCompl l l' := Classical.choose_spec _
  let inf' := Classical.choose (Submodule.exists_isCompl inf)
  have inf'p : IsCompl inf inf' := Classical.choose_spec _
  have f' : l' ≃ₗ[α] inf' := by
    apply LinearEquiv.ofFinrankEq
    apply add_left_cancel (a := 2)
    conv =>
      congr
      · lhs
        tactic =>
          change 2 = FiniteDimensional.finrank α l
          rw [finrank_eq_nat_card_basis b₁]
          simp
      · lhs
        tactic =>
          change 2 = FiniteDimensional.finrank α inf
          rw [finrank_eq_nat_card_basis b₂]
          simp
    rw [Submodule.finrank_add_eq_of_isCompl, Submodule.finrank_add_eq_of_isCompl] <;> assumption
  have f'₁ := Submodule.prodEquivOfIsCompl l l' l'p
  have f'₂ := Submodule.prodEquivOfIsCompl inf inf' inf'p
  exact f'₁.symm ≪≫ₗ (LinearEquiv.prod f f') ≪≫ₗ f'₂

lemma project_p (p q : α × α) (h : p ≠ q) : (projective_transform p q h) ⟨p.1, p.2, 1⟩ = ⟨1,0,0⟩ := by
  let p' : Submodule.pair p q := ⟨⟨p.1, p.2, 1⟩, mem_span1 p q⟩
  simp [projective_transform]
  rw [(Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero ..).mpr (mem_span1 p q)]
  have : (⟨p.1, p.2, 1⟩ : (α × α × α)) = ↑p' := by simp [p']
  simp
  rw [this, Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp [p']
  rw [repr_pair_basis_first]
  simp [infinity_first]

lemma project_q (p q : α × α) (h : p ≠ q) : (projective_transform p q h) ⟨q.1, q.2, 1⟩ = ⟨0,1,0⟩ := by
  let q' : Submodule.pair p q := ⟨(q.1, q.2, 1), mem_span2 p q⟩
  simp [projective_transform]
  rw [(Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero ..).mpr (mem_span2 p q)]
  have : (⟨q.1, q.2, 1⟩ : (α × α × α)) = ↑q' := by simp [q']
  simp
  rw [this, Submodule.prodEquivOfIsCompl_symm_apply_left]
  simp [q']
  rw [repr_pair_basis_second]
  simp [infinity_second]

lemma of_line (p q : α × α) (h : p ≠ q) (x : α × α × α) (h₂ : x ∈ (Submodule.pair p q : Set _)) :
  (projective_transform p q h) x ∈ (Submodule.infinity α : Set _) := by
  rw [infinity_mem]
  simp at h₂
  rw [Submodule.pair, Submodule.mem_span_pair] at h₂
  have ⟨a, b, h₂⟩ := h₂
  rw [←h₂]
  simp [-Prod.smul_mk, -Prod.mk_add_mk]
  rw [project_p, project_q]
  simp

lemma of_infinity (p q : α × α) (h : p ≠ q) (x : α × α × α) (h₂ : x ∈ (Submodule.infinity α : Set _)) :
  (projective_transform p q h).symm x ∈ (Submodule.pair p q : Set _) := by
  rw [infinity_mem] at h₂
  simp [Submodule.pair, Submodule.mem_span_pair, -Prod.smul_mk, -Prod.mk_add_mk]
  exists x.1, x.2.1
  rw [LinearEquiv.eq_symm_apply]
  simp [-Prod.smul_mk, -Prod.mk_add_mk]
  rw [project_p, project_q]
  aesop

lemma non_erasing (p q x : α × α) (h : p ≠ q) (h₂ : ¬x ∈ Line.of p q h) :
  ((projective_transform p q h) ⟨x.1, x.2, 1⟩).2.2 ≠ 0 := by
  intro nh
  rw [←infinity_mem] at nh
  suffices x ∈ Line.of p q h by contradiction
  have := of_infinity p q h _ nh
  simp at this
  exact this
