import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Ring
import LeanAPAP.Prereqs.Expect.Basic

open Finset BigOps

variable {α β γ : Type*} [Fintype α] [DecidableEq β]

noncomputable def transfer [AddCommMonoid γ] (f : α → β) (g : α → γ) : (β → γ) :=
  (fun x => ∑ y in univ.filter (fun y => f y = x), g y)

infixr:75 " # " => transfer

theorem transfer_add [AddCommMonoid γ] (f : α → β) (g h : α → γ) :
  f # (g + h) = f # g + f # h := by
  unfold transfer
  ext a
  simp [sum_add_distrib]

theorem comp_transfer [AddCommMonoid γ] [AddCommMonoid γ₂] [FunLike G γ γ₂] [AddMonoidHomClass G γ γ₂]
    (f : α → β) (g : α → γ) (h : G):
  h ∘ (f # g) = f # (h ∘ g) := by
  unfold transfer
  ext a
  simp

theorem transfer_sub [SubtractionCommMonoid γ] (f : α → β) (g h : α → γ) :
  f # (g - h) = f # g - f # h := by
  unfold transfer
  ext a
  simp

theorem transfer_sum [Fintype β] [Semiring γ] (f : α → β) (g : α → γ) (h : β → γ):
  ∑ x, (f # g) x * h x = ∑ x, (g x) * (h (f x)) := by
  unfold transfer
  simp_rw [sum_mul]
  conv =>
    lhs
    rhs
    intro x
    tactic =>
      apply sum_congr
      rfl
      intro i hi
      simp only [filter_congr_decidable, mem_filter, mem_univ, true_and] at hi
      change _ = g i * h (f i)
      congr
      exact hi.symm
  rw [sum_fiberwise]

theorem transfer_expect [Fintype β] [Semiring γ] [Module NNRat γ] [Nonempty β] [Nonempty α]
   (f : α → β) (g : α → γ) (h : β → γ):
  𝔼 x, (f # g) x * h x = ((Fintype.card α) / (Fintype.card β) : NNRat) • 𝔼 x, (g x) * (h (f x)) := by
  rw [expect, expect, transfer_sum, ← smul_assoc]
  congr
  field_simp
  rw [mul_comm]; rfl
