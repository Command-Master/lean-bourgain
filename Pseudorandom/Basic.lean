import Mathlib.Algebra.BigOperators.Basic

open Finset BigOperators

variable {α β γ : Type*} [Fintype α] [AddCommMonoid γ] [DecidableEq β]

noncomputable def transfer (f : α → β) (g : α → γ) : (β → γ) :=
  (fun x => ∑ y in univ.filter (fun y => f y = x), g y)

infixr:75 "#" => transfer
