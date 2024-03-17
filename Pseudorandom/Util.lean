import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image

lemma exists_eq_card_filter_of_card_le_one {α : Type*}
  {p : α → Prop} [DecidablePred p] (A : Finset α) (h : (A.filter p).card ≤ 1) :
  (if ∃ a ∈ A, p a then 1 else 0) = (A.filter p).card := by
  split
  rename_i h2
  have ⟨a, pa⟩ := h2
  apply le_antisymm
  apply Finset.Nonempty.card_pos
  apply Finset.nonempty_of_ne_empty
  apply Finset.ne_empty_of_mem (a := a)
  simp [pa]
  assumption
  apply Eq.symm
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_of_forall_not_mem
  simp_all
