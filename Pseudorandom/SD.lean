import Pseudorandom.PMF

open Classical Finset BigOperators

attribute [local simp] Set.Finite.bddAbove Set.finite_range card_univ

attribute [local aesop unsafe 20% apply] le_of_lt

variable
   {α : Type u1} [Nonempty α] [Fintype α]
   {β : Type u2} [Nonempty β] [Fintype β]
   (a b : FinPMF α)

-- Definition of statistical distance
noncomputable def SD : ℝ :=
  ∑ x, |1 / 2 * (a x - b x)|

-- A simple lemma about absolute value.
lemma abs_ite (x : ℝ) : |x| = if x ≥ 0 then x else -x := by aesop

-- A proof of equivalence of an alternative definiton for statistical distance.
theorem SD_eq_sup_sum_diff : SD a b = ⨆ S : (Finset α) , (∑ x in S, (a x - b x)) := by
  let best_set := Finset.univ.filter (fun x : α => a x - b x ≥ 0)
  let maxv := ∑ x in best_set, (a x - b x)
  have h : ⨆ S : (Finset α) , (∑ x in S, (a x - b x)) = maxv := by
    apply le_antisymm
    · apply ciSup_le
      intro w
      let cond := (fun x : α => a x - b x ≥ 0)
      calc ∑ x in w, (a x - b x)
        _ = _ := by
          have := sum_union (f := fun x => a x - b x) (disjoint_filter_filter_neg w w cond)
          rewrite [filter_union_filter_neg_eq] at this
          exact this
        _ ≤ ∑ x in w.filter cond, (a x - b x) := by
          simp [-sum_sub_distrib]
          apply sum_nonpos
          aesop
        _ ≤ maxv := by
          apply sum_le_sum_of_subset_of_nonneg
          · apply filter_subset_filter
            simp
          · aesop
    · apply le_ciSup (f := fun S => ∑ x in S, (a x - b x))
      simp
  rw [h]
  clear h
  calc SD a b
    _ = ∑ x in best_set, 1/2*(a x - b x) -
        ∑ x in best_setᶜ, 1/2*(a x - b x) := by simp [SD, abs_ite, sum_ite, best_set]; rfl
    _ = 1/2 * ∑ x in best_set, a x - 1/2 * ∑ x in best_set, b x
        - 1/2* ∑ x in best_setᶜ, a x + 1/2* ∑ x in best_setᶜ, b x := by simp [←mul_sum]; ring
    _ = 1/2 * ∑ x in best_set, a x - 1/2 * ∑ x in best_set, b x
        - 1/2* (∑ x, a x - ∑ x in best_set, a x)
        + 1/2* (∑ x, b x - ∑ x in best_set, b x) := by repeat rw [←sum_compl_add_sum best_set]; ring_nf
    _ = 1/2 * ∑ x in best_set, a x - 1/2 * ∑ x in best_set, b x
        - 1/2* (1 - ∑ x in best_set, a x)
        + 1/2* (1 - ∑ x in best_set, b x) := by simp
    _ = ∑ x in best_set, a x - ∑ x in best_set, b x := by ring
    _ = maxv := by simp [maxv]

-- A useful consequence of the previous theorem.
lemma prb_le_prb_add_sd (t : Finset α) : ∑ x in t, a x ≤ ∑ x in t, b x + SD a b := by
  have : SD a b ≥ ∑ x in t, (a x - b x) := by calc
    SD a b = _ := SD_eq_sup_sum_diff ..
    _ ≥ ∑ x in t, (a x - b x) := by apply le_ciSup (f := fun S => ∑ x in S, (a x - b x)); simp
  simp_all
  linarith