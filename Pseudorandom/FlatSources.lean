import Pseudorandom.PMF
import Pseudorandom.Extractor

variable
   {α : Type u1} [Nonempty α] [Fintype α]
   (a : FinPMF α)

open Finset BigOperators

lemma card_filter_indexOf_lt [DecidableEq α] (l : ℕ) (vals : List α) (h : vals.Nodup)
  (h₂ : l ≤ vals.length):
  (filter (fun x => (vals.indexOf x) < l) univ).card = l := by
  rw [← card_range l]
  apply card_congr (fun x _ => vals.indexOf x)
  · intros
    simp_all only [one_div, card_range, mem_filter, mem_univ, true_and, mem_range]
  · intros
    rwa [← List.indexOf_inj (l := vals)]
    repeat {
    rw [← List.indexOf_lt_length]
    calc
      _ < l := by simp_all only [card_range, mem_filter]
      _ ≤ vals.length := h₂
    }
  · intros b hb
    simp_all only [one_div, List.getElem_eq_get, mem_range, card_range, mem_filter, mem_univ,
      true_and, exists_prop]
    exists vals[b]
    suffices vals.indexOf vals[b] = b by simp_all only [List.getElem_eq_get, and_self]
    simp [List.get_indexOf, h]

noncomputable def measure_complexity (a : FinPMF α) (l : ℕ+) : ℕ := (univ.filter fun x => a x ≠ 0 ∧ a x ≠ (1/l : ℝ)).card

set_option maxHeartbeats 500000

theorem split_to_flat_sources [DecidableEq α] (a : FinPMF α) (l : ℕ+) (h : max_val a ≤ (1 / l : ℝ)) :
  ∃ f : FinPMF {x : Finset α // x.card = l},
    FinPMF.linear_combination f (fun x : {x : Finset α // x.card = l} => Uniform ⟨x.1, by
    apply Finset.card_pos.mp
    rw [x.2]
    apply PNat.pos
  ⟩) = a := by
  let αlist : List α := univ.toList
  let vals := αlist.mergeSort (a · ≥ a ·)
  -- Can't use univ.sort because the relation isn't antisymmetric
  have p : List.Perm vals αlist := List.perm_mergeSort (a · ≥ a ·) αlist
  have vnp : vals.Nodup := p.nodup_iff.mpr (Finset.nodup_toList _)
  have : IsTotal α (a · ≥ a ·) := ⟨fun _ _ => le_total ..⟩
  have : IsTrans α (a · ≥ a ·) := ⟨fun _ _ _ h1 h2 => le_trans h2 h1⟩
  have : IsRefl α (a · ≥ a ·) := ⟨fun _ => le_refl ..⟩
  have vs : List.Sorted (a · ≥ a ·) vals := List.sorted_mergeSort (a · ≥ a ·) αlist
  by_cases l ≤ vals.length
  let supp := univ.filter (vals.indexOf · < l)
  let supp' : {x : Finset α // x.card = l} := ⟨supp, card_filter_indexOf_lt l vals vnp (by assumption)⟩
  by_cases ev : if h : l < vals.length then a vals[(l : ℕ)] = 0 else True
  · exists Uniform_singleton supp'
    apply DFunLike.ext
    simp only [instFunLike, FinPMF.linear_combination, Uniform_singleton, Uniform, mem_singleton, card_singleton,
      Nat.cast_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, one_div, mul_ite, ite_mul,
      one_mul, zero_mul, mul_zero]
    intro x
    rw [sum_eq_single_of_mem supp', card_filter_indexOf_lt l vals vnp (by assumption)]
    simp only [filter_congr_decidable, mem_filter, mem_univ, true_and, ↓reduceIte, supp]
    rw [eq_comm]
    change a x = if vals.indexOf x < l then (l:ℝ)⁻¹ else 0
    revert x
    suffices (∀ x ∈ univ, a x = if vals.indexOf x < l then (1/l:ℝ) else 0) by simp [this]
    rw [← sum_eq_sum_iff_of_le]
    simp only [FinPMF.sum_coe, one_div, sum_ite, sum_const, nsmul_eq_mul, not_le, sum_const_zero,
      add_zero]
    field_simp
    rw [card_filter_indexOf_lt l vals vnp (by assumption)]
    intros i _
    have : vals.indexOf i < vals.length := List.indexOf_lt_length.mpr <| p.mem_iff.mpr <| by simp [αlist]
    split
    · calc
        a i ≤ max_val a := by simp
        _ ≤ 1 / l := h
    · have : l < vals.length := by linarith
      simp only [this, ↓reduceDite] at ev
      calc
        0 = a vals[(l : ℕ)] := ev.symm
        _ ≥ a vals[vals.indexOf i] := by
          apply vs.rel_get_of_le
          simp_all
        _ = a i := by
          simp
    apply mem_univ
    intro b _ hb
    simp [hb]
  · have : l < vals.length := by
      by_contra nh
      simp [nh] at ev
    have pred_lt : l.natPred < l := Nat.sub_lt (PNat.pos l) zero_lt_one
    simp only [this, ↓reduceDite] at ev
    have al_pos : 0 < a vals[(l : ℕ)] := by
      apply lt_of_le_of_ne
      simp
      exact Ne.symm ev
    have large_early (i : ℕ) (h' : i < vals.length) (h : a vals[i] = (l : ℝ)⁻¹) : i < l.natPred := by
      by_contra! nh
      have := calc
        1 = ∑ x : α, a x := by simp
        _ > ∑ x : α, if vals.indexOf x < l then a x else 0 := by
          apply sum_lt_sum
          intros
          split <;> simp
          exists vals[(l : ℕ)]
          constructor
          apply mem_univ
          simp [List.get_indexOf, vnp]
          simp at al_pos
          exact al_pos
        _ ≥ ∑ x : α, a vals[i] * if vals.indexOf x < l then 1 else 0 := by
          gcongr with i _
          split
          rename_i h₂
          have : i = vals[vals.indexOf i] := by simp
          rw [this, mul_one]
          apply vs.rel_get_of_le
          simp only [Fin.mk_le_mk]
          suffices vals.indexOf i ≤ l.natPred by linarith
          apply Nat.le_pred_of_lt
          simp [h₂]
          simp
        _ = (a vals[i]) * (univ.filter fun x => vals.indexOf x < l).card := by rw [← mul_sum]; simp
        _ = (l : ℝ)⁻¹ * l := by
          congr
          rw [card_filter_indexOf_lt]
          repeat assumption
        _ = 1 := by field_simp
      linarith
    have small_late (i : ℕ) (h' : i < vals.length) (h : a vals[i] = 0) : l < i := by
      by_contra! nh
      suffices a vals[(l : ℕ)] ≤ 0 by linarith
      rw [← h]
      apply vs.rel_get_of_le
      simp [nh]
    let pr := min (1 - l * a vals[(l : ℕ)]) (l * a vals[l.natPred])
    have pr_nonneg : 0 ≤ pr := by
      simp only [le_min_iff, sub_nonneg, gt_iff_lt, Nat.cast_pos, PNat.pos,
        mul_nonneg_iff_of_pos_left, FinPMF.nonneg, and_true, pr]
      calc l * a vals[(l : ℕ)]
        _ ≤ l * max_val a := by
          gcongr
          simp
        _ ≤ l * (1 / l : ℝ) := by gcongr
        _ = 1 := by field_simp
    have pr_lt_one : pr < 1 := calc
      pr ≤ 1 - l * a vals[(l : ℕ)] := by simp [pr]
      _ < 1 - 0*0 := by
        gcongr
        norm_num
      _ = 1 := by norm_num
    have zero_lt_inv_pr : 0 < 1 - pr := sub_pos.mpr pr_lt_one
    have inv_pr_ne_zero : 1 - pr ≠ 0 := Ne.symm <| ne_of_lt zero_lt_inv_pr
    let a'' (x : α) : ℝ := if vals.indexOf x < l then (a x - pr/l) / (1 - pr) else
      (a x) / (1 - pr)
    let a' : FinPMF α := ⟨a'', by
      constructor
      · simp only [sum_ite, ← sum_div, sum_sub_distrib, sum_const,
          card_filter_indexOf_lt l vals vnp (by assumption), nsmul_eq_mul, a'', ← add_div]
        rw [mul_div_cancel_left]
        rw [sub_add_eq_add_sub, sum_filter_add_sum_filter_not]
        field_simp
        simp
      · intro x
        simp [a'']
        split
        · apply div_nonneg
          rw [sub_nonneg]
          calc
            a x = a vals[vals.indexOf x] := by simp
            _ ≥ a vals[l.natPred] := by
              apply vs.rel_get_of_le
              simp only [Fin.mk_le_mk]
              apply Nat.le_of_lt_succ
              simp [Nat.succ_eq_add_one]
              assumption
            _ = l * a vals[l.natPred] / l := by rw [mul_div_cancel_left]; simp
            _ ≥ pr / l := by gcongr; simp [pr]
          exact le_of_lt zero_lt_inv_pr
        · apply div_nonneg
          simp
          exact le_of_lt zero_lt_inv_pr⟩
    have : max_val a' ≤ (1 / l : ℝ) := by
      unfold max_val
      apply ciSup_le
      intro x
      simp [a', a'', instFunLike]
      split
      rename_i h₃
      calc (a x - pr / l) / (1 - pr)
        _ ≤ (max_val a - pr / l) / (1 - pr) := by gcongr; simp
        _ ≤ (1/l - pr / l) / (1 - pr) := by gcongr
        _ = (l : ℝ)⁻¹ := by field_simp; ring
      rename_i h₃
      have : vals.indexOf x < vals.length := List.indexOf_lt_length.mpr <| p.mem_iff.mpr <| by simp [αlist]
      calc a x / (1 - pr)
        _ = a vals[vals.indexOf x] / (1 - pr) := by simp
        _ ≤ a vals[(l : ℕ)] / (1 - pr) := by
          gcongr
          apply vs.rel_get_of_le
          simp at h₃
          simp [h₃]
        _ ≤ a vals[(l : ℕ)] / (1 - (1 - l * a vals[(l : ℕ)])) := by
          gcongr
          simp only [al_pos, sub_sub_cancel, gt_iff_lt, Nat.cast_pos, PNat.pos,
            mul_pos_iff_of_pos_left]
          simp [pr]
        _ = (l : ℝ)⁻¹ := by
          simp only [sub_sub_cancel]
          rw [div_mul_left]
          simp
          exact ev
    have dec : measure_complexity a' l < measure_complexity a l := by
      unfold measure_complexity
      apply card_lt_card
      rw [ssubset_iff_of_subset]
      -- sorry
      by_cases h₂ : 1 - l * a vals[(l : ℕ)] ≤ l * a vals[l.natPred]
      · exists vals[(l : ℕ)]
        simp [-List.getElem_eq_get]
        refine' ⟨⟨ev, _⟩, fun _ => _⟩
        · intro v
          have := large_early l (by assumption) v
          linarith
        · simp only [instFunLike, vnp, List.get_indexOf, lt_self_iff_false,
            ↓reduceIte, a', a'', List.getElem_eq_get]
          simp only [ge_iff_le, h₂, min_eq_left, sub_sub_cancel, pr]
          simp only [← List.getElem_eq_get]
          change a vals[(l : ℕ)] / (l * a vals[(l : ℕ)]) = (l : ℝ)⁻¹
          rw [div_mul_left]
          simp
          exact ev
      · exists vals[l.natPred]
        simp only [ne_eq, one_div, mem_filter, mem_univ, true_and, not_and', not_not]
        constructor
        constructor
        · intro v
          have := small_late l.natPred (by linarith) v
          linarith
        · intro v
          have := large_early l.natPred (by linarith) v
          linarith
        · intro _
          simp only [instFunLike, vnp, List.get_indexOf, lt_self_iff_false,
            ↓reduceIte, a', a'', List.getElem_eq_get, pred_lt]
          simp only [div_eq_zero_iff]
          left
          rw [sub_eq_zero]
          simp only [min_def, h₂, ↓reduceIte, pr]
          rw [mul_div_cancel_left]
          simp
          rfl
          simp
      · rw [subset_iff]
        intro x
        have : vals.indexOf x < vals.length := List.indexOf_lt_length.mpr <| p.mem_iff.mpr <| by simp [αlist]
        contrapose
        simp [-not_and, not_and_or]
        intro v
        cases v
        · rename_i h₂
          left
          simp [a', a'', instFunLike]
          split
          · exfalso
            have := small_late (vals.indexOf x) this (by simp; exact h₂)
            linarith
          · change a x / (1 - pr) = 0
            simp [h₂]
        · rename_i h₂
          right
          simp [a', a'', instFunLike]
          split
          · change (a x - pr / l) / (1 - pr) = (l : ℝ)⁻¹
            field_simp [h₂]
            apply mul_comm
          · exfalso
            have := large_early (vals.indexOf x) this (by simp; exact h₂)
            linarith
    have ⟨f', hf⟩ := split_to_flat_sources a' l this
    exists f'.adjust supp' pr pr_nonneg <| le_of_lt pr_lt_one
    unfold FinPMF.adjust
    rw [linear_combination_linear_combination]
    apply DFunLike.ext
    intro x
    apply Subtype.ext_iff.mp at hf
    simp only [instFunLike, FinPMF.linear_combination] at hf
    have hf' := congrFun hf x
    simp only [FinPMF.linear_combination, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, uniform_single_value, ite_mul, one_mul, zero_mul,
      sum_ite_eq', mem_univ, ↓reduceIte]
    simp only [instFunLike, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Subtype.coe_eta, hf']
    simp [a'']
    split
    rename_i h₃
    simp [supp, h₃, Uniform, card_filter_indexOf_lt l vals vnp (by assumption)]
    field_simp
    ring_nf!
    rfl
    rename_i h₃
    simp [supp, h₃, Uniform]
    field_simp
    rw [mul_comm]
    rfl
  · rename_i h₃
    exfalso
    have := (card_inv_le_max_val a).trans h
    simp at this
    rw [inv_le_inv] at this
    norm_cast at this
    rw [p.length_eq] at h₃
    simp [αlist, card_univ] at h₃
    linarith
    simp [Fintype.card_pos]
    simp
  termination_by
    measure_complexity a l

#print split_to_flat_sources

example (a b : ℕ) : ℕ := a - b
