import Pseudorandom.PMF
import Pseudorandom.Extractor

variable
   {α : Type u1} [Nonempty α] [Fintype α]
   (a : FinPMF α)

open Finset

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


theorem split_to_flat_sources [inhb: Inhabited α] [DecidableEq α] (l : ℕ+) (h : max_val a ≤ (1 / l : ℝ)) :
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
  · exists Uniform ⟨{supp'}, singleton_nonempty ..⟩
    apply DFunLike.ext
    simp only [instFunLike, FinPMF.linear_combination, Uniform, mem_singleton, card_singleton,
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
    simp only [this, ↓reduceDite] at ev
    have : l.natPred < l := Nat.sub_lt (PNat.pos l) zero_lt_one
    let pr := min (1 - a vals[(l : ℕ)]) (a vals[l.natPred])
    have pr_lt_one : pr < 1 := calc
      pr ≤ 1 - a vals[(l : ℕ)] := by simp [pr]
      _ < 1 - 0 := by
        gcongr
        apply lt_of_le_of_ne
        simp
        exact Ne.symm ev
      _ = 1 := by norm_num
    let a' (x : α) : ℝ := if vals.indexOf x < l then (a x - pr/l) / (1 - pr) else
      (a x) / (1 - pr)

    sorry
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
