import Pseudorandom.Transfer
import LeanAPAP.Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Real.Basic
import LeanAPAP.Prereqs.Discrete.Convolution.Basic

open Finset BigOps

variable {α : Type*} [Fintype α] [DecidableEq α]
        {β : Type*} [Fintype β] [DecidableEq β]
        (a : FinPMF α)

section basic

variable [Nonempty α]

-- Definition of PMF over finite types
def FinPMF (α : Type u) [Fintype α] : Type u :=
  { f : α → ℝ // ∑ x, f x = 1 ∧ ∀ x, f x ≥ 0}

instance instFunLike : FunLike (FinPMF α) α ℝ where
  coe p := p.1
  coe_injective' _ _ h := Subtype.eq h

@[simp]
theorem FinPMF.sum_coe (p : FinPMF α) : ∑ a, p a = 1 := p.2.1


theorem FinPMF.val_apply (f : FinPMF α) :
    f x = (f.val) x := rfl


theorem FinPMF.val_mk (f : α → ℝ) {h : ∑ x, f x = 1 ∧ ∀ x, f x ≥ 0} :
    (⟨f, h⟩ : FinPMF α).val = f := rfl

@[simp]
theorem FinPMF.nonneg (p : FinPMF α) : 0 ≤ p x := by simp [FinPMF.val_apply, p.2.2]

attribute [local simp] Set.Finite.bddAbove Set.finite_range card_univ

-- The uniform distribution over some nonempty set.
noncomputable def Uniform (t : { x : Finset α // x.Nonempty }) : FinPMF α := ⟨fun x : α => if x ∈ t.1 then (1 / (t.1.card) : ℝ) else 0, by
  simp [sum_ite]
  have : t.1.card > 0 := Nonempty.card_pos t.2
  simp_all [Nat.pos_iff_ne_zero]
  intro x
  split <;> simp
⟩

noncomputable def Uniform_singleton (x : α) : FinPMF α := Uniform ⟨{x}, singleton_nonempty ..⟩

-- The value of the uniform distribution over the universe.
@[simp]
lemma uniform_single_value (x y : α) : (Uniform_singleton x) y = if y = x then 1 else 0 := by
  simp [Uniform_singleton, Uniform, FinPMF.val_apply]

-- The value of the uniform distribution over the universe.
@[simp]
lemma Uniform.univ_uniform : (Uniform ⟨(univ : Finset α), univ_nonempty⟩) x = 1/(Fintype.card α) := by
  simp [Uniform, FinPMF.val_apply]

-- Multiplication of FinPMFs, treating them as independent.
instance instMulFinPMF : HMul (FinPMF α) (FinPMF β) (FinPMF (α × β)) where
  hMul := fun a b => ⟨fun x => (a x.1) * (b x.2), by
    constructor
    simp only [Fintype.sum_prod_type, ← sum_mul_sum, FinPMF.sum_coe, mul_one]
    intros
    apply mul_nonneg <;> simp
  ⟩

@[simp]
theorem FinPMF.mul_val (b : FinPMF β) : (a * b) (x, y) = (a x) * (b y) := rfl

end basic

section apply

-- Applying some function to a random variable.
noncomputable def FinPMF.apply (a : FinPMF α) (f : α → β) : FinPMF β :=
  ⟨f # a, by
    unfold transfer
    constructor
    simp
    rw [←sum_biUnion]
    have : Finset.biUnion univ (fun x => filter (fun y => f y = x) univ) = univ := by
      apply subset_antisymm
      · simp
      · aesop
    simp_all
    apply Set.pairwiseDisjoint_filter
    simp [sum_nonneg]
    ⟩

-- If B = g(A) then E[f(B)] = E[f(g(A))].
theorem apply_weighted_sum [RCLike 𝕜] (g: α → β) (f : β → 𝕜) : ∑ x, ((a.apply g) x) * (f x) = ∑ y, (a y) * (f (g y)) := by
  change ∑ x, (RCLike.ofRealAm ∘ (g # ↑a)) x * f x = ∑ x, (a x) * f (g x)
  simp_rw [comp_transfer]
  apply transfer_sum

lemma FinPMF.apply_equiv (f : α ≃ β) : (a.apply f) x = a (f.symm x) := by
  unfold apply transfer
  change ∑ y ∈ univ.filter (fun y => f y = x), a y = _
  convert_to ∑ y ∈ {f.symm x}, a y = _
  congr
  ext v
  constructor
  · intro o
    simp only [mem_filter, mem_univ, true_and] at o
    rw [← o]
    simp
  · intro o
    simp only [mem_singleton] at o
    simp [o]
  simp

lemma FinPMF.apply_swap (b : FinPMF β) : (a*b).apply Prod.swap = b*a := by
  apply Subtype.ext
  ext x
  have ⟨x1, x2⟩ := x
  unfold apply transfer
  simp only [filter_congr_decidable]
  convert_to ∑ x ∈ univ.filter (fun x => x = (x2, x1)), (a*b) x = (b*a) (x1, x2)
  congr
  ext v
  constructor
  · intro o
    apply_fun Prod.swap at o
    exact o
  · intro o
    rw [o]
    rfl
  simp [filter_eq', mul_comm]

lemma FinPMF.apply_apply (f : α → β) (g : β → γ) [Nonempty γ] [Fintype γ] [DecidableEq γ] :
    (a.apply f).apply g = a.apply (g ∘ f) := by
  apply Subtype.ext
  apply transfer_transfer

lemma FinPMF.eq_apply_id : a.apply id = a := by
  apply Subtype.ext
  apply transfer_id

end apply

section monoid

-- Subtraction of FinPMFs, treating them as independent.
noncomputable instance instSubFinPMF [Sub α] : Sub (FinPMF α) where
  sub := fun a b => (a*b).apply (fun x => x.1 - x.2)

-- Addition of FinPMFs, treating them as independent.
noncomputable instance instAddFinPMF [Add α] : Add (FinPMF α) where
  add := fun a b => (a*b).apply (fun x => x.1 + x.2)

-- Negation of FinPMF
noncomputable instance instNegFinPMF [Neg α] : Neg (FinPMF α) where
  neg := fun a => a.apply (fun x => -x)

-- Zero of FinPMF
noncomputable instance instZeroFinPMF [Zero α] : Zero (FinPMF α) where
  zero := ⟨fun x => if x = 0 then 1 else 0, by aesop⟩

@[simp]
lemma FinPMF.neg_apply [InvolutiveNeg α] : (-a) x = a (-x) := calc
  (-a) x = ∑ z ∈ (univ.filter fun z => -z = x), a z := rfl
  _ = ∑ z ∈ {-x}, a z := by
    congr
    aesop
  _ = a (-x) := by simp

@[simp]
lemma FinPMF.neg_neg [InvolutiveNeg α] : - -a = a := by
  apply Subtype.ext
  ext x
  change (- (- a)) x = a x
  rw [FinPMF.neg_apply, FinPMF.neg_apply]
  simp

lemma FinPMF.neg_add [AddCommGroup α] : -(a + b) = -a + -b := by
  apply Subtype.ext
  ext x
  calc (-(a + b)) x
    _ = (a + b) (- x) := by simp
    _ = ∑ y ∈ univ.filter (fun (y : α × α) => y.1 + y.2 = -x), a y.1 * b y.2 := rfl
    _ = ∑ y ∈ univ.filter (fun (y : α × α) => y.1 + y.2 = x), a (-y.1) * b (-y.2) := by
      apply sum_bijective (fun x => (-x.1, -x.2))
      · apply Function.Involutive.bijective
        intro x
        simp
      · rintro ⟨i1, i2⟩
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · intro v
          apply_fun (- ·) at v
          simp at v
          rw [← v]
          rw [add_comm]
        · intro v
          apply_fun (- ·) at v
          simp at v
          rw [← v]
          rw [add_comm]
      · intros
        simp
    _ = ∑ y ∈ univ.filter (fun (y : α × α) => y.1 + y.2 = x), (-a) y.1 * (-b) y.2 := by simp
    _ = (-a + -b) x := rfl

lemma FinPMF.sub_eq_add_neg [AddGroup α] : (a - b) = (a + -b) := by
  apply Subtype.ext
  ext x
  calc (a - b) x
    _ = ∑ y ∈ univ.filter (fun (y : α × α) => y.1 - y.2 = x), a y.1 * b y.2 := rfl
    _ = ∑ y ∈ univ.filter (fun (y : α × α) => y.1 + y.2 = x), a y.1 * b (-y.2) := by
      apply sum_bijective (fun x => (x.1, -x.2))
      · apply Function.Involutive.bijective
        intro x
        simp
      · rintro ⟨i1, i2⟩
        simp [_root_.sub_eq_add_neg]
      · intros
        simp
    _ = ∑ y ∈ univ.filter (fun (y : α × α) => y.1 + y.2 = x), a y.1 * (-b) y.2 := by simp
    _ = (a + -b) x := rfl

noncomputable instance FinPMFCommMonoid [AddCommGroup α] : AddCommMonoid (FinPMF α) := {
  add := Add.add
  add_assoc := by
    intros a b c
    apply Subtype.ext
    ext x
    calc (a + b + c) x
      _ = (a ∗ b ∗ c) x := rfl
      _ = (a ∗ (b ∗ c)) x := by rw [conv_assoc]
      _ = (a + (b + c)) x := rfl
  add_comm := by
    intros a b
    apply Subtype.ext
    ext x
    calc (a + b) x
      _ = (a ∗ b) x := rfl
      _ = (b ∗ a) x := by rw [conv_comm]
      _ = (b + a) x := rfl
  zero := 0
  zero_add := by
    intro a
    apply Subtype.ext
    ext x
    calc (0 + a) x
      _ = (trivChar ∗ a) x := rfl
      _ = a x := by rw [trivChar_conv]
  add_zero := by
    intro a
    apply Subtype.ext
    ext x
    calc (a + 0) x
      _ = (a ∗ trivChar) x := rfl
      _ = a x := by rw [conv_trivChar]
  nsmul := nsmulRec
}

lemma FinPMF.sub_val [Sub α] : a - b = (a*b).apply (fun x => x.1-x.2) := rfl

lemma FinPMF.add_val [Add α] : a + b = (a*b).apply (fun x => x.1+x.2) := rfl

lemma FinPMF.apply_mul (a : FinPMF α) (b : FinPMF β) (f : α → γ) (g : β → γ₂) [Nonempty γ] [Fintype γ] [DecidableEq γ]
    [Nonempty γ₂] [Fintype γ₂] [DecidableEq γ₂]:
    a.apply f * b.apply g = (a*b).apply (fun x => (f x.1, g x.2)) := by
  apply Subtype.ext
  ext x
  have ⟨x1, x2⟩ := x
  change (a.apply f * b.apply g) (x1, x2) = (a*b).apply _ _
  rw [FinPMF.mul_val]
  apply Eq.symm
  convert_to ∑ y ∈ univ.filter (fun y => (f y.1, g y.2) = (x1, x2)), (a*b) y = _
  unfold apply transfer
  simp only [filter_congr_decidable]
  calc ∑ y ∈ univ.filter (fun y => (f y.1, g y.2) = (x1, x2)), (a*b) y
    _ = ∑ y ∈ univ.filter (fun y => f y.1 = x1 ∧ g y.2 = x2), (a*b) y := by simp
    _ = ∑ y ∈ (univ ×ˢ univ).filter (fun y => f y.1 = x1 ∧ g y.2 = x2), (a*b) y := by simp
    _ = ∑ y ∈ (univ.filter (fun y => f y = x1)) ×ˢ (univ.filter (fun y => g y = x2)), (a*b) y := by
      congr
      exact Finset.filter_product (fun y => f y = x1) (fun y => g y = x2)
    _ = ∑ y1 ∈ univ.filter (fun y => f y = x1), ∑ y2 ∈ univ.filter (fun y => g y = x2), (a*b) (y1, y2) := by
      rw [Finset.sum_product]
    _ = ∑ y1 ∈ univ.filter (fun y => f y = x1), ∑ y2 ∈ univ.filter (fun y => g y = x2), a y1 * b y2 := rfl
    _ = (∑ y ∈ univ.filter (fun y => f y = x1), a y) * (∑ y ∈ univ.filter (fun y => g y = x2), b y) := by
      rw [sum_mul_sum]

lemma FinPMF.apply_add (a : FinPMF α) (b : FinPMF β) (f : α → γ) (g : β → γ) [Nonempty γ] [Fintype γ] [Add γ] [DecidableEq γ]:
    a.apply f + b.apply g = (a*b).apply (fun x => f x.1 + g x.2) := by
  apply Subtype.ext
  ext x
  change (apply a f + apply b g) x = _
  rw [FinPMF.add_val, FinPMF.apply_mul, FinPMF.apply_apply]
  rfl

theorem apply_ne_zero (a : FinPMF α) (f : α → β) (x : β)
    (h : a.apply f x ≠ 0) : ∃ i, x = f i := transfer_ne_zero f a x h

end monoid

section linear_combination

noncomputable def FinPMF.linear_combination (a : FinPMF α) (f : α → FinPMF β) : FinPMF β :=
  ⟨(fun x => ∑ y ∈ univ, (a y) * (f y x)), by
    constructor
    rw [sum_comm]
    simp [← mul_sum]
    intros
    apply sum_nonneg
    intros
    exact mul_nonneg (nonneg _) (nonneg _)
    ⟩

theorem linear_combination_linear_combination [Fintype γ] (a : FinPMF α) (f : α → FinPMF β) (g : β → FinPMF γ):
  FinPMF.linear_combination (FinPMF.linear_combination a f) g =
  FinPMF.linear_combination a (fun x => FinPMF.linear_combination (f x) g) := by
  simp only [FinPMF.linear_combination]
  apply Subtype.ext
  simp only [FinPMF.val_apply]
  ext x
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  simp [mul_assoc]

theorem linear_combination_apply [Nonempty γ] [Fintype γ] [DecidableEq γ] (a : FinPMF α) (f : α → FinPMF β) (g : β → γ) :
  (FinPMF.linear_combination a f).apply g = FinPMF.linear_combination a (fun x => (f x).apply g) := by
  unfold FinPMF.apply transfer FinPMF.linear_combination
  apply Subtype.ext
  simp only [FinPMF.val_apply]
  ext x
  simp only [mul_sum]
  rw [sum_comm]

theorem linear_combination_mul [Nonempty α'] [Fintype α'] [Nonempty β'] [Fintype β'] (a : FinPMF α) (f : α → FinPMF α')
    (b : FinPMF β) (g : β → FinPMF β') :
    (a.linear_combination f) * (b.linear_combination g) = (a * b).linear_combination (fun ⟨x, y⟩ => (f x) * (g y)) := by
  unfold FinPMF.linear_combination
  simp only [FinPMF.val_apply, instMulFinPMF]
  apply Subtype.ext
  simp only
  ext x
  simp [sum_mul_sum]
  apply sum_congr
  rfl
  intros
  apply sum_congr
  rfl
  intros
  ring

noncomputable def FinPMF.adjust (a : FinPMF α) (x : α) (p : ℝ) (h₁ : 0 ≤ p) (h₂ : p ≤ 1) : FinPMF α :=
  FinPMF.linear_combination (α := Fin 2) ⟨![1-p, p], by
    constructor
    simp
    rw [Fin.forall_fin_two]
    simp [h₁, h₂]
  ⟩ (![a, Uniform_singleton x] : Fin 2 → FinPMF α)

end linear_combination

section high_entropy

noncomputable def close_high_entropy [Fintype α] (n : ℝ) (ε : ℝ) (a : FinPMF α) : Prop :=
  ∀ (H : Finset α), (H.card ≤ n) → ∑ v ∈ H, a v ≤ ε

lemma close_high_entropy_of_floor [Fintype α] (n : ℝ) (ε : ℝ) (a : FinPMF α)
    (h : close_high_entropy ⌊n⌋₊ ε a):
    close_high_entropy n ε a := by
  intro H hH
  apply h
  simp only [Nat.cast_le]
  rw [Nat.le_floor_iff]
  exact hH
  refine LE.le.trans ?_ hH
  simp

lemma close_high_entropy_of_le [Fintype α] (n : ℝ) (ε₁ ε₂ : ℝ) (hε : ε₁ ≤ ε₂) (a : FinPMF α)
    (h : close_high_entropy n ε₁ a):
    close_high_entropy n ε₂ a := by
  intro H hH
  apply (h H hH).trans hε

lemma close_high_entropy_apply_equiv [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (n ε : ℝ) (a : FinPMF α)
    (h : close_high_entropy n ε a) (e : α ≃ β) :
    close_high_entropy n ε (a.apply e) := by
  intro H hX
  simp_rw [FinPMF.apply_equiv]
  convert_to ∑ x ∈ H.map e.symm, a x ≤ ε
  simp
  apply h
  simp [hX]

lemma add_close_high_entropy [Fintype α] [Nonempty α] [AddCommGroup α]
    (n ε : ℝ) (a b : FinPMF α)
    (h : close_high_entropy n ε a) :
    close_high_entropy n ε (a+b) := by
  intro H hX
  change ∑ v ∈ H, ∑ x ∈ univ.filter (fun (x : α × α) => x.1 + x.2 = v), a x.1 * b x.2 ≤ ε
  convert_to ∑ v ∈ H, ∑ x, a (v - x) * b x ≤ ε
  congr with v
  apply sum_nbij' (fun x => x.2) (fun x => (v-x, x))
  · simp
  · simp
  · simp only [mem_filter, mem_univ, true_and, Prod.forall, Prod.mk.injEq, and_true]
    intros _ _ h
    rw [← h]
    abel
  · simp
  · simp only [mem_filter, mem_univ, true_and, mul_eq_mul_right_iff, Prod.forall]
    intros _ _ h
    left
    rw [← h]
    congr
    abel
  rw [sum_comm]
  simp_rw [← sum_mul, mul_comm]
  convert_to ∑ x, b x * ∑ i ∈ H.image (fun y => y - x), a i ≤ ε
  congr with x
  congr 1
  apply Eq.symm
  apply sum_image
  · intros _ _ _ _ h
    exact sub_left_inj.mp h
  trans ∑ x, b x * ε
  gcongr
  simp
  apply h
  trans (H.card : ℝ)
  exact_mod_cast card_image_le
  exact hX
  simp [← sum_mul]



lemma close_high_entropy_linear_combination [Fintype α] [Fintype β] [DecidableEq β] (n : ℝ) (ε : ℝ) (a : FinPMF β)
    (g : β → FinPMF α) (h : ∀ x, 0 < a x → close_high_entropy n ε (g x)) :
  close_high_entropy n ε (a.linear_combination g) := by
  intro H hH
  unfold FinPMF.linear_combination
  change ∑ v ∈ H, ∑ y, a y * (g y) v ≤ ε
  rw [sum_comm]
  simp_rw [← mul_sum]
  calc ∑ x, a x * ∑ i ∈ H, (g x) i
    _ = ∑ x ∈ univ.filter (fun x => 0 < a x), a x * ∑ i ∈ H, (g x) i := by
      apply Eq.symm
      apply sum_subset_zero_on_sdiff
      simp
      intro x hx
      simp at hx
      have : 0 ≤ a x := by simp
      have : 0 = a x := by linarith
      rw [← this]
      simp
      simp
    _ ≤ ∑ x ∈ univ.filter (fun x => 0 < a x), a x * ε := by
      gcongr with i hi
      simp
      simp only [mem_filter, mem_univ, true_and] at hi
      apply h i hi _ hH
    _ = ∑ x, a x * ε := by
      apply sum_subset_zero_on_sdiff
      simp
      intro x hx
      simp at hx
      have : 0 ≤ a x := by simp
      have : 0 = a x := by linarith
      rw [← this]
      simp
      simp
    _ = ε := by simp [← sum_mul]

end high_entropy

lemma filter_neg_le_inv_card_le (a : FinPMF α) (n : ℝ) (hn : 0 < n) :
    (univ.filter fun x => ¬a x ≤ 1/n).card ≤ n := calc ((univ.filter fun x => ¬a x ≤ 1/n).card : ℝ)
  _ = (∑ x ∈ univ.filter (fun x => ¬a x ≤ 1/n), 1 / n) * n := by field_simp
  _ ≤ (∑ x ∈ univ.filter (fun x => ¬a x ≤ 1/n), a x) * n := by
    gcongr
    simp_all [le_of_lt]
  _ ≤ (∑ x, a x) * n := by
    gcongr
    apply sum_le_sum_of_subset_of_nonneg
    simp
    intros
    simp
  _ = n := by simp
