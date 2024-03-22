import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fin.VecNotation
import LeanAPAP.Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.SetNotation
import Mathlib.Data.Set.Finite
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Algebra.BigOperators.Fin

open Classical Finset BigOps

variable
   {α : Type u1} [Nonempty α] [Fintype α]
   {β : Type u2} [Nonempty β] [Fintype β]
   (a b : FinPMF α)

-- Definition of PMF over finite types
def FinPMF (α : Type u) [Fintype α] : Type u :=
  { f : α → ℝ // ∑ x, f x = 1 ∧ ∀ x, f x ≥ 0}

instance instFunLike : FunLike (FinPMF α) α ℝ where
  coe p := p.1
  coe_injective' _ _ h := Subtype.eq h

@[simp]
theorem FinPMF.sum_coe (p : FinPMF α) : ∑ a, p a = 1 := p.2.1

@[simp]
theorem FinPMF.nonneg (p : FinPMF α) : 0 ≤ p x := by simp [instFunLike, p.2.2]

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
  simp [Uniform_singleton, Uniform, instFunLike]

-- The value of the uniform distribution over the universe.
@[simp]
lemma Uniform.univ_uniform : (Uniform ⟨(univ : Finset α), univ_nonempty⟩) x = 1/(Fintype.card α) := by
  simp [Uniform, instFunLike]

-- Multiplication of FinPMFs, treating them as independent.
instance instMulFinPMF : HMul (FinPMF α) (FinPMF β) (FinPMF (α × β)) where
  hMul := fun a b => ⟨fun x => (a x.1) * (b x.2), by
    constructor
    simp only [Fintype.sum_prod_type, ← sum_mul_sum, FinPMF.sum_coe, mul_one]
    intros
    apply mul_nonneg <;> simp
  ⟩

@[simp]
theorem FinPMF.mul_val : (a * b) (x, y) = (a x) * (b y) := rfl



-- Applying some function to a random variable.
noncomputable def FinPMF.apply (a : FinPMF α) (f : α → β) : FinPMF β :=
  ⟨(fun x => ∑ y in univ.filter (fun y => f y = x), a y), by
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
theorem apply_weighted_sum (g: α → β) (f : β → ℝ) : ∑ x, ((a.apply g) x) * (f x) = ∑ y, (a y) * (f (g y)) := by
  simp [FinPMF.apply, instFunLike, sum_mul]
  have (x) : ∑ i in filter (fun y => g y = x) univ, a i * f x =
    ∑ i in filter (fun y => g y = x) univ, a i * f (g i) := by
    apply sum_subset_zero_on_sdiff <;> aesop
  conv =>
    lhs
    rhs
    intro x
    exact this x
  rw [←sum_biUnion]
  have : Finset.biUnion univ (fun x => filter (fun y => g y = x) univ) = univ := by
    apply subset_antisymm
    · simp
    · aesop
  simp_all
  rfl
  apply Set.pairwiseDisjoint_filter

-- Subtraction of FinPMFs, treating them as independent.
noncomputable instance instSubFinPMF [Sub α] : HSub (FinPMF α) (FinPMF α) (FinPMF α) where
  hSub := fun a b => (a*b).apply (fun x => x.1 - x.2)

theorem FinPMF.sub_val [Sub α] : a - b = (a*b).apply (fun x => x.1-x.2) := rfl

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
  simp only [instFunLike]
  ext x
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  simp [mul_assoc]

noncomputable def FinPMF.adjust (a : FinPMF α) (x : α) (p : ℝ) (h₁ : 0 ≤ p) (h₂ : p ≤ 1) : FinPMF α :=
  FinPMF.linear_combination (α := Fin 2) ⟨![1-p, p], by
    constructor
    simp
    rw [Fin.forall_fin_two]
    simp [h₁, h₂]
  ⟩ (![a, Uniform_singleton x] : Fin 2 → FinPMF α)
