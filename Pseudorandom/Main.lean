import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Order.SetNotation
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.GroupTheory.FiniteAbelian
import Mathlib.Algebra.Order.Chebyshev
import LeanAPAP.Prereqs.Discrete.DFT.Basic
import LeanAPAP.Prereqs.Expect.Basic

open Classical Finset Real Std Matrix RealInnerProductSpace BigOps

universe u1 u2 u3

attribute [local aesop unsafe 20% apply] le_of_lt
attribute [local simp] Set.Finite.bddAbove Set.finite_range card_univ

section general

variable
   {α : Type u1} [Nonempty α] [Fintype α]
   {β : Type u2} [Nonempty β] [Fintype β]
   (a b : FinPMF α)
   (n : Nat)

-- Definition of PMF over finite types
def FinPMF (α : Type u) [Fintype α] : Type u :=
  { f : α → ℝ // ∑ x, f x = 1 ∧ ∀ x, f x ≥ 0}

instance instFunLike : FunLike (FinPMF α) α ℝ where
  coe p a := p.1 a
  coe_injective' _ _ h := Subtype.eq h

@[simp]
theorem FinPMF.sum_coe (p : FinPMF α) : ∑ a, p a = 1 := p.2.1

@[simp]
theorem FinPMF.nonneg (p : FinPMF α) : 0 ≤ p x := by simp [instFunLike, p.2.2]

-- The maximum value a PMF takes is greater than zero
lemma FinPMF.not_all_zero : 0 < ⨆ x, a x := by
  by_contra
  simp_all
  have := by
    calc
      1 = ∑ x, a x := by simp
      _ ≤ 0 := by
        apply sum_nonpos
        intro i _
        calc
          a i ≤ ⨆ x, a x := by apply le_ciSup; simp
          _ ≤ 0 := by assumption
  linarith

-- Definition of statistical distance
noncomputable def SD : ℝ :=
  ∑ x, |1 / 2 * (a x - b x)|

-- The uniform distribution over some nonempty set.
noncomputable def Uniform (t : { x : Finset α // x.Nonempty }) : FinPMF α := ⟨fun x : α => if x ∈ t.1 then (1 / (t.1.card) : ℝ) else 0, by
  simp [sum_ite]
  have : t.1.card > 0 := Nonempty.card_pos t.2
  simp_all [Nat.pos_iff_ne_zero]
  intro x
  split <;> simp
⟩

-- The value of the uniform distribution over the universe.
@[simp]
lemma Uniform.univ_uniform : (Uniform ⟨(univ : Finset α), univ_nonempty⟩) x = 1/(Fintype.card α) := by
  simp [Uniform, instFunLike]

-- A simple lemma about absolute value.
lemma abs_ite (x : ℝ) : |x| = if x ≥ 0 then x else -x := by aesop

noncomputable def min_entropy : ℝ :=
  -(logb 2 (⨆ x : α, a x))

lemma min_entropy_le (k : ℝ) : min_entropy a ≥ k ↔ ∀ i, a i ≤ 2^(-k) := by
  constructor
  intros p i
  calc
    a i ≤ ⨆ x, a x := by apply le_ciSup; simp
    _ = 2^(logb 2 (⨆ x, a x)) := by rw [rpow_logb]; aesop; aesop; apply FinPMF.not_all_zero
    _ = 2^(-min_entropy a) := by simp [min_entropy]
    _ ≤ 2^(-k) := by apply rpow_le_rpow_of_exponent_le <;> linarith
  intro p
  simp [min_entropy]
  rw [le_neg]
  rw [←logb_rpow (x := -k) zero_lt_two (OfNat.ofNat_ne_one 2)]
  apply logb_le_logb_of_le
  exact one_lt_two
  apply FinPMF.not_all_zero
  exact ciSup_le p

-- min entropy implies a bound on the L2 norm of the function.
lemma min_entropy_l2_norm (k : ℕ) (a : FinPMF α) (h : ↑k ≤ min_entropy a):
  ‖(WithLp.equiv 2 (α → ℝ)).symm a‖ ≤ 2 ^ (-k/2 : ℝ) := by
    rw [PiLp.norm_eq_sum]
    simp
    suffices ∑ x : α, a x ^ 2 ≤ 2 ^ (-k : ℝ) by
      rw [←one_div, div_eq_mul_one_div (-k : ℝ) 2, rpow_mul]
      apply rpow_le_rpow
      apply sum_nonneg
      repeat aesop
    calc
      ∑ x : α, a x ^ 2 ≤ ∑ x : α, a x * 2^(-k:ℝ) := by
        apply sum_le_sum
        intro i _
        rw [sq (a i)]
        apply mul_le_mul_of_nonneg_left
        apply (min_entropy_le a _).1
        simp_all
        simp
      _ ≤ 2^(-k:ℝ) := by simp [←sum_mul]
    simp

-- Multiplication of FinPMFs, treating them as independent.
instance instMulFinPMF : HMul (FinPMF α) (FinPMF β) (FinPMF (α × β)) where
  hMul := fun a b => ⟨fun x => (a x.1) * (b x.2), by
    constructor
    simp [←sum_mul_sum]
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

/- A function in an (k, ε)-two extractor if for any two indepndent random variables,
  each with min entropy at least k, the distance of the function from uniformity is
  at most ε.
-/
noncomputable def two_extractor {γ : Type u3} [Nonempty γ] [Fintype γ]
  (h : (α × β) → γ) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ a, ∀ b, (min_entropy a ≥ k ∧ min_entropy b ≥ k) → (SD ((a * b).apply h) (Uniform ⟨univ, univ_nonempty⟩) ≤ ε)


end general

section chor_goldreich

-- An alternative expression for the statistical distance from uniformity in ℤ₂
lemma SD_Uni2 (a : FinPMF (ZMod 2)) : SD a (Uniform ⟨univ, univ_nonempty⟩) = |∑ x, (a x) * (-1)^(x.val)| * (1/2) := by
  simp [SD]
  conv =>
    lhs
    apply Fin.sum_univ_two
  conv =>
    rhs
    lhs
    rhs
    apply Fin.sum_univ_two
  simp [ZMod.val]
  have : a 0 = 1 - a 1 := by
    apply eq_sub_of_add_eq
    rw [(Fin.sum_univ_two a).symm]
    apply FinPMF.sum_coe
  rw [this]
  ring_nf
  have : -(1/4 + a 1 * (-1/2)) = (-1/4 + a 1 * (1/2)) := by ring
  rw [←this, abs_neg, ←mul_two, mul_one_div]
  field_simp
  rw [mul_assoc, ←abs_of_nonneg (a := (2*2 : ℝ)), ←abs_mul]
  ring_nf
  exact mul_self_nonneg 2

/- For a nontrivial character, the sum over the domain is 0.
   This is only the proof for ℤ₂ⁿ.
-/
lemma inner_product_sum (n : ℕ)
  (x : Fin n → ZMod 2) (h : x ≠ 0) :
  ∑ y : Fin n → ZMod 2, (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) = 0 := by
  have : ¬∀ i, x i = 0 := by
    intro v
    suffices x = 0 by trivial
    funext a
    exact v a
  simp at this
  have ⟨i, hi_⟩ := this
  clear this
  have hi : x i = 1 := by
    have := Fin.exists_fin_two.mp (Exists.intro (x i) rfl)
    simp_all
  clear hi_ h
  calc ∑ y : Fin n → ZMod 2, (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x)
    _ = ∑ y in univ.filter (fun (x: Fin n → ZMod 2) => x i = 0), (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) +
        ∑ y in (univ.filter (fun (x: Fin n → ZMod 2) => x i = 0))ᶜ, (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) := by
      rw [sum_add_sum_compl]
    _ = ∑ y in univ.filter (fun (x: Fin n → ZMod 2) => x i = 0), (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) +
        ∑ y in univ.filter (fun (x: Fin n → ZMod 2) => x i = 0), -(-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) := by
        congr 1
        apply sum_nbij' (fun x => Function.update x i 0) (fun x => Function.update x i 1)
        · intros
          simp
        · intros
          simp
        repeat {
          intros x h
          funext j
          by_cases h₂ : i = j
          · rw [h₂]
            simp
            rw [h₂] at h
            simp at h
            have := Fin.exists_fin_two.mp (Exists.intro (x j) rfl)
            simp_all only [false_or]
          · simp_all
            rw [Function.update_noteq]
            tauto
          }
        · intros y h'
          simp_all
          have h : y i = 1 := by
            have := Fin.exists_fin_two.mp (Exists.intro (y i) rfl)
            simp_all
          clear h'
          rw [neg_eq_neg_one_mul ((-1) ^ _), ←pow_succ]
          rw [(_ : 1 = ZMod.val (1 : ZMod 2))]
          conv =>
            rhs
            rw [neg_one_pow_eq_pow_mod_two, ←ZMod.val_add]
          congr
          simp [Matrix.dotProduct]
          conv =>
            congr <;> rw [sum_eq_add_sum_diff_singleton (i := i) (mem_univ i)]
          simp only [h, hi, mul_one, Function.update_same, zero_add, add_comm]
          congr 1
          apply sum_congr
          rfl
          aesop
          trivial
    _ = 0 := by simp

/- Any two different characters are orthogonal.
   This is only the proof for ℤ₂ⁿ.
-/
lemma inner_product_orthogonal (n : ℕ)
  (x z : Fin n → ZMod 2) (h : x ≠ z) :
  ∑ y : Fin n → ZMod 2, (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) * (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ z) = 0 := by
  simp [←pow_add]
  conv =>
    lhs
    rhs
    intro x
    rw [neg_one_pow_eq_pow_mod_two, ←ZMod.val_add, ←dotProduct_add]
  apply inner_product_sum
  intro v
  suffices x = z by contradiction
  funext i
  apply sub_eq_zero.1
  have : (x + z) i = (0 : Fin n → ZMod 2) i := by rw [v]
  simp_all

-- The Chor-Goldreich Extractor
theorem inner_product_extractor (n k : ℕ) : two_extractor (fun (x : (Fin n → ZMod 2) × (Fin n → ZMod 2)) => Matrix.dotProduct x.1 x.2)
  k (2^(n/2 - k - 1 : ℝ)) := by
  simp only [two_extractor, ge_iff_le, and_imp]
  intros a b _ _
  rw [SD_Uni2]
  simp [apply_weighted_sum]
  calc |∑ x : Fin n → ZMod 2, ∑ x_1 : Fin n → ZMod 2, a x * b x_1 * (-1) ^ ZMod.val (x ⬝ᵥ x_1)| * 2⁻¹
    _ = |a ⬝ᵥ (∑ x, (fun y => (-1) ^ ZMod.val (y ⬝ᵥ x) * b x))| * 2⁻¹ := by
      simp only [dotProduct, Finset.sum_apply, mul_eq_mul_right_iff, inv_eq_zero,
        OfNat.ofNat_ne_zero, or_false, mul_sum]
      congr
      funext x
      congr
      funext y
      ring_nf
    _ = ‖⟪(WithLp.equiv 2 ((Fin n → ZMod 2) → ℝ)).symm a,
        (WithLp.equiv 2 _).symm (∑ x, (fun y => (-1) ^ ZMod.val (y ⬝ᵥ x) * b x))⟫_ℝ‖ * 2⁻¹ := rfl
    _ ≤ ‖(WithLp.equiv 2 ((Fin n → ZMod 2) → ℝ)).symm a‖ *
      ‖(WithLp.equiv 2 _).symm (∑ x, (fun y => (-1) ^ ZMod.val (y ⬝ᵥ x) * b x))‖ * 2⁻¹ := by
          apply mul_le_mul_of_nonneg_right
          apply norm_inner_le_norm -- Cauchy-Schwartz
          simp only [inv_nonneg]
          exact zero_le_two
    _ ≤ 2^(-k/2 : ℝ) * ‖(WithLp.equiv 2 _).symm
          (∑ x, (fun y => (-1) ^ ZMod.val (y ⬝ᵥ x) * b x))‖ * 2⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_right
      apply min_entropy_l2_norm
      assumption
      apply norm_nonneg
      simp only [inv_nonneg]
      exact zero_le_two
    _ ≤ 2^(-k/2 : ℝ) * 2^(n/2 - k/2 : ℝ) * 2⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_left
      calc ‖(WithLp.equiv 2 _).symm (∑ x, (fun y => (-1) ^ ZMod.val (y ⬝ᵥ x) * b x))‖
        _ = sqrt (∑ y, (∑ x, (-1) ^ ZMod.val (y ⬝ᵥ x) * b x)^2) := by
          simp [EuclideanSpace.norm_eq]
        _ = sqrt (∑ y, ∑ x, ∑ z, ((-1) ^ ZMod.val (y ⬝ᵥ x) * b x) *
            ((-1) ^ ZMod.val (y ⬝ᵥ z) * b z)) := by simp [sq, sum_mul_sum]
        _ = sqrt (∑ x, ∑ z, ∑ y, ((-1) ^ ZMod.val (y ⬝ᵥ x) * b x) *
            ((-1) ^ ZMod.val (y ⬝ᵥ z) * b z)) := by
          rw [sum_comm]
          congr
          congr
          funext
          rw [sum_comm]
        _ = sqrt (∑ x, ∑ z, b x * b z * ∑ y, (-1) ^ ZMod.val (y ⬝ᵥ x) * (-1) ^ ZMod.val (y ⬝ᵥ z)) := by
          congr
          congr; funext; congr; funext
          ring_nf
          simp [mul_sum, mul_assoc]
        _ = sqrt (∑ x, b x * b x * 2^(n:ℝ)) := by
          congr
          funext x
          rw [sum_eq_add_sum_diff_singleton (i := x)]
          have : ∑ x_1 in univ \ {x}, b x * b x_1 * ∑ y, (-1) ^ ZMod.val (y ⬝ᵥ x) *
            (-1) ^ ZMod.val (y ⬝ᵥ x_1) = 0 := by
            apply sum_eq_zero
            intro z p
            simp
            right
            have D : x ≠ z := by aesop
            exact inner_product_orthogonal n x z D
          rw [this]
          simp
          left
          conv =>
            lhs
            rhs
            intro y
            rw [←sq, ←pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
          rw [sum_const]
          simp
          apply mem_univ
        _ = 2^(n/2 : ℝ) * ‖(WithLp.equiv 2 ((Fin n → ZMod 2) → ℝ)).symm b‖ := by
          rw [←sum_mul, mul_comm, sqrt_mul, sqrt_eq_rpow, ←rpow_mul]
          simp [EuclideanSpace.norm_eq, sq]
          left
          ring_nf
          exact zero_le_two
          apply rpow_nonneg zero_le_two
        _ ≤ 2^(n/2 : ℝ) * 2^(-k/2 : ℝ) := by
          apply mul_le_mul_of_nonneg_left
          apply min_entropy_l2_norm
          assumption
          apply rpow_nonneg zero_le_two
        _ = 2^(n/2-k/2 : ℝ) := by rw [←rpow_add]; congr; ring; exact zero_lt_two
      apply rpow_nonneg zero_le_two
      simp
    _ = (2^(n/2 - k - 1 : ℝ)) := by simp [←rpow_neg_one, ←rpow_add, ←rpow_add]; congr 1; ring

end chor_goldreich


variable
   {α : Type u1} [Nonempty α] [Fintype α] [AddCommGroup α]
   (a b : FinPMF α)
   (n : Nat)

-- Subtraction of FinPMFs, treating them as independent.
noncomputable instance instSubFinPMF : HSub (FinPMF α) (FinPMF α) (FinPMF α) where
  hSub := fun a b => (a*b).apply (fun x => x.1 - x.2)

theorem FinPMF.sub_val : a - b = (a*b).apply (fun x => x.1-x.2) := rfl

open scoped NNReal

-- Note: their DFT isn't normalized.

theorem XOR_lemma' (ε : ℝ≥0) (h : ∀ χ : AddChar α ℂ, (AddChar.IsNontrivial χ) → ‖dft (a ·) χ‖ ≤ ε) :
  ∑ x : α, (a x - (Fintype.card α : ℝ)⁻¹)^2 ≤ (ε : ℝ)^2 := by
  let f := (fun x => (a x : ℂ)) - Function.const α ((Fintype.card α : ℂ)⁻¹)
  calc ∑ x : α, (a x - (Fintype.card α : ℝ)⁻¹)^2
    _ = ‖f‖_[2]^2 := by
      simp [lpNorm_eq_sum']
      rw [←rpow_mul_natCast]
      simp
      apply sum_congr
      rfl
      intros
      rw [←(Complex.abs_re_eq_abs).mpr]
      simp [f]
      simp [f]
      apply sum_nonneg
      aesop
    _ = ‖dft f‖ₙ_[2]^2 := by rw [nl2Norm_dft]
    _ = 𝔼 x, ‖dft f x‖^2 := by
      simp [nlpNorm_eq_expect']
      rw [←rpow_mul_natCast]
      simp
      apply expect_nonneg
      aesop
    _ ≤ 𝔼 (x : AddChar α ℂ), (ε : ℝ)^2 := by
      apply expect_le_expect
      intro i _
      rw [sq_le_sq]
      rw [Complex.norm_eq_abs, Complex.abs_abs, NNReal.abs_eq, ←Complex.norm_eq_abs]
      by_cases h₂ : i = 0
      simp [h₂, dft_apply, l2Inner_eq_sum, f]
      have : ∑ x, (a x : ℂ) = Complex.ofReal (∑ x, a x) := by
        simp only [map_sum, Complex.ofReal_eq_coe]
      rw [this]
      simp
      simp [dft_sub, f]
      rw [dft_const]
      simp
      apply h i
      rw [AddChar.isNontrivial_iff_ne_trivial]
      aesop
      aesop
    _ = (ε : ℝ)^2 := by simp

theorem XOR_lemma (ε : ℝ≥0) (h : ∀ χ : AddChar α ℂ, (AddChar.IsNontrivial χ) → ‖dft (a ·) χ‖ ≤ ε) :
  SD a (Uniform ⟨univ, univ_nonempty⟩) ≤ 2⁻¹ * ε * Real.sqrt (Fintype.card α) := by
  simp [SD, Uniform.univ_uniform]
  calc ∑ x : α, |2⁻¹ * (a x - (↑(Fintype.card α))⁻¹)|
    _ = Real.sqrt ((∑ x : α, |2⁻¹ * (a x - (↑(Fintype.card α))⁻¹)|)^2) := by
      apply Eq.symm
      apply sqrt_sq
      apply sum_nonneg
      intros
      apply abs_nonneg
    _ ≤ Real.sqrt ((Fintype.card α) * (∑ x : α, |2⁻¹ * (a x - (↑(Fintype.card α))⁻¹)|^2)) := by
      apply Real.sqrt_le_sqrt
      apply sq_sum_le_card_mul_sum_sq
    _ = Real.sqrt ((Fintype.card α) * (∑ x : α, (2⁻¹ * (a x - (↑(Fintype.card α))⁻¹))^2)) := by congr; ext; apply sq_abs
    _ = Real.sqrt ((Fintype.card α) * (∑ x : α, 2⁻¹^2 * (a x - (↑(Fintype.card α))⁻¹)^2)) := by
      congr
      ext
      rw [mul_pow]
    _ = Real.sqrt ((Fintype.card α) * 2⁻¹^2 * (∑ x : α, (a x - (↑(Fintype.card α))⁻¹)^2)) := by
      congr 1
      simp [←mul_sum]
      ring
    _ ≤ Real.sqrt ((Fintype.card α) * 2⁻¹^2 * ε^2) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left (XOR_lemma' a ε h)
      simp
    _ = 2⁻¹ * ε * Real.sqrt (Fintype.card α) := by
      rw [Real.sqrt_eq_iff_sq_eq]
      ring_nf
      simp
      apply mul_nonneg
      simp
      apply sq_nonneg
      apply mul_nonneg
      apply mul_nonneg
      simp
      simp
      apply sqrt_nonneg



-- lemma lemma_7

#print axioms inner_product_extractor
#check inner_product_extractor
