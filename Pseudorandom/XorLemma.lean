import Pseudorandom.SD
import Pseudorandom.LpLemmas
import Mathlib.Tactic.Rify
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Chebyshev
import LeanAPAP.Prereqs.Discrete.DFT.Compact
import LeanAPAP.Prereqs.Expect.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Int.CardIntervalMod

open Real Finset BigOps

variable {α : Type*} [αnonempty: Nonempty α] [Fintype α] [AddCommGroup α]
  {β : Type*} [Nonempty β] [Fintype β] [AddCommGroup β]
  (a b : α → ℝ)

theorem L1_le_card_rpow_mul_dft_norm :
    ‖a‖_[1] ≤ ((Fintype.card α)^(3/2 : ℝ) : ℝ) * ‖cft (a ·)‖_[⊤] :=
  calc
    ‖a‖_[1] ≤ Real.sqrt (Fintype.card α) * ‖a‖_[(2 : NNReal)] := l1Norm_le_sqrt_card_mul_l2Norm ..
    _ = (Fintype.card α) * ‖a‖ₙ_[2] := by
      rw [lpNorm_eq_card_rpow_mul_nlpNorm]
      rw [← mul_assoc]
      congr
      rw [Real.sqrt_eq_rpow, ← rpow_add]
      norm_num
      simp [Fintype.card_pos]
      norm_num
    _ = (Fintype.card α) * ‖cft (a ·)‖_[2] := by
      congr
      rw [l2Norm_cft, nlpNorm_eq_expect', nlpNorm_eq_expect']
      congr
      ext
      simp
      simp
      simp
    _ ≤ (Fintype.card α) * (Real.sqrt (Fintype.card α) * ‖cft (a ·)‖_[⊤]) := by
      gcongr
      rw [Real.sqrt_eq_rpow]
      convert lpNorm_le_card_rpow_mul_linftyNorm (cft (a ·)) 2 (by norm_num) using 3
      simp
      simp
    _ = ((Fintype.card α)^(3/2 : ℝ) : ℝ) * ‖cft (a ·)‖_[⊤] := by
      rw [sqrt_eq_rpow, ← mul_assoc, ← rpow_one_add']
      congr 1
      norm_num
      simp
      norm_num

lemma lemma43 [DecidableEq β] (t ε : NNReal)
    (h : ∀ χ : AddChar α ℂ, (AddChar.IsNontrivial χ) → ‖cft (a ·) χ‖ ≤ ε / (Fintype.card α))
    (σ : α → β) (h₂ : ∀ χ : AddChar β ℂ,
      ‖cft (χ ∘ σ)‖_[1] ≤ t
    ):
    ‖σ # a - σ # (Function.const α (𝔼 x, a x))‖_[1] ≤ t * ε * Real.sqrt (Fintype.card β)
  := by
  suffices ‖cft (fun x => (σ # a - σ # (Function.const α (𝔼 x, a x))) x)‖_[⊤] ≤ t * ε / (Fintype.card β) by
    calc ‖σ # a - σ # (Function.const α (𝔼 x, a x))‖_[1]
      _ ≤ (Fintype.card β)^(3/2 : ℝ) * ‖cft (fun x => (σ # a - σ # (Function.const α (𝔼 x, a x))) x)‖_[⊤] := L1_le_card_rpow_mul_dft_norm _
      _ ≤ (Fintype.card β)^(3/2 : ℝ) * (t * ε / (Fintype.card β)) := by gcongr
      _ = t * ε * ((Fintype.card β)^(3/2 : ℝ) / (Fintype.card β)) := by ring
      _ = t * ε * Real.sqrt (Fintype.card β) := by
        rw [sqrt_eq_rpow, ← rpow_sub_one]
        norm_num
        simp
  rw [linftyNorm_eq_ciSup]
  apply ciSup_le
  intro χ
  dsimp only [cft_apply, nl2Inner_eq_expect]
  simp_rw [← transfer_sub]
  change ‖expect _ fun i => _ * (Complex.ofReal ∘ _) i‖ ≤ _
  simp_rw [comp_transfer]
  conv =>
    lhs
    rhs
    rhs
    intro
    rw [mul_comm]
  rw [transfer_expect]
  simp_rw [mul_comm]
  rw [← nl2Inner_eq_expect]
  by_cases he : χ = 0
  · simp only [he, AddChar.one_apply, Function.comp_apply, Pi.sub_apply, map_sub,
      Complex.ofReal_eq_coe, map_div₀, map_sum, map_natCast, Complex.norm_eq_abs]
    change Complex.abs (_ • nl2Inner (Function.const α 1) _) ≤ _
    rw [nl2Inner_const_left]
    simp [expect_sub_distrib]
    positivity
  · calc ‖(Fintype.card α / Fintype.card β : NNRat) • nl2Inner (χ ∘ σ) (⇑Complex.ofReal ∘ (a - Function.const α (expect univ fun x => a x)))‖
      _ = (Fintype.card α / Fintype.card β : ℝ) * ‖nl2Inner (χ ∘ σ) (⇑Complex.ofReal ∘ (a - Function.const α (expect univ fun x => a x)))‖ := by
        rw [← nnratCast_smul_eq_nnqsmul ℝ]
        simp
      _ = (Fintype.card α / Fintype.card β : ℝ) * ‖l2Inner (cft (χ ∘ σ)) (cft (⇑Complex.ofReal ∘ (a - Function.const α (expect univ fun x => a x))))‖ := by
        rw [l2Inner_cft]
      _ ≤ (Fintype.card α / Fintype.card β : ℝ) * (‖cft (χ ∘ σ)‖_[1] * ‖cft (⇑Complex.ofReal ∘ (a - Function.const α (expect univ fun x => a x)))‖_[⊤]) := by
        gcongr
        apply l2Inner_le_l1Norm_mul_linftyNorm
      _ ≤ (Fintype.card α / Fintype.card β : ℝ) * (t * (ε / (Fintype.card α))) := by
        gcongr
        apply h₂
        rw [linftyNorm_eq_ciSup]
        apply ciSup_le
        intro ψ
        by_cases hψ : ψ = 0
        · simp only [map_comp_sub, Function.comp_const, Complex.ofReal_eq_coe,
          Complex.ofReal_expect, hψ, cft_apply, AddChar.coe_zero, Complex.norm_eq_abs]
          change Complex.abs (nl2Inner (Function.const α 1) _) ≤ _
          rw [nl2Inner_const_left]
          simp [expect_sub_distrib]
          positivity
        · simp only [map_comp_sub, Function.comp_const, Complex.ofReal_eq_coe,
          Complex.ofReal_expect, cft_sub, Pi.sub_apply]
          rw [cft_const]
          simp only [sub_zero]
          apply h
          exact (AddChar.isNontrivial_iff_ne_trivial _).mpr hψ
          exact hψ
      _ = t * ε / (Fintype.card β) := by
        field_simp
        ring_nf


variable (n m : ℕ+) (hₘ : m ≤ n)

local notation "α" => ZMod n
local notation "β" => ZMod m
def lemma44C : ℝ := 1

lemma range_eq_zmod_image : range ↑n = image (fun t => ZMod.val t) (univ : Finset α) := by
  ext x
  simp only [mem_range, mem_image, mem_univ, true_and]
  constructor
  intro v
  exists x
  simp only [ZMod.val_nat_cast]
  apply Nat.mod_eq_of_lt v
  rintro ⟨a, ha⟩
  rw [← ha]
  apply ZMod.val_lt

lemma le_add_div_add_of_le_of_le (a b n : ℝ) (hb : 0 < b) (hn : 0 < n)
    (h : a/b ≤ n) : a/b ≤ (a + 1)/(b + 1/n) := by
  rw [div_le_div_iff]
  rw [div_le_iff] at h
  ring_nf
  gcongr
  rwa [mul_inv_le_iff]
  exact hn
  exact hb
  exact hb
  positivity

lemma circle_lower_bound (x : ℝ) :
  2 - |4 * x - 2| ≤ ‖(Circle.e x : ℂ) - 1‖ := by
  simp only [Circle.coe_e, Complex.ofReal_ofNat, Complex.norm_eq_abs]
  rw [Complex.exp_mul_I, Complex.abs_eq_sqrt_sq_add_sq]
  conv =>
    rhs
    rhs
    congr
    · lhs
      simp [-Complex.ofReal_mul, Complex.cos_ofReal_re]
    · simp [-Complex.ofReal_mul, Complex.sin_ofReal_re]
  conv =>
    rhs
    rhs
    tactic =>
      change _ = 2 - 2 * cos (2 * π * x)
      rw [Real.sin_sq]
      ring_nf
  wlog h : (0 ≤ x ∧ x ≤ 1/2) generalizing x
  · simp only [not_and_or, not_le] at h
    cases h
    · calc
        2 - |4 * x - 2| ≤ 0 := by
          rw [abs_of_nonpos]
          linarith
          linarith
        _ ≤ Real.sqrt (2 - 2 * cos (2 * π * x)) := by positivity
    by_cases x ≤ 1
    · convert this (1 - x) (by constructor <;> linarith) using 2
      · rw [abs_eq_abs]
        right
        ring_nf
      · congr 2
        ring_nf
        conv =>
          rhs
          rw [mul_comm]
        simp
    · calc
        2 - |4 * x - 2| ≤ 0 := by
          rw [abs_of_nonneg]
          linarith
          linarith
        _ ≤ Real.sqrt (2 - 2 * cos (2 * π * x)) := by positivity
  have ⟨h1, h2⟩ := h
  rw [← ge_iff_le]
  calc Real.sqrt (2 - 2 * cos (2 * π * x))
    _ ≥ Real.sqrt (2 - 2 * (1 - 2 / π^2 * (2 * π * x)^2)) := by
      apply Real.sqrt_le_sqrt
      gcongr
      apply Real.cos_quadratic_upper_bound
      rw [abs_of_nonneg]
      rw [mul_comm, ← mul_assoc]
      apply mul_le_of_le_one_left
      positivity
      linarith
      positivity
    _ = Real.sqrt ((4 * x)^2) := by
      congr
      field_simp
      ring_nf
    _ = 4 * x := by apply Real.sqrt_sq; linarith
    _ = 2 - |4 * x - 2| := by
      rw [abs_of_nonpos]
      ring_nf
      linarith

lemma bound_on_apply_uniform :
    ‖((fun (x : α) => (x.val : β)) # (Uniform ⟨univ, univ_nonempty⟩)) - ⇑(Uniform ⟨univ, univ_nonempty⟩)‖_[1]
    ≤ m / n := calc ‖((fun (x : α) => (x.val : β)) # (Uniform ⟨univ, univ_nonempty⟩)) - ⇑(Uniform ⟨univ, univ_nonempty⟩)‖_[1]
  _ = ∑ x, ‖((fun (x : α) => (x.val : β)) # (Uniform ⟨univ, univ_nonempty⟩)) x - 1/m‖ := by
    rw [l1Norm_eq_sum]
    rcongr
    simp
  _ = ∑ x : β, ‖∑ y ∈ (univ.filter fun (y : α) => y.val = x), 1/(n : ℝ) - 1/m‖ := by
    rcongr
    simp
  _ = ∑ x : β, ‖(univ.filter fun (y : α) => y.val = x).card / (n : ℝ) - 1/m‖ := by
    simp [div_eq_mul_inv]
  _ = ∑ x : β, ‖((range n).filter fun (y : ℕ) => y = x).card / (n : ℝ) - 1/m‖ := by
    congr with x
    congr 4
    apply card_congr (fun x _ => x.val)
    · intros
      simp_all [ZMod.val_lt]
    · intros _ _ _ _ h
      exact ZMod.val_injective n h
    · intros a ha
      exists a
      simp_all only [mem_filter, mem_range, mem_univ,
        true_and, exists_prop]
      rw [ZMod.val_cast_of_lt]
      exact ⟨ha.2, rfl⟩
      exact ha.1
  _ = ∑ x : β, ‖(Nat.count (fun (y : ℕ) => y ≡ x.val [MOD m]) n) / (n : ℝ) - 1/m‖ := by
    congr with x
    rw [Nat.count_eq_card_filter_range]
    congr with y
    have : x = (x.val) := by simp
    conv =>
      lhs
      rw [this]
    exact ZMod.eq_iff_modEq_nat m
  _ = ∑ x : β, ‖⌈(n - (x.val % m : ℕ)) / (m : ℚ)⌉ / (n : ℝ) - 1/m‖ := by
    rcongr x
    norm_cast
    rw [Nat.count_modEq_card_eq_ceil n (r := m) (by simp) x.val]
    norm_cast
  _ = ∑ x : β, ‖(⌈(n - (x.val % m : ℕ)) / (m : ℚ)⌉ - n/m) / (n : ℝ)‖ := by
    rcongr
    field_simp [mul_comm]
  _ = (∑ x : β, ‖(⌈(n - (x.val % m : ℕ)) / (m : ℚ)⌉ - n/m : ℝ)‖) / (n : ℝ) := by
    simp_rw [sum_div, norm_div]
    rcongr
    simp
  _ ≤ (∑ x : β, 1) / (n : ℝ) := by
    gcongr with x
    simp only [norm_eq_abs, abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add]
      calc (⌈(n - (x.val % m : ℕ)) / (m : ℚ)⌉ : ℝ)
        _ ≤ ⌊(n - (x.val % m : ℕ)) / (m : ℚ)⌋ + 1 := by
          norm_cast
          apply Int.ceil_le_floor_add_one
        _ ≤ (n - (x.val % m : ℕ)) / (m : ℚ) + 1 := by
          norm_cast
          push_cast
          rel [Int.floor_le ( Rat.divInt (Int.subNatNat n (x.val % m : ℕ)) m )]
        _ ≤ n / m + 1 := by
          gcongr
          norm_num
          norm_num
          rfl
        _ = 1 + n/m := add_comm ..
    · rw [sub_le_iff_le_add]
      calc n / (m : ℝ)
        _ = 1 + (n - m) / m := by field_simp
        _ ≤ 1 + (n - (x.val % m : ℕ)) / m := by
          gcongr
          norm_cast
          apply le_of_lt (Nat.mod_lt ..)
          simp
        _ ≤ 1 + ⌈(n - (x.val % m : ℕ)) / (m : ℚ)⌉ := by
          gcongr
          norm_cast
          apply Int.le_ceil
  _ = m / n := by simp [card_univ]

set_option maxHeartbeats 500000

theorem lemma44 (χ : AddChar β ℂ) : ‖cft (χ ∘ (fun x : α => (x.val : β)))‖_[1] ≤ 6 * Real.log n + 6 := by
  simp_rw [l1Norm_eq_sum, cft_apply, nl2Inner, expect]
  simp only [Function.comp_apply, ← nnratCast_smul_eq_nnqsmul ℂ, NNRat.cast_inv, NNRat.cast_natCast,
    smul_eq_mul, norm_mul, norm_inv, Complex.norm_nat]
  simp_rw [← AddChar.map_neg_eq_conj, ← mul_sum]
  let w := (AddChar.zmodAddEquiv (n := m) (by simp)).symm χ
  have (y) : χ y = (AddChar.zmod m w) y := by
    have : χ = AddChar.zmodAddEquiv (n := m) (by simp) w := by unfold_let w; simp
    simp [this]
    rfl
  simp_rw [this]
  rw [← Equiv.sum_comp (ι := α) (κ := AddChar α ℂ) (AddChar.zmodAddEquiv (n := n) (by simp))]
  conv =>
    lhs
    rhs
    rhs
    intro t
    rhs
    rhs
    intro x
    tactic =>
      simp only [EquivLike.coe_coe, AddChar.zmodAddEquiv_apply]
      change ((AddChar.zmod n t) (-x) * (AddChar.zmod m w) (x.val) : circle) = (_ : ℂ)
      convert_to ((AddChar.zmod n (t.val : ℤ)) (- x.val : ℤ) * (AddChar.zmod m (w.val : ℤ)) (x.val : ℤ) : circle) = (_ : ℂ)
      congr <;> simp
      simp only [AddChar.zmod_apply]
      simp only [ZMod.nat_cast_val, ZMod.int_cast_cast, Int.cast_neg, mul_neg, ←
        AddChar.map_add_mul]
      convert_to Circle.e (x.val * (w.val * n - t.val * m) / (n * m)) = (_ : ℂ)
      congr
      simp only [ZMod.nat_cast_val]
      field_simp
      ring
      rfl
  calc (univ.card : ℝ)⁻¹ * ∑ t : α, ‖∑ x : α, (Circle.e (x.val * (w.val * n - t.val * m) / (n * m)) : ℂ)‖
    _ = (n : ℝ)⁻¹ * ∑ t : α, ‖∑ x ∈ Finset.range n,
        (Circle.e (x * (w.val * n - t.val * m) / (n * m)) : ℂ)‖ := by
      congr
      simp [card_univ]
      ext t
      congr 1
      apply Eq.symm
      convert Finset.sum_image ?_
      apply range_eq_zmod_image
      intro x _ y _ v
      apply ZMod.val_injective n v
    _ = (n : ℝ)⁻¹ * ∑ t : α, ‖∑ x ∈ Finset.range n,
        (Circle.e ((w.val * n / m - t.val) / n) : ℂ)^x‖ := by
      congr with _
      congr with _
      rw [← SubmonoidClass.coe_pow, ← AddChar.map_nsmul_pow]
      congr 2
      field_simp
      ring_nf
    _ ≤ (n : ℝ)⁻¹ * ∑ t : α,
        (‖(Circle.e ((w.val * n / m - t.val) / n) : ℂ)^↑n - 1‖ + 1) /
        (‖(Circle.e ((w.val * n / m - t.val) / n) : ℂ) - 1‖ + 1 / n) := by
      gcongr with t ht
      by_cases h : (Circle.e ((w.val * n / m - t.val) / n) : ℂ) = 1
      · rw [h]
        simp
      · have := geom_sum_eq (x := (Circle.e ((w.val * n / m - t.val) / n) : ℂ)) h n
        apply_fun (‖·‖) at this
        rw [norm_div] at this
        rw [this]
        apply le_add_div_add_of_le_of_le
        simp only [Complex.norm_eq_abs, AbsoluteValue.pos_iff]
        exact fun v => h (eq_of_sub_eq_zero v)
        simp
        rw [← this]
        convert norm_sum_le ..
        convert_to ∑ i ∈ Finset.range n, (1 : ℝ) = _
        simp
        apply sum_congr
        rfl
        intros
        simp [-Circle.coe_e]
    _ ≤ (n : ℝ)⁻¹ * ∑ t : α,
        ((‖(Circle.e ((w.val * n / m - t.val) / n) : ℂ)^↑n‖ + ‖(1 : ℂ)‖) + 1) /
        (‖(Circle.e ((w.val * n / m - t.val) / n) : ℂ) - 1‖ + 1 / n) := by
      gcongr
      apply norm_sub_le
    _ ≤ (n : ℝ)⁻¹ * ∑ t : α,
        ((1 + (1 : ℝ)) + 1) /
        (‖(Circle.e ((w.val * n / m - t.val) / n) : ℂ) - 1‖ + 1 / n) := by
      simp [-Circle.coe_e]
    _ = 3 * ∑ t : α,
        (n : ℝ)⁻¹ /
        (‖(Circle.e ((w.val * n / m - t.val) / n) : ℂ) - 1‖ + 1 / n) := by
      rw [mul_sum, mul_sum]
      congr
      ext
      ring_nf
    _ = 3 * ∑ t : α,
        1 / (n * (‖(Circle.e ((w.val * n / m - t.val) / n) : ℂ) - 1‖ + 1 / n)) := by
      congr
      ext
      field_simp
    _ = 3 * ∑ t : α,
        1 / (n * (‖(Circle.e (Int.fract ((w.val * n / m - t.val) / n)) : ℂ) - 1‖ + 1 / n)) := by
      simp
    _ ≤ 3 * ∑ t : α,
        1 / (n * ((2 - |4 * Int.fract ((w.val * n / m - t.val) / n : ℝ) - 2|) + 1 / n)) := by
      gcongr
      · apply mul_pos
        simp
        apply add_pos_of_nonneg_of_pos
        apply sub_nonneg_of_le
        simp only [abs_sub_le_iff]
        constructor
        apply sub_left_le_of_le_add
        norm_num
        exact le_of_lt (Int.fract_lt_one _)
        apply sub_le_self
        apply mul_nonneg
        norm_num
        apply Int.fract_nonneg
        simp
      apply circle_lower_bound
    _ = 3 * ∑ t : α,
        1 / (2*n - |4 * (n * Int.fract ((w.val * n / m - t.val) / n : ℝ)) - 2 * n| + 1) := by
      rcongr
      ring_nf
      conv =>
        lhs
        rhs
        rhs
        rw [← abs_of_nonneg (by simp : 0 ≤ (n : ℝ)), ← abs_mul, abs_of_nonneg (by simp : 0 ≤ (n : ℝ))]
      field_simp
      ring_nf
    _ = 3 * ∑ t : α,
        1 / (2*n - |4 * (n * Int.fract (((⌊w.val * n / (m : ℝ)⌋ + Int.fract (w.val * n / m : ℝ)) - t.val) / n : ℝ)) - 2 * n| + 1) := by simp
    _ = 3 * ∑ t : α,
        1 / (2*n - |4 * (n * Int.fract ((Int.fract (w.val * n / m : ℝ) + (⌊w.val * n / (m : ℝ)⌋ - t.val)) / n : ℝ)) - 2 * n| + 1) := by
      rcongr
      ring_nf
    _ = 3 * ∑ t : α,
        1 / (2*n - |4 * (n * Int.fract ((Int.fract (w.val * n / m : ℝ) + (⌊w.val * n / (m : ℝ)⌋ - t).val) / n : ℝ)) - 2 * n| + 1) := by
      congr with t
      congr 7
      rw [Int.fract_eq_fract]
      field_simp
      rw [← ZMod.nat_cast_val, ← ZMod.nat_cast_val, ← ZMod.nat_cast_val]
      norm_cast
      apply exists_eq_mul_left_of_dvd
      rw [← ZMod.int_cast_zmod_eq_zero_iff_dvd]
      simp
    _ = 3 * ∑ t : α,
        1 / (2*n - |4 * (n * Int.fract ((Int.fract (w.val * n / m : ℝ) + t.val) / n : ℝ)) - 2 * n| + 1) := by
      congr 1
      apply Fintype.sum_bijective (fun (x : α) => (⌊w.val * n / (m : ℝ)⌋ - x))
      · apply Function.Involutive.bijective
        intro x
        simp
      · intro x
        rfl
    _ = 3 * ∑ t : α,
        1 / (2*n - |4 * (n * ((Int.fract (w.val * n / m : ℝ) + t.val) / n : ℝ)) - 2 * n| + 1) := by
      rcongr
      rw [Int.fract_eq_self]
      constructor
      · apply div_nonneg
        apply add_nonneg
        simp
        norm_cast
        simp
        simp
      · rw [div_lt_one, ← lt_sub_iff_add_lt]
        refine (Int.fract_lt_one _).trans_le ?_
        rw [le_sub_iff_add_le]
        norm_cast
        rw [Nat.one_add_le_iff]
        apply ZMod.val_lt
        simp
    _ = 3 * ∑ t : α,
        1 / (2*n - |4 * (Int.fract (w.val * n / m : ℝ) + t.val) - 2 * n| + 1) := by
      rcongr
      field_simp
      ring_nf
    _ = 3 * ∑ t ∈ Finset.range n,
        1 / (2*n - |4 * (Int.fract (w.val * n / m : ℝ) + t) - 2 * n| + 1) := by
      congr 1
      apply Eq.symm
      convert Finset.sum_image ?_
      apply range_eq_zmod_image
      intro x _ y _ v
      apply ZMod.val_injective n v
    _ = 3 * ∑ t ∈ Finset.range n,
        if t ≤ n/2 - Int.fract (w.val * n / m : ℝ) then
          1 / (4 * (Int.fract (w.val * n / m : ℝ) + t) + 1)
        else
          1 / (4 * (n - (Int.fract (w.val * n / m : ℝ) + t)) + 1) := by
      rcongr t
      split
      · rw [abs_of_nonpos]
        ring_nf
        linarith
      · rw [abs_of_nonneg]
        ring_nf
        linarith
    _ ≤ 3 * ∑ t ∈ Finset.range n,
        if t ≤ n/2 - Int.fract (w.val * n / m : ℝ) then
          1 / (4 * t + 1 : ℝ)
        else
          1 / (4 * (n - (1 + t)) + 1 : ℝ) := by
      gcongr with i hi
      split
      · rw [one_div, one_div, inv_le_inv]
        linarith [Int.fract_nonneg (w.val * n / m : ℝ)]
        linarith [Int.fract_nonneg (w.val * n / m : ℝ)]
        positivity
      · have : 1 ≤ (n : ℕ) := by norm_cast; simp
        simp only [mem_range] at hi
        apply Nat.le_sub_one_of_lt at hi
        have : (i : ℝ) ≤ (n : ℝ) - 1 := by exact_mod_cast hi
        rw [one_div, one_div, inv_le_inv]
        linarith [Int.fract_lt_one (w.val * n / m : ℝ)]
        linarith [Int.fract_lt_one (w.val * n / m : ℝ)]
        linarith
    _ ≤ 3 * ∑ t ∈ Finset.range n,
        (1 / (4 * t + 1 : ℝ) + 1 / (4 * (n - (1 + t)) + 1 : ℝ)) := by
      gcongr with i hi
      have : 1 ≤ (n : ℕ) := by norm_cast; simp
      simp only [mem_range] at hi
      apply Nat.le_sub_one_of_lt at hi
      have : (i : ℝ) ≤ (n : ℝ) - 1 := by exact_mod_cast hi
      split
      · simp only [one_div, le_add_iff_nonneg_right, inv_nonneg]
        linarith
      · simp only [one_div, le_add_iff_nonneg_left, inv_nonneg, ge_iff_le]
        linarith
    _ = 3 * (∑ t ∈ Finset.range n, 1 / (4 * t + 1 : ℝ) + ∑ t ∈ Finset.range n, 1 / (4 * (n - (1 + t)) + 1 : ℝ)) := by
      rw [sum_add_distrib]
    _ = 3 * (∑ t ∈ Finset.range n, 1 / (4 * t + 1 : ℝ) + ∑ t ∈ Finset.range n, 1 / (4 * t + 1 : ℝ)) := by
      congr 2
      convert Finset.sum_range_reflect ?_ n
      rename_i x hx
      congr 3
      simp only [mem_range] at hx
      have : 1+x ≤ (n : ℕ) := Nat.one_add_le_iff.mpr hx
      norm_cast
      rw [Nat.sub_add_eq]
    _ = 6 * (∑ t ∈ Finset.range n, 1 / (4 * t + 1 : ℝ)) := by rw [← two_mul]; ring
    _ ≤ 6 * ((∑ t ∈ Finset.range n, (t + 1 : ℚ)⁻¹ : ℚ) : ℝ) := by
      push_cast
      simp only [one_div]
      gcongr
      linarith
    _ = 6 * (harmonic n : ℝ) := by
      unfold harmonic
      norm_cast
    _ ≤ 6 * (1 + Real.log n) := by gcongr; apply harmonic_le_one_add_log
    _ = 6 * Real.log n + 6 := by ring_nf

theorem generalized_XOR_lemma (ε : NNReal)
    (a : FinPMF α) (h : ∀ χ : AddChar α ℂ, (AddChar.IsNontrivial χ) → ‖cft (a ·) χ‖ ≤ ε / Fintype.card α) :
    SD (a.apply fun x => (x.val : β)) (Uniform ⟨univ, univ_nonempty⟩) ≤
    ε * Real.sqrt m * (3 * Real.log n + 3) + m / (2*n) := calc SD (a.apply fun x => (x.val : β)) (Uniform ⟨univ, univ_nonempty⟩)
  _ = 1/2 * ‖⇑(a.apply fun x => (x.val : β)) - ⇑(Uniform ⟨univ, univ_nonempty⟩)‖_[1] := SD_eq_half_L1 ..
  _ = 1/2 * ‖((fun (x : α) => (x.val : β)) # a) - ⇑(Uniform ⟨univ, univ_nonempty⟩)‖_[1] := rfl
  _ ≤ 1/2 * (‖((fun (x : α) => (x.val : β)) # a) - ((fun (x : α) => (x.val : β)) # (Uniform ⟨univ, univ_nonempty⟩))‖_[1] +
      ‖((fun (x : α) => (x.val : β)) # (Uniform ⟨univ, univ_nonempty⟩)) - ⇑(Uniform ⟨univ, univ_nonempty⟩)‖_[1]) := by
    gcongr
    apply lpNorm_sub_le_lpNorm_sub_add_lpNorm_sub
    rfl
  _ = 1/2 * (‖((fun (x : α) => (x.val : β)) # a) - ((fun (x : α) => (x.val : β)) # (Function.const α (𝔼 x, a x)))‖_[1] +
      ‖((fun (x : α) => (x.val : β)) # (Uniform ⟨univ, univ_nonempty⟩)) - ⇑(Uniform ⟨univ, univ_nonempty⟩)‖_[1]) := by
    congr
    ext
    congr
    ext x
    simp [expect, ← nnratCast_smul_eq_nnqsmul ℝ, card_univ]
  _ ≤ 1/2 * ((6 * Real.log n + 6).toNNReal * ε * Real.sqrt (Fintype.card β) +
      ‖((fun (x : α) => (x.val : β)) # (Uniform ⟨univ, univ_nonempty⟩)) - ⇑(Uniform ⟨univ, univ_nonempty⟩)‖_[1]) := by
    gcongr
    apply lemma43
    exact h
    intro χ
    simp only [coe_toNNReal', le_max_iff]
    left
    apply lemma44
  _ = 1/2 * ((6 * Real.log n + 6) * ε * Real.sqrt (Fintype.card β) +
      ‖((fun (x : α) => (x.val : β)) # (Uniform ⟨univ, univ_nonempty⟩)) - ⇑(Uniform ⟨univ, univ_nonempty⟩)‖_[1]) := by
    congr
    simp only [coe_toNNReal', max_eq_left_iff]
    apply add_nonneg
    simp only [gt_iff_lt, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
    apply Real.log_nonneg
    norm_cast
    simp
    norm_num
  _ ≤ 1/2 * ((6 * Real.log n + 6) * ε * Real.sqrt (Fintype.card β) + m/n) := by
    gcongr
    apply bound_on_apply_uniform
  _ = ε * Real.sqrt m * (3 * Real.log n + 3) + m / (2*n) := by
    simp
    ring_nf
