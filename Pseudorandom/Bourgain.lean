import Pseudorandom.Extractor
import Pseudorandom.XorLemma
import Pseudorandom.FlatSources
import Pseudorandom.ChorGoldreich
import Pseudorandom.Incidence.Incidence

open Finset BigOps ComplexConjugate

variable {p : ℕ} [fpprm : Fact p.Prime]

local notation "α" => ZMod p

noncomputable def lapply (a : FinPMF α) (b : FinPMF (α × α × α)) : FinPMF (α × α) :=
  (a * b).apply (fun ⟨x, y⟩ => (x + y.1, y.2.1 * (x + y.1) + y.2.2))

lemma lapply_linear_combination [Fintype γ] [Fintype γ₂]
    (a : FinPMF γ) (b : FinPMF γ₂)
    (f : γ → FinPMF α) (g : γ₂ → FinPMF (α × α × α)) :
  lapply (a.linear_combination f) (b.linear_combination g) =
  (a*b).linear_combination (fun ⟨x, y⟩ => lapply (f x) (g y)) := by
  unfold lapply
  rw [linear_combination_mul, linear_combination_apply]

theorem line_point_large_l2_aux (n : ℕ+) (β : ℝ) (hβ : 0 < β) (hkl : (p^β : ℝ) ≤ n) (hku: n ≤ (p^(2 - β) : ℝ))
    (a' : {x : Finset α // x.Nonempty}) (b' : {x : Finset (α × α × α) // x.Nonempty})
    (hD : Set.InjOn Prod.snd (b' : Set (α × α × α))) (hbSz : b'.1.card ≤ n) :
    close_high_entropy n (1/(a'.1.card * b'.1.card) * ST_C * n^(3/2 - ST_prime_field_eps β)) (lapply (Uniform a') (Uniform b')) := by
  intro H hhSz
  let a := Uniform a'
  let b := Uniform b'
  change ∑ x ∈ H, lapply a b x ≤ _
  calc ∑ x ∈ H, ((a * b).apply (fun ⟨x, y⟩ => (x + y.1, y.2.1 * (x + y.1) + y.2.2))) x
    _ = ∑ z ∈ H,
        ∑ y ∈ (univ.filter (fun ⟨x, y⟩ => (x + y.1, y.2.1 * (x + y.1) + y.2.2) = z) : Finset (α × α × α × α)), a y.1 * b y.2 := by
      unfold FinPMF.apply transfer
      dsimp only [FinPMF.val_apply]
      rcongr
    _ = ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x),
        (if y.1 ∈ a'.1 then 1 / a'.1.card else 0 : ℝ) * (if y.2 ∈ b'.1 then 1 / b'.1.card else 0 : ℝ) := by
      rcongr
      · unfold_let a
        unfold Uniform
        dsimp only [FinPMF.val_apply]
        congr
      · unfold_let b
        unfold Uniform
        dsimp only [FinPMF.val_apply]
        congr
    _ = ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x),
        (1/a'.1.card * (if y.1 ∈ a'.1 then 1 else 0 : ℝ)) * (1/b'.1.card * (if y.2 ∈ b'.1 then 1 else 0 : ℝ)) := by
      simp only [one_div, mul_ite, ite_mul, zero_mul, mul_zero, mul_one]
    _ = ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x),
        1/(a'.1.card*b'.1.card) * ((if y.1 ∈ a'.1 then 1 else 0 : ℝ) * (if y.2 ∈ b'.1 then 1 else 0 : ℝ)) := by
      congr
      ext
      congr
      ext
      ring_nf
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x),
        ((if y.1 ∈ a'.1 then 1 else 0 : ℝ) * (if y.2 ∈ b'.1 then 1 else 0 : ℝ)) := by simp only [← mul_sum]
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x),
        (if y.1 ∈ a'.1 ∧ y.2 ∈ b'.1 then 1 else 0 : ℝ) := by
      rcongr
      rw [ite_zero_mul_ite_zero]
      simp
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        (univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x ∧ z ∈ a'.1 ∧ y ∈ b'.1)).card := by
      simp only [one_div, sum_boole, Nat.cast_sum, add_right_inj, Finset.filter_filter]
    _ ≤ 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        (univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x ∧ y ∈ b'.1)).card := by
      gcongr
      apply Finset.monotone_filter_right
      rw [Pi.le_def]
      intros
      simp_all only [le_Prop_eq, and_self, and_imp, implies_true]
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        (univ.filter (fun (y : α × α ) => y.1 * x.1 + y.2 = x.2 ∧ y ∈ b'.1.image Prod.snd)).card := by
      congr
      ext x
      have ⟨x1, x2⟩ := x
      apply Finset.card_congr (fun x _ => x.2.2)
      · intros a ha
        simp_all only [Prod.mk.injEq, mem_filter, mem_univ, true_and, mem_image]
        rw [← ha.1.1]
        exact ⟨ha.1.2, a.2, ha.2, rfl⟩
      · rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ ha hb _
        simp only [Prod.mk.injEq, mem_filter, mem_univ, true_and] at ha
        simp only [Prod.mk.injEq, mem_filter, mem_univ, true_and] at hb
        have := hD ha.2 hb.2
        simp_all only [Prod.mk.injEq, and_true, forall_true_left]
        linear_combination ha.1 - hb.1.1
      · intros b hb
        simp only [mem_image, mem_filter, mem_univ, true_and] at hb
        have ⟨hb, a, ha⟩ := hb
        exists ⟨x1 - a.1, a⟩
        simp_all only [Prod.exists, exists_eq_right, true_and, Prod.mk.injEq,
          mem_filter, mem_univ, sub_add_cancel, and_self, exists_const]
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        ((b'.1.image Prod.snd).filter (fun (y : α × α) => y.1 * x.1 + y.2 = x.2)).card := by
      congr
      ext
      congr 1
      conv =>
        rhs
        rw [← Finset.filter_univ_mem (b'.1.image Prod.snd)]
      rw [Finset.filter_filter]
      simp_rw [and_comm]
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        ((b'.1.image Prod.snd).filter (fun (y : α × α) => x ∈ Line.of_equation y.1 y.2)).card := by
      rcongr
      apply Iff.symm
      apply mem_of_equation_iff
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        (((b'.1.image Prod.snd).image (Function.uncurry Line.of_equation)).filter (fun y => x ∈ y)).card := by
      congr
      ext
      apply card_congr (fun x _ => (Function.uncurry Line.of_equation) x)
      · intros x hx
        simp_all only [mem_filter, mem_image, Function.uncurry_apply_pair]
        constructor
        exact ⟨x, hx.1, rfl⟩
        exact hx.2
      · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ _ _ h
        exact Line.uncurry_of_equation_injective h
      · intros b hb
        simp only [mem_filter, mem_image, Function.uncurry_apply_pair] at hb
        have ⟨⟨⟨l1, l2⟩, hl, h⟩, hm⟩ := hb
        exists (l1, l2)
        simp_all
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        (IntersectionsL x ((b'.1.image Prod.snd).image (Function.uncurry Line.of_equation))).card := rfl
    _ = 1/(a'.1.card*b'.1.card) * (Intersections H ((b'.1.image Prod.snd).image (Function.uncurry Line.of_equation))).card := by rw [IntersectionsL_sum]
    _ ≤ 1/(a'.1.card*b'.1.card) * (ST_C * n^(3/2 - ST_prime_field_eps β)) := by
      gcongr
      apply ST_prime_field
      exact hβ
      exact_mod_cast hkl
      exact_mod_cast hku
      exact_mod_cast hhSz
      exact Finset.card_image_le.trans (Finset.card_image_le.trans hbSz)
    _ = 1/(a'.1.card * b'.1.card) * ST_C * n^(3/2 - ST_prime_field_eps β) := by ring

theorem line_point_large_l2' (n : ℕ+) (β : ℝ) (hβ : 0 < β) (hkl : (p^β : ℝ) ≤ n) (hku: n ≤ (p^(2 - β) : ℝ))
    (a : FinPMF α) (b : FinPMF (α × α × α)) (m : ℕ+) (hm : m ≤ n)
    (hD : Set.InjOn Prod.snd (Function.support b : Set (α × α × α))) (hbSz : max_val b ≤ 1/m) :
    close_high_entropy n (1 / (⌊1/ max_val a⌋₊ * m) * ST_C * n^(3/2 - ST_prime_field_eps β)) (lapply a b) := by
  let l1 := ⌊1 / max_val a⌋₊.toPNat'
  let l2 := m
  obtain ⟨f, hf⟩ := split_to_flat_sources a l1 <| by
    unfold_let l1
    simp only [one_div, Nat.toPNat'_coe, Nat.cast_ite, Nat.cast_one]
    split
    calc max_val a
      _ = ((max_val a)⁻¹)⁻¹ := by simp
      _ ≤ (⌊(max_val a)⁻¹⌋₊ : ℝ)⁻¹ := by
        gcongr
        apply Nat.floor_le
        simp [le_of_lt (zero_lt_max_val ..)]
    simp [max_val_le_one _]
  obtain ⟨f2, hf2⟩ := split_to_flat_sources b l2 <| by
    unfold_let l2
    simp only [one_div]
    calc max_val b
      _ = ((max_val b)⁻¹)⁻¹ := by simp
      _ ≤ (((1/m : ℝ))⁻¹)⁻¹ := by
        gcongr
        simp
        apply zero_lt_max_val
      _ = (m : ℝ)⁻¹ := by simp
  convert_to close_high_entropy n (1 / (l1 * l2) * ST_C * n^(3/2 - ST_prime_field_eps β)) (lapply a b)
  congr
  · unfold_let l1
    suffices 0 < ⌊(max_val a)⁻¹⌋₊ by simp [this]
    rw [Nat.floor_pos, one_le_inv_iff]
    simp [max_val_le_one _, zero_lt_max_val _]
  conv =>
    rhs
    rw [← hf, ← hf2]
  rw [lapply_linear_combination]
  apply close_high_entropy_linear_combination
  rintro ⟨x, y⟩ hpos
  simp only [FinPMF.mul_val, mul_pos_iff] at hpos
  cases hpos
  rename_i hpos
  convert line_point_large_l2_aux n β hβ hkl hku ⟨x, by
    apply Finset.card_pos.mp
    rw [x.2]
    apply PNat.pos
  ⟩ ⟨y, by
    apply Finset.card_pos.mp
    rw [y.2]
    apply PNat.pos
  ⟩ ?_ ?_
  · simp [x.2]
  · simp [y.2]
  · apply Set.InjOn.mono _ hD
    rw [Set.subset_def]
    intro x2 hx
    simp only [Function.mem_support, ne_eq]
    apply_fun (· x2) at hf2
    rw [← hf2]
    apply ne_of_gt
    unfold FinPMF.linear_combination
    simp only [FinPMF.val_apply]
    apply sum_pos'
    intros
    apply mul_nonneg <;> simp [← FinPMF.val_apply]
    exists y, mem_univ y
    apply mul_pos
    exact hpos.2
    unfold Uniform
    dsimp
    split
    simp [y.2]
    contradiction
  · simp only [y.2, PNat.coe_le_coe]
    exact hm
  · have : 0 ≤ f x := by simp
    linarith

theorem line_point_large_l2 (n : ℝ) (β : ℝ) (hβ : 0 < β) (hβ2 : β < 1)
    (hkl : p ≤ n) (hku: n ≤ (p^(2 - β) : ℝ))
    (a : FinPMF α) (b : FinPMF (α × α × α)) (m : ℝ) (hm : m ≤ ⌊n⌋)
    (hD : Set.InjOn Prod.snd (Function.support b : Set (α × α × α))) (hbSz : max_val b ≤ 1/(2*m)) :
    close_high_entropy n (1 / (2 / max_val a * (2 * m)) * ST_C * n^(3/2 - ST_prime_field_eps β)) (lapply a b) := by
  have := line_point_large_l2' (p := p) ⌊n⌋₊.toPNat' β hβ sorry sorry a b ⌈m⌉₊.toPNat' sorry
      hD sorry
  replace this : close_high_entropy ⌊n⌋₊ _ (lapply a b) := by
    convert this
    simp only [Nat.toPNat'_coe]
    split
    rfl
    exfalso
    rename_i hi
    simp only [not_lt, nonpos_iff_eq_zero, Nat.floor_eq_zero] at hi
    have := hkl.trans_lt hi
    have := fpprm.out.one_lt
    rify at this
    linarith
  apply close_high_entropy_of_floor
  sorry

def lmap (x : α × α) : α × α × α := (x.1 + x.2, (2 * (x.1 + x.2), -((x.1 + x.2)^2 + (x.1^2 + x.2^2))))

def decoder : (α × α) ≃ (α × α) := Function.Involutive.toPerm (fun x => (x.1, x.1^2 - x.2)) (by intro; simp)

lemma jurl (b : FinPMF α) :
    ((b * b * b).apply fun x => (x.1.1 + x.1.2 + x.2, x.1.1^2 + x.1.2^2 + x.2^2)) =
    (lapply b ((b * b).apply lmap)).apply decoder := calc
  ((b * b * b).apply fun x => (x.1.1 + x.1.2 + x.2, x.1.1^2 + x.1.2^2 + x.2^2))
  _ = ((b * b * b).apply fun x => (x.1.1 + x.1.2 + x.2, (x.1.1 + x.1.2 + x.2)^2 - (x.1.1^2 + x.1.2^2 + x.2^2))).apply
      fun x => (x.1, x.1^2 - x.2) := by
    rw [FinPMF.apply_apply]
    congr
    ext x
    rfl
    dsimp
    ring_nf
  _ = ((b * b * b).apply fun x => (x.2 + (x.1.1 + x.1.2), 2 * (x.1.1 + x.1.2) * (x.2 + (x.1.1 + x.1.2)) + -((x.1.1 + x.1.2)^2 + (x.1.1^2 + x.1.2^2)))).apply
      fun x => (x.1, x.1^2 - x.2) := by
    congr
    ext x
    ring
    ring
  _ = (lapply (b.apply id) ((b * b).apply lmap)).apply decoder := by
    congr 1
    unfold lapply
    rw [FinPMF.apply_mul, FinPMF.apply_apply]
    conv =>
      rhs
      arg 1
      rw [← FinPMF.apply_swap]
    rw [FinPMF.apply_apply]
    rfl
  _ = (lapply b ((b * b).apply lmap)).apply decoder := by
    congr
    rw [FinPMF.eq_apply_id]

noncomputable def bourgainβ : ℝ := 1/2

noncomputable def bourgainα : ℝ := ST_prime_field_eps bourgainβ

noncomputable def bourgain_C : ℝ := (4 * ST_C + 1)^(64⁻¹ : ℝ)

theorem bourgain_extractor (ε : ℝ) (a b : FinPMF α) (χ : AddChar α ℂ) (h : χ.IsNontrivial)
    (n : ℕ) (hn : (p^(1/2 - 2/7 * bourgainα) : ℝ) ≤ n) (hA : max_val a ≤ (1 / n : ℝ)) (hB : max_val b ≤ (1 / n : ℝ)):
    ‖∑ x, a x * ∑ y, b y * χ (x * y + x^2 * y^2)‖ ≤ bourgain_C * p^(-1/224 * bourgainα) := by
  let a' := a.apply fun x => (x, x^2)
  let b' := b.apply fun x => (x, x^2)
  calc ‖∑ x, a x * ∑ y, b y * χ (x * y + x^2 * y^2)‖
  -- _ = ‖∑ x, a x * ∑ y, (b.apply fun x => (x, x^2)) y * χ (x * y.1 + x^2 * y.2)‖ := by
  --   congr with _
  --   congr 1
  --   apply Eq.symm
  --   apply apply_weighted_sum
  -- _ = ‖∑ x, (a.apply fun x => (x, x^2)) x * ∑ y, (b.apply fun x => (x, x^2)) y * χ (x.1 * y.1 + x.2 * y.2)‖ := by
  --   congr 1
  --   apply Eq.symm
  --   apply apply_weighted_sum
  -- _ = ‖∑ x, a' x * ∑ y, b' y * χ (IP x y)‖ := rfl
  -- _ ≤ ‖∑ x, a' x * ∑ y, (b' - b') y * χ (IP x y)‖^(2⁻¹ : ℝ) := bourgain_extractor_aux₁' ..
  -- _ ≤ (‖∑ x, a' x * ∑ y, ((b' - b') - (b' - b')) y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
  --   gcongr
  --   apply bourgain_extractor_aux₁'
  -- _ ≤ ((‖∑ x, a' x * ∑ y, (((b' - b') - (b' - b')) - ((b' - b') - (b' - b'))) y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
    -- gcongr
    -- apply bourgain_extractor_aux₁'
  -- _ = ((‖∑ x, a' x * ∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
    -- rcongr
    -- simp only [FinPMF.sub_eq_add_neg, FinPMF.neg_add, FinPMF.neg_neg]
    -- generalize -b'=c'
    -- abel
  -- _ ≤ ((‖∑ x, a' x * ∑ y, (b' + b' + b') y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
  --   gcongr
  --   sorry
  -- _ = ‖∑ x, a' x * ∑ y, (b' + b' + b') y * χ (IP x y)‖^(8⁻¹ : ℝ) := by
  --   rw [← Real.rpow_mul, ← Real.rpow_mul]
  --   congr
  --   norm_num
  --   positivity
  --   positivity
  -- _ = ‖∑ y, (b' + b' + b') y * ∑ x, a' x * χ (IP x y)‖^(8⁻¹ : ℝ) := by
  --   simp_rw [mul_sum]
  --   rw [sum_comm]
  --   congr with _
  --   congr with _
  --   ring
  -- _ = ‖∑ y, (b' + b' + b') y * ∑ x, a' x * χ (IP y x)‖^(8⁻¹ : ℝ) := by
  --   simp_rw [IP_comm]
  -- _ ≤ (‖∑ y, (b' + b' + b') y * ∑ x, (a' - a') x * χ (IP y x)‖^(2⁻¹ : ℝ))^(8⁻¹ : ℝ) := by
  --   gcongr
  --   apply bourgain_extractor_aux₁'
  -- _ ≤ ((‖∑ y, (b' + b' + b') y * ∑ x, ((a' - a') - (a' - a')) x * χ (IP y x)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(8⁻¹ : ℝ) := by
  --   gcongr
  --   apply bourgain_extractor_aux₁'
  -- _ ≤ (((‖∑ y, (b' + b' + b') y * ∑ x, (((a' - a') - (a' - a')) - ((a' - a') - (a' - a'))) x * χ (IP y x)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(8⁻¹ : ℝ) := by
  --   gcongr
  --   apply bourgain_extractor_aux₁'
  -- _ = ‖∑ y, (b' + b' + b') y * ∑ x, (((a' - a') - (a' - a')) - ((a' - a') - (a' - a'))) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
  --   rw [← Real.rpow_mul, ← Real.rpow_mul, ← Real.rpow_mul]
  --   congr
  --   norm_num
  --   repeat positivity
  -- _ = ‖∑ y, (b' + b' + b') y * ∑ x, ((a' + a' + a') + (a' - a' - a' - a' - a')) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
  --   rcongr
  --   simp only [FinPMF.sub_eq_add_neg, FinPMF.neg_add, FinPMF.neg_neg]
  --   generalize -a'=c'
  --   abel
  _ ≤ ‖∑ y, (b' + b' + b') y * ∑ x, (a' + a' + a') x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
    -- gcongr
    sorry
  _ = ‖∑ y, ((b * b * b).apply fun x => (x.1.1 + x.1.2 + x.2, x.1.1^2 + x.1.2^2 + x.2^2)) y *
      ∑ x, ((a * a * a).apply fun x => (x.1.1 + x.1.2 + x.2, x.1.1^2 + x.1.2^2 + x.2^2)) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
    rcongr
    · unfold_let b'
      rw [FinPMF.apply_add, FinPMF.apply_add]
      rfl
    · unfold_let a'
      rw [FinPMF.apply_add, FinPMF.apply_add]
      rfl
  _ = ‖∑ y, ((lapply b ((b * b).apply lmap)).apply decoder) y *
      ∑ x, ((lapply a ((a * a).apply lmap)).apply decoder) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
    simp_rw [jurl]
  _ ≤ (Fintype.card α / p^(1 + 2/7 * bourgainα) + 2 * (2 * ST_C * p^(-2/7 * bourgainα)))^(64⁻¹ : ℝ) := by
    gcongr
    apply bourgain_extractor_aux₂
    apply mul_pos
    apply mul_pos
    norm_num
    exact_mod_cast ST_C_pos
    apply Real.rpow_pos_of_pos
    exact_mod_cast fpprm.out.pos
    apply Real.rpow_pos_of_pos
    exact_mod_cast fpprm.out.pos
    exact h
    apply close_high_entropy_apply_equiv
    sorry
    apply close_high_entropy_apply_equiv
    sorry
  _ = (p^(1 : ℝ) / p^(1 + 2/7 * bourgainα) + 2 * (2 * ST_C * p^(-2/7 * bourgainα)))^(64⁻¹ : ℝ) := by
    congr
    simp [card_univ]
  _ = (p^((1 : ℝ) - (1 + 2/7 * bourgainα)) + 2 * (2 * ST_C * p^(-2/7 * bourgainα)))^(64⁻¹ : ℝ) := by
    rw [← Real.rpow_sub]
    exact_mod_cast fpprm.out.pos
  _ = ((4 * ST_C + 1) * p^(-2/7 * bourgainα))^(64⁻¹ : ℝ) := by
    ring_nf
  _ = (4 * ST_C + 1)^(64⁻¹ : ℝ) * p^(-1/224 * bourgainα) := by
    rw [Real.mul_rpow, ← Real.rpow_mul]
    ring_nf
    simp
    positivity
    apply Real.rpow_nonneg
    simp
