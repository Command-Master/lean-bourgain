import Pseudorandom.Extractor
import Pseudorandom.XorLemma
import Pseudorandom.FlatSources
import Pseudorandom.ChorGoldreich
import Pseudorandom.Incidence.Incidence

open Finset BigOps ComplexConjugate

variable {p : ℕ} [fpprm : Fact p.Prime] [pnot2 : Fact (p ≠ 2)]

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
    (a : FinPMF α) (b : FinPMF (α × α × α)) (m : ℝ) (hm : m ≤ n)
    (hm₂ : 1 ≤ m)
    (hD : Set.InjOn Prod.snd (Function.support b : Set (α × α × α))) (hbSz : max_val b ≤ 1/m) :
    close_high_entropy n (1 / (1 / (2 * max_val a) * (m / 2)) * ST_C * n^(3/2 - ST_prime_field_eps β)) (lapply a b) := by
  have npneq : ⌊n⌋₊.toPNat' = ⌊n⌋₊ := by
    suffices 0 < ⌊n⌋₊ by simp [this]
    rw [Nat.floor_pos]
    exact hm₂.trans hm
  have mpmeq : ⌊m⌋₊.toPNat' = ⌊m⌋₊ := by
    suffices 0 < ⌊m⌋₊ by simp [this]
    rw [Nat.floor_pos]
    exact hm₂
  have := line_point_large_l2' (p := p) ⌊n⌋₊.toPNat' β hβ (calc
      (p^β : ℝ) ≤ p^(1 : ℝ) := by gcongr; simp [fpprm.out.one_le]
      _ = p := by simp
      _ ≤ ⌊n⌋₊ := by
        simp only [Nat.cast_le]
        rw [Nat.le_floor_iff]
        exact hkl
        linarith
      _ = ⌊n⌋₊.toPNat' := by rw [npneq]
    ) (calc
      (⌊n⌋₊.toPNat' : ℝ) = ⌊n⌋₊ := by rw [npneq]
      _ ≤ n := by apply Nat.floor_le; linarith
      _ ≤ p^(2-β) := hku
    ) a b ⌊m⌋₊.toPNat' (by
      unfold Nat.toPNat'
      simp only [Nat.succPNat_le_succPNat]
      apply Nat.pred_le_pred
      apply Nat.floor_le_floor
      exact hm
    ) hD (calc
      max_val b ≤ 1 / m := hbSz
      _ ≤ 1 / ⌊m⌋₊ := by
        gcongr
        norm_cast
        rw [Nat.floor_pos]
        exact hm₂
        apply Nat.floor_le
        linarith
      _ = 1 / ⌊m⌋₊.toPNat' := by rw [mpmeq]
    )
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
  apply close_high_entropy_of_le (h := this)
  have := zero_lt_max_val a
  gcongr
  · convert half_le_floor_of_one_le (1 / max_val a) <| by
      rw [one_div, one_le_inv_iff]
      simp only [this, max_val_le_one, and_self] using 1
    ring
  · simp only [Nat.toPNat'_coe, Nat.floor_pos, hm₂, ↓reduceIte]
    exact half_le_floor_of_one_le m hm₂
  · unfold ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂
    have := ntlSGeps β
    linarith
  · have := fpprm.out.one_lt
    rify at this
    replace this := this.trans_le hkl
    replace this : 0 < ⌊n⌋₊ := by
      rw [Nat.floor_pos]
      exact le_of_lt this
    simp [this]
    apply Nat.floor_le
    linarith

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
      rw [← FinPMF.apply_swap]
    rw [FinPMF.apply_apply]
    rfl
  _ = (lapply b ((b * b).apply lmap)).apply decoder := by
    congr
    rw [FinPMF.eq_apply_id]

noncomputable def bourgainβ : ℝ := 107059887596204928/107059887596204929

noncomputable def bourgainα : ℝ := ST_prime_field_eps bourgainβ

lemma bα_val : bourgainα = 11/2 * (1 - bourgainβ) := by
  unfold bourgainα ST_prime_field_eps ST_prime_field_eps₂ ST_prime_field_eps₃ ST_prime_field_eps₄ SG_eps SG_eps₂ SG_eps₃
    full_C full_C₂
  have : ⌈Real.logb (3 / 2) (1 / (bourgainβ / 4))⌉₊ = 4 := by
    unfold bourgainβ
    rw [Nat.ceil_eq_iff]
    constructor
    rw [Real.lt_logb_iff_rpow_lt] <;> norm_num
    rw [Real.logb_le_iff_le_rpow] <;> norm_num
    norm_num
  rw [this]
  unfold bourgainβ
  norm_num

/-
1 + 2/11 * ST_prime_field_eps bourgainβ = 2 - bourgainβ
bourgainβ + 2/11 * ST_prime_field_eps bourgainβ = 1
bourgainβ + 2/1485 * SG_eps₃ bourgainβ = 1
α + 2/1485 * ((α / 4) / (full_C (α / 4) * 9212 / 45)) = 1
α + 2/1485 * ((α / 4) / (full_C 1/4 * 9212 / 45)) = 1
α + α 2/1485 * (45 / (4 * 9 * 374^4 * 9212)) = 1
α = 1 / (1 + 1/107059887596204928)

-/

noncomputable def bourgain_C : ℝ := (16 * ST_C + 1)^(64⁻¹ : ℝ)


-- Thanks to Richard Copley: https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/There.20aren't.20many.20solutions.20to.20.60x.2By.3Da.2C.20xy.3Db.60/near/43202385
open Polynomial in
lemma quadratic_not_many_roots (a b : α) :
    (univ.filter (fun x => 1*x*x + a*x + b = 0)).card ≤ 2 := by
  let p := C 1 * X ^ 2 + C a * X + C b
  have hdegree : p.degree = 2 := Polynomial.degree_quadratic one_ne_zero
  have hnonzero : p ≠ 0 := Polynomial.ne_zero_of_coe_le_degree hdegree.ge
  suffices univ.filter (fun x => 1*x*x + a*x + b = 0) = p.roots.toFinset by
    rw [this]
    exact p.roots.toFinset_card_le.trans <| Nat.cast_le_ofNat.mp <|
      le_of_le_of_eq (Polynomial.card_roots hnonzero) hdegree
  ext x
  trans p.eval x = 0
  · simp [p, sq]
  · simp [Polynomial.mem_roots hnonzero]

lemma max_val_of_apply_lmap (b : FinPMF α) : max_val ((b*b).apply lmap) ≤ (max_val b)^2 * 2 := by
  conv =>
    lhs
    unfold max_val
  apply ciSup_le
  intro x
  calc (b*b).apply lmap x
    _ = ∑ y ∈ univ.filter (fun y => lmap y = x), (b * b) y := by
      unfold FinPMF.apply transfer
      dsimp [FinPMF.val_apply]
    _ = ∑ y ∈ univ.filter (fun y => lmap y = x), b y.1 * b y.2 := by rfl
    _ ≤ ∑ __ ∈ univ.filter (fun y => lmap y = x), (max_val b) * (max_val b) := by
      gcongr
      simp
      exact le_of_lt (zero_lt_max_val _)
      apply le_max_val
      apply le_max_val
    _ = (max_val b)^2 * (univ.filter (fun y => lmap y = x)).card := by simp [mul_comm, sq]
    _ ≤ (max_val b)^2 * 2 := by
      gcongr
      norm_cast
      obtain ⟨x1, x2, x3⟩ := x
      unfold lmap
      simp only [neg_add_rev, Prod.mk.injEq]
      calc (univ.filter (fun (y : α × α) => y.1 + y.2 = x1 ∧ 2 * (y.1 + y.2) = x2 ∧ -y.2^2 + -y.1^2 + -(y.1 + y.2)^2 = x3)).card
        _ ≤ (univ.filter (fun (y : α × α) => y.1 + y.2 = x1 ∧ -y.2^2 + -y.1^2 + -(y.1 + y.2)^2 = x3)).card := by
          gcongr
          apply Finset.monotone_filter_right
          rw [Pi.le_def]
          intro
          tauto
        _ = (univ.filter (fun (y : α × α) => y.1 + y.2 = x1 ∧ y.1 * y.2 = x1^2 + x3/2)).card := by
          congr
          ext y
          have : (2 : α) ≠ 0 := fun h => by
            change ((2 : ℕ) : α) = 0 at h
            rw [ZMod.nat_cast_zmod_eq_zero_iff_dvd, Nat.prime_dvd_prime_iff_eq] at h
            exact pnot2.out h
            exact fpprm.out
            exact Nat.prime_two
          constructor
          · rintro ⟨v1, v2⟩
            refine ⟨v1, ?_⟩
            rw [← v1, ← v2]
            field_simp
            ring_nf
          · rintro ⟨v1, v2⟩
            rw [← v1] at v2
            refine ⟨v1, ?_⟩
            linear_combination (norm := (field_simp; ring)) 2*v2
        _ = (univ.filter (fun (y : α) => 1*y*y + x1*y + (x1^2 + x3/2) = 0)).card := by
          apply card_congr (fun x _ => -x.1)
          · simp only [mem_filter, mem_univ, true_and, one_mul, and_imp, Prod.forall]
            intros a b h₁ h₂
            rw [← h₂, ← h₁]
            ring
          · simp only [mem_filter, mem_univ, true_and, neg_inj, and_imp, Prod.forall,
            Prod.mk.injEq]
            intro a b a2 b2 h₁ _ h₃ _ h
            rw [h] at h₁
            rw [← h₁] at h₃
            apply add_left_cancel at h₃
            exact ⟨h, h₃.symm⟩
          · simp only [one_mul, mem_filter, mem_univ, true_and, exists_prop, Prod.exists,
            exists_and_right]
            intro b h
            exists -b
            simp only [neg_mul, neg_neg, and_true]
            exists x1 + b
            ring_nf
            simp only [true_and]
            linear_combination -h
        _ ≤ 2 := quadratic_not_many_roots ..



lemma bourgain_extractor_aux₃ (b : FinPMF α)
    (hB : max_val b ≤ (p^(- 1/2 + 2/11 * bourgainα) : ℝ)) :
    close_high_entropy (↑p ^ (1 + 2 / 11 * bourgainα)) (8 * ↑ST_C * ↑p ^ (-2 / 11 * bourgainα))
    (FinPMF.apply (lapply b (FinPMF.apply (b * b) lmap)) decoder)
   := by
  apply close_high_entropy_apply_equiv
  have := line_point_large_l2 (p := p) (p^(1 + 2/11 * bourgainα)) bourgainβ (by unfold bourgainβ; norm_num)
      (by unfold bourgainβ; norm_num) (calc (p : ℝ)
        _ = p^(1 : ℝ) := by simp
        _ ≤ p^(1 + 2/11 * bourgainα) := by gcongr; simp [fpprm.out.one_le]; rw [bα_val]; unfold bourgainβ; norm_num
        ) (by
          apply le_of_eq
          congr 1
          rw [bα_val]
          ring
        ) -- ↑p ^ (1 - 4 / 11 * bourgainα) / 2 ≤ ↑p ^ (1 + 2 / 11 * bourgainα)
      b ((b*b).apply lmap) (p^(1 - 4/11 * bourgainα) / 2) (calc
        (p^(1 - 4/11 * bourgainα) : ℝ) / 2 ≤ p^(1 - 4/11 * bourgainα) := by
          simp only [half_le_self_iff]
          apply Real.rpow_nonneg
          simp
        _ ≤ p^(1 + 2/11 * bourgainα) := by
          gcongr
          simp [fpprm.out.one_le]
          rw [bα_val]
          unfold bourgainβ
          norm_num
      ) (calc
        (1 : ℝ) ≤ 3^(3/4 : ℝ) / 2 := by
          rw [le_div_iff, div_eq_mul_inv, Real.rpow_mul, Real.le_rpow_inv_iff_of_pos]
          repeat norm_num
        _ ≤ p^(3/4 : ℝ) / 2 := by
          gcongr
          have := pnot2.out
          have := fpprm.out.two_le
          simp
          omega
        _ ≤ p^(1 - 4/11 * bourgainα) / 2 := by
          gcongr
          simp [fpprm.out.one_le]
          rw [bα_val]
          unfold bourgainβ
          norm_num
      ) (by
        rintro ⟨a1, a2, a3⟩ ha ⟨b1, b2, b3⟩ hb v
        simp only [Prod.mk.injEq] at v
        simp only [v, Prod.mk.injEq, and_true]
        simp only [Function.mem_support, ne_eq] at ha
        apply apply_ne_zero at ha
        have ⟨x₁, h₁⟩ := ha
        simp only [Function.mem_support, ne_eq] at hb
        apply apply_ne_zero at hb
        have ⟨x₂, h₂⟩ := hb
        unfold lmap at h₁ h₂
        simp only [neg_add_rev, Prod.mk.injEq] at h₁ h₂
        have : 2 * (x₁.1 + x₁.2) = 2 * (x₂.1 + x₂.2) := by
          rw [← h₁.2.1, ← h₂.2.1]
          exact v.1
        rw [h₁.1, h₂.1]
        apply_fun (2⁻¹ * ·) at this
        simp only [mul_eq_mul_left_iff, inv_eq_zero, or_self_right] at this
        cases this
        assumption
        exfalso
        rename_i h
        change ((2 : ℕ) : α) = 0 at h
        rw [ZMod.nat_cast_zmod_eq_zero_iff_dvd, Nat.prime_dvd_prime_iff_eq] at h
        exact pnot2.out h
        exact fpprm.out
        exact Nat.prime_two
      ) (calc
          max_val ((b*b).apply lmap) ≤ (max_val b)^2 * 2 := max_val_of_apply_lmap ..
          _ ≤ (p^(-1/2 + 2/11 * bourgainα))^2 * 2 := by gcongr; exact le_of_lt (zero_lt_max_val ..)
          _ = 1 / (p^(1 - 4/11 * bourgainα) / 2) := by
            rw [← Real.rpow_mul_natCast]
            ring_nf
            rw [← Real.rpow_neg]
            ring_nf
            simp
            simp
      )
  apply close_high_entropy_of_le (h := this)
  clear this
  ring_nf
  simp only [inv_inv, gt_iff_lt, Nat.ofNat_pos, mul_le_mul_right]
  rw [← Real.rpow_neg, mul_rotate, mul_mul_mul_comm, ← Real.rpow_mul, ← Real.rpow_add]
  ring_nf
  rw [mul_assoc]
  gcongr
  calc max_val b * p ^ (1 / 2 + bourgainα * (7/11) + (bourgainα * ST_prime_field_eps bourgainβ * (-2 / 11) - ST_prime_field_eps bourgainβ))
    _ ≤ p^(-1/2 + 2/11 * bourgainα) * p ^ (1 / 2 + bourgainα * (7/11) + (0 - ST_prime_field_eps bourgainβ)) := by
      gcongr
      simp [fpprm.out.one_le]
      change bourgainα * bourgainα * (-2 / 11) ≤ 0
      rw [bα_val]
      unfold bourgainβ
      norm_num
    _ = p ^ (bourgainα * (-2 / 11)) := by
      rw [← Real.rpow_add]
      congr 1
      unfold bourgainα
      ring_nf
      simp [fpprm.out.pos]
  simp [fpprm.out.pos]
  simp
  simp

-- 2/137 for full balance? No need

theorem bourgain_extractor (a b : FinPMF α)
    (hA : max_val a ≤ (p^(- 1/2 + 2/11 * bourgainα) : ℝ))
    (hB : max_val b ≤ (p^(- 1/2 + 2/11 * bourgainα) : ℝ))
    (χ : AddChar α ℂ) (h : χ.IsNontrivial) :
    ‖∑ x, a x * ∑ y, b y * χ (x * y + x^2 * y^2)‖ ≤ bourgain_C * p^(-1/352 * bourgainα) := by
  let a' := a.apply fun x => (x, x^2)
  let b' := b.apply fun x => (x, x^2)
  calc ‖∑ x, a x * ∑ y, b y * χ (x * y + x^2 * y^2)‖
    _ = ‖∑ x, a x * ∑ y, (b.apply fun x => (x, x^2)) y * χ (x * y.1 + x^2 * y.2)‖ := by
      congr with _
      congr 1
      apply Eq.symm
      apply apply_weighted_sum
    _ = ‖∑ x, (a.apply fun x => (x, x^2)) x * ∑ y, (b.apply fun x => (x, x^2)) y * χ (x.1 * y.1 + x.2 * y.2)‖ := by
      congr 1
      apply Eq.symm
      apply apply_weighted_sum
    _ = ‖∑ x, a' x * ∑ y, b' y * χ (IP x y)‖ := rfl
    _ ≤ ‖∑ x, a' x * ∑ y, (b' - b') y * χ (IP x y)‖^(2⁻¹ : ℝ) := bourgain_extractor_aux₁' ..
    _ ≤ (‖∑ x, a' x * ∑ y, ((b' - b') - (b' - b')) y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
      gcongr
      apply bourgain_extractor_aux₁'
    _ ≤ ((‖∑ x, a' x * ∑ y, (((b' - b') - (b' - b')) - ((b' - b') - (b' - b'))) y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
      gcongr
      apply bourgain_extractor_aux₁'
    _ = ((‖∑ x, a' x * ∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
      rcongr
      simp only [FinPMF.sub_eq_add_neg, FinPMF.neg_add, FinPMF.neg_neg]
      generalize -b'=c'
      abel
    _ = ‖∑ x, a' x * ∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * χ (IP x y)‖^(8⁻¹ : ℝ) := by
      rw [← Real.rpow_mul, ← Real.rpow_mul]
      congr
      norm_num
      positivity
      positivity
    _ = ‖∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * ∑ x, a' x * χ (IP x y)‖^(8⁻¹ : ℝ) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      congr with _
      congr with _
      ring
    _ = ‖∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * ∑ x, a' x * χ (IP y x)‖^(8⁻¹ : ℝ) := by
      simp_rw [IP_comm]
    _ ≤ (‖∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * ∑ x, (a' - a') x * χ (IP y x)‖^(2⁻¹ : ℝ))^(8⁻¹ : ℝ) := by
      gcongr
      apply bourgain_extractor_aux₁'
    _ ≤ ((‖∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * ∑ x, ((a' - a') - (a' - a')) x * χ (IP y x)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(8⁻¹ : ℝ) := by
      gcongr
      apply bourgain_extractor_aux₁'
    _ ≤ (((‖∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * ∑ x, (((a' - a') - (a' - a')) - ((a' - a') - (a' - a'))) x * χ (IP y x)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(8⁻¹ : ℝ) := by
      gcongr
      apply bourgain_extractor_aux₁'
    _ = ‖∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * ∑ x, (((a' - a') - (a' - a')) - ((a' - a') - (a' - a'))) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
      rw [← Real.rpow_mul, ← Real.rpow_mul, ← Real.rpow_mul]
      congr
      norm_num
      repeat positivity
    _ = ‖∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * ∑ x, ((a' + a' + a') + (a' - a' - a' - a' - a')) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
      rcongr
      simp only [FinPMF.sub_eq_add_neg, FinPMF.neg_add, FinPMF.neg_neg]
      generalize -a'=c'
      abel
    _ = ‖∑ y, (((b * b * b).apply fun x => (x.1.1 + x.1.2 + x.2, (x.1.1^2 + x.1.2^2 + x.2^2 : α))) + (b' - b' - b' - b' - b')) y *
        ∑ x, (((a * a * a).apply fun x => (x.1.1 + x.1.2 + x.2, (x.1.1^2 + x.1.2^2 + x.2^2 : α))) + (a' - a' - a' - a' - a')) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
      rcongr
      · unfold_let b'
        rw [FinPMF.apply_add, FinPMF.apply_add]
        rfl
      · unfold_let a'
        rw [FinPMF.apply_add, FinPMF.apply_add]
        rfl
    _ = ‖∑ y, ((lapply b ((b * b).apply lmap)).apply decoder + (b' - b' - b' - b' - b')) y *
        ∑ x, ((lapply a ((a * a).apply lmap)).apply decoder + (a' - a' - a' - a' - a')) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
      simp_rw [jurl]
    _ ≤ (Fintype.card α / p^(1 + 2/11 * bourgainα) + 2 * (8 * ST_C * p^(-2/11 * bourgainα)))^(64⁻¹ : ℝ) := by
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
      apply add_close_high_entropy
      apply bourgain_extractor_aux₃; assumption
      apply add_close_high_entropy
      apply bourgain_extractor_aux₃; assumption
    _ = (p^(1 : ℝ) / p^(1 + 2/11 * bourgainα) + 2 * (8 * ST_C * p^(-2/11 * bourgainα)))^(64⁻¹ : ℝ) := by
      congr
      simp [card_univ]
    _ = (p^((1 : ℝ) - (1 + 2/11 * bourgainα)) + 2 * (8 * ST_C * p^(-2/11 * bourgainα)))^(64⁻¹ : ℝ) := by
      rw [← Real.rpow_sub]
      exact_mod_cast fpprm.out.pos
    _ = ((16 * ST_C + 1) * p^(-2/11 * bourgainα))^(64⁻¹ : ℝ) := by
      ring_nf
    _ = (16 * ST_C + 1)^(64⁻¹ : ℝ) * p^(-1/352 * bourgainα) := by
      rw [Real.mul_rpow, ← Real.rpow_mul]
      ring_nf
      simp
      positivity
      apply Real.rpow_nonneg
      simp

theorem bourgain_extractor_final' (a b : FinPMF α)
    (hA : max_val a ≤ (p^(- 1/2 + 2/11 * bourgainα) : ℝ))
    (hB : max_val b ≤ (p^(- 1/2 + 2/11 * bourgainα) : ℝ)) (m : ℕ+) :
    SD ((a*b).apply fun ⟨x, y⟩ => ((x * y + x^2 * y^2).val : ZMod m)) (Uniform ⟨univ, univ_nonempty⟩)
    ≤ bourgain_C * p^(-1/352 * bourgainα) * Real.sqrt m * (3 * Real.log p + 3) + m / (2 * p) := by
  convert_to SD (((a*b).apply fun ⟨x, y⟩ => x * y + x^2 * y^2).apply fun x => (x.val : ZMod m)) (Uniform ⟨univ, univ_nonempty⟩) ≤ _
  rw [FinPMF.apply_apply]
  rfl
  have : (p.toPNat fpprm.out.pos) = p := rfl
  convert generalized_XOR_lemma (p.toPNat fpprm.out.pos) ..
  apply Eq.symm
  apply Real.coe_toNNReal
  apply mul_nonneg
  unfold bourgain_C
  positivity
  positivity
  intro χ hχ
  rw [le_div_iff]

  unfold cft nl2Inner
  simp only [expect_univ, ZMod.card, ← nnratCast_smul_eq_nnqsmul ℝ, NNRat.cast_inv,
    NNRat.cast_natCast, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_nat_cast, norm_mul,
    norm_inv, Complex.norm_nat, Complex.norm_eq_abs, Real.coe_toNNReal', this]
  rw [Complex.abs_natCast, le_max_iff]
  left
  rw [mul_comm, ← mul_assoc, mul_inv_cancel, one_mul, ← Complex.norm_eq_abs]
  conv =>
    lhs
    rhs
    rhs
    intro
    rw [mul_comm, ← AddChar.inv_apply_eq_conj, ← AddChar.inv_apply']
  conv =>
    lhs
    rhs
    apply apply_weighted_sum
  rw [Fintype.sum_prod_type]
  simp only [FinPMF.mul_val, RCLike.ofReal_mul]
  simp_rw [mul_assoc, ← mul_sum]
  apply bourgain_extractor
  assumption
  assumption
  rw [AddChar.isNontrivial_iff_ne_trivial, inv_ne_one, ← AddChar.isNontrivial_iff_ne_trivial]
  exact hχ
  simp [fpprm.out.ne_zero]
  simp


theorem bourgain_extractor_final (m : ℕ+) :
    two_extractor (fun (⟨x, y⟩ : α × α) => ((x * y + x^2 * y^2).val : ZMod m))
    ((1/2 - 2/11 * bourgainα) * Real.logb 2 p) (bourgain_C * p^(-1/352 * bourgainα) * Real.sqrt m * (3 * Real.log p + 3) + m / (2 * p)) := by
  rintro a b ⟨ha, hb⟩
  rw [ge_iff_le, ← min_entropy_of_max_val_le] at ha hb
  convert bourgain_extractor_final' (p := p) a b ?_ ?_ m
  · convert ha using 1
    conv =>
      rhs
      rhs
      tactic =>
        rw [mul_comm, Real.rpow_mul, Real.rpow_logb]
        norm_num
        norm_num
        simp [fpprm.out.pos]
        norm_num
    rw [← Real.rpow_neg]
    congr 1
    ring
    simp
  · convert hb using 1
    conv =>
      rhs
      rhs
      tactic =>
        rw [mul_comm, Real.rpow_mul, Real.rpow_logb]
        norm_num
        norm_num
        simp [fpprm.out.pos]
        norm_num
    rw [← Real.rpow_neg]
    congr 1
    ring
    simp
