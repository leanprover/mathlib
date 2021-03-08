/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Benjamin Davidson
-/
import measure_theory.interval_integral

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various simple functions, including `pow`, `exp`,
`inv`/`one_div`, `sin`, `cos`, and `λ x, 1 / (1 + x^2)`.

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`. Scroll to the
bottom of the file for examples.

This file is incomplete; we are working on expanding it.
-/

open real set
variables {a b : ℝ} {f f' g : ℝ → ℝ}

namespace interval_integral
open measure_theory

theorem integral_deriv_eq_sub' (f) (hderiv : deriv f = f')
  (hdiff : ∀ x ∈ interval a b, differentiable_at ℝ f x)
  (hcont' : continuous_on f' (interval a b)) :
  ∫ y in a..b, f' y = f b - f a :=
by rw [← hderiv, integral_deriv_eq_sub hdiff]; cc

@[simp]
lemma integral_const_mul (c : ℝ) : ∫ x in a..b, c * f x = c * ∫ x in a..b, f x :=
integral_smul c

@[simp]
lemma integral_mul_const (c : ℝ) : ∫ x in a..b, f x * c = (∫ x in a..b, f x) * c :=
by simp only [mul_comm, integral_const_mul]

@[simp]
lemma integral_div' (c : ℝ) : ∫ x in a..b, f x / c = (∫ x in a..b, f x) * c⁻¹ :=
integral_mul_const c⁻¹

lemma integral_div (c : ℝ) : ∫ x in a..b, f x / c = (∫ x in a..b, f x) / c :=
integral_div' c

@[simp]
lemma interval_integrable_pow (n : ℕ) : interval_integrable (λ x, x^n) volume a b :=
(continuous_pow n).interval_integrable a b

@[simp]
lemma interval_integrable_id : interval_integrable (λ x, x) volume a b :=
continuous_id.interval_integrable a b

@[simp]
lemma interval_integrable_const (c : ℝ) : interval_integrable (λ x, c) volume a b :=
continuous_const.interval_integrable a b

@[simp]
lemma interval_integrable.const_mul (c : ℝ) (h : interval_integrable f volume a b) :
  interval_integrable (λ x, c * f x) volume a b :=
by convert h.smul c

lemma interval_integrable_one_div (hf : continuous_on f (interval a b))
  (h : ∀ x : ℝ, x ∈ interval a b → f x ≠ 0) :
  interval_integrable (λ x, 1 / f x) volume a b :=
(continuous_on_const.div hf h).interval_integrable

@[simp]
lemma interval_integrable_inv (hf : continuous_on f (interval a b))
  (h : ∀ x : ℝ, x ∈ interval a b → f x ≠ 0) :
  interval_integrable (λ x, (f x)⁻¹) volume a b :=
by simpa only [one_div] using interval_integrable_one_div hf h

@[simp]
lemma interval_integrable_exp : interval_integrable exp volume a b :=
continuous_exp.interval_integrable a b

@[simp]
lemma interval_integrable_sin : interval_integrable sin volume a b :=
continuous_sin.interval_integrable a b

@[simp]
lemma interval_integrable_cos : interval_integrable cos volume a b :=
continuous_cos.interval_integrable a b

end interval_integral

open interval_integral

@[simp]
lemma integral_pow (n : ℕ) : ∫ x in a..b, x ^ n = (b^(n+1) - a^(n+1)) / (n + 1) :=
begin
  have hderiv : deriv (λ x:ℝ, x^(n + 1) / (n + 1)) = λ x, x ^ n,
  { have hne : (n + 1 : ℝ) ≠ 0 := by exact_mod_cast nat.succ_ne_zero n,
    ext,
    simp [mul_div_assoc, mul_div_cancel' _ hne] },
  rw integral_deriv_eq_sub' _ hderiv;
  norm_num [div_sub_div_same, (continuous_pow n).continuous_on],
end

@[simp]
lemma integral_id : ∫ x in a..b, x = (b^2 - a^2) / 2 :=
by simpa using integral_pow 1

@[simp]
lemma integral_one : ∫ x in a..b, (1:ℝ) = b - a :=
by simp

@[simp]
lemma integral_exp : ∫ x in a..b, exp x = exp b - exp a :=
by rw integral_deriv_eq_sub'; norm_num [continuous_exp.continuous_on]

@[simp]
lemma integral_inv (h : (0:ℝ) ∉ interval a b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
begin
  have h' := λ x hx, ne_of_mem_of_not_mem hx h,
  rw [integral_deriv_eq_sub' _ deriv_log' (λ x hx, differentiable_at_log (h' x hx))
        (continuous_on_inv'.mono (subset_compl_singleton_iff.mpr h)),
      log_div (h' b right_mem_interval) (h' a left_mem_interval)],
end

@[simp]
lemma integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
integral_inv $ not_mem_interval_of_lt ha hb

@[simp]
lemma integral_inv_of_neg (ha : a < 0) (hb : b < 0) : ∫ x in a..b, x⁻¹ = log (b / a) :=
integral_inv $ not_mem_interval_of_gt ha hb

lemma integral_one_div (h : (0:ℝ) ∉ interval a b) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv h]

lemma integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv_of_pos ha hb]

lemma integral_one_div_of_neg (ha : a < 0) (hb : b < 0) : ∫ x : ℝ in a..b, 1/x = log (b / a) :=
by simp only [one_div, integral_inv_of_neg ha hb]

@[simp]
lemma integral_sin : ∫ x in a..b, sin x = cos a - cos b :=
by rw integral_deriv_eq_sub' (λ x, -cos x); norm_num [continuous_sin.continuous_on]

@[simp]
lemma integral_cos : ∫ x in a..b, cos x = sin b - sin a :=
by rw integral_deriv_eq_sub'; norm_num [continuous_on_cos]

@[simp]
lemma integral_inv_one_add_sq : ∫ x : ℝ in a..b, (1 + x^2)⁻¹ = arctan b - arctan a :=
begin
  simp only [← one_div],
  refine integral_deriv_eq_sub' _ _ _ (continuous_const.div _ (λ x, _)).continuous_on,
  { norm_num },
  { norm_num },
  { continuity },
  { nlinarith },
end

lemma integral_one_div_one_add_sq : ∫ x : ℝ in a..b, 1 / (1 + x^2) = arctan b - arctan a :=
by simp

open measure_theory
open_locale real

-- @[simp] lemma interval_integrable.add' (hf : interval_integrable f volume a b)
--   (hg : interval_integrable g volume a b) : interval_integrable (λ x, f x + g x) volume a b :=
-- ⟨hf.1.add hg.1, hf.2.add hg.2⟩

-- @[simp] lemma interval_integrable.sub' (hf : interval_integrable f volume a b)
--   (hg : interval_integrable g volume a b) : interval_integrable (λ x, f x - g x) volume a b :=
-- ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

example : ∫ x:ℝ in 0..1, 3*x^2 + 2*x = 2 := by norm_num

example : ∫ x:ℝ in 0..1, 3*x^2 + 2*x + 1 = 3 :=
begin
  norm_num,

  -- have : interval_integrable (λ x:ℝ, 3 * x ^ 2 + 2 * x) volume 0 1,
  -- { apply interval_integrable.add; simp },
  -- norm_num [this],

  -- have h1 : interval_integrable (λ x:ℝ, 3*x^2) volume 0 1 := by simp,
  -- have h2 : interval_integrable (λ x:ℝ, 2*x) volume 0 1 := by simp,
  -- have h3 : interval_integrable (λ x:ℝ, (1:ℝ)) volume 0 1 := by simp,
  -- have H := integral_add (h1.add h2) h3,
  -- simp only [pi.add_apply] at H,
  -- norm_num [H],
end

example : ∫ x:ℝ in 0..1, 4*x^3 + 3*x^2 + 2*x + 1 = 4 :=
begin
  norm_num,

  -- have h1 : interval_integrable (λ x:ℝ, 4 * x ^ 3 + 3 * x ^ 2) volume 0 1,
  -- { apply interval_integrable.add; simp },
  -- have h2 : interval_integrable (λ x:ℝ, 4 * x ^ 3 + 3 * x ^ 2 + 2 * x) volume 0 1,
  -- { apply h1.add, simp },
  -- norm_num [h1, h2],

  -- have h0 : interval_integrable (λ x:ℝ, 4*x^3) volume 0 1 := by simp,
  -- have h1 : interval_integrable (λ x:ℝ, 3*x^2) volume 0 1 := by simp,
  -- have h2 : interval_integrable (λ x:ℝ, 2*x) volume 0 1 := by simp,
  -- have h3 : interval_integrable (λ x:ℝ, (1:ℝ)) volume 0 1 := by simp,
  -- have H1 := integral_add ((h0.add h1).add h2) h3,
  -- have H2 := integral_add (h0.add h1) h2,
  -- simp only [pi.add_apply] at H1 H2,
  -- norm_num [H1, H2],
end
