/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.free
import algebra.magma_algebra

/-!
# Free algebras

Given a commutative ring `R` and a type `X` we construct the free non-unital, non-associative
algebra on `X` with coefficients in `R` together with its universal property.

## Main definitions

  * `lib`
  * `lib.lift`
  * `lib.of`

## Implementation details

We define the free algebra as the magma algebra, with coefficients in `R`, of the free magma on `X`.

## Tags

free algebra, non-unital, non-associative, free magma, magma algebra, universal property,
forgetful functor, adjoint functor
-/

universes u v w w₁ w₂

noncomputable theory

variables (R : Type u) (X : Type v) [comm_ring R]

/-- The free non-unital, non-associative algebra on the type `X` with coefficients in `R`. -/
def lib := magma_algebra R (free_magma X) -- TODO: rename `lib` too short for global namespace

namespace lib

variables {X}

def of : X → lib R X := (magma_algebra.of R) ∘ free_magma.of

instance : non_unital_non_assoc_semiring (lib R X) := magma_algebra.non_unital_non_assoc_semiring

instance : non_unital_non_assoc_algebra R (lib R X) :=
magma_algebra.non_unital_non_assoc_algebra

variables {A : Type w} [non_unital_non_assoc_semiring A] [non_unital_non_assoc_algebra R A]

def lift : (X → A) ≃ non_unital_non_assoc_algebra_hom R (lib R X) A :=
free_magma.lift.trans (magma_algebra.lift R)

@[simp] lemma lift_symm_apply (F : non_unital_non_assoc_algebra_hom R (lib R X) A) :
  (lift R).symm F = F ∘ (of R) :=
rfl

@[simp] lemma of_comp_lift (f : X → A) : (lift R f) ∘ (of R) = f :=
(lift R).left_inv f

@[simp] lemma lift_of_apply (f : X → A) (x) : lift R f (of R x) = f x :=
by rw [← function.comp_app (lift R f) (of R) x, of_comp_lift]

@[simp] lemma lift_unique (f : X → A) (g : non_unital_non_assoc_algebra_hom R (lib R X) A) :
  g ∘ (of R) = f ↔ g = lift R f :=
(lift R).symm_apply_eq

attribute [irreducible] of lift

@[simp] lemma lift_comp_of (g : non_unital_non_assoc_algebra_hom R (lib R X) A) :
  lift R (g ∘ (of R)) = g :=
begin
  ext a,
  simp only [lift, of, equiv.coe_trans, function.comp_app],
  rw [← function.comp.assoc, ← g.coe_to_mul_hom, ← mul_hom.coe_comp, free_magma.lift_comp_of,
    non_unital_non_assoc_algebra_hom.coe_to_mul_hom, magma_algebra.lift_comp_of],
end

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma hom_ext {f g : non_unital_non_assoc_algebra_hom R (lib R X) A}
  (h : f ∘ (of R) = g ∘ (of R)) : f = g :=
begin
  rw [← lift_symm_apply, ← lift_symm_apply] at h,
  exact (lift R).symm.injective h,
end

end lib
