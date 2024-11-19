import Mathlib

section missing_instance
/-

Andrew's definition of the algebra structure on `HomogeneousLocalization 𝒜 S`.

-/
open HomogeneousLocalization in
instance {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
  [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    Algebra R (HomogeneousLocalization 𝒜 S) :=
  ((fromZeroRingHom 𝒜 S).comp (algebraMap _ _)).toAlgebra

@[simp]
lemma HomogeneousLocalization.algebraMap_eq
  {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
  [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    algebraMap R (HomogeneousLocalization 𝒜 S) = ((fromZeroRingHom 𝒜 S).comp (algebraMap _ _)) := rfl

end missing_instance

noncomputable section statement

variable {R₀ S : Type}
variable [CommRing R₀] [CommRing S] [Algebra R₀ S]
variable (𝒜 : ℕ → Submodule R₀ S) [GradedAlgebra 𝒜]
variable {d : ℕ} [NeZero d]
variable {f : S} (hf : f ∈ 𝒜 d)
variable [Algebra.FiniteType R₀ S]

open HomogeneousLocalization

variable {A : Type} [CommRing A] [IsDomain A] [ValuationRing A]
variable {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]

/-
The diagram in the question

                  φ
              K <--- S(f)
              /\      /\
     canonical|       |canonical
              |       |
              A <---- R₀
                  φ₀
-/

variable [Algebra R₀ A] -- φ
variable [Algebra (Away 𝒜 f) K] -- φ₀
variable [Algebra R₀ K] -- the diagonal
  -- bottom triangle commutes
  [IsScalarTower R₀ A K]
  -- top triangle commutes
  [IsScalarTower R₀ (Away 𝒜 f) K]

theorem projective_implies_proper_aux : ∃ (x₀ : S) (e : ℕ) (he : 0 < e) (h₀ : x₀ ∈ 𝒜 e)
    (φ' : Away 𝒜 x₀ →+* A), φ'.comp (algebraMap R₀ (Away 𝒜 x₀)) = algebraMap R₀ A := by
  sorry

end statement
