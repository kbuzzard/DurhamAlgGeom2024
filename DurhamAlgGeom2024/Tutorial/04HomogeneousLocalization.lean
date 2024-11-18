import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.AlgebraicGeometry.ValuativeCriterion

open Classical

variable {ι R A : Type}
variable [AddCommMonoid ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
variable (S : Submonoid A)

#synth CommRing (𝒜 0)
#synth Algebra R (𝒜 0)

#check HomogeneousLocalization 𝒜 S
#synth CommRing (HomogeneousLocalization 𝒜 S)
#synth SMul R (HomogeneousLocalization 𝒜 S)
--#synth Algebra R (HomogeneousLocalization 𝒜 S) -- fails **TODO** fix!

variable (y : HomogeneousLocalization 𝒜 S)

open HomogeneousLocalization
#check HomogeneousLocalization.val y
#check y.val

#check y.num
#check y.den
#check y.deg
example : y.num ∈ 𝒜 (y.deg) := y.num_mem_deg
example : y.den ∈ 𝒜 (y.deg) := y.den_mem_deg
example : y.den ∈ S := y.den_mem
example : y.val = .mk y.num ⟨y.den, y.den_mem⟩ := y.eq_num_div_den
