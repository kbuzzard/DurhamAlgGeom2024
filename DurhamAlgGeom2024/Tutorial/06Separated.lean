import Mathlib

noncomputable section statement

variable {R₀ S : Type}
-- let R₀ and S be commutative rings, and let
-- S be an R₀-algebra
variable [CommRing R₀] [CommRing S] [Algebra R₀ S]
-- Say S is ⨁ 𝒜ᵢ for i ∈ ℕ with the 𝒜ᵢ R₀-submodules
variable (𝒜 : ℕ → Submodule R₀ S) [GradedAlgebra 𝒜]
-- Say d and e are nonzero
variable {d e : ℕ} [NeZero d] [NeZero e]
-- Say f and g are homogeneous of degrees d and e
variable {f : S} (hf : f ∈ 𝒜 d)
variable {g : S} (hg : g ∈ 𝒜 e)

-- let's not have to type HomogeneousLocalization everywhere
open HomogeneousLocalization

-- Let's define a map from S_(f) to S_(fg)

def srtrts (x : S) (hx : x = f * g) :
    Away 𝒜 f →+* Away 𝒜 x where
  toFun := _
  map_add' := sorry
  map_mul' := sorry
  map_one' := sorry
  map_zero' := sorry
