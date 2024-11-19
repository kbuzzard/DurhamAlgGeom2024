import Mathlib
set_option linter.style.header false

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
open Submonoid (powers)

-- Let's define a map from S_(f) to S_(fg)
variable (x : S) (hx : x = f * g)

#check Localization.awayMap

lemma lemma1 : IsUnit ((algebraMap S (Localization.Away x)) f) := sorry

def map1 : Away 𝒜 f →+* Localization.Away x :=
  (Localization.awayLift (algebraMap S _) _ (lemma1 ..)).comp
    (algebraMap (Away 𝒜 f) (Localization.Away f))

lemma lemma2 : Set.range (map1 𝒜 (f := f) x) ⊆ Set.range (val (𝒜 := 𝒜)) := by
  sorry
