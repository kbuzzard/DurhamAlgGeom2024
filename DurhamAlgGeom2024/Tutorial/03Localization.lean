import Mathlib

variable (R : Type) [CommRing R] (S : Submonoid R)

#check Localization S

#synth CommRing (Localization S)

example (r : R) (s : S) : Localization S :=
  Localization.mk r s

open Localization
example (r : R) (s t : S) : mk r s * mk 1 t = mk r (s * t) := by
  sorry

example (s : S) : mk (s : R) s = 1 := by
  sorry
