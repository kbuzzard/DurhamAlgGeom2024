import Mathlib

open Function

-- a finite integral domain is a field
example (R : Type) [CommRing R] [IsDomain R] [Finite R] : IsField R := by
  sorry
