import Mathlib
import DurhamAlgGeom2024.Tutorial.«06point5MoreHomogeneousLocalization»
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

instance : Algebra (𝒜 0) S := (SetLike.GradeZero.subalgebra 𝒜).toAlgebra
--variable [Algebra.FiniteType (𝒜 0) S]

/-

## Generation of S by homogeneous elements

By definition `S = ⨁ᵢ (𝒜 i)` is a graded ring (graded by `ℕ`) and
in particular `S` is an `𝒜 0`-algebra.

By assumption `S` is finitely-generated `𝒜 0`-algebra.

What we next claim is that `S` is generated by finitely many *homogeneous*
elements of `S`.

-/

-- But we need homogeneous generators.
-- This preliminary version gives homogeneous generators
-- but allows generators in degree 0
variable [Algebra.FiniteType (𝒜 0) S] in
theorem FG_by_homogeneous₀ : ∃ (ι₀ : Type) (x : ι₀ → S) (_ : Fintype ι₀),
    (Algebra.adjoin (𝒜 0) (Set.range x) = ⊤) ∧
    (∀ i : ι₀, ∃ n : ℕ, x i ∈ 𝒜 n) := by
  classical
  -- S is finitely-generated
  obtain ⟨F, hF⟩ := Algebra.FiniteType.out (R := 𝒜 0) (A := S)
  -- ι₀ is pairs (s,n) such that s ∈ F and sₙ ≠ 0
  let ι₀ := Σ (x : F), (DirectSum.decompose 𝒜 x.1).support
  -- x(s,n) is sₙ
  let x (i : ι₀) : S := ((DirectSum.decompose 𝒜) i.1 i.2).1
  -- This should work
  refine ⟨ι₀, x, inferInstance, ?_, ?_⟩
  · rw [← top_le_iff, ← hF]
    apply Algebra.adjoin_le
    -- STP that if s ∈ F then s ∈ 𝒜₀[tₘ] for t running through F
    intro s hs
    -- Well s = ∑ₙ sₙ
    rw [← DirectSum.sum_support_decompose 𝒜 s]
    -- so it suffices that ∀ n, sₙ ∈ 𝒜₀[tₘ]
    apply sum_mem
    intro n hn
    -- so it suffices that sₙ is one of the tₘ
    apply Algebra.subset_adjoin
    -- but this is obvious
    use ⟨⟨s, hs⟩, n, hn⟩
  · rintro ⟨f, nf⟩
    use nf
    exact ((DirectSum.decompose 𝒜) f nf).2

variable [Algebra.FiniteType (𝒜 0) S] in
theorem FG_by_homogeneous : ∃ (ι : Type) (x : ι → S) (_ : Fintype ι),
    (Algebra.adjoin (𝒜 0) (Set.range x) = ⊤) ∧
    (∀ i : ι, ∃ n : ℕ, 0 < n ∧ x i ∈ 𝒜 n) := by
  obtain ⟨ι₀, x, _, h1, h2⟩ := FG_by_homogeneous₀ 𝒜
  choose n hn using h2
  use {i : ι₀ // 0 < n i}, fun j ↦ x j.1, inferInstance
  refine ⟨?_, ?_⟩
  · rw [← top_le_iff, ← h1]
    apply Algebra.adjoin_le
    rintro s ⟨i, rfl⟩
    by_cases hi : 0 < n i
    · apply Algebra.subset_adjoin
      use ⟨i, hi⟩
    · have hi0 : n i = 0 := by omega
      exact Subalgebra.algebraMap_mem
        (Algebra.adjoin (↥(𝒜 0)) (Set.range fun (j : {i : ι₀ // 0 < n i}) ↦ x j)) ⟨x i, hi0 ▸ hn i⟩
  · rintro ⟨i, hi⟩
    use n i, hi
    apply hn

open HomogeneousLocalization

/-

## S_{(f)} is an 𝒜₀-algebra

Although S_{(f)} isn't an S-algebra (because S has
stuff in degree not zero but S_{(f)} is only degree 0 stuff)

-/

variable {d : ℕ}
variable {f : S} (hf : f ∈ 𝒜 d)

--#synth Algebra (𝒜 0) (Away 𝒜 f)

variable {A : Type} [CommRing A] [IsDomain A] [ValuationRing A]
variable {K : Type} [Field K] [Algebra A K] [IsFractionRing A K]

/-
The diagram in the question

                  φ
              K <--- S(f)
              /\      /\
     canonical|       |canonical
              |       |
              A <---- 𝒜₀
                  φ₀
-/

variable (φ₀ : (𝒜 0) →+* A)
variable (φ : (Away 𝒜 f) →+* K)
variable (hcomm : (algebraMap A K).comp φ₀ = φ.comp (fromZeroRingHom 𝒜 _))

/-
projective_implies_proper_aux {R₀ S : Type} [CommRing R₀] [CommRing S] [Algebra R₀ S] (𝒜 : ℕ → Submodule R₀ S)
  [GradedAlgebra 𝒜] [Algebra.FiniteType (↥(𝒜 0)) S] {d : ℕ} {f : S} (hf : f ∈ 𝒜 d) {A : Type} [CommRing A] [IsDomain A]
  [ValuationRing A] {K : Type} [Field K] [Algebra A K] [IsFractionRing A K] (φ : Away 𝒜 f →+* K) (hd : 0 < d) :
  ∃ x₀ e,
    ∃ (_ : 0 < e) (h₀ : x₀ ∈ 𝒜 e),
      ∃ φ', φ'.comp (map2 𝒜 h₀ ⋯) = φ ∧ Set.range ⇑(φ'.comp (map2 𝒜 hf ⋯)) ⊆ Set.range ⇑(algebraMap A K)
-/

omit [GradedAlgebra 𝒜] in
lemma away_zero_subsingleton : Subsingleton (Away 𝒜 0) := by
  apply HomogeneousLocalization.subsingleton
  use 1
  simp

lemma f_ne_zero_of_away_ringHom (φ : Away 𝒜 f →+* K) : f ≠ 0 := by
  rintro rfl
  have : Subsingleton (Away 𝒜 0) :=
    away_zero_subsingleton 𝒜
  have : Subsingleton K := RingHom.codomain_trivial φ
  have : Nontrivial K := CommGroupWithZero.toNontrivial
  exact false_of_nontrivial_of_subsingleton K

lemma ι_nonempty (hd : 0 < d) (ι : Type) (x : ι → S)
    {f : S} (hf : f ∈ 𝒜 d) (φ : Away 𝒜 f →+* K)
    (hι : Algebra.adjoin (↥(𝒜 0)) (Set.range x) = ⊤) : Nonempty ι := by
  suffices ¬ IsEmpty ι by exact not_isEmpty_iff.mp this
  intro hempty
  have hf0 : f ≠ 0 := by exact f_ne_zero_of_away_ringHom 𝒜 φ
  have := Algebra.adjoin_empty (𝒜 0) S
  have range_empty : Set.range x = ∅ := by
    rw [Set.eq_empty_iff_forall_not_mem]
    intro s ⟨i, hi⟩
    exact IsEmpty.false i
  rw [range_empty, this] at hι
  have hf2 : f ∈ (⊤ : Subalgebra (𝒜 0) S) := by exact trivial
  rw [← hι] at hf2
  suffices d = 0 by omega
  refine DirectSum.degree_eq_of_mem_mem 𝒜 hf ?_ hf0
  rw [Algebra.mem_bot] at hf2
  obtain ⟨⟨g, hg1⟩, hg⟩ := hf2
  rw [← hg]
  exact hg1

instance (x : Submonoid S) : Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x) :=
  (HomogeneousLocalization.fromZeroRingHom 𝒜 x).toAlgebra

theorem SetLike.prod_mem_graded {ι R S : Type*} [SetLike S R] [CommMonoid R]
    [AddCommMonoid ι] {A : ι → S} [SetLike.GradedMonoid A] {κ : Type*} ⦃i : κ → ι⦄ {g : κ → R}
    {F : Finset κ} (hF : ∀ k ∈ F, g k ∈ A (i k)) : ∏ k ∈ F, g k ∈ A (∑ k ∈ F, i k) := by
  classical
  induction F using Finset.induction_on
  · simp [GradedOne.one_mem]
  · case insert j F' hF2 h3 =>
    rw [Finset.prod_insert hF2, Finset.sum_insert hF2]
    apply SetLike.mul_mem_graded (hF j <| Finset.mem_insert_self j F')
    apply h3
    intro k hk
    apply hF k
    exact Finset.mem_insert_of_mem hk

theorem SetLike.fintype_prod_mem_graded {ι R S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι]
    {A : ι → S} [SetLike.GradedMonoid A] {κ : Type*} [Fintype κ] ⦃i : κ → ι⦄ {g : κ → R}
    (hF : ∀ k, g k ∈ A (i k)) : ∏ k, g k ∈ A (∑ k, i k) :=
  prod_mem_graded fun k _ ↦ hF k

theorem SetLike.fintype_prod_pow_mem_graded {ι R S : Type*} [SetLike S R] [CommMonoid R] [AddCommMonoid ι]
    {A : ι → S} [SetLike.GradedMonoid A] {κ : Type*} [Fintype κ] ⦃i : κ → ι⦄ {g : κ → R}
    {v : κ → ℕ}
    (hF : ∀ k, g k ∈ A (i k)) : ∏ k, g k ^ v k ∈ A (∑ k, v k • i k) :=
  SetLike.prod_mem_graded fun k _ ↦ (SetLike.pow_mem_graded (v k) (hF _))


lemma algebraMap_eq' (x : Submonoid S) (a) :
    algebraMap (𝒜 0) (HomogeneousLocalization 𝒜 x) a =
      HomogeneousLocalization.fromZeroRingHom 𝒜 x a := rfl

theorem Submonoid.exists_finsupp_of_mem_closure_range {M : Type*} [CommMonoid M] {ι : Type*}
    (f : ι → M) {x} (hx : x ∈ Submonoid.closure (Set.range f)) :
    ∃ a : ι →₀ ℕ, x = a.prod (f · ^ ·) := by
  classical
  induction hx using Submonoid.closure_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; exact ⟨Finsupp.single i 1, by simp⟩
  | one => use 0; simp
  | mul x y hx hy hx' hy' =>
    obtain ⟨⟨v, rfl⟩, w, rfl⟩ := And.intro hx' hy'
    use v + w
    rw [Finsupp.prod_add_index]
    · simp
    · simp [pow_add]

theorem Submonoid.exists_of_mem_closure_range {M : Type*} [CommMonoid M] {ι : Type*} [Fintype ι]
    (f : ι → M) {x} (hx : x ∈ Submonoid.closure (Set.range f)) :
    ∃ a : ι → ℕ, x = ∏ i, f i ^ a i := by
  obtain ⟨a, rfl⟩ := Submonoid.exists_finsupp_of_mem_closure_range f hx
  exact ⟨a, by simp⟩

open HomogeneousLocalization in
theorem HomogeneousLocalization.Away.span_monomial_eq_top (f : S) (d : ℕ) (hf : f ∈ 𝒜 d)
    (ι : Type) (x : ι → S) (_ : Fintype ι)
    (hx : Algebra.adjoin (𝒜 0) (Set.range x) = ⊤) (dx : ι → ℕ ) (hxd : ∀i, x i ∈ 𝒜 (dx i)) :
    Submodule.span (𝒜 0) { mk (𝒜 := 𝒜) (x := .powers f)
      ⟨a * d, ⟨∏ i, x i ^ ai i, hai ▸ SetLike.fintype_prod_pow_mem_graded hxd⟩,
        ⟨f ^ a, SetLike.pow_mem_graded a hf⟩, by use a⟩ |
        (a : ℕ) (ai : ι → ℕ) (hai : ∑ i, ai i * dx i = a * d) } = ⊤ := by
  by_cases HH : Subsingleton (HomogeneousLocalization.Away 𝒜 f)
  · exact Subsingleton.elim _ _
  classical
  rw [← top_le_iff]
  rintro x -
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, ⟨j, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
  by_cases hfj : f ^ j = 0
  · exact (HH (HomogeneousLocalization.subsingleton _ ⟨_, hfj⟩)).elim
  have : DirectSum.decompose 𝒜 a n = ⟨a, ha⟩ := Subtype.ext (DirectSum.decompose_of_mem_same 𝒜 ha)
  simp_rw [← this]
  clear this ha
  have : a ∈ Submodule.span (𝒜 0) (Submonoid.closure (Set.range x)) := by
    rw [← Algebra.adjoin_eq_span, hx]
    trivial
  induction this using Submodule.span_induction with
  | mem a ha' =>
    obtain ⟨ai, rfl⟩ := Submonoid.exists_of_mem_closure_range _ ha'
    clear ha'
    by_cases H : ∑ i, ai i * dx i = n
    · apply Submodule.subset_span
      refine ⟨j, ai, H.trans ?_, ?_⟩
      · exact DirectSum.degree_eq_of_mem_mem 𝒜 hb'
          (SetLike.pow_mem_graded j hf) hfj
      · ext
        simp only [val_mk]
        congr
        refine (DirectSum.decompose_of_mem_same _ ?_).symm
        exact H ▸ SetLike.fintype_prod_pow_mem_graded hxd
    · convert zero_mem (Submodule.span (𝒜 0) _)
      ext
      have : (DirectSum.decompose 𝒜 (∏ i : ι, x i ^ ai i) n).1= 0 := by
        refine DirectSum.decompose_of_mem_ne _ ?_ H
        exact SetLike.fintype_prod_pow_mem_graded hxd
      simp [this, Localization.mk_zero]
  | zero =>
      convert zero_mem (Submodule.span (𝒜 0) _)
      ext; simp [Localization.mk_zero]
  | add s t hs ht hs' ht'  =>
    convert add_mem hs' ht'
    ext; simp [← Localization.add_mk_self]
  | smul r x hx hx' =>
    convert Submodule.smul_mem _ r hx'
    ext
    simp only [val_mk, Algebra.smul_def, val_mul, algebraMap_eq',
      fromZeroRingHom, DirectSum.decompose_mul, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, val_mk,
      SetLike.GradeZero.coe_one, Localization.mk_mul,
      Submonoid.mk_mul_mk, one_mul]
    congr
    erw [DirectSum.decompose_coe]
    clear hx hx'
    induction x using DirectSum.Decomposition.inductionOn 𝒜 with
    | h_zero => simp
    | @h_homogeneous i m =>
      simp [DirectSum.of_mul_of]
      by_cases H : i = n
      · subst H
        simp only [DirectSum.of_eq_same]
        convert congr($(DirectSum.of_eq_same (β := fun i ↦ 𝒜 i) (0 + i)
          (GradedMonoid.GMul.mul (A := (𝒜 ·)) r m)).1) <;> simp
      · rw [DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne]
        · simp
        · exact H
        · simpa
    | h_add =>
      simp_all [mul_add]

theorem Localization.mk_prod {R : Type*} [CommRing R] {S : Submonoid R} {ι} (t : Finset ι)
    (f : ι → R) (s : ι → S) :
    ∏ i in t, Localization.mk (f i) (s i) = Localization.mk (∏ i in t, f i) (∏ i in t, s i) := by
  classical
  induction t using Finset.induction_on
  · simp [Localization.mk_one]
  · simp [Finset.prod_insert ‹_›, *, Localization.mk_mul]

theorem projective_implies_proper_aux
    (ι : Type) [Fintype ι] (x : ι → S)
    (h2 : Algebra.adjoin (↥(𝒜 0)) (Set.range x) = (⊤ : Subalgebra (𝒜 0) S))
    (j : ι)
    (φ : Away 𝒜 (x j) →+* K)
    (d : ι → ℕ)
    (hdi : ∀ i, 0 < d i)
    (hxdi : ∀ i, x i ∈ 𝒜 (d i)) :
    ∃ (x₀ : S) (e : ℕ) (he : 0 < e)
      (h₀ : x₀ ∈ 𝒜 e)
      (φ' : Away 𝒜 ((x j) * x₀) →+* K),
      (φ'.comp (map2 𝒜 h₀ rfl) = φ) ∧
      Set.range (φ'.comp (map2 𝒜 (hxdi j) (mul_comm (x j) x₀))) ⊆ Set.range (algebraMap A K) := by
  classical
  let ψ : (i : ι) → ValuationRing.ValueGroup A K :=
    fun i ↦ ValuationRing.valuation A K <| (φ (mk {
      deg := (d j) * d i
      num := ⟨x i ^ d j, SetLike.pow_mem_graded (d j) (hxdi i) ⟩
      den := ⟨(x j)^(d i) , mul_comm (d j) (d i) ▸ SetLike.pow_mem_graded (d i) ( hxdi j)⟩
      den_mem := ⟨_, rfl⟩
    }))^ ∏ k in Finset.univ.erase i, d k
  have hιnonempty : Nonempty ι := by exact ι_nonempty 𝒜 (hdi j) ι x (hxdi j) φ h2
  have foo : (Finset.image ψ Finset.univ).Nonempty := by rwa [Finset.image_nonempty, Finset.univ_nonempty_iff]
  set Kmax := Finset.max' (Finset.image ψ Finset.univ) foo
  have : Kmax ∈ _ := Finset.max'_mem (Finset.image ψ Finset.univ) foo
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at this
  obtain ⟨i0, hi1⟩ := this
  have hi0 : ∀ (j : ι), ψ j ≤ ψ i0 := by
    intro j
    rw [hi1]
    exact Finset.le_max' (Finset.image ψ Finset.univ) (ψ j) (by simp)
  use x i0, d i0, hdi i0, hxdi i0
  have hKmax : Kmax ≠ 0 := by
    intro hKmax
    unfold Kmax at hKmax
    have : ∀ i : ι, ψ i ≤ 0 := by
      intro i
      rw [← hKmax]
      apply Finset.le_max'
      simp
    have this : ∀ i, ψ i = 0 := by
      intro i
      specialize this i
      exact le_zero_iff.mp this
    unfold ψ at this
    simp only [map_pow, pow_eq_zero_iff', map_eq_zero, ne_eq] at this
    specialize this j
    suffices φ 1 = 0 by
      simp only [map_one, one_ne_zero] at this
    convert this.1
    ext
    simp only [val_one, val_mk]
    symm
    convert Localization.mk_self _
    rfl
  have hKmax : 0 < Kmax := zero_lt_iff.mpr hKmax
  have foo := HomogeneousLocalization.Away.isLocalization_mul 𝒜 (x j) (x i0) (d j) (d i0)
    (hxdi j) (hxdi i0) (hdi _).ne' (hdi _).ne'
  letI := awayAlgebra 𝒜 (x j) (x i0) (d i0) (hxdi i0)
  have foounit : IsUnit (φ (mk { deg := d j * d i0,
                                 num := ⟨x i0 ^ d j, SetLike.pow_mem_graded (d j) (hxdi i0)⟩,
                                 den := ⟨x j ^ d i0, mul_comm (d j) (d i0) ▸ SetLike.pow_mem_graded (d i0) ( hxdi j)⟩,
                                 den_mem := ⟨d i0, rfl⟩})) := by
    unfold ψ at hi1
    apply Ne.isUnit
    intro rid
    rw [rid] at hi1
    simp only [map_pow, map_zero] at hi1
    rw [zero_pow] at hi1
    · exact hKmax.ne' hi1.symm
    simp only [ne_eq, Finset.prod_eq_zero_iff, Finset.mem_erase, Finset.mem_univ, and_true,
      not_exists, not_and]
    intro k _ hk
    exact hdi k |>.ne' hk
  let φ' := @IsLocalization.Away.lift _ _ _ _ _ _ _ _ foo φ foounit
  have hφ' : ∀ s, φ' _ = _ := @IsLocalization.Away.AwayMap.lift_eq _ _ _ _ _ _ _ _ foo _ foounit
  use φ'
  use IsLocalization.Away.AwayMap.lift_comp ..
  rintro _ ⟨sx, rfl⟩
  rw [Set.mem_range, ← ValuationRing.mem_integer_iff]
  rw [Valuation.mem_integer_iff]
  have := HomogeneousLocalization.Away.span_monomial_eq_top 𝒜 (x i0) (d i0) (hxdi i0) ι
    x inferInstance h2 d hxdi
  letI inst1 : Algebra (𝒜 0) (Away 𝒜 (x i0)) := inferInstance
  letI inst2 : Module (𝒜 0) (Away 𝒜 (x i0)) := Algebra.toModule
  have foo2 : sx ∈ (⊤ : Submodule (𝒜 0) (Away 𝒜 (x i0))) := Submodule.mem_top
  rw [← this] at foo2
  induction foo2 using Submodule.span_induction with
  | mem x1 h =>
    obtain ⟨a, ai, hai, rfl⟩ := h
    suffices (ValuationRing.valuation A K)
        (φ (mk {deg := a * d i0 * d j,
                num := ⟨(∏ i : ι, x i ^ ai i) * (x i0) ^ (a * (d j - 1)), by
                  convert SetLike.mul_mem_graded
                    (SetLike.fintype_prod_pow_mem_graded (v := ai) (i := d) hxdi)
                    (SetLike.pow_mem_graded (a * (d j - 1)) (hxdi i0)) using 2
                  simp only [smul_eq_mul]
                  rw [hai]
                  have hdj : (d j ≠ 0) := (hdi j).ne'
                  revert hdj
                  cases (d j)
                  · simp only [ne_eq, not_true_eq_false, mul_zero, zero_le, Nat.sub_eq_zero_of_le,
                    zero_mul, add_zero, zero_eq_mul, IsEmpty.forall_iff]
                  · intro _
                    simp only [add_tsub_cancel_right]
                    ring
                ⟩,
                den := ⟨(x j) ^ (a * d i0), SetLike.pow_mem_graded (a * d i0) (hxdi j)⟩,
                den_mem := ⟨_, rfl⟩}) /
          (φ (mk {deg := d j * d i0,
                  num := ⟨(x i0) ^ d j, SetLike.pow_mem_graded (d j) (hxdi i0)⟩,
                  den := ⟨(x j) ^ (d i0), by
                    have := SetLike.pow_mem_graded (d i0) (hxdi j)
                    convert this using 2
                    apply mul_comm⟩,
                  den_mem := ⟨_, rfl⟩})) ^ a) ≤ 1 by
      convert this
      rw [eq_div_iff <| by rw [←isUnit_iff_ne_zero]; exact IsUnit.pow _ foounit]
      rw [← hφ', ← hφ']
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [← map_pow, ← map_mul]
      congr
      ext
      rw [val_mul]
      rw [val_map2_mk 𝒜]
      simp only [val_pow]
      -- Kevin is working on the below sorry
      let foo : Algebra (Away 𝒜 (x j)) (Away 𝒜 (x j * x i0)) := inferInstance
      sorry
      -- Kevin is working on the above sorry
    rw [map_div₀]
    -- the below sorry: use foounit which says it's a unit in K and hence
    -- nonzero and hence its valuation is positive.
    rw [div_le_iff₀ sorry, one_mul]
    rw [← pow_le_pow_iff_left₀ (n := d j * ∏ i, d i) zero_le' zero_le' <| by
      -- product of positive things is nonzero
      sorry
    ]
    convert_to (∏ i, ψ i ^ (d i * ai i)) * ψ i0 ^ (d i0 * a * (d j - 1)) ≤ _
    · simp only [ψ, ← map_pow, ← map_prod, ← map_mul]
      congr 2
      apply (show Function.Injective (algebraMap (Away 𝒜 (x j)) (Localization.Away (x j)))
        from val_injective _)
      simp only [map_pow, map_prod, map_mul]
      simp only [HomogeneousLocalization.algebraMap_apply, val_mk,
        Localization.mk_pow, Localization.mk_prod, Localization.mk_mul]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      use 1
      simp only [OneMemClass.coe_one, SubmonoidClass.mk_pow, ← pow_mul, Submonoid.coe_mul,
        SubmonoidClass.coe_finset_prod, one_mul]
      simp_rw [Finset.mul_prod_erase Finset.univ d (h := Finset.mem_univ _),
        mul_assoc, ← mul_assoc (Finset.prod ..),
        Finset.prod_erase_mul Finset.univ d (h := Finset.mem_univ _)]
      rw [Finset.prod_pow_eq_pow_sum, ← pow_add, mul_pow, ← Finset.prod_pow]
      simp_rw [← pow_mul]
      congr 3
      · simp_rw [mul_assoc, ← Finset.mul_sum, mul_comm (d _) (ai _), hai]
        have : d j ≠ 0 := (hdi j).ne'
        revert this
        cases d j
        · simp
        · intro _
          simp
          ring
      · ext i
        congr 1
        ring
      · ring
    · trans (∏ i : ι, ψ i0 ^ (d i * ai i)) * ψ i0 ^ (d i0 * a * (d j - 1))
      · gcongr
        · exact zero_le'
        · exact hi0 _
      · rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
        convert_to (ψ i0) ^ (d i0 * a * d j) ≤ _
        · congr 1
          simp_rw [mul_comm (d _) (ai _), hai]
          have : d j ≠ 0 := (hdi j).ne'
          revert this
          cases d j
          · simp
          · intro _
            simp
            ring
        · apply le_of_eq
          simp only [ψ, ← map_pow, ← map_prod, ← map_mul]
          congr 2
          rw [← pow_mul, mul_assoc, ← mul_assoc,
            Finset.prod_erase_mul Finset.univ d (h := Finset.mem_univ _),
            mul_left_comm, pow_mul]
          congr 1
          rw [mul_comm]
  | zero => simp
  | add x y hx hy hhx hhy =>
    simp only [RingHom.coe_comp, Function.comp_apply, map_add, ge_iff_le]
    transitivity
    refine Valuation.map_add (ValuationRing.valuation A K) _ _
    rw [sup_le_iff]
    exact ⟨hhx, hhy⟩
  | smul a x hx _ =>
    -- a • x is (image of a in K) * x, which is (image of a in A) * x,
    -- and stuff in A has valuation <= 1. This involves a tricky diagram
    -- chase in practice though. Justus was thinking about this sorry
    sorry

end statement
