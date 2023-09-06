import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Data.Sign

noncomputable section

#check ExteriorAlgebra
variable (R) [CommRing R] (n : ℕ)
variable  (ι : Type) [LinearOrder ι]

-- a list of indices, sorted
abbrev Model.Index := {l : List ι // l.Sorted (· < ·) }

def Model := Model.Index ι →₀ R



instance : AddCommGroup (Model R ι) := by
  unfold Model
  infer_instance
instance : Module R (Model R ι) := by
  unfold Model
  infer_instance

instance : One (Model R ι) where
  one := Finsupp.single ⟨[], by simp⟩ 1

  /-
  # todos
  define multiplication, prove associativity

  instance : Ring (Model R ι)
  instance : Algebra R (Model R ι)

  square single should give quadratic form
  -/

variable { ι }
def Model.single ( i : ι ) : Model R ι :=
  Finsupp.single {
    val := [i]
    property := by
      simp
  } 1

set_option pp.proofs.withType false

#check Model.single ℤ (1 : Fin 3) + (3:ℤ) • Model.single ℤ (2 : Fin 3)


def mul_helper : Model.Index ι → Model.Index ι → Model.Index ι × SignType :=
  sorry

-- def list_sort_concat
open scoped BigOperators

instance : Mul (Model R ι) where
  -- multiply pairwise
  mul v w :=
    ∑ i in v.support, ∑ j in w.support,
      let ⟨k,s⟩:=mul_helper i j
      Finsupp.single k (s * v.toFun i * w.toFun j)

lemma single_mul_single (i : ι) : Model.single R i * Model.single R i = 0 := sorry

instance : Ring (Model R ι) where
  -- inheritance in lean 4 is (somewhat) broken currently
  __ := inferInstanceAs (AddCommGroup (Model R ι))

  left_distrib := sorry
  right_distrib := sorry

  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one_mul := sorry
  mul_one := sorry

instance : Algebra R (Model R ι) where
  toFun := Finsupp.single ⟨[], by simp⟩
  map_one' := rfl
  map_mul' := sorry
  -- we came up with this by using `by simp`
  map_zero' := Finsupp.single_zero _
  map_add' x y := sorry
  commutes' r x := sorry
  smul_def' r x := sorry

-- @[simps! symm_apply]
variable { A : Type } [Ring A] [Algebra R A]
variable { M : Type } [AddCommGroup M] [Module R M]
def lift : { f : (ι →₀ R) →ₗ[R] A // ∀ m, f m * f m = 0 } ≃ (Model R ι →ₐ[R] A) := sorry
