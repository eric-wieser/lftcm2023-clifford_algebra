import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

noncomputable section

#check ExteriorAlgebra
variable (R) [CommRing R] (n : ℕ)
variable  (ι : Type) [LinearOrder ι]

def model1 := Finset (Fin n) → R


def model2 := Finset ι →₀ R


-- a list of indices, sorted
def Model := {l : List ι // l.Sorted (· < ·) }  →₀ R

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
def single ( i : ι ) : Model R ι :=
  Finsupp.single {
    val := [i]
    property := by
      simp
  } 1

set_option pp.proofs.withType false

#check single ℤ (1 : Fin 3) + (3:ℤ) • single ℤ (2 : Fin 3)

instance : Mul (Model R ι) where
  -- multiply pairwise
  mul v w := sorry

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
