import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

noncomputable section

#check ExteriorAlgebra
variable (R) [CommRing R] (n : ℕ)
variable  (ι : Type) [LinearOrder ι]

def model1 := Finset (Fin n) → R


def model2 := Finset ι →₀ R


def model3 := {l : List ι // l.Sorted (· < ·) }  →₀ R

instance : AddCommGroup (model3 R ι) := by
  unfold model3
  infer_instance
instance : Module R (model3 R ι) := by
  unfold model3
  infer_instance

instance : One (model3 R ι) where
  one := Finsupp.single ⟨[], by simp⟩ 1

  /-
  # todos
  define multiplication, prove associativity

  instance : Ring (model3 R ι)
  instance : Algebra R (model3 R ι)

  square single should give quadratic form
  -/

variable { ι }
def single ( i : ι ) : model3 R ι :=
  Finsupp.single {
    val := [i]
    property := by
      simp
  } 1


#check single ℤ (1 : Fin 3) + (3:ℤ) • single ℤ (2 : Fin 3)

instance : NatCast (model3 R ι) where
  natCast n := n • (1: model3 R ι)

#check ( 3 : model3 ℤ (Fin 3) )

instance : Ring (model3 R ι) where
  -- inheritance in lean 4 is (somewhat) broken currently
  __ := inferInstanceAs (AddCommGroup (model3 R ι))

  mul := sorry
  left_distrib := sorry
  right_distrib := sorry

  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := sorry
  one_mul := sorry
  mul_one := sorry
  natCast_zero := sorry
  natCast_succ := sorry
  npow := sorry
  npow_zero := sorry
  npow_succ := sorry
