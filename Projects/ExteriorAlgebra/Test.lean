import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
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

def single : ι → model3 R ι :=
  fun i ↦ Finsupp.single {
    val := [i]
    property := by
      simp
  } 1
