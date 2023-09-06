import Projects.ExteriorAlgebra.Test
import Mathlib.LinearAlgebra.TensorAlgebra.Basis

/-!
This files contains the "main" targets of this project.
Any of these results would be great!
-/

open FiniteDimensional (finrank)
open Module (rank)

universe uι uR uM
variable {ι : Type} [LinearOrder ι] {R : Type} {M : Type}
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- Given a basis, we can consider our exterior algebra in terms of our model. The `sorry` here
should be the model we choose. -/
def ExteriorAlgebra.equivModel (b : Basis ι R M) :
    ExteriorAlgebra R M ≃ₐ[R] ( Model R ι ):=
  sorry

/-- When applied to a single basis vector, the result is a single element of the model.
The first `sorry` here should be the `single` function of the basis. -/
theorem ExteriorAlgebra.equivModel_ι_basis (b : Basis ι R M) (i : ι) :
    ExteriorAlgebra.equivModel b (ExteriorAlgebra.ι R (b i)) = Model.single R i :=
  sorry


/-- When applied to a single element of the model, the result is a single basis vector.
The first `sorry` here should be the `single` function of the basis. -/
theorem ExteriorAlgebra.equivModel_symm_single (b : Basis ι R M) (i : ι) :
    (ExteriorAlgebra.equivModel b).symm (Model.single R i) = ExteriorAlgebra.ι R (b i) :=
  sorry

/-- Given a basis on the module, produce a basis on the free algebra -/
def Basis.exteriorAlgebra (b : Basis ι R M) :
    Basis (Model.Index ι) R (ExteriorAlgebra R M) :=
  Basis.ofRepr <|
    let e := ExteriorAlgebra.equivModel b
    let e' : ExteriorAlgebra R M ≃ₗ[R] Model R ι := by exact AlgEquiv.toLinearEquiv e
    e' ≪≫ₗ (by exact Model.ofFinsupp)

#check TensorAlgebra.instModuleFree -- should help with
/-- An exterior algebra over a free module is itself a free module -/
instance [Module.Free R M] : Module.Free R (ExteriorAlgebra R M) :=
  sorry


-- this might be false when `M` is not finite
lemma ExteriorAlgebra.rank_eq [Module.Free R M] :
    rank R (ExteriorAlgebra R M) = Cardinal.lift.{uR} (2 ^ rank R M) :=
  sorry

lemma ExteriorAlgebra.finrank_eq [Module.Free R M] [Module.Finite R M] :
    finrank R (ExteriorAlgebra R M) = 2 ^ finrank R M :=
  sorry

-- even harder:

instance : NoZeroSMulDivisors R (ExteriorAlgebra R M) :=
  -- feel free to skip this one
  sorry

lemma wedge_ne_zero_iff_linearIndependent (n) (v : Fin n → M):
    ExteriorAlgebra.ιMulti R n v ≠ 0 ↔ LinearIndependent R v := by
  rw [not_iff_comm]
  constructor
  · apply AlternatingMap.map_linearDependent _ _
  · intros h₁ h₂
    sorry
