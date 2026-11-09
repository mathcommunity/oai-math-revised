import OAI.MathematicalPhysics.BFSS.Contrib.Kotler.OperatorDependencies.SU2BFSSG4EFermionHilbertUnitaryProbe

/-!
# BFSS SU(2) G4-F — real color coefficients and forward annihilator covariance

The accepted G4-E unitary Hilbert representation acts by the same
G4-B complex-linear equivalences. G4-C gave creator covariance with
column U(g) j i, but annihilator covariance in the dual (row) form.

The exact SU(2) matrix is REAL (complex-extended from G3-B), so
U(g⁻¹) i j = U(g) j i, with no conjugation. Use this, the accepted
group law and G4-C to get the forward annihilator equation needed
for each of the 48 real self-adjoint paired Majoranas.

This does not yet claim the complete pinned GaugeData theta covariance.
-/

namespace FCP.BFSSSU2GaugeG4F
noncomputable section

open scoped BigOperators
open OAI.BFSSQuantum
open FCP.BFSSFermionF1
open FCP.BFSSSU2GaugeG3C
open FCP.BFSSSU2GaugeG4A
open FCP.BFSSSU2GaugeG4B
open FCP.BFSSSU2GaugeG4C

/-- Because U(g) comes from an exact real orthogonal matrix, its
inverse entry is the literal transposed entry, NOT its conjugate. -/
theorem complexOneParticleMatrix_inv_entry
    (g : GaugeGroup 2) (i j : Fin 24) :
    complexOneParticleMatrix g⁻¹ i j =
      complexOneParticleMatrix g j i := by
  rw [← complexOneParticleMatrix_adjoint_inv,
    complexOneParticleMatrix_conjTranspose]
  rfl

/-- The color adjoint SU(2) coefficients really have zero
imaginary part, and so are fixed by complex conjugation. -/
theorem complexOneParticleMatrix_star_entry
    (g : GaugeGroup 2) (i j : Fin 24) :
    star (complexOneParticleMatrix g i j) =
      complexOneParticleMatrix g i j := by
  simp [complexOneParticleMatrix, Matrix.map_apply]

/-- Acting by g followed by g⁻¹ is the identity on the exact
2^24-dimensional Fermion 2 space. The actual G4-B action is used. -/
theorem fermionGauge_cancel_inv (g : GaugeGroup 2) (v : Fermion 2) :
    fermionGaugeLinearEquiv g (fermionGaugeLinearEquiv g⁻¹ v) = v := by
  obtain ⟨x, rfl⟩ := fockAlgebraToBFSS.surjective v
  rw [fermionGaugeLinearEquiv_intertwine (g⁻¹) x,
    fermionGaugeLinearEquiv_intertwine g
      (exteriorGauge g⁻¹ x),
    exteriorGauge_mul, mul_inv_cancel, exteriorGauge_one]

/-- Forward covariance of the exact accepted annihilator:
the REAL column U(g) j i now matches creator covariance, so
each Majorana pair will transform without creator/annihilator mixing. -/
theorem annihilator_fermionGauge_forward
    (g : GaugeGroup 2) (i : Fin 24) (v : Fermion 2) :
    fermionGaugeLinearEquiv g (annihilator i v) =
      ∑ j : Fin 24, complexOneParticleMatrix g j i •
        annihilator j (fermionGaugeLinearEquiv g v) := by
  have h := annihilator_fermionGauge_covariant
    g⁻¹ i (fermionGaugeLinearEquiv g v)
  have hleft : fermionGaugeLinearEquiv g⁻¹
      (fermionGaugeLinearEquiv g v) = v := by
    simpa only [inv_inv] using (fermionGauge_cancel_inv g⁻¹ v)
  rw [hleft] at h
  have ht := congrArg (fermionGaugeLinearEquiv g) h
  simp only [map_sum, map_smul,
    fermionGauge_cancel_inv, complexOneParticleMatrix_inv_entry] at ht
  exact ht

#print axioms complexOneParticleMatrix_inv_entry
#print axioms complexOneParticleMatrix_star_entry
#print axioms fermionGauge_cancel_inv
#print axioms annihilator_fermionGauge_forward

end
end FCP.BFSSSU2GaugeG4F
