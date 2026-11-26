import OrderedPartitions.CubicActualBox
import OrderedPartitions.CubicChamberBoxTransfer

noncomputable section
namespace OrderedPartitions.CubicChamber.Box

/-- At the actual ranks the rational cell supplies one common upper bound V for
the two-root separation criterion, with the corrected leading increment positive. -/
theorem actual_conditions {j m : ℕ} (hj : 64≤j) (hm : m<j) :
    let r := actualRow j m
    ∃ V : ℝ, 0≤r.a ∧ 0<r.b ∧ 0<r.c ∧ 0<r.d ∧ 0<r.e ∧ 0<r.f ∧
      r.d*r.f/r.e^2 ≤ 4/25 ∧
      (∀v : ℝ, 1≤v → v≤5/4 → 1-v+(r.d*r.f/r.e^2)*v^2=0 → v≤V) ∧
      V*r.d*max 0 (r.b*r.d-r.f)<(r.a*r.d-r.e)*r.e ∧
      V*r.a*r.f/(r.b*r.e)+r.c*r.e/(r.b*r.f)<1 := by
  obtain ⟨cell,valid,_,enc⟩ := actual_box_exists hj hm
  obtain ⟨a,b,_,d,e,f,cap,v,near,far⟩ := conditions_from_box valid enc
  have cp := (Kernel.normalizedMoment_pos_iff (by omega : 2≤j) 2).2
    (by omega : (2+1)*j≤3*j+m)
  have jp : 0<(j:ℝ) := by exact_mod_cast (show 0<j by omega)
  exact ⟨_,a,b,div_pos cp (pow_pos jp 3),d,e,f,cap,v,near,far⟩

#print axioms actual_conditions
end OrderedPartitions.CubicChamber.Box
