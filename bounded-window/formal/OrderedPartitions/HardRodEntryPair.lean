import OrderedPartitions.HardRodStableDegree
import OrderedPartitions.HardRodIntegerEscape

noncomputable section
namespace OrderedPartitions.RootTracking
open Filter Polynomial InterlacingStep Kernel HardRod
open scoped Topology

/-- At an integral limiting ratio entered from above, adjoin the escaping root
to the finite lower root array. Its sign supplies precisely the missing bracket. -/
theorem normalized_entry_pair {J N : ℕ→ℕ} {D : ℕ} (hd : 2≤D)
    (hj : Tendsto J atTop atTop)
    (hn : Tendsto (fun n ↦ (N n:ℝ)/(J n:ℝ)) atTop (𝓝 (D:ℝ)))
    (above : ∀ᶠ n in atTop,D*J n≤N n) :
    ∀ᶠ n in atTop, OrderedPair D (windowPoly D (J n) (N n))
      (windowPoly D (J n) (N n+1)) := by
  obtain ⟨d,rfl⟩ : ∃d,D=d+2 := ⟨D-2,by omega⟩
  obtain ⟨b,z,hb,conv,evt⟩ := finite_branches (d:=d) (M:=d+1) (Nat.le_succ d)
    (x:=((d+2:ℕ):ℝ)) (by push_cast;linarith) (by push_cast;linarith) hj hn
  let T := b 0 - 1
  have first : T<b 0 := by dsimp [T];linarith
  have below := (conv 0).eventually_const_lt first
  filter_upwards [evt,below,windowPoly_integer_escape hd hj hn above T,above,
    upper_rank_lt_next_layer hj hn,hj.eventually_ge_atTop 2] with n info mid far low upper big
  obtain ⟨r,small,hroot,strong⟩ := far
  obtain ⟨mon,tests⟩ := info
  let u : Fin (d+2)→ℝ := Fin.cons r (z n)
  have firstGap (i : Fin (d+1)) : r<z n i := small.trans (mid.trans_le (mon.monotone (Fin.zero_le i)))
  have order : StrictMono u := Fin.strictMono_cons.mpr ⟨firstGap,mon⟩
  have negative (i : Fin (d+2)) : u i<0 :=
    Fin.cases ((firstGap 0).trans (tests 0).1) (fun k ↦ (tests k).1) i
  have roots (i : Fin (d+2)) : (windowPoly (d+2) (J n) (N n)).eval (u i)=0 :=
    Fin.cases hroot (fun k ↦ (tests k).2.1) i
  have sg (i : Fin (d+2)) : 0<(-1:ℝ)^(d+2-i.val)*
      (windowPoly (d+2) (J n) (N n+1)).eval (u i) := by
    refine Fin.cases (by simpa [u] using strong) (fun k ↦ ?_) i
    simpa [u,Nat.succ_sub_succ_eq_sub] using (tests k).2.2
  have P := window_shape (M:=d+2) big (by omega : 1≤d+2) (le_refl _) low (by omega)
  have Q := window_shape (M:=d+2) big (by omega : 1≤d+2) (le_refl _) (low.trans (Nat.le_succ _)) upper
  refine ⟨u,⟨order,negative,?_,P.1,roots⟩,Or.inl (equal_of_alternating_sign order negative
    (by linarith [Q.2.2]) Q.1 sg)⟩
  intro h
  have hz := P.2.2
  simp [h] at hz

#print axioms normalized_entry_pair
end OrderedPartitions.RootTracking
