/-
  Part III, §15: the stability predicate `St_k(ξ)` (Definition 15.2) and the relation predicate
  `Rel_k(ξ, η)` (Definition 15.4), built over the *padding* finite-stage Tarski–Vaught condition
  `TVqP` of `StRelP.lean` instead of the `TVq` of `TV.lean`.

  `StKP` and `RelKP` are the two predicates of `TV.lean` with `TVq` replaced by `TVqP`, so their
  Lévy complexity (`piDef_StKP`, `sigmaDef_RelKP`) is proved exactly as there, from `piDef_TVqP`.

  The point of the file is the *correctness* half.  In `StRel.lean` one direction of Lemma 15.3
  goes through the Lévy complexity of the truth predicate — a transfer lemma, not the paper's
  argument.  Here `stKP_iff` and `relKP_iff` inherit the bridge `tvqP_iff_elemHat`, whose two
  directions both go through the correctness of the truth predicate (Theorem 13.6) evaluated in
  `L θ` and in `L ξ`.  No complexity detour occurs anywhere below.
-/
import Bm4.SetTheory.StRelP
import Bm4.SetTheory.LCodeEx

universe u

namespace BM4.ST

open Fm

/-- Definition 15.2, over the padding `TV_q`. -/
def StKP (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (k : ℕ) (ξ : ZFSet.{u}) : Prop :=
  ∀ M, D M → ∀ c, D c → LCode h w ξ M c → TVqP D h w (k + 2) M

/-- Definition 15.4, over the padding `TV_q`:

    Rel_k(ξ, η) :⟺ Ord(ξ) ∧ Ord(η) ∧ ξ < η ∧ ∃M ∃c (LCode(η, M, c) ∧ St_k(ξ)^M).

`StKP (· ∈ M) …` is the *semantic* reading of the paper's relativization `St_k(ξ)^M`.  As in
Definition 14.2 the semantic and the syntactic reading agree exactly when `M` is a transitive
nonempty set containing the parameters `h`, `w`, `ξ`, so the relativized stability is asserted
under those hypotheses.  They hold for the only `M` a hierarchy code can name, namely `L η`. -/
def RelKP (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (k : ℕ) (ξ η : ZFSet.{u}) : Prop :=
  ξ.IsOrdinal ∧ η.IsOrdinal ∧ ξ ∈ η ∧
    ∃ M, D M ∧ ∃ c, D c ∧ LCode h w η M c ∧
      (M.IsTransitive → (∃ z, z ∈ M) → h ∈ M → w ∈ M → ξ ∈ M → StKP (· ∈ M) h w k ξ)

/-! ### Complexity -/

theorem piDef_StKP (k : ℕ) (h w x : ℕ) (hhw : h ≠ w) (hhx : h ≠ x) (hwx : w ≠ x) :
    PiDef (k + 2) {h, w, x} (fun D v => StKP.{u} D (v h) (v w) k (v x)) := by
  set m := h + w + x + 1 with hm
  have hLC : Delta0Def.{u} {h, w, x, m, m + 1}
      (fun _ v => LCode (v h) (v w) (v x) (v m) (v (m + 1))) :=
    delta0_lcode h w x m (m + 1) hhw hhx (by omega) (by omega) hwx (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hTV : PiDef (k + 2) {h, w, m} (fun D v => TVqP.{u} D (v h) (v w) (k + 2) (v m)) := by
    have hc := piDef_TVqP.{u} (k + 2) h w m hhw (by omega) (by omega)
    rwa [show max (k + 2) 1 = k + 2 by omega] at hc
  have hI := (hLC.sigma (k + 2)).imp_pi hTV
  have hall := (hI.all (m + 1) (by omega)).all m (by omega)
  refine (hall.congr ?_).of_eq ?_
  · intro D v _ _
    simp only [StKP]
    apply forall_congr'; intro xM; apply imp_congr_right; intro _
    apply forall_congr'; intro xc; apply imp_congr_right; intro _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · ext j
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
    omega

theorem sigmaDef_RelKP (k : ℕ) (h w x y : ℕ) (hhw : h ≠ w) (hhx : h ≠ x) (hhy : h ≠ y)
    (hwx : w ≠ x) (hwy : w ≠ y) (hxy : x ≠ y) :
    SigmaDef 1 {h, w, x, y} (fun D v => RelKP.{u} D (v h) (v w) k (v x) (v y)) := by
  set m := h + w + x + y + 1 with hm
  obtain ⟨Q, hQ0, hQiff⟩ := (piDef_StKP.{u} k h w x hhw hhx hwx).relativize m (by
    simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
  have hG : Delta0Def.{u} {h, w, x, m} (fun _ v =>
      (v m).IsTransitive ∧ (∃ z, z ∈ v m) ∧ v h ∈ v m ∧ v w ∈ v m ∧ v x ∈ v m) := by
    refine ((delta0_isTransitive.{u} m).and ((delta0_nonemptyMem.{u} m).and
      ((Delta0Def.mem.{u} h m).and ((Delta0Def.mem.{u} w m).and
        (Delta0Def.mem.{u} x m))))).of_eq ?_
    ext j
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    tauto
  have hLC : Delta0Def.{u} {h, w, y, m, m + 1}
      (fun _ v => LCode (v h) (v w) (v y) (v m) (v (m + 1))) :=
    delta0_lcode h w y m (m + 1) hhw hhy (by omega) (by omega) hwy (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hInner : Delta0Def.{u} {h, w, x, y, m, m + 1} (fun D v =>
      LCode (v h) (v w) (v y) (v m) (v (m + 1)) ∧
      ((v m).IsTransitive → (∃ z, z ∈ v m) → v h ∈ v m → v w ∈ v m → v x ∈ v m →
        StKP.{u} (· ∈ v m) (v h) (v w) k (v x))) := by
    refine ((hLC.and (hG.imp hQ0)).congr ?_).of_eq ?_
    · intro D v _ _
      have key : ∀ (_ : (v m).IsTransitive ∧ (∃ z, z ∈ v m) ∧ v h ∈ v m ∧ v w ∈ v m ∧ v x ∈ v m),
          (Q D v ↔ StKP.{u} (· ∈ v m) (v h) (v w) k (v x)) := by
        rintro ⟨htr, hne, hhm, hwm, hxm⟩
        refine hQiff D v (goodDom_mem htr hne) ?_
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl
        · exact hhm
        · exact hwm
        · exact hxm
      refine and_congr Iff.rfl ?_
      constructor
      · intro H htr hne hhm hwm hxm
        exact (key ⟨htr, hne, hhm, hwm, hxm⟩).mp (H ⟨htr, hne, hhm, hwm, hxm⟩)
      · rintro H ⟨htr, hne, hhm, hwm, hxm⟩
        exact (key ⟨htr, hne, hhm, hwm, hxm⟩).mpr (H htr hne hhm hwm hxm)
    · ext j
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      omega
  have hex := ((hInner.sigma 1).ex (m + 1) le_rfl).ex m le_rfl
  have hOrd : Delta0Def.{u} {x, y}
      (fun _ v => (v x).IsOrdinal ∧ (v y).IsOrdinal ∧ v x ∈ v y) := by
    refine (((delta0_isOrdinal.{u} x).and ((delta0_isOrdinal.{u} y).and
      (Delta0Def.mem.{u} x y))).of_eq ?_)
    ext j
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    tauto
  refine (((hOrd.sigma 1).and hex).congr ?_).of_eq ?_
  · intro D v _ _
    simp only [RelKP]
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨⟨ho1, ho2, ho3⟩, xM, hxM, xc, hxc, hlc, hs⟩
      exact ⟨ho1, ho2, ho3, xM, hxM, xc, hxc, hlc, hs⟩
    · rintro ⟨ho1, ho2, ho3, xM, hxM, xc, hxc, hlc, hs⟩
      exact ⟨⟨ho1, ho2, ho3⟩, xM, hxM, xc, hxc, hlc, hs⟩
  · ext j
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
    omega

/-! ### Lemma 10.5(2) in the outside universe

`lcode_exists_in_L` runs the construction of a hierarchy code *inside* `L θ`, where the KP of
`L θ` has to do the work.  Lemma 15.5(1) needs the same code in `V`, where ZFC is available: the
three functions `H`, `S`, `D` are `graphBelow` sets outright, and the single auxiliary set `U` of
condition 1 is a rank initial segment `V_γ` large enough to hold all of them.  No admissible
ordinal above `η` is needed, and none is available in general. -/

/-- **Lemma 10.5(2)**, outside version: every ordinal has a hierarchy code in the universe. -/
theorem lcode_exists_ext (η : Ordinal.{u}) :
    ∃ M c, LCode (L Ordinal.omega0.{u}) ωZ.{u} η.toZFSet M c := by
  classical
  -- one auxiliary set: a rank initial segment containing all the data
  set Z : ZFSet.{u} := ofList [graphBelow L (η + 1), graphBelow LTr η,
    graphBelow (fun a => defEnum (L a) (LTr a)) η, L η, η.toZFSet, ωZ.{u}] with hZ
  set γ : Ordinal.{u} := ZFSet.rank Z + Ordinal.omega0 with hγ
  have hγlim : Order.IsSuccLimit γ := Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0
  set U := ZFSet.vonNeumann γ with hU
  have hmemU : ∀ x : ZFSet.{u}, x ∈ U ↔ ZFSet.rank x < γ := fun x => ZFSet.mem_vonNeumann
  have hUtrans : U.IsTransitive := ZFSet.isTransitive_vonNeumann γ
  have hZU : ∀ x ∈ Z, x ∈ U := by
    intro x hx
    rw [hmemU]
    exact (ZFSet.rank_lt_of_mem hx).trans (lt_add_of_pos_right _ Ordinal.omega0_pos)
  have hpucl : PUCl U := by
    intro x hx y hy
    rw [hmemU] at hx hy
    refine ⟨?_, ?_⟩
    · rw [hmemU, ZFSet.rank_pair]
      exact max_lt (hγlim.succ_lt hx) (hγlim.succ_lt hy)
    · rw [hmemU]
      exact lt_of_le_of_lt (ZFSet.rank_sUnion_le x) hx
  have hHU : graphBelow L (η + 1) ∈ U := hZU _ (mem_ofList.mpr (by simp))
  have hSU : graphBelow LTr η ∈ U := hZU _ (mem_ofList.mpr (by simp))
  have hDU : graphBelow (fun a => defEnum (L a) (LTr a)) η ∈ U :=
    hZU _ (mem_ofList.mpr (by simp))
  have hMU : L η ∈ U := hZU _ (mem_ofList.mpr (by simp))
  have hηU : η.toZFSet ∈ U := hZU _ (mem_ofList.mpr (by simp))
  have hωU : ωZ.{u} ∈ U := hZU _ (mem_ofList.mpr (by simp))
  have hstage : ∀ a : Ordinal.{u}, a < η + 1 → L a ∈ U := by
    intro a ha
    have hp : ZFSet.pair a.toZFSet (L a) ∈ graphBelow L (η + 1) :=
      pair_mem_graphBelow_iff.mpr ⟨ha, rfl⟩
    exact (kpair_mem_of_trans hUtrans (hUtrans.subset_of_mem hHU hp)).2
  have htr : ∀ a : Ordinal.{u}, a < η → LTr a ∈ U := by
    intro a ha
    have hp : ZFSet.pair a.toZFSet (LTr a) ∈ graphBelow LTr η :=
      pair_mem_graphBelow_iff.mpr ⟨ha, rfl⟩
    exact (kpair_mem_of_trans hUtrans (hUtrans.subset_of_mem hSU hp)).2
  have hsat : ∀ a : Ordinal.{u}, a < η →
      SatCode (L Ordinal.omega0) ωZ (L a) U (LTr a) := fun a ha =>
    satCode_truthSet hUtrans (hstage a (ha.trans (ordinal_lt_add_one η))) (htr a ha) hωU hpucl
  refine ⟨L η, fourTuple U (graphBelow L (η + 1)) (graphBelow LTr η)
      (graphBelow (fun a => defEnum (L a) (LTr a)) η),
    U, graphBelow L (η + 1), graphBelow LTr η,
    graphBelow (fun a => defEnum (L a) (LTr a)) η, fourCode_fourTuple _ _ _ _,
    ⟨ZFSet.isOrdinal_toZFSet η, hUtrans, hηU, hMU, hHU, hSU, hDU, hωU, hpucl⟩,
    ⟨graphBelow_isFunc _ _, ?_, graphBelow_isFunc _ _, graphBelow_isDom _ _,
      graphBelow_isFunc _ _, graphBelow_isDom _ _, ?_⟩, ?_, ?_, ?_,
    ⟨?_, limClause_graphBelow_L η le_rfl⟩, ?_⟩
  · rw [← Ordinal.toZFSet_add_one]; exact graphBelow_isDom _ _
  · have h0 : ZFSet.pair (0 : Ordinal.{u}).toZFSet (L (0 : Ordinal.{u})) ∈
        graphBelow L (η + 1) :=
      pair_mem_graphBelow_iff.mpr ⟨lt_of_le_of_lt (ordinal_zero_le η) (ordinal_lt_add_one η), rfl⟩
    rwa [Ordinal.toZFSet_zero, L_zero, ← natZ_zero] at h0
  · intro s hs Hx hHx Sx hSx
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hHx
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hSx
    exact hsat a ha
  · intro s hs Hx hHx Sx hSx Dx hDx
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hHx
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hSx
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hDx
    exact isDefEnum_defEnum (hsat a ha)
  · intro s hs Dx hDx Hx' hHx'
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hDx
    rw [← Ordinal.toZFSet_add_one] at hHx'
    obtain ⟨-, rfl⟩ := pair_mem_graphBelow_iff.mp hHx'
    intro y
    rw [L_succ, ← mem_ran_defEnum_iff (hsat a ha) (isDefEnum_defEnum (hsat a ha))]
  · intro s hs
    obtain ⟨a, ha, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    exact limClause_graphBelow_L a ha.le
  · exact pair_mem_graphBelow_iff.mpr ⟨ordinal_lt_add_one η, rfl⟩

/-! ### Lemma 15.3 and Lemma 15.5, the paper's way -/

/-- **Lemma 15.3**: for good `ξ < θ`, the internal predicate `St_k(ξ)` evaluated in `L θ`
expresses `L ξ ≺*_{k+2} L θ`.  Correctness comes from `tvqP_iff_elemHat`, i.e. from Theorem 13.6
applied twice — no Lévy-complexity transfer. -/
theorem stKP_iff {ξ θ : Ordinal.{u}} (hθ : GoodOrd θ) (hξ : GoodOrd ξ) (hlt : ξ < θ) (k : ℕ) :
    StKP (· ∈ L θ) (L Ordinal.omega0) ωZ k ξ.toZFSet ↔ ElemHat (k + 2) (L ξ) (L θ) := by
  constructor
  · intro hst
    obtain ⟨c, hc, hcode⟩ := hθ.lcode_L hlt
    exact (tvqP_iff_elemHat hθ hξ hlt k).mp (hst (L ξ) (hθ.L_mem hlt) c hc hcode)
  · intro hel M hM c hc hcode
    have hM' : M = L ξ := lcode_sound hcode
    subst hM'
    exact (tvqP_iff_elemHat hθ hξ hlt k).mpr hel

/-- **Lemma 15.5**: for good `ξ < η < θ`, the internal predicate `Rel_k(ξ, η)` evaluated in `L θ`
expresses `L ξ ≺*_{k+2} L η`. -/
theorem relKP_iff {ξ η θ : Ordinal.{u}} (hθ : GoodOrd θ) (hη : GoodOrd η) (hξ : GoodOrd ξ)
    (hξη : ξ < η) (hηθ : η < θ) (k : ℕ) :
    RelKP (· ∈ L θ) (L Ordinal.omega0) ωZ k ξ.toZFSet η.toZFSet ↔ ElemHat (k + 2) (L ξ) (L η) := by
  constructor
  · rintro ⟨-, -, -, M, -, c, -, hcode, hst⟩
    have hM' : M = L η := lcode_sound hcode
    subst hM'
    exact (stKP_iff hη hξ hξη k).mp
      (hst hη.transitive ⟨ωZ, hη.omegaZ_mem⟩ hη.Lomega_mem hη.omegaZ_mem (hη.toZFSet_mem hξη))
  · intro hel
    obtain ⟨c, hc, hcode⟩ := hθ.lcode_L hηθ
    exact ⟨ZFSet.isOrdinal_toZFSet ξ, ZFSet.isOrdinal_toZFSet η,
      Ordinal.toZFSet_mem_toZFSet_iff.mpr hξη,
      L η, hθ.L_mem hηθ, c, hc, hcode, fun _ _ _ _ _ => (stKP_iff hη hξ hξη k).mpr hel⟩

/-- **Lemma 15.5(1)**: for admissible `ξ < η`, the *external* `Rel_k(ξ, η)` — read in the outside
universe, where the domain is everything — expresses `L ξ ≺*_{k+2} L η`, i.e. `ξ ◁_k η`. -/
theorem relKP_iff_ext {ξ η : Ordinal.{u}} (hη : GoodOrd η) (hξ : GoodOrd ξ) (hξη : ξ < η)
    (k : ℕ) :
    RelKP (fun _ => True) (L Ordinal.omega0) ωZ k ξ.toZFSet η.toZFSet ↔
      ElemHat (k + 2) (L ξ) (L η) := by
  constructor
  · rintro ⟨-, -, -, M, -, c, -, hcode, hst⟩
    have hM' : M = L η := lcode_sound hcode
    subst hM'
    exact (stKP_iff hη hξ hξη k).mp
      (hst hη.transitive ⟨ωZ, hη.omegaZ_mem⟩ hη.Lomega_mem hη.omegaZ_mem (hη.toZFSet_mem hξη))
  · intro hel
    obtain ⟨M, c, hcode⟩ := lcode_exists_ext η
    have hM' : M = L η := lcode_sound hcode
    subst hM'
    exact ⟨ZFSet.isOrdinal_toZFSet ξ, ZFSet.isOrdinal_toZFSet η,
      Ordinal.toZFSet_mem_toZFSet_iff.mpr hξη,
      L η, trivial, c, trivial, hcode, fun _ _ _ _ _ => (stKP_iff hη hξ hξη k).mpr hel⟩

end BM4.ST
