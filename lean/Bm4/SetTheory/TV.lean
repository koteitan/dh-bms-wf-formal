/-
  Part III, §14–15: the finite-stage Tarski–Vaught condition `TV_q(M)` (Definition 14.2), the
  stability predicate `St_k(ξ)` (Definition 15.2) and the relation predicate `Rel_k(ξ, η)`
  (Definition 15.4), together with their Lévy complexity.
-/
import Bm4.SetTheory.Truth
import Bm4.SetTheory.LCode
import Bm4.SetTheory.Rel

universe u

namespace BM4.ST

open Fm

/-! ### Auxiliary Δ₀ predicate -/

/-- `M` is nonempty. -/
theorem delta0_nonemptyMem (M : ℕ) : Delta0Def.{u} {M} (fun _ v => ∃ x, x ∈ v M) := by
  have h1 := Delta0Def.top.{u}.bex (M + 1) M (by omega)
  refine (h1.congr ?_).of_eq ?_
  · intro D v _ _
    exact ⟨fun ⟨x, hx, _⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨x, hx, trivial⟩⟩
  · ext k
    simp

/-! ### Definition 14.2: the finite-stage Tarski–Vaught condition -/

/-- Definition 14.2, as a recursive finite conjunction. `M` must be a good domain and contain the
parameters, so those requirements are part of the predicate. -/
def TVBody (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (j : ℕ) (M : ZFSet.{u}) : Prop :=
  ∀ e ∈ M, ∀ a ∈ M, IsSigCodeW h w j e → IsSeqA w M a →
    TrSigS D h w j e a → TrSigS (· ∈ M) h w j e a

/-- The conjunction of `TVBody` over the stages `1, …, q`. -/
def TVConj (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → Prop
  | 0, _ => True
  | j + 1, M => TVConj D h w j M ∧ TVBody D h w (j + 1) M

/-- `TV_q(M)` (Definition 14.2). -/
def TVq (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (q : ℕ) (M : ZFSet.{u}) : Prop :=
  M.IsTransitive ∧ (∃ x, x ∈ M) ∧ h ∈ M ∧ w ∈ M ∧ TVConj D h w q M

/-- Definition 15.2. -/
def StK (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (k : ℕ) (ξ : ZFSet.{u}) : Prop :=
  ∀ M, D M → ∀ c, D c → LCode h w ξ M c → TVq D h w (k + 2) M

/-- Definition 15.4 (the relativization of `St_k` to the coded `L η`). The relativization is only
meaningful when the model `M` is a good domain containing the parameters `h`, `w`, `ξ`, so those
requirements are part of the predicate. -/
def RelK (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (k : ℕ) (ξ η : ZFSet.{u}) : Prop :=
  ∃ M, D M ∧ (M.IsTransitive ∧ (∃ z, z ∈ M) ∧ h ∈ M ∧ w ∈ M ∧ ξ ∈ M) ∧
    ∃ c, D c ∧ LCode h w η M c ∧ StK (· ∈ M) h w k ξ

/-! ### Complexity -/

theorem piDef_TVq (q : ℕ) (h w M : ℕ) (hhw : h ≠ w) (hhM : h ≠ M) (hwM : w ≠ M) :
    PiDef (max q 1) {h, w, M} (fun D v => TVq.{u} D (v h) (v w) q (v M)) := by
  induction q with
  | zero =>
    have d1 := delta0_isTransitive.{u} M
    have d2 := delta0_nonemptyMem.{u} M
    have d3 := Delta0Def.mem.{u} h M
    have d4 := Delta0Def.mem.{u} w M
    have hd : Delta0Def.{u} {h, w, M} (fun D v => TVq.{u} D (v h) (v w) 0 (v M)) := by
      refine ((d1.and (d2.and (d3.and d4))).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [TVq, TVConj, and_true]
        try tauto
      · ext k
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
        tauto
    exact hd.pi _
  | succ q ih =>
    set m := h + w + M + 1 with hm
    have hX : PiDef (q + 1) {h, w, M} (fun D v => TVq.{u} D (v h) (v w) q (v M)) :=
      ih.pad (by omega)
    have hP0 : Delta0Def.{u} {h, w, M}
        (fun _ v => (v M).IsTransitive ∧ (∃ x, x ∈ v M) ∧ v h ∈ v M ∧ v w ∈ v M) := by
      refine ((delta0_isTransitive.{u} M).and ((delta0_nonemptyMem.{u} M).and
        ((Delta0Def.mem.{u} h M).and (Delta0Def.mem.{u} w M)))).of_eq ?_
      ext k
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      tauto
    have hTr : SigmaDef (q + 1) {h, w, m, m + 1}
        (fun D v => TrSigS.{u} D (v h) (v w) (q + 1) (v m) (v (m + 1))) := by
      have hc := (trComplexity.{u} (q + 1) h w m (m + 1) hhw (by omega) (by omega) (by omega)
        (by omega) (by omega)).1
      rwa [show max (q + 1) 1 = q + 1 by omega] at hc
    obtain ⟨Q, hQ0, hQiff⟩ := hTr.relativize M (by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega)
    have hA : Delta0Def.{u} {h, w, m} (fun _ v => IsSigCodeW (v h) (v w) (q + 1) (v m)) :=
      delta0_isSigCodeW (q + 1) h w m hhw (by omega) (by omega)
    have hB : Delta0Def.{u} {w, M, m + 1} (fun _ v => IsSeqA (v w) (v M) (v (m + 1))) :=
      delta0_isSeqA w M (m + 1) hwM (by omega) (by omega)
    have hAnt : Delta0Def.{u} {h, w, M, m, m + 1} (fun _ v =>
        v m ∈ v M ∧ v (m + 1) ∈ v M ∧
          ((v M).IsTransitive ∧ (∃ x, x ∈ v M) ∧ v h ∈ v M ∧ v w ∈ v M)) := by
      refine ((Delta0Def.mem.{u} m M).and ((Delta0Def.mem.{u} (m + 1) M).and hP0)).of_eq ?_
      ext k
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      tauto
    have hL4 := hTr.imp_pi (hQ0.pi (q + 1))
    have hL3 := (hB.sigma (q + 1)).imp_pi hL4
    have hL2 := (hA.sigma (q + 1)).imp_pi hL3
    have hL1 := (hAnt.sigma (q + 1)).imp_pi hL2
    have hL1' : PiDef (q + 1) {h, w, M, m, m + 1} (fun D v =>
        (v m ∈ v M ∧ v (m + 1) ∈ v M ∧
          ((v M).IsTransitive ∧ (∃ x, x ∈ v M) ∧ v h ∈ v M ∧ v w ∈ v M)) →
        IsSigCodeW (v h) (v w) (q + 1) (v m) →
        IsSeqA (v w) (v M) (v (m + 1)) →
        TrSigS.{u} D (v h) (v w) (q + 1) (v m) (v (m + 1)) →
        TrSigS.{u} (· ∈ v M) (v h) (v w) (q + 1) (v m) (v (m + 1))) := by
      refine (hL1.congr ?_).of_eq ?_
      · intro D v _ _
        have key : ∀ (_ : v m ∈ v M ∧ v (m + 1) ∈ v M ∧
            ((v M).IsTransitive ∧ (∃ x, x ∈ v M) ∧ v h ∈ v M ∧ v w ∈ v M)),
            (Q D v ↔ TrSigS.{u} (· ∈ v M) (v h) (v w) (q + 1) (v m) (v (m + 1))) := by
          rintro ⟨hem, ham, htr, hne, hhm', hwm'⟩
          refine hQiff D v (goodDom_mem htr hne) ?_
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl | rfl | rfl
          · exact hhm'
          · exact hwm'
          · exact hem
          · exact ham
        constructor
        · intro H hant h1 h2 h3
          exact (key hant).mp (H hant h1 h2 h3)
        · intro H hant h1 h2 h3
          exact (key hant).mpr (H hant h1 h2 h3)
      · ext k
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
        omega
    have hball := (hL1'.ball (m + 1) M (by omega) (by omega)).ball m M (by omega) (by omega)
    have hbody : PiDef (q + 1) {h, w, M} (fun D v =>
        ((v M).IsTransitive ∧ (∃ x, x ∈ v M) ∧ v h ∈ v M ∧ v w ∈ v M) →
        TVBody.{u} D (v h) (v w) (q + 1) (v M)) := by
      refine (hball.congr ?_).of_eq ?_
      · intro D v _ _
        simp (disch := omega) only [TVBody, Function.update_self, Function.update_of_ne]
        constructor
        · intro H hP e' he' a' ha'
          exact H e' he' a' ha' ⟨he', ha', hP⟩
        · intro H e' he' a' ha' hant
          exact H hant.2.2 e' he' a' ha'
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
        omega
    refine (((hX.and hbody).congr ?_).of_eq ?_).pad (by omega)
    · intro D v _ _
      simp only [TVq, TVConj]
      constructor
      · rintro ⟨⟨htr, hne, hhm', hwm', hconj⟩, hb⟩
        exact ⟨htr, hne, hhm', hwm', hconj, hb ⟨htr, hne, hhm', hwm'⟩⟩
      · rintro ⟨htr, hne, hhm', hwm', hconj, hbd⟩
        exact ⟨⟨htr, hne, hhm', hwm', hconj⟩, fun _ => hbd⟩
    · ext k
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      tauto

theorem piDef_StK (k : ℕ) (h w x : ℕ) (hhw : h ≠ w) (hhx : h ≠ x) (hwx : w ≠ x) :
    PiDef (k + 2) {h, w, x} (fun D v => StK.{u} D (v h) (v w) k (v x)) := by
  set m := h + w + x + 1 with hm
  have hLC : Delta0Def.{u} {h, w, x, m, m + 1}
      (fun _ v => LCode (v h) (v w) (v x) (v m) (v (m + 1))) :=
    delta0_lcode h w x m (m + 1) hhw hhx (by omega) (by omega) hwx (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have hTV : PiDef (k + 2) {h, w, m} (fun D v => TVq.{u} D (v h) (v w) (k + 2) (v m)) := by
    have hc := piDef_TVq.{u} (k + 2) h w m hhw (by omega) (by omega)
    rwa [show max (k + 2) 1 = k + 2 by omega] at hc
  have hI := (hLC.sigma (k + 2)).imp_pi hTV
  have hall := (hI.all (m + 1) (by omega)).all m (by omega)
  refine (hall.congr ?_).of_eq ?_
  · intro D v _ _
    simp only [StK]
    apply forall_congr'; intro xM; apply imp_congr_right; intro _
    apply forall_congr'; intro xc; apply imp_congr_right; intro _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
  · ext j
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
    omega

theorem sigmaDef_RelK (k : ℕ) (h w x y : ℕ) (hhw : h ≠ w) (hhx : h ≠ x) (hhy : h ≠ y)
    (hwx : w ≠ x) (hwy : w ≠ y) (hxy : x ≠ y) :
    SigmaDef 1 {h, w, x, y} (fun D v => RelK.{u} D (v h) (v w) k (v x) (v y)) := by
  set m := h + w + x + y + 1 with hm
  obtain ⟨Q, hQ0, hQiff⟩ := (piDef_StK.{u} k h w x hhw hhx hwx).relativize m (by
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
      ((v m).IsTransitive ∧ (∃ z, z ∈ v m) ∧ v h ∈ v m ∧ v w ∈ v m ∧ v x ∈ v m) ∧
      LCode (v h) (v w) (v y) (v m) (v (m + 1)) ∧
      StK.{u} (· ∈ v m) (v h) (v w) k (v x)) := by
    refine ((hG.and (hLC.and hQ0)).congr ?_).of_eq ?_
    · intro D v _ _
      have key : ∀ (_ : (v m).IsTransitive ∧ (∃ z, z ∈ v m) ∧ v h ∈ v m ∧ v w ∈ v m ∧ v x ∈ v m),
          (Q D v ↔ StK.{u} (· ∈ v m) (v h) (v w) k (v x)) := by
        rintro ⟨htr, hne, hhm, hwm, hxm⟩
        refine hQiff D v (goodDom_mem htr hne) ?_
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl
        · exact hhm
        · exact hwm
        · exact hxm
      constructor
      · rintro ⟨hg, hlc, hq⟩
        exact ⟨hg, hlc, (key hg).mp hq⟩
      · rintro ⟨hg, hlc, hs⟩
        exact ⟨hg, hlc, (key hg).mpr hs⟩
    · ext j
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
      omega
  have hex := ((hInner.sigma 1).ex (m + 1) le_rfl).ex m le_rfl
  refine (hex.congr ?_).of_eq ?_
  · intro D v _ _
    simp only [RelK]
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨xM, hxM, xc, hxc, hg, hlc, hs⟩
      exact ⟨xM, hxM, hg, xc, hxc, hlc, hs⟩
    · rintro ⟨xM, hxM, hg, xc, hxc, hlc, hs⟩
      exact ⟨xM, hxM, xc, hxc, hg, hlc, hs⟩
  · ext j
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
    omega

end BM4.ST
