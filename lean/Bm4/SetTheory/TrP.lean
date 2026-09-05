/-
  Part III, §13 over the *padding* block update of §12.

  `Truth.lean` and `TrCorrect.lean` build the alternating-block truth predicates on
  `IsBlkUpd`, whose block variables must already lie in the domain of the assignment; that
  requirement reappears in `GoodAsn` as the clause
  `∀ i ∈ b.blockVars, ∃ y, ⟨natZ i, y⟩ ∈ a`.

  Here the same development is carried out over `IsBlkUpdP` of `BlkP.lean`, which pads the
  domain up to `max (dom a) {ν i + 1}`.  The padding is exactly what makes that clause
  superfluous, so `GoodAsnP` has one clause fewer than `GoodAsn`.
-/
import Bm4.SetTheory.TrCorrect
import Bm4.SetTheory.BFCodeD
import Bm4.SetTheory.BlkP

universe u

namespace BM4.ST

open Fm

/-! ### The alternating-block truth predicates (Definition 13.4, padding form) -/

mutual
/-- Truth predicate for codes of `Sig q` block formulas, over the padding block update. -/
def TrSigP (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, e, a => TrMSig D h w e a
  | 1, e, a => IsSigCodeWD h w 1 e ∧ ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpdP w a ν t b ∧ TrMSig D h w d b
  | q + 2, e, a => IsSigCodeWD h w (q + 2) e ∧ ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpdP w a ν t b ∧ TrPiP D h w (q + 1) d b
/-- Truth predicate for codes of `Pi q` block formulas, over the padding block update. -/
def TrPiP (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → ZFSet.{u} → Prop
  | 0, e, a => TrMPi D h w e a
  | 1, e, a => IsPiCodeWD h w 1 e ∧ ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpdP w a ν t b → TrMPi D h w d b
  | q + 2, e, a => IsPiCodeWD h w (q + 2) e ∧ ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpdP w a ν t b → TrSigP D h w (q + 1) d b
end

theorem trSigP_zero (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrSigP D h w 0 e a = TrMSig D h w e a := rfl

theorem trPiP_zero (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrPiP D h w 0 e a = TrMPi D h w e a := rfl

theorem trSigP_one (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrSigP D h w 1 e a = (IsSigCodeWD h w 1 e ∧ ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpdP w a ν t b ∧ TrMSig D h w d b) := rfl

theorem trPiP_one (D : ZFSet.{u} → Prop) (h w e a : ZFSet.{u}) :
    TrPiP D h w 1 e a = (IsPiCodeWD h w 1 e ∧ ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpdP w a ν t b → TrMPi D h w d b) := rfl

theorem trSigP_add_two (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (q : ℕ) (e a : ZFSet.{u}) :
    TrSigP D h w (q + 2) e a = (IsSigCodeWD h w (q + 2) e ∧
      ∃ ν, D ν ∧ ∃ d, D d ∧ ∃ t, D t ∧ ∃ b, D b ∧
      e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsBlkUpdP w a ν t b ∧
        TrPiP D h w (q + 1) d b) := rfl

theorem trPiP_add_two (D : ZFSet.{u} → Prop) (h w : ZFSet.{u}) (q : ℕ) (e a : ZFSet.{u}) :
    TrPiP D h w (q + 2) e a = (IsPiCodeWD h w (q + 2) e ∧
      ∀ ν, D ν → ∀ d, D d → ∀ t, D t → ∀ b, D b →
      e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) → IsBlkUpdP w a ν t b →
        TrSigP D h w (q + 1) d b) := rfl

/-! ### Complexity (Lemma 13.5, padding form) -/

/-- **Lemma 13.5** for the padding truth predicates: the predicate for `Sig q` codes is `Σ̂q`
(`Σ̂₁` for `q ≤ 1`) and the one for `Pi q` codes is `Π̂q`. -/
theorem trComplexityP : ∀ q : ℕ, ∀ h w e a : ℕ, h ≠ w → h ≠ e → h ≠ a → w ≠ e → w ≠ a → e ≠ a →
    SigmaDef (max q 1) {h, w, e, a} (fun D v => TrSigP.{u} D (v h) (v w) q (v e) (v a)) ∧
    PiDef (max q 1) {h, w, e, a} (fun D v => TrPiP.{u} D (v h) (v w) q (v e) (v a)) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro h w e a hhw hhe hha hwe hwa hea
  match q with
  | 0 =>
    exact ⟨sigmaDef_trMSig h w e a hhw hhe hha hwe hwa hea,
      piDef_trMPi h w e a hhw hhe hha hwe hwa hea⟩
  | 1 =>
    set m := h + w + e + a + 1 with hm
    constructor
    · have g1 := (delta0_tagPair.{u} 1 e m (m + 1) (by omega) (by omega)).sigma 1
      have g2 := (delta0_isBlkUpdP.{u} w a m (m + 2) (m + 3) hwa (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).sigma 1
      have g3 := sigmaDef_trMSig.{u} h w (m + 1) (m + 3) hhw (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hmat := g1.and (g2.and g3)
      have s4 := (((hmat.ex (m + 3) le_rfl).ex (m + 2) le_rfl).ex (m + 1) le_rfl).ex m le_rfl
      have gc := (delta0_isSigCodeWD.{u} 1 h w e hhw hhe hwe).sigma 1
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trSigP_one]
        apply and_congr_right; intro _
        apply exists_congr; intro ν; apply and_congr_right; intro _
        apply exists_congr; intro d; apply and_congr_right; intro _
        apply exists_congr; intro t; apply and_congr_right; intro _
        apply exists_congr; intro b; apply and_congr_right; intro _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
        omega
    · have g1 := (delta0_tagPair.{u} 2 e m (m + 1) (by omega) (by omega)).sigma 1
      have g2 := (delta0_isBlkUpdP.{u} w a m (m + 2) (m + 3) hwa (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).sigma 1
      have g3 := piDef_trMPi.{u} h w (m + 1) (m + 3) hhw (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hmat := g1.imp_pi (g2.imp_pi g3)
      have s4 := (((hmat.all (m + 3) le_rfl).all (m + 2) le_rfl).all (m + 1) le_rfl).all m le_rfl
      have gc := (delta0_isPiCodeWD.{u} 1 h w e hhw hhe hwe).pi 1
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trPiP_one]
        apply and_congr_right; intro _
        apply forall_congr'; intro ν; apply imp_congr_right; intro _
        apply forall_congr'; intro d; apply imp_congr_right; intro _
        apply forall_congr'; intro t; apply imp_congr_right; intro _
        apply forall_congr'; intro b; apply imp_congr_right; intro _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
        omega
  | n + 2 =>
    set m := h + w + e + a + 1 with hm
    obtain ⟨ihS, ihP⟩ := ih (n + 1) (by omega) h w (m + 1) (m + 3) hhw (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [show max (n + 1) 1 = n + 1 by omega] at ihS ihP
    rw [show max (n + 2) 1 = n + 2 by omega]
    constructor
    · have g1 := (delta0_tagPair.{u} 1 e m (m + 1) (by omega) (by omega)).pi (n + 1)
      have g2 := (delta0_isBlkUpdP.{u} w a m (m + 2) (m + 3) hwa (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).pi (n + 1)
      have hmat := g1.and (g2.and ihP)
      have s4 := (((hmat.ex (m + 3)).ex (m + 2) (by omega)).ex (m + 1) (by omega)).ex m (by omega)
      have gc := (delta0_isSigCodeWD.{u} (n + 2) h w e hhw hhe hwe).sigma (n + 2)
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trSigP_add_two]
        apply and_congr_right; intro _
        apply exists_congr; intro ν; apply and_congr_right; intro _
        apply exists_congr; intro d; apply and_congr_right; intro _
        apply exists_congr; intro t; apply and_congr_right; intro _
        apply exists_congr; intro b; apply and_congr_right; intro _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
        omega
    · have g1 := (delta0_tagPair.{u} 2 e m (m + 1) (by omega) (by omega)).pi (n + 1)
      have g2 := (delta0_isBlkUpdP.{u} w a m (m + 2) (m + 3) hwa (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).pi (n + 1)
      have hmat := g1.imp_sigma (g2.imp_sigma ihS)
      have s4 := (((hmat.all (m + 3)).all (m + 2) (by omega)).all (m + 1) (by omega)).all m
        (by omega)
      have gc := (delta0_isPiCodeWD.{u} (n + 2) h w e hhw hhe hwe).pi (n + 2)
      refine ((gc.and s4).congr ?_).of_eq ?_
      · intro D v _ _
        simp only [trPiP_add_two]
        apply and_congr_right; intro _
        apply forall_congr'; intro ν; apply imp_congr_right; intro _
        apply forall_congr'; intro d; apply imp_congr_right; intro _
        apply forall_congr'; intro t; apply imp_congr_right; intro _
        apply forall_congr'; intro b; apply imp_congr_right; intro _
        simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton, Finset.mem_union]
        omega

/-! ### Padding block updates inside `W` -/

/-- The value part of a padding block update along `l` has domain `l.length`. -/
theorem isDom_of_blkUpdP {w a t b : ZFSet.{u}} {l : List ℕ}
    (hbu : IsBlkUpdP w a (seqOfNats.{u} l) t b) : IsDom t (natZ.{u} l.length) := by
  intro c
  constructor
  · intro hc
    obtain ⟨j, hj, rfl⟩ := mem_natZ_iff.mp hc
    have hν : ZFSet.pair (natZ.{u} j) (natZ.{u} (l[j]'hj)) ∈ seqOfNats.{u} l :=
      mem_seqOfNats.mpr (List.getElem?_eq_getElem hj)
    exact hbu.2.2.1 _ _ hν
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := hbu.2.2.2.1 _ _ hy
    obtain ⟨n, i, hni, he⟩ := mem_seqOfNats_iff.mp hx
    obtain ⟨rfl, -⟩ := ZFSet.pair_injective he
    exact natZ_mem_natZ_iff.mpr (List.getElem?_eq_some_iff.mp hni).1

/-- Any padding block update inside `W` comes from a list of values of `W`.  Unlike
`blkUpd_list` this needs no hypothesis on the domain of `a`. -/
theorem blkUpdP_list {W : ZFSet.{u}} (hWt : W.IsTransitive) (hW : WClosed W)
    {a : ZFSet.{u}} (ha : IsSeqA ωZ W a) {l : List ℕ} (hnd : l.Nodup)
    {t b : ZFSet.{u}} (htW : t ∈ W) (hbu : IsBlkUpdP ωZ a (seqOfNats.{u} l) t b) :
    ∃ xs : List ZFSet.{u}, xs.length = l.length ∧ (∀ x ∈ xs, x ∈ W) ∧
      IsSeqA ωZ W b ∧ SeqVal b = updList (SeqVal a) l xs := by
  have hft : IsFunc t := hbu.2.1
  have hvalt : ∀ i x, ZFSet.pair i x ∈ t → x ∈ W := fun i x hix =>
    snd_mem_of_kpair_mem hWt (hWt.subset_of_mem htW hix)
  have hdt : IsDom t (natZ.{u} l.length) := isDom_of_blkUpdP hbu
  obtain ⟨xs, hlen, hxsW, hteq⟩ : ∃ xs : List ZFSet.{u}, xs.length = l.length ∧
      (∀ x ∈ xs, x ∈ W) ∧ t = seqOfVals xs := by
    refine ⟨(List.range l.length).map (SeqVal.{u} t), by simp, ?_, seq_eq_seqOfVals hft hdt⟩
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact seqVal_mem_of_vals hW.empty_mem hft hvalt k
  rw [hteq] at hbu
  obtain ⟨b₀, hbu₀, hseq₀, hval₀⟩ := exists_blkUpdP hW.empty_mem ha l hnd xs hlen hxsW
  have hbb : b₀ = b := isBlkUpdP_unique hbu₀ hbu
  subst hbb
  exact ⟨xs, hlen, hxsW, hseq₀, hval₀⟩

/-- The padding block update of a sequence of `W` by values of `W` exists inside `W`.  Unlike
`exists_blkUpd_W` this needs no hypothesis on the domain of `a`. -/
theorem exists_blkUpdP_W {W : ZFSet.{u}} (hW : WClosed W) {a : ZFSet.{u}} (ha : IsSeqA ωZ W a)
    {l : List ℕ} (hnd : l.Nodup)
    {xs : List ZFSet.{u}} (hlen : xs.length = l.length) (hxs : ∀ x ∈ xs, x ∈ W) :
    ∃ b, IsBlkUpdP ωZ a (seqOfNats.{u} l) (seqOfVals xs) b ∧ IsSeqA ωZ W b ∧ b ∈ W ∧
      SeqVal b = updList (SeqVal a) l xs := by
  obtain ⟨b, hbu, hseq, hval⟩ := exists_blkUpdP hW.empty_mem ha l hnd xs hlen hxs
  exact ⟨b, hbu, hseq, isSeqA_mem_of_wClosed hW hseq, hval⟩

/-! ### Good assignments for the padding block update -/

/-- The assignment `a` is a finite sequence over `W`.  Compared with `GoodAsn` the clause
`∀ i ∈ b.blockVars, ∃ y, ⟨natZ i, y⟩ ∈ a` is **absent**: the padding of `IsBlkUpdP` supplies
the missing entries.  What remains records that the block variable lists have no repetitions
(otherwise the block update is not well defined), that the code of `b` lies in `W`, and that
`W` is closed under `∅` and `insert`. -/
def GoodAsnP (W : ZFSet.{u}) (b : BF) (a : ZFSet.{u}) : Prop :=
  IsSeqA ωZ W a ∧ a ∈ W ∧ b.blockVars.Nodup ∧ BF.code.{u} b ∈ W ∧ WClosed W

/-- At the Δ₀ level the block variable list is empty, so `GoodAsnP` already gives `GoodAsn`. -/
theorem goodAsn_of_goodAsnP_delta {W : ZFSet.{u}} {sg : Bool} {φ : Fm} {a : ZFSet.{u}}
    (hg : GoodAsnP W (BF.delta sg φ) a) : GoodAsn W (BF.delta sg φ) a := by
  obtain ⟨ha, haW, hnd, hcode, hW⟩ := hg
  refine ⟨ha, haW, ?_, hnd, hcode, hW⟩
  intro i hi
  simp only [BF.blockVars, List.not_mem_nil] at hi

/-! ### The quantifier-block step -/

theorem trSigP_step {W : ZFSet.{u}} (hWt : W.IsTransitive) {l : List ℕ} {ψ : BF}
    {a : ZFSet.{u}} (hg : GoodAsnP W (BF.exs l ψ) a)
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hP : ∀ b, GoodAsnP W ψ b → (P (BF.code.{u} ψ) b ↔ Sat (· ∈ W) (SeqVal b) ψ.toFm)) :
    (∃ ν, ν ∈ W ∧ ∃ d, d ∈ W ∧ ∃ t, t ∈ W ∧ ∃ b, b ∈ W ∧
        BF.code.{u} (BF.exs l ψ) = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧
        IsBlkUpdP ωZ a ν t b ∧ P d b) ↔
      Sat (· ∈ W) (SeqVal a) (BF.exs l ψ).toFm := by
  obtain ⟨ha, haW, hnd, hcode, hW⟩ := hg
  simp only [BF.blockVars] at hnd
  have hndl : l.Nodup := (List.nodup_append.mp hnd).1
  have hndψ : ψ.blockVars.Nodup := (List.nodup_append.mp hnd).2.1
  rw [code_exs] at hcode
  have hcodeψ : BF.code.{u} ψ ∈ W :=
    snd_mem_of_kpair_mem hWt (snd_mem_of_kpair_mem hWt hcode)
  rw [toFm_exs, sat_exs_iff_exsD, exsD_iff_exists_list]
  constructor
  · rintro ⟨ν, hνW, d, hdW, t, htW, b, hbW, heq, hbu, hPd⟩
    rw [code_exs] at heq
    obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
    obtain ⟨xs, hlen, hxsW, hseqb, hvalb⟩ := blkUpdP_list hWt hW ha hndl htW hbu
    refine ⟨xs, hlen, hxsW, ?_⟩
    rw [← hvalb]
    exact (hP b ⟨hseqb, hbW, hndψ, hcodeψ, hW⟩).mp hPd
  · rintro ⟨xs, hlen, hxsW, hsat⟩
    obtain ⟨b, hbu, hseqb, hbW, hvalb⟩ := exists_blkUpdP_W hW ha hndl hlen hxsW
    refine ⟨seqOfNats.{u} l, hW.seqOfNats_mem l, BF.code.{u} ψ, hcodeψ,
      seqOfVals xs, hW.seqOfVals_mem xs hxsW, b, hbW, code_exs l ψ, hbu, ?_⟩
    refine (hP b ⟨hseqb, hbW, hndψ, hcodeψ, hW⟩).mpr ?_
    rw [hvalb]
    exact hsat

theorem trPiP_step {W : ZFSet.{u}} (hWt : W.IsTransitive) {l : List ℕ} {ψ : BF}
    {a : ZFSet.{u}} (hg : GoodAsnP W (BF.alls l ψ) a)
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hP : ∀ b, GoodAsnP W ψ b → (P (BF.code.{u} ψ) b ↔ Sat (· ∈ W) (SeqVal b) ψ.toFm)) :
    (∀ ν, ν ∈ W → ∀ d, d ∈ W → ∀ t, t ∈ W → ∀ b, b ∈ W →
        BF.code.{u} (BF.alls l ψ) = ZFSet.pair (natZ 2) (ZFSet.pair ν d) →
        IsBlkUpdP ωZ a ν t b → P d b) ↔
      Sat (· ∈ W) (SeqVal a) (BF.alls l ψ).toFm := by
  obtain ⟨ha, haW, hnd, hcode, hW⟩ := hg
  simp only [BF.blockVars] at hnd
  have hndl : l.Nodup := (List.nodup_append.mp hnd).1
  have hndψ : ψ.blockVars.Nodup := (List.nodup_append.mp hnd).2.1
  rw [code_alls] at hcode
  have hcodeψ : BF.code.{u} ψ ∈ W :=
    snd_mem_of_kpair_mem hWt (snd_mem_of_kpair_mem hWt hcode)
  rw [toFm_alls, sat_alls_iff_allD, allD_iff_forall_list]
  constructor
  · intro H xs hlen hxsW
    obtain ⟨b, hbu, hseqb, hbW, hvalb⟩ := exists_blkUpdP_W hW ha hndl hlen hxsW
    have hPd := H (seqOfNats.{u} l) (hW.seqOfNats_mem l) (BF.code.{u} ψ) hcodeψ
      (seqOfVals xs) (hW.seqOfVals_mem xs hxsW) b hbW (code_alls l ψ) hbu
    rw [← hvalb]
    exact (hP b ⟨hseqb, hbW, hndψ, hcodeψ, hW⟩).mp hPd
  · intro H ν hνW d hdW t htW b hbW heq hbu
    rw [code_alls] at heq
    obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
    obtain ⟨xs, hlen, hxsW, hseqb, hvalb⟩ := blkUpdP_list hWt hW ha hndl htW hbu
    refine (hP b ⟨hseqb, hbW, hndψ, hcodeψ, hW⟩).mpr ?_
    rw [hvalb]
    exact H xs hlen hxsW

/-! ### Theorem 13.6 for the padding truth predicates -/

/-- The two halves of **Theorem 13.6** over the padding block update, by simultaneous strong
induction on the number of alternating blocks. -/
theorem trSigPiP_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W) :
    ∀ (q : ℕ) (b : BF),
      (BF.Sig q b → ∀ a, GoodAsnP W b a →
        (TrSigP (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code.{u} b) a ↔
          Sat (· ∈ W) (SeqVal a) b.toFm)) ∧
      (BF.Pi q b → ∀ a, GoodAsnP W b a →
        (TrPiP (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code.{u} b) a ↔
          Sat (· ∈ W) (SeqVal a) b.toFm)) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro b
  match q with
  | 0 =>
    constructor
    · intro hs a hg
      cases hs with
      | zero hφ =>
        rw [trSigP_zero]
        exact trMSig_correct hWt hbase hφ (goodAsn_of_goodAsnP_delta hg)
    · intro hs a hg
      cases hs with
      | zero hφ =>
        rw [trPiP_zero]
        exact trMPi_correct hWt hbase hφ (goodAsn_of_goodAsnP_delta hg)
  | 1 =>
    constructor
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trSigP_one, and_iff_right (isSigCodeWD_code (BF.Sig.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2.1))]
        refine trSigP_step hWt hg ?_
        intro b' hg'
        cases hψ with
        | zero hφ => exact trMSig_correct hWt hbase hφ (goodAsn_of_goodAsnP_delta hg')
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trPiP_one, and_iff_right (isPiCodeWD_code (BF.Pi.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2.1))]
        refine trPiP_step hWt hg ?_
        intro b' hg'
        cases hψ with
        | zero hφ => exact trMPi_correct hWt hbase hφ (goodAsn_of_goodAsnP_delta hg')
  | n + 2 =>
    constructor
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trSigP_add_two, and_iff_right (isSigCodeWD_code (BF.Sig.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2.1))]
        refine trSigP_step hWt hg ?_
        intro b' hg'
        exact (ih (n + 1) (by omega) _).2 hψ b' hg'
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trPiP_add_two, and_iff_right (isPiCodeWD_code (BF.Pi.succ hl hψ)
          (BF.nodupBlocks_of_blockVars_nodup hg.2.2.1))]
        refine trPiP_step hWt hg ?_
        intro b' hg'
        exact (ih (n + 1) (by omega) _).1 hψ b' hg'

/-- **Theorem 13.6** (Σ side) over the padding block update. -/
theorem trSigP_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W) :
    ∀ (q : ℕ) (b : BF), BF.Sig q b → ∀ a, GoodAsnP W b a →
      (TrSigP (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        Sat (· ∈ W) (SeqVal a) b.toFm) :=
  fun q b => (trSigPiP_correct hWt hbase q b).1

/-- **Theorem 13.6** (Π side) over the padding block update. -/
theorem trPiP_correct {W : ZFSet.{u}} (hWt : W.IsTransitive) (hbase : BaseCorrect W) :
    ∀ (q : ℕ) (b : BF), BF.Pi q b → ∀ a, GoodAsnP W b a →
      (TrPiP (· ∈ W) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        Sat (· ∈ W) (SeqVal a) b.toFm) :=
  fun q b => (trSigPiP_correct hWt hbase q b).2

end BM4.ST
