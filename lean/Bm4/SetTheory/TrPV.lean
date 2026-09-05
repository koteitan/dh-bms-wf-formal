/-
  Theorem 13.6, last sentence, for the padding truth predicates of Definition 13.4:
  the same equivalence holds in the external universe `V`.

  `Bm4/StRelP.lean` proves Theorem 13.6 inside a set `W` (`trSigPiQ_correct`); this file repeats it with `W` replaced by
  the whole universe.  As in `Bm4/TrCorrect.lean` the clauses `a ∈ W`, `BF.code b ∈ W` and the
  closure of `W` become vacuous, so a good assignment is just a finite sequence whose block
  variable lists have no repetitions; the padding of `IsBlkUpdP` supplies the missing entries of
  the domain, so no condition on `dom(a)` is needed.
-/
import Bm4.SetTheory.TrP
import Bm4.SetTheory.BaseOK

namespace BM4.ST

open Fm

universe u

/-- A good assignment in the external universe: a finite sequence whose block variable lists
have no repetitions *inside a block*, which is all Definition 12.1 asks.  The clauses `a ∈ W`,
`BF.code b ∈ W` and the closure of `W` of `GoodAsnQ` are vacuous in `V`, and the padding of
`IsBlkUpdP` removes the need for any condition on `dom(a)`. -/
def GoodAsnVQ (b : BF) (a : ZFSet.{u}) : Prop :=
  IsSeqV ωZ a ∧ b.NodupBlocks

theorem trSigQ_step_V {l : List ℕ} {ψ : BF} {a : ZFSet.{u}} (hg : GoodAsnVQ (BF.exs l ψ) a)
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hP : ∀ b, GoodAsnVQ ψ b → (P (BF.code.{u} ψ) b ↔ SatV (SeqVal b) ψ.toFm)) :
    (∃ ν, True ∧ ∃ d, True ∧ ∃ t, True ∧ ∃ b, True ∧
        BF.code.{u} (BF.exs l ψ) = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧
        IsBlkUpdP ωZ a ν t b ∧ P d b) ↔
      SatV (SeqVal a) (BF.exs l ψ).toFm := by
  obtain ⟨ha, hnd⟩ := hg
  obtain ⟨hndl, hndψ⟩ := (BF.nodupBlocks_exs l ψ).mp hnd
  rw [toFm_exs, SatV, sat_exs_iff_exsD, exsD_iff_exists_list]
  constructor
  · rintro ⟨ν, -, d, -, t, -, b, -, heq, hbu, hPd⟩
    rw [code_exs] at heq
    obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
    obtain ⟨W, hWt, hW, haW, htW⟩ := exists_wClosed_mem a t
    obtain ⟨xs, hlen, -, hseqb, hvalb⟩ :=
      blkUpdP_list hWt hW (isSeqA_of_isSeqV hWt ha haW) hndl htW hbu
    refine ⟨xs, hlen, fun _ _ => trivial, ?_⟩
    rw [← hvalb]
    exact (hP b ⟨isSeqV_of_isSeqA hseqb, hndψ⟩).mp hPd
  · rintro ⟨xs, hlen, -, hsat⟩
    obtain ⟨W, hWt, hW, haW, hvW⟩ := exists_wClosed_mem a (seqOfVals xs)
    obtain ⟨b, hbu, hseqb, -, hvalb⟩ :=
      exists_blkUpdP_W hW (isSeqA_of_isSeqV hWt ha haW) hndl hlen (mem_of_seqOfVals_mem hWt hvW)
    refine ⟨seqOfNats.{u} l, trivial, BF.code.{u} ψ, trivial, seqOfVals xs, trivial, b, trivial,
      code_exs l ψ, hbu, ?_⟩
    refine (hP b ⟨isSeqV_of_isSeqA hseqb, hndψ⟩).mpr ?_
    rw [hvalb]
    exact hsat

theorem trPiQ_step_V {l : List ℕ} {ψ : BF} {a : ZFSet.{u}} (hg : GoodAsnVQ (BF.alls l ψ) a)
    {P : ZFSet.{u} → ZFSet.{u} → Prop}
    (hP : ∀ b, GoodAsnVQ ψ b → (P (BF.code.{u} ψ) b ↔ SatV (SeqVal b) ψ.toFm)) :
    (∀ ν, True → ∀ d, True → ∀ t, True → ∀ b, True →
        BF.code.{u} (BF.alls l ψ) = ZFSet.pair (natZ 2) (ZFSet.pair ν d) →
        IsBlkUpdP ωZ a ν t b → P d b) ↔
      SatV (SeqVal a) (BF.alls l ψ).toFm := by
  obtain ⟨ha, hnd⟩ := hg
  obtain ⟨hndl, hndψ⟩ := (BF.nodupBlocks_alls l ψ).mp hnd
  rw [toFm_alls, SatV, sat_alls_iff_allD, allD_iff_forall_list]
  constructor
  · intro H xs hlen _
    obtain ⟨W, hWt, hW, haW, hvW⟩ := exists_wClosed_mem a (seqOfVals xs)
    obtain ⟨b, hbu, hseqb, -, hvalb⟩ :=
      exists_blkUpdP_W hW (isSeqA_of_isSeqV hWt ha haW) hndl hlen (mem_of_seqOfVals_mem hWt hvW)
    have hPd := H (seqOfNats.{u} l) trivial (BF.code.{u} ψ) trivial (seqOfVals xs) trivial b
      trivial (code_alls l ψ) hbu
    rw [← hvalb]
    exact (hP b ⟨isSeqV_of_isSeqA hseqb, hndψ⟩).mp hPd
  · intro H ν _ d _ t _ b _ heq hbu
    rw [code_alls] at heq
    obtain ⟨-, heq2⟩ := ZFSet.pair_injective heq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective heq2
    obtain ⟨W, hWt, hW, haW, htW⟩ := exists_wClosed_mem a t
    obtain ⟨xs, hlen, -, hseqb, hvalb⟩ :=
      blkUpdP_list hWt hW (isSeqA_of_isSeqV hWt ha haW) hndl htW hbu
    refine (hP b ⟨isSeqV_of_isSeqA hseqb, hndψ⟩).mpr ?_
    rw [hvalb]
    exact H xs hlen (fun _ _ => trivial)

/-- The two halves of **Theorem 13.6** in the external universe `V`, over the padding block
update of §12. -/
theorem trSigPiQ_correct_V (hbase : BaseCorrectV.{u}) :
    ∀ (q : ℕ) (b : BF),
      (BF.Sig q b → ∀ a, GoodAsnVQ b a →
        (TrSigP (fun _ => True) (L Ordinal.omega0) ωZ q (BF.code.{u} b) a ↔
          SatV (SeqVal a) b.toFm)) ∧
      (BF.Pi q b → ∀ a, GoodAsnVQ b a →
        (TrPiP (fun _ => True) (L Ordinal.omega0) ωZ q (BF.code.{u} b) a ↔
          SatV (SeqVal a) b.toFm)) := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro b
  match q with
  | 0 =>
    constructor
    · intro hs a hg
      cases hs with
      | zero hφ => rw [trSigP_zero]; exact trMSig_correct_V hbase hφ hg.1
    · intro hs a hg
      cases hs with
      | zero hφ => rw [trPiP_zero]; exact trMPi_correct_V hbase hφ hg.1
  | 1 =>
    constructor
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trSigP_one, and_iff_right (isSigCodeWD_code (BF.Sig.succ hl hψ)
          hg.2)]
        refine trSigQ_step_V hg ?_
        intro b' hg'
        cases hψ with
        | zero hφ => exact trMSig_correct_V hbase hφ hg'.1
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trPiP_one, and_iff_right (isPiCodeWD_code (BF.Pi.succ hl hψ)
          hg.2)]
        refine trPiQ_step_V hg ?_
        intro b' hg'
        cases hψ with
        | zero hφ => exact trMPi_correct_V hbase hφ hg'.1
  | n + 2 =>
    constructor
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trSigP_add_two, and_iff_right (isSigCodeWD_code (BF.Sig.succ hl hψ)
          hg.2)]
        refine trSigQ_step_V hg ?_
        intro b' hg'
        exact (ih (n + 1) (by omega) _).2 hψ b' hg'
    · intro hs a hg
      cases hs with
      | succ hl hψ =>
        rw [trPiP_add_two, and_iff_right (isPiCodeWD_code (BF.Pi.succ hl hψ)
          hg.2)]
        refine trPiQ_step_V hg ?_
        intro b' hg'
        exact (ih (n + 1) (by omega) _).1 hψ b' hg'

/-- **Theorem 13.6** (Σ side), last sentence: the equivalence in the external universe `V`. -/
theorem trSigP_correct_ext :
    ∀ (q : ℕ) (b : BF), BF.Sig q b → ∀ a : ZFSet.{u}, GoodAsnVQ b a →
      (TrSigP (fun _ => True) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        SatV (SeqVal a) b.toFm) :=
  fun q b => (trSigPiQ_correct_V baseCorrect_V q b).1

/-- **Theorem 13.6** (Π side), last sentence: the equivalence in the external universe `V`. -/
theorem trPiP_correct_ext :
    ∀ (q : ℕ) (b : BF), BF.Pi q b → ∀ a : ZFSet.{u}, GoodAsnVQ b a →
      (TrPiP (fun _ => True) (L Ordinal.omega0) ωZ q (BF.code b) a ↔
        SatV (SeqVal a) b.toFm) :=
  fun q b => (trSigPiQ_correct_V baseCorrect_V q b).2

/-! ### Definition 13.4 with `Vars` and `Body` as terms -/

/-
  In the external universe the bound `D` is `fun _ => True`, so the bounding of Definition 13.4
  disappears entirely.  Together with `trSigP_one_vars_body` and its companions this makes
  `TrSigP` and `TrPiP` at the code of an alternating block formula literally what the paper
  writes: the projections `ν = Vars(e)` and `d = Body(e)` occur as terms and the only
  quantifiers are `∃t ∃b` on the Σ side and `∀t ∀b` on the Π side.
-/

/-- **Definition 13.4** (Σ, `q = 1`) in `V`, exactly as the paper writes it. -/
theorem trSigP_one_vars_body_V {h w a : ZFSet.{u}} (l : List ℕ) (ψ : BF) :
    TrSigP (fun _ => True) h w 1 (BF.code.{u} (BF.exs l ψ)) a ↔
      IsSigCodeWD h w 1 (BF.code.{u} (BF.exs l ψ)) ∧
        ∃ t, ∃ b, IsBlkUpdP w a (seqOfNats.{u} l) t b ∧
          TrMSig (fun _ => True) h w (BF.code.{u} ψ) b := by
  rw [trSigP_one_vars_body (D := fun _ => True) (code_exs l ψ) trivial trivial]
  simp only [true_and]

/-- **Definition 13.4** (Π, `q = 1`) in `V`, exactly as the paper writes it. -/
theorem trPiP_one_vars_body_V {h w a : ZFSet.{u}} (l : List ℕ) (ψ : BF) :
    TrPiP (fun _ => True) h w 1 (BF.code.{u} (BF.alls l ψ)) a ↔
      IsPiCodeWD h w 1 (BF.code.{u} (BF.alls l ψ)) ∧
        ∀ t, ∀ b, IsBlkUpdP w a (seqOfNats.{u} l) t b →
          TrMPi (fun _ => True) h w (BF.code.{u} ψ) b := by
  rw [trPiP_one_vars_body (D := fun _ => True) (code_alls l ψ) trivial trivial]
  simp only [true_implies]

/-- **Definition 13.4** (Σ, `q + 2`) in `V`, exactly as the paper writes it. -/
theorem trSigP_add_two_vars_body_V {h w a : ZFSet.{u}} {q : ℕ} (l : List ℕ) (ψ : BF) :
    TrSigP (fun _ => True) h w (q + 2) (BF.code.{u} (BF.exs l ψ)) a ↔
      IsSigCodeWD h w (q + 2) (BF.code.{u} (BF.exs l ψ)) ∧
        ∃ t, ∃ b, IsBlkUpdP w a (seqOfNats.{u} l) t b ∧
          TrPiP (fun _ => True) h w (q + 1) (BF.code.{u} ψ) b := by
  rw [trSigP_add_two_vars_body (D := fun _ => True) (code_exs l ψ) trivial trivial]
  simp only [true_and]

/-- **Definition 13.4** (Π, `q + 2`) in `V`, exactly as the paper writes it. -/
theorem trPiP_add_two_vars_body_V {h w a : ZFSet.{u}} {q : ℕ} (l : List ℕ) (ψ : BF) :
    TrPiP (fun _ => True) h w (q + 2) (BF.code.{u} (BF.alls l ψ)) a ↔
      IsPiCodeWD h w (q + 2) (BF.code.{u} (BF.alls l ψ)) ∧
        ∀ t, ∀ b, IsBlkUpdP w a (seqOfNats.{u} l) t b →
          TrSigP (fun _ => True) h w (q + 1) (BF.code.{u} ψ) b := by
  rw [trPiP_add_two_vars_body (D := fun _ => True) (code_alls l ψ) trivial trivial]
  simp only [true_implies]

end BM4.ST
