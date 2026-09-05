/-
  Part III: code recognizers for Σ̂q / Π̂q block formulas.  Definition 12.1 asks every quantifier
  block to be a nonempty finite block of *pairwise distinct* variables, so the sequence
  recognizer `IsNeSeqWD` demands, on top of being a nonempty finite sequence of variables, that
  the sequence be injective.  These are the only Σ̂q / Π̂q code recognizers in the development;
  `Bm4.SetTheory.BFCode` supplies the Δ₀ block codes and the Δ₀-definability machinery they
  are built from.
-/
import Bm4.SetTheory.BFCode

universe u

namespace BM4.ST

open Fm

/-! ### Duplicate-free lists via `getElem?` -/

theorem nodup_iff_getElem?_inj {α : Type*} {l : List α} :
    l.Nodup ↔ ∀ (n n' : ℕ) (i : α), l[n]? = some i → l[n']? = some i → n = n' := by
  rw [List.nodup_iff_getElem?_ne_getElem?]
  constructor
  · intro h n n' i hn hn'
    rcases Nat.lt_trichotomy n n' with hlt | heq | hgt
    · exact absurd (hn.trans hn'.symm) (h n n' hlt (List.getElem?_eq_some_iff.mp hn').1)
    · exact heq
    · exact absurd (hn'.trans hn.symm) (h n' n hgt (List.getElem?_eq_some_iff.mp hn).1)
  · intro h i j hij hj hE
    have hjl : l[j]? = some l[j] := List.getElem?_eq_getElem hj
    exact absurd (h i j l[j] (hE.trans hjl) hjl) (by omega)

/-! ### Injective finite sequences -/

/-- `ν` takes each value at most once. -/
def IsInjSeq (ν : ZFSet.{u}) : Prop :=
  ∀ k k' x, ZFSet.pair k x ∈ ν → ZFSet.pair k' x ∈ ν → k = k'

theorem delta0_isInjSeq (n : ℕ) : Delta0Def.{u} {n} (fun _ v => IsInjSeq (v n)) := by
  set m := n + 1 with hm
  -- `∀ p ∈ n, ∀ q ∈ p, ∀ k ∈ q, ∀ q' ∈ p, ∀ x ∈ q', p = pair k x →`
  -- `  ∀ p₂ ∈ n, ∀ q₂ ∈ p₂, ∀ k' ∈ q₂, p₂ = pair k' x → k = k'`
  have a1 := delta0_isKPair m (m + 2) (m + 4) (by omega) (by omega)
  have b1 := (delta0_isKPair (m + 5) (m + 7) (m + 4) (by omega) (by omega)).imp
    (Delta0Def.eq (m + 2) (m + 7))
  have b2 := b1.ball (m + 7) (m + 6) (by omega)
  have b3 := b2.ball (m + 6) (m + 5) (by omega)
  have b4 := b3.ball (m + 5) n (by omega)
  have b5 := a1.imp b4
  have b6 := b5.ball (m + 4) (m + 3) (by omega)
  have b7 := b6.ball (m + 3) m (by omega)
  have b8 := b7.ball (m + 2) (m + 1) (by omega)
  have b9 := b8.ball (m + 1) m (by omega)
  have h2 := b9.ball m n (by omega)
  refine (h2.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · intro H k k' x hkx hk'x
      exact H _ hkx _ (singleton_mem_pair k x) k (ZFSet.mem_singleton.mpr rfl) _
        (upair_mem_pair k x) x (mem_upair_right k x) rfl _ hk'x _ (singleton_mem_pair k' x)
        k' (ZFSet.mem_singleton.mpr rfl) rfl
    · intro H p hp q _ k _ q' _ x _ hpkx p2 hp2 q2 _ k' _ hpk'x
      subst hpkx
      subst hpk'x
      exact H k k' x hp hp2
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Nonempty finite sequences of variables (auxiliary) -/

/-- Auxiliary (not Definition 12.1): `ν` is a nonempty finite sequence of elements of `w`, with
no distinctness demanded of its values.  Only `IsNeSeqWD` below, which adds that distinctness,
is exported. -/
private def IsNeSeqW (w ν : ZFSet.{u}) : Prop :=
  IsFunc ν ∧ (∃ d ∈ w, IsDom ν d ∧ d ≠ ∅) ∧ ∀ k x, ZFSet.pair k x ∈ ν → x ∈ w

private theorem delta0_isNeSeqW (w n : ℕ) (hwn : w ≠ n) :
    Delta0Def {w, n} (fun _ v => IsNeSeqW (v w) (v n)) := by
  set m := w + n + 1 with hm
  have h1 := delta0_isFunc n
  have h2 := ((delta0_isDom n m (by omega)).and (delta0_isEmpty m).not).bex m w (by omega)
  have c0 := (delta0_isKPair (m + 1) (m + 3) (m + 5) (by omega) (by omega)).imp
    (Delta0Def.mem (m + 5) w)
  have c1 := c0.ball (m + 5) (m + 4) (by omega)
  have c2 := c1.ball (m + 4) (m + 1) (by omega)
  have c3 := c2.ball (m + 3) (m + 2) (by omega)
  have c4 := c3.ball (m + 2) (m + 1) (by omega)
  have h3 := c4.ball (m + 1) n (by omega)
  refine ((h1.and (h2.and h3)).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    unfold IsNeSeqW
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    rw [forall_pair_mem_iff_bounded]
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- The natural-number value of the sequence `ν` at index `m` (arbitrary if undefined). -/
private noncomputable def seqNatVal (ν : ZFSet.{u}) (m : ℕ) : ℕ :=
  Classical.epsilon (fun k : ℕ => ZFSet.pair (natZ.{u} m) (natZ.{u} k) ∈ ν)

private theorem seqNatVal_mem {ν : ZFSet.{u}} {m : ℕ}
    (h : ∃ k : ℕ, ZFSet.pair (natZ.{u} m) (natZ.{u} k) ∈ ν) :
    ZFSet.pair (natZ.{u} m) (natZ.{u} (seqNatVal ν m)) ∈ ν :=
  Classical.epsilon_spec h

private theorem seqNatVal_spec {ν : ZFSet.{u}} (hf : IsFunc ν) {m k : ℕ}
    (hk : ZFSet.pair (natZ.{u} m) (natZ.{u} k) ∈ ν) : seqNatVal ν m = k :=
  natZ_injective (hf.2 _ _ _ (seqNatVal_mem ⟨k, hk⟩) hk)

private theorem isNeSeqW_iff (ν : ZFSet.{u}) :
    IsNeSeqW ωZ ν ↔ ∃ l : List ℕ, l ≠ [] ∧ ν = seqOfNats.{u} l := by
  constructor
  · rintro ⟨hf, ⟨d, hd, hdom, hne⟩, hval⟩
    obtain ⟨N, rfl⟩ := mem_ωZ_iff.mp hd
    have hN : N ≠ 0 := by rintro rfl; exact hne rfl
    refine ⟨(List.range N).map (seqNatVal ν), ?_, ?_⟩
    · intro hnil
      have hz : ((List.range N).map (seqNatVal ν)).length = 0 := by rw [hnil]; rfl
      simp only [List.length_map, List.length_range] at hz
      exact hN hz
    · ext p
      constructor
      · intro hp
        obtain ⟨a, b, rfl⟩ := hf.1 p hp
        have ha : a ∈ natZ N := (hdom a).mpr ⟨b, hp⟩
        obtain ⟨mm, hmm, rfl⟩ := mem_natZ_iff.mp ha
        obtain ⟨kk, rfl⟩ := mem_ωZ_iff.mp (hval _ _ hp)
        have hv : seqNatVal ν mm = kk := seqNatVal_spec hf hp
        rw [← hv]
        exact mem_seqOfNats.mpr (getElem?_map_range (seqNatVal ν) hmm)
      · intro hp
        obtain ⟨mm, i, hli, rfl⟩ := mem_seqOfNats_iff.mp hp
        have hmm : mm < N := by
          have hh := (List.getElem?_eq_some_iff.mp hli).1
          simpa using hh
        have hi : i = seqNatVal ν mm := by
          rw [getElem?_map_range (seqNatVal ν) hmm] at hli
          exact (Option.some.inj hli).symm
        subst hi
        have hex : ∃ k : ℕ, ZFSet.pair (natZ.{u} mm) (natZ.{u} k) ∈ ν := by
          obtain ⟨b, hb⟩ := (hdom (natZ mm)).mp (mem_natZ_iff.mpr ⟨mm, hmm, rfl⟩)
          obtain ⟨k, rfl⟩ := mem_ωZ_iff.mp (hval _ _ hb)
          exact ⟨k, hb⟩
        exact seqNatVal_mem hex
  · rintro ⟨l, hl, rfl⟩
    have hlen : 0 < l.length := by
      cases l with
      | nil => exact absurd rfl hl
      | cons a t => simp
    refine ⟨⟨?_, ?_⟩, ⟨natZ l.length, natZ_mem_ωZ _, ?_, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨n, i, _, rfl⟩ := mem_seqOfNats_iff.mp hp
      exact ⟨_, _, rfl⟩
    · intro a b b' hab hab'
      obtain ⟨n, i, hni, hp⟩ := mem_seqOfNats_iff.mp hab
      obtain ⟨n', i', hni', hp'⟩ := mem_seqOfNats_iff.mp hab'
      rw [ZFSet.pair_inj] at hp hp'
      obtain ⟨rfl, rfl⟩ := hp
      obtain ⟨ha, rfl⟩ := hp'
      have hnn : n = n' := natZ_injective ha
      subst hnn
      rw [hni] at hni'
      rw [Option.some.inj hni']
    · intro a
      rw [mem_natZ_iff]
      constructor
      · rintro ⟨mm, hmm, rfl⟩
        exact ⟨natZ l[mm], mem_seqOfNats.mpr (List.getElem?_eq_getElem hmm)⟩
      · rintro ⟨b, hb⟩
        obtain ⟨n, i, hni, hp⟩ := mem_seqOfNats_iff.mp hb
        rw [ZFSet.pair_inj] at hp
        exact ⟨n, (List.getElem?_eq_some_iff.mp hni).1, hp.1⟩
    · intro hE
      have hmem : natZ.{u} 0 ∈ natZ.{u} l.length := natZ_mem_natZ_iff.mpr hlen
      rw [hE] at hmem
      exact ZFSet.notMem_empty _ hmem
    · intro k x hkx
      obtain ⟨n, i, _, hp⟩ := mem_seqOfNats_iff.mp hkx
      rw [ZFSet.pair_inj] at hp
      rw [hp.2]
      exact natZ_mem_ωZ i

/-! ### Nonempty injective finite sequences of variables -/

/-- Definition 12.1, one block: `ν` is a nonempty finite sequence of elements of `w` whose
values are pairwise distinct. -/
def IsNeSeqWD (w ν : ZFSet.{u}) : Prop := IsNeSeqW w ν ∧ IsInjSeq ν

theorem delta0_isNeSeqWD (w n : ℕ) (hwn : w ≠ n) :
    Delta0Def.{u} {w, n} (fun _ v => IsNeSeqWD (v w) (v n)) := by
  refine (((delta0_isNeSeqW w n hwn).and (delta0_isInjSeq n)).congr
    (fun _ _ _ _ => Iff.rfl)).of_eq ?_
  ext k; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]; tauto

theorem isNeSeqWD_iff (ν : ZFSet.{u}) :
    IsNeSeqWD ωZ ν ↔ ∃ l : List ℕ, l ≠ [] ∧ l.Nodup ∧ ν = seqOfNats.{u} l := by
  constructor
  · rintro ⟨hne, hinj⟩
    obtain ⟨l, hl, rfl⟩ := (isNeSeqW_iff ν).mp hne
    refine ⟨l, hl, ?_, rfl⟩
    refine nodup_iff_getElem?_inj.mpr ?_
    intro n n' i hn hn'
    have h1 : ZFSet.pair (natZ.{u} n) (natZ.{u} i) ∈ seqOfNats.{u} l := mem_seqOfNats.mpr hn
    have h2 : ZFSet.pair (natZ.{u} n') (natZ.{u} i) ∈ seqOfNats.{u} l := mem_seqOfNats.mpr hn'
    exact natZ_injective (hinj _ _ _ h1 h2)
  · rintro ⟨l, hl, hnd, rfl⟩
    refine ⟨(isNeSeqW_iff _).mpr ⟨l, hl, rfl⟩, ?_⟩
    intro k k' x hkx hk'x
    obtain ⟨n, i, hni, hp⟩ := mem_seqOfNats_iff.mp hkx
    obtain ⟨n', i', hni', hp'⟩ := mem_seqOfNats_iff.mp hk'x
    rw [ZFSet.pair_inj] at hp hp'
    obtain ⟨rfl, hx⟩ := hp
    obtain ⟨rfl, hx'⟩ := hp'
    have hii : i = i' := natZ_injective (hx.symm.trans hx')
    subst hii
    rw [nodup_iff_getElem?_inj.mp hnd n n' i hni hni']

/-! ### Recognizers for codes of Σ̂q / Π̂q block formulas with distinct block variables -/

mutual
/-- Recognizer, by recursion on `q`, of codes of Σ̂q block formulas whose blocks are
duplicate-free. -/
def IsSigCodeWD (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → Prop
  | 0, e => IsDeltaBFCodeW h w e
  | q + 1, e => ∃ ν d, e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧ IsNeSeqWD w ν ∧
      IsPiCodeWD h w q d
/-- Recognizer, by recursion on `q`, of codes of Π̂q block formulas whose blocks are
duplicate-free. -/
def IsPiCodeWD (h w : ZFSet.{u}) : ℕ → ZFSet.{u} → Prop
  | 0, e => IsDeltaBFCodeW h w e
  | q + 1, e => ∃ ν d, e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) ∧ IsNeSeqWD w ν ∧
      IsSigCodeWD h w q d
end

theorem isSigCodeWD_zero (h w e : ZFSet.{u}) :
    IsSigCodeWD h w 0 e ↔ IsDeltaBFCodeW h w e := Iff.rfl

theorem isPiCodeWD_zero (h w e : ZFSet.{u}) :
    IsPiCodeWD h w 0 e ↔ IsDeltaBFCodeW h w e := Iff.rfl

theorem isSigCodeWD_succ (h w : ZFSet.{u}) (q : ℕ) (e : ZFSet.{u}) :
    IsSigCodeWD h w (q + 1) e ↔ ∃ ν d, e = ZFSet.pair (natZ 1) (ZFSet.pair ν d) ∧
      IsNeSeqWD w ν ∧ IsPiCodeWD h w q d := Iff.rfl

theorem isPiCodeWD_succ (h w : ZFSet.{u}) (q : ℕ) (e : ZFSet.{u}) :
    IsPiCodeWD h w (q + 1) e ↔ ∃ ν d, e = ZFSet.pair (natZ 2) (ZFSet.pair ν d) ∧
      IsNeSeqWD w ν ∧ IsSigCodeWD h w q d := Iff.rfl

theorem delta0_isSigPiCodeWD : ∀ (q : ℕ) (h w e : ℕ), h ≠ w → h ≠ e → w ≠ e →
    Delta0Def.{u} {h, w, e} (fun _ v => IsSigCodeWD (v h) (v w) q (v e)) ∧
    Delta0Def.{u} {h, w, e} (fun _ v => IsPiCodeWD (v h) (v w) q (v e)) := by
  intro q
  induction q with
  | zero =>
    intro h w e hhw hhe hwe
    exact ⟨(delta0_isDeltaBFCodeW h w e hhw hhe hwe).congr (fun _ _ _ _ => Iff.rfl),
      (delta0_isDeltaBFCodeW h w e hhw hhe hwe).congr (fun _ _ _ _ => Iff.rfl)⟩
  | succ q ih =>
    intro h w e hhw hhe hwe
    constructor
    · refine (delta0_pairShape (Q := fun W ν => IsNeSeqWD W ν)
        (P := fun H W d => IsPiCodeWD H W q d) 1 h w e hhw hhe hwe
        (fun a _ hwa _ => delta0_isNeSeqWD w a hwa)
        (fun d hhd hwd _ => (ih h w d hhw hhd hwd).2)).congr (fun _ _ _ _ => ?_)
      rfl
    · refine (delta0_pairShape (Q := fun W ν => IsNeSeqWD W ν)
        (P := fun H W d => IsSigCodeWD H W q d) 2 h w e hhw hhe hwe
        (fun a _ hwa _ => delta0_isNeSeqWD w a hwa)
        (fun d hhd hwd _ => (ih h w d hhw hhd hwd).1)).congr (fun _ _ _ _ => ?_)
      rfl

theorem delta0_isSigCodeWD (q : ℕ) (h w e : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hwe : w ≠ e) :
    Delta0Def.{u} {h, w, e} (fun _ v => IsSigCodeWD (v h) (v w) q (v e)) :=
  (delta0_isSigPiCodeWD q h w e hhw hhe hwe).1

theorem delta0_isPiCodeWD (q : ℕ) (h w e : ℕ) (hhw : h ≠ w) (hhe : h ≠ e) (hwe : w ≠ e) :
    Delta0Def.{u} {h, w, e} (fun _ v => IsPiCodeWD (v h) (v w) q (v e)) :=
  (delta0_isSigPiCodeWD q h w e hhw hhe hwe).2

/-! ### Correctness of the block-code recognizers with distinct block variables -/

theorem isSigPiCodeWD_iff : ∀ (q : ℕ) (e : ZFSet.{u}),
    (IsSigCodeWD (L Ordinal.omega0) ωZ q e ↔
      ∃ b : BF, BF.Sig q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b) ∧
    (IsPiCodeWD (L Ordinal.omega0) ωZ q e ↔
      ∃ b : BF, BF.Pi q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b) := by
  intro q
  induction q with
  | zero =>
    intro e
    constructor
    · refine (isDeltaBFCodeW_iff e).trans ?_
      constructor
      · rintro ⟨sg, φ, hφ, rfl⟩; exact ⟨BF.delta sg φ, BF.Sig.zero hφ, trivial, rfl⟩
      · rintro ⟨b, hb, -, rfl⟩
        cases hb with
        | @zero sg φ hφ => exact ⟨sg, φ, hφ, rfl⟩
    · refine (isDeltaBFCodeW_iff e).trans ?_
      constructor
      · rintro ⟨sg, φ, hφ, rfl⟩; exact ⟨BF.delta sg φ, BF.Pi.zero hφ, trivial, rfl⟩
      · rintro ⟨b, hb, -, rfl⟩
        cases hb with
        | @zero sg φ hφ => exact ⟨sg, φ, hφ, rfl⟩
  | succ q ih =>
    intro e
    constructor
    · rw [isSigCodeWD_succ]
      constructor
      · rintro ⟨ν, d, H, hν, hd⟩
        obtain ⟨l, hl, hnd, rfl⟩ := (isNeSeqWD_iff ν).mp hν
        obtain ⟨b, hb, hnb, rfl⟩ := (ih d).2.mp hd
        exact ⟨BF.exs l b, BF.Sig.succ hl hb, ⟨hnd, hnb⟩, H⟩
      · rintro ⟨b, hb, hnb, rfl⟩
        cases hb with
        | @succ q' l hl ψ hψ =>
          obtain ⟨hndl, hndψ⟩ : l.Nodup ∧ ψ.NodupBlocks := hnb
          exact ⟨seqOfNats.{u} l, BF.code.{u} ψ, rfl,
            (isNeSeqWD_iff _).mpr ⟨l, hl, hndl, rfl⟩, (ih _).2.mpr ⟨ψ, hψ, hndψ, rfl⟩⟩
    · rw [isPiCodeWD_succ]
      constructor
      · rintro ⟨ν, d, H, hν, hd⟩
        obtain ⟨l, hl, hnd, rfl⟩ := (isNeSeqWD_iff ν).mp hν
        obtain ⟨b, hb, hnb, rfl⟩ := (ih d).1.mp hd
        exact ⟨BF.alls l b, BF.Pi.succ hl hb, ⟨hnd, hnb⟩, H⟩
      · rintro ⟨b, hb, hnb, rfl⟩
        cases hb with
        | @succ q' l hl ψ hψ =>
          obtain ⟨hndl, hndψ⟩ : l.Nodup ∧ ψ.NodupBlocks := hnb
          exact ⟨seqOfNats.{u} l, BF.code.{u} ψ, rfl,
            (isNeSeqWD_iff _).mpr ⟨l, hl, hndl, rfl⟩, (ih _).1.mpr ⟨ψ, hψ, hndψ, rfl⟩⟩

theorem isSigCodeWD_iff (q : ℕ) (e : ZFSet.{u}) :
    IsSigCodeWD (L Ordinal.omega0) ωZ q e ↔
      ∃ b : BF, BF.Sig q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b :=
  (isSigPiCodeWD_iff q e).1

theorem isPiCodeWD_iff (q : ℕ) (e : ZFSet.{u}) :
    IsPiCodeWD (L Ordinal.omega0) ωZ q e ↔
      ∃ b : BF, BF.Pi q b ∧ b.NodupBlocks ∧ e = BF.code.{u} b :=
  (isSigPiCodeWD_iff q e).2

end BM4.ST
