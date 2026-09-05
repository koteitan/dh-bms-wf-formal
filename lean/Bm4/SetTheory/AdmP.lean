/-
  Part III, §11: the internal Σ̂₁ predicate `AdmP(η)` expressing that `η` is admissible
  (Definition 11.1) and its correctness inside an admissible `L θ` (Lemma 11.2).
-/
import Bm4.SetTheory.LCode
import Bm4.SetTheory.BFCode
import Bm4.SetTheory.SatInL
import Bm4.SetTheory.BaseOK

universe u

namespace BM4.ST

open Fm

/-! ### Finite sequences inside `L θ` -/

/-- The sequence coding a valuation lies in `L θ` for a limit `θ > ω`. -/
theorem seqOfVal_mem_L {θ : Ordinal.{u}} (hlim : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 ≤ θ) {N : ℕ} {v : ℕ → ZFSet.{u}} (hv : ∀ k, k < N → v k ∈ L θ) :
    seqOfVal N v ∈ L θ := by
  rw [seqOfVal]
  refine ofList_mem_L_of_limit hlim _ ?_
  intro x hx
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  exact kpair_mem_L_of_limit hlim (L_mono hω (natZ_mem_Lω k)) (hv k hk)

/-- Beyond `N` the coded valuation takes the default value. -/
theorem seqVal_seqOfVal_ge {N : ℕ} {v : ℕ → ZFSet.{u}} {k : ℕ} (hk : N ≤ k) :
    SeqVal (seqOfVal N v) k = ∅ := by
  refine seqVal_of_notMem ?_
  intro y hy
  obtain ⟨m, hm, he⟩ := mem_seqOfVal.mp hy
  rw [ZFSet.pair_inj] at he
  have : k = m := natZ_injective he.1
  omega

/-- Beyond its domain a finite sequence takes the default value. -/
theorem seqVal_of_ge_dom {a : ZFSet.{u}} {n : ℕ} (hdom : IsDom a (natZ n)) {k : ℕ} (hk : n ≤ k) :
    SeqVal a k = ∅ := by
  refine seqVal_of_notMem ?_
  intro y hy
  have h := (hdom (natZ k)).mpr ⟨y, hy⟩
  rw [natZ_mem_natZ_iff] at h
  omega

/-- A finite sequence in `L θ` realising a valuation on a finite index set. -/
theorem exists_seq_of_val_in_L {θ : Ordinal.{u}} (hlim : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 ≤ θ) (t : Finset ℕ) (v : ℕ → ZFSet.{u}) (hv : ∀ k ∈ t, v k ∈ L θ) :
    ∃ q ∈ L θ, IsSeqA ωZ (L θ) q ∧ (∀ k ∈ t, InDomZ q (natZ k)) ∧
      ∀ k ∈ t, SeqVal q k = v k := by
  classical
  set N := t.sup id + 1 with hN
  set v' : ℕ → ZFSet.{u} := fun k => if k ∈ t then v k else ∅ with hv'
  have hlt : ∀ k ∈ t, k < N := fun k hk => Nat.lt_succ_of_le (Finset.le_sup (f := id) hk)
  have hmem : ∀ k, k < N → v' k ∈ L θ := by
    intro k _
    by_cases hkt : k ∈ t
    · simp only [hv', if_pos hkt]; exact hv k hkt
    · simp only [hv', if_neg hkt]; exact empty_mem_L_of_limit hlim
  refine ⟨seqOfVal N v', seqOfVal_mem_L hlim hω hmem, isSeqA_seqOfVal hmem,
    fun k hk => ⟨v' k, mem_seqOfVal.mpr ⟨k, hlt k hk, rfl⟩⟩, fun k hk => ?_⟩
  rw [seqVal_seqOfVal hmem (hlt k hk)]
  simp only [hv', if_pos hk]

/-- The double update of a finite sequence, realised inside `L θ`. -/
theorem exists_upd2_in_L {θ : Ordinal.{u}} (hlim : Order.IsSuccLimit θ)
    (hω : Ordinal.omega0 ≤ θ) {a : ZFSet.{u}} (ha : IsSeqA ωZ (L θ) a) {i j : ℕ} (hij : i ≠ j)
    {x y : ZFSet.{u}} (hx : x ∈ L θ) (hy : y ∈ L θ) (N₀ : ℕ) :
    ∃ q ∈ L θ, IsSeqA ωZ (L θ) q ∧ (∀ k < N₀, InDomZ q (natZ k)) ∧
      SeqVal q = Function.update (Function.update (SeqVal a) i x) j y := by
  classical
  have hemp : (∅ : ZFSet.{u}) ∈ L θ := empty_mem_L_of_limit hlim
  obtain ⟨n, hdom⟩ := isSeqA_dom ha
  set N := max (max (max n (i + 1)) (j + 1)) N₀ with hNdef
  set f : ℕ → ZFSet.{u} := Function.update (Function.update (SeqVal a) i x) j y with hf
  have hmem : ∀ k, k < N → f k ∈ L θ := by
    intro k _
    by_cases hkj : k = j
    · subst hkj; simp only [hf, Function.update_self]; exact hy
    · rw [hf, Function.update_of_ne hkj]
      by_cases hki : k = i
      · subst hki; simp only [Function.update_self]; exact hx
      · rw [Function.update_of_ne hki]; exact seqVal_mem ha hemp k
  refine ⟨seqOfVal N f, seqOfVal_mem_L hlim hω hmem, isSeqA_seqOfVal hmem,
    fun k hk => ⟨f k, mem_seqOfVal.mpr ⟨k, by omega, rfl⟩⟩, ?_⟩
  funext k
  by_cases hk : k < N
  · exact seqVal_seqOfVal hmem hk
  · rw [seqVal_seqOfVal_ge (by omega)]
    have hkj : k ≠ j := by omega
    have hki : k ≠ i := by omega
    rw [hf, Function.update_of_ne hkj, Function.update_of_ne hki]
    exact (seqVal_of_ge_dom hdom (by omega)).symm


/-! ### Definition 11.1: the internal predicate -/

/-- `q` is the assignment `v` updated at `i ↦ x` and `j ↦ y`, expressed internally: `q` is a
finite sequence over `M` taking the value `x` at `i`, `y` at `j`, and agreeing with `v`
everywhere else. -/
def IsUpd2 (w M v i x j y q : ZFSet.{u}) : Prop :=
  IsSeqA w M q ∧ ValAt q i x ∧ ValAt q j y ∧
    ∀ k ∈ w, ∀ z ∈ M, k ≠ i → k ≠ j → (ValAt q k z ↔ ValAt v k z)

/-- All instances of Δ₀-Collection hold in the structure `M` described by the satisfaction
code `S`: every Δ₀ code `d`, every pair of distinct variables `i ≠ j`, every assignment `v` and
every `a ∈ M` satisfy the collection axiom for `d`. All quantifiers are bounded. -/
def CollTrue (h w M S : ZFSet.{u}) : Prop :=
  ∀ d ∈ h, IsDelta0CodeW h w d → ∀ i ∈ w, ∀ j ∈ w, i ≠ j → ∀ v ∈ M, IsSeqA w M v → ∀ a ∈ M,
    (∀ x ∈ a, ∃ y ∈ M, ∃ q ∈ M, IsUpd2 w M v i x j y q ∧ IsAsn h w M d q ∧
      ZFSet.pair d q ∈ S) →
    ∃ b ∈ M, ∀ x ∈ a, ∃ y ∈ b, ∃ q ∈ M, IsUpd2 w M v i x j y q ∧ IsAsn h w M d q ∧
      ZFSet.pair d q ∈ S

/-- **Definition 11.1**: `η` is admissible, internally. -/
def AdmP (D : ZFSet.{u} → Prop) (h w η : ZFSet.{u}) : Prop :=
  w ∈ η ∧ (∀ ζ ∈ η, insert ζ ζ ∈ η) ∧
    ∃ M, D M ∧ ∃ c, D c ∧ ∃ U, D U ∧ ∃ S, D S ∧
      LCode h w η M c ∧ SatCode h w M U S ∧ CollTrue h w M S

/-! ### `IsUpd2` and `SeqVal` -/

theorem isUpd2_seqVal {M v q : ZFSet.{u}} {i j : ℕ} {x y : ZFSet.{u}}
    (hemp : (∅ : ZFSet.{u}) ∈ M) (hij : i ≠ j) (hv : IsSeqA ωZ M v)
    (hu : IsUpd2 ωZ M v (natZ i) x (natZ j) y q) :
    SeqVal q = Function.update (Function.update (SeqVal v) i x) j y := by
  obtain ⟨hq, hxi, hyj, hag⟩ := hu
  funext k
  by_cases hkj : k = j
  · subst hkj
    rw [Function.update_self]
    exact ((valAt_iff hq.1).mp hyj).symm
  · rw [Function.update_of_ne hkj]
    by_cases hki : k = i
    · subst hki
      rw [Function.update_self]
      exact ((valAt_iff hq.1).mp hxi).symm
    · rw [Function.update_of_ne hki]
      have hz : SeqVal q k ∈ M := seqVal_mem hq hemp k
      have h := (hag (natZ k) (natZ_mem_ωZ k) (SeqVal q k) hz
        (fun he => hki (natZ_injective he)) (fun he => hkj (natZ_injective he))).mp
        ((valAt_iff hq.1).mpr rfl)
      exact (valAt_iff hv.1).mp h

theorem isUpd2_of_seqVal {M v q : ZFSet.{u}} {i j : ℕ} {x y : ZFSet.{u}} (hij : i ≠ j)
    (hq : IsSeqA ωZ M q) (hv : IsSeqA ωZ M v)
    (he : SeqVal q = Function.update (Function.update (SeqVal v) i x) j y) :
    IsUpd2 ωZ M v (natZ i) x (natZ j) y q := by
  refine ⟨hq, ?_, ?_, ?_⟩
  · rw [valAt_iff hq.1, he, Function.update_of_ne hij, Function.update_self]
  · rw [valAt_iff hq.1, he, Function.update_self]
  · intro k hk z _ hki hkj
    obtain ⟨k', rfl⟩ := mem_ωZ_iff.mp hk
    have h1 : k' ≠ i := fun h => hki (by rw [h])
    have h2 : k' ≠ j := fun h => hkj (by rw [h])
    rw [valAt_iff hq.1, valAt_iff hv.1, he, Function.update_of_ne h2, Function.update_of_ne h1]


/-! ### Δ₀-definability -/

set_option linter.unusedVariables false in
/-- `pair a b ∈ p` is Δ₀-definable. -/
theorem delta0_kpairMem (p a b : ℕ) (hpa : p ≠ a) (hpb : p ≠ b) :
    Delta0Def {p, a, b} (fun _ v => ZFSet.pair (v a) (v b) ∈ v p) := by
  set m := p + a + b + 1 with hm
  have h := (delta0_isKPair m a b (by omega) (by omega)).bex m p (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro H; exact ⟨_, H, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]; omega

theorem delta0_isUpd2 (w M v i x j y q : ℕ) (hwM : w ≠ M) (hwq : w ≠ q) (hMq : M ≠ q)
    (hqi : q ≠ i) (hqx : q ≠ x) (hix : i ≠ x) (hqj : q ≠ j) (hqy : q ≠ y) (hjy : j ≠ y) :
    Delta0Def {w, M, v, i, x, j, y, q}
      (fun _ vv => IsUpd2 (vv w) (vv M) (vv v) (vv i) (vv x) (vv j) (vv y) (vv q)) := by
  set m := w + M + v + i + x + j + y + q + 1 with hm
  have h1 := delta0_isSeqA w M q hwM hwq hMq
  have h2 := delta0_valAt q i x hqi hqx hix
  have h3 := delta0_valAt q j y hqj hqy hjy
  have c0 := ((Delta0Def.eq m i).not).imp
    (((Delta0Def.eq m j).not).imp
      ((delta0_valAt q m (m + 1) (by omega) (by omega) (by omega)).iff
        (delta0_valAt v m (m + 1) (by omega) (by omega) (by omega))))
  have c1 := c0.ball (m + 1) M (by omega)
  have c2 := c1.ball m w (by omega)
  refine ((h1.and (h2.and (h3.and c2))).congr ?_).mono ?_
  · intro D vv _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢
    omega

set_option linter.unusedVariables false in
theorem delta0_collTrue (h w M S : ℕ) (hhw : h ≠ w) (hhM : h ≠ M) (hhS : h ≠ S)
    (hwM : w ≠ M) (hwS : w ≠ S) (hMS : M ≠ S) :
    Delta0Def {h, w, M, S} (fun _ v => CollTrue (v h) (v w) (v M) (v S)) := by
  set m := h + w + M + S + 1 with hm
  -- `d := m`, `i := m+1`, `j := m+2`, `v := m+3`, `a := m+4`, `b := m+5`,
  -- `x := m+6`, `y := m+7`, `q := m+8`, `x' := m+9`, `y' := m+10`, `q' := m+11`
  have u1 := (delta0_isUpd2 w M (m + 3) (m + 1) (m + 6) (m + 2) (m + 7) (m + 8)
      hwM (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).and
    ((delta0_isAsn h w M m (m + 8) hhw (by omega) hwM (by omega) (by omega) (by omega)).and
      (delta0_kpairMem S m (m + 8) (by omega) (by omega)))
  have a1 := u1.bex (m + 8) M (by omega)
  have a2 := a1.bex (m + 7) M (by omega)
  have a3 := a2.ball (m + 6) (m + 4) (by omega)
  have u2 := (delta0_isUpd2 w M (m + 3) (m + 1) (m + 9) (m + 2) (m + 10) (m + 11)
      hwM (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)).and
    ((delta0_isAsn h w M m (m + 11) hhw (by omega) hwM (by omega) (by omega) (by omega)).and
      (delta0_kpairMem S m (m + 11) (by omega) (by omega)))
  have b1 := u2.bex (m + 11) M (by omega)
  have b2 := b1.bex (m + 10) (m + 5) (by omega)
  have b3 := b2.ball (m + 9) (m + 4) (by omega)
  have b4 := b3.bex (m + 5) M (by omega)
  have c1 := a3.imp b4
  have c2 := c1.ball (m + 4) M (by omega)
  have c3 := (delta0_isSeqA w M (m + 3) hwM (by omega) (by omega)).imp c2
  have c4 := c3.ball (m + 3) M (by omega)
  have c5 := ((Delta0Def.eq (m + 1) (m + 2)).not).imp c4
  have c6 := c5.ball (m + 2) w (by omega)
  have c7 := c6.ball (m + 1) w (by omega)
  have c8 := (delta0_isDelta0CodeW h w m hhw (by omega) (by omega)).imp c7
  have c9 := c8.ball m h (by omega)
  refine (c9.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢
    omega

theorem sigmaDef_admP (h w x : ℕ) (hhw : h ≠ w) (hhx : h ≠ x) (hwx : w ≠ x) :
    SigmaDef 1 {h, w, x} (fun D v => AdmP.{u} D (v h) (v w) (v x)) := by
  set m := h + w + x + 1 with hm
  -- `M := m`, `c := m+1`, `U := m+2`, `S := m+3`
  have hlc := delta0_lcode h w x m (m + 1) hhw hhx (by omega) (by omega) hwx (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have hsc := delta0_satCode h w m (m + 2) (m + 3) hhw (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hct := delta0_collTrue h w m (m + 3) hhw (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have core := hlc.and (hsc.and hct)
  have e1 := (core.sigma 1).ex (m + 3) le_rfl
  have e2 := e1.ex (m + 2) le_rfl
  have e3 := e2.ex (m + 1) le_rfl
  have e4 := e3.ex m le_rfl
  have s0 := (delta0_isSucc (m + 5) (m + 4) (by omega)).bex (m + 5) x (by omega)
  have s1 : Delta0Def.{u} {x, m + 4} (fun _ v => insert (v (m + 4)) (v (m + 4)) ∈ v x) := by
    refine (s0.congr ?_).of_eq ?_
    · intro D v _ _
      simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      constructor
      · rintro ⟨z, hz, rfl⟩; exact hz
      · intro H; exact ⟨_, H, rfl⟩
    · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]; omega
  have s2 := s1.ball (m + 4) x (by omega)
  have hcl := (Delta0Def.mem w x).and s2
  refine (((hcl.sigma 1).and e4).congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    simp only [AdmP, and_assoc]
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢
    omega


/-! ### Lemma 11.2: correctness inside an admissible `L θ` -/

/-- **Lemma 11.2**: `AdmP` is correct inside an admissible `L θ`.

The hypothesis `hcode` — a code for the constructible hierarchy up to `η` exists inside `L θ` —
is the content of `GoodOrd.lcode`; it is not derivable from `IsAdmissible θ` alone in the present
development, so it is assumed here. -/
theorem admP_iff {θ η : Ordinal.{u}} (hθ : IsAdmissible θ) (hη : η < θ)
    (hcode : ∃ M ∈ L θ, ∃ c ∈ L θ, LCode (L Ordinal.omega0.{u}) ωZ.{u} η.toZFSet M c) :
    AdmP (· ∈ L θ) (L Ordinal.omega0.{u}) ωZ.{u} η.toZFSet ↔ IsAdmissible η := by
  constructor
  · rintro ⟨hwη, hsucc, M, hM, c, hcM, U, hU, S, hS, hlc, hsat, hcoll⟩
    have hωη : Ordinal.omega0 < η := Ordinal.toZFSet_mem_toZFSet_iff.mp hwη
    have hpos : (0 : Ordinal.{u}) < η := Ordinal.omega0_pos.trans hωη
    have hlim : Order.IsSuccLimit η := by
      rw [Ordinal.isSuccLimit_iff]
      refine ⟨hpos.ne', Order.isSuccPrelimit_iff_succ_lt.mpr ?_⟩
      intro ξ hξ
      rw [Order.succ_eq_add_one]
      have h1 := hsucc ξ.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr hξ)
      rw [← Ordinal.toZFSet_add_one] at h1
      exact Ordinal.toZFSet_mem_toZFSet_iff.mp h1
    have hMeq : M = L η := lcode_sound hlc
    subst hMeq
    have hemp : (∅ : ZFSet.{u}) ∈ L η := empty_mem_L hpos
    have hωle : Ordinal.omega0 ≤ η := hωη.le
    have hDgood : GoodDom (· ∈ L η) := goodDom_mem (L_transitive η) (L_nonempty hpos)
    have hUcl : ∀ q : ZFSet.{u}, IsSeqA ωZ (L η) q → q ∈ U :=
      fun _ hq => seq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl hq
    refine ⟨hωη, hlim, ?_⟩
    intro s P hP i' j' hij' v hv a ha hcol
    obtain ⟨φ, hφ, hfv, hsatφ⟩ := id hP
    obtain ⟨vv, hvvL, hvvseq, hvvdom, hvvval⟩ :=
      exists_seq_of_val_in_L hlim hωle ((s.erase i').erase j') v hv
    have hval : ∀ z ∈ L η, ∀ y ∈ L η,
        ValD (· ∈ L η) s (Function.update (Function.update v i' z) j' y) := by
      intro z hz y hy k hk
      by_cases hkj : k = j'
      · subst hkj; simpa using hy
      · rw [Function.update_of_ne hkj]
        by_cases hki : k = i'
        · subst hki; simpa using hz
        · rw [Function.update_of_ne hki]
          exact hv k (Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hk⟩⟩)
    have hagree : ∀ z y : ZFSet.{u}, ∀ k ∈ fv φ,
        Function.update (Function.update (SeqVal vv) i' z) j' y k
          = Function.update (Function.update v i' z) j' y k := by
      intro z y k hk
      by_cases hkj : k = j'
      · subst hkj; simp
      · rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
        by_cases hki : k = i'
        · subst hki; simp
        · rw [Function.update_of_ne hki, Function.update_of_ne hki]
          exact hvvval k (Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, hfv hk⟩⟩)
    have hante : ∀ z ∈ a, ∃ y ∈ L η, ∃ q ∈ L η,
        IsUpd2 ωZ (L η) vv (natZ i') z (natZ j') y q ∧
          IsAsn (L Ordinal.omega0) ωZ (L η) (Fm.code.{u} φ) q ∧
          ZFSet.pair (Fm.code.{u} φ) q ∈ S := by
      intro z hz
      obtain ⟨y, hyL, hPy⟩ := hcol z hz
      have hzL : z ∈ L η := (L_transitive η).subset_of_mem ha hz
      obtain ⟨q, hqL, hqseq, hqdom, hqval⟩ :=
        exists_upd2_in_L hlim hωle hvvseq hij' hzL hyL (fvSup φ)
      have hqcov : ∀ k ∈ fv φ, InDomZ q (natZ k) := fun k hk => hqdom k (lt_fvSup hk)
      refine ⟨y, hyL, q, hqL, isUpd2_of_seqVal hij' hqseq hvvseq hqval,
        isAsn_code_iff.mpr ⟨hqseq, hqcov⟩, ?_⟩
      rw [satCode_correct hsat φ q hqseq hqcov (hUcl q hqseq), hqval]
      exact (sat_congr (hagree z y)).mpr
        ((hsatφ (· ∈ L η) _ hDgood (hval z hzL y hyL)).mpr hPy)
    obtain ⟨b, hbL, hbspec⟩ := hcoll (Fm.code.{u} φ) (Fm.code_mem_Lω φ)
      ((isDelta0CodeW_iff _).mpr ⟨φ, hφ, rfl⟩) (natZ i') (natZ_mem_ωZ i') (natZ j')
      (natZ_mem_ωZ j') (natZ_ne hij') vv hvvL hvvseq a ha hante
    refine ⟨b, hbL, ?_⟩
    intro z hz
    obtain ⟨y, hyb, q, hqL, hu, hasn, hmem⟩ := hbspec z hz
    have hyL : y ∈ L η := (L_transitive η).subset_of_mem hbL hyb
    have hzL : z ∈ L η := (L_transitive η).subset_of_mem ha hz
    refine ⟨y, hyb, ?_⟩
    have hqseq := hu.1
    obtain ⟨-, hqcov⟩ := isAsn_code_iff.mp hasn
    have hs := (satCode_correct hsat φ q hqseq hqcov (hUcl q hqseq)).mp hmem
    rw [isUpd2_seqVal hemp hij' hvvseq hu] at hs
    exact (hsatφ (· ∈ L η) _ hDgood (hval z hzL y hyL)).mp ((sat_congr (hagree z y)).mp hs)
  · intro hadm
    have hlim := hadm.isSuccLimit
    have hωη := hadm.omega_lt
    have hpos : (0 : Ordinal.{u}) < η := hadm.pos
    have hemp : (∅ : ZFSet.{u}) ∈ L η := empty_mem_L hpos
    have hωle : Ordinal.omega0 ≤ η := hωη.le
    refine ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr hωη, ?_, ?_⟩
    · intro ζ hζ
      obtain ⟨ξ, hξ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ
      rw [← Ordinal.toZFSet_add_one]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (hlim.add_one_lt hξ)
    · obtain ⟨M0, hM0, c0, hc0, hlc⟩ := hcode
      have hMeq : M0 = L η := lcode_sound hlc
      subst hMeq
      obtain ⟨U, hU, S, hS, hsat⟩ :=
        satCode_exists_in_L hθ (L_mem_L hη)
      have hUcl : ∀ q : ZFSet.{u}, IsSeqA ωZ (L η) q → q ∈ U :=
        fun _ hq => seq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl hq
      refine ⟨L η, L_mem_L hη, c0, hc0, U, hU, S, hS, hlc, hsat, ?_⟩
      intro d hd hdcode i hi j hj hij v hvM hvseq a ha hante
      obtain ⟨φ, hφ, rfl⟩ := (isDelta0CodeW_iff d).mp hdcode
      obtain ⟨i', rfl⟩ := mem_ωZ_iff.mp hi
      obtain ⟨j', rfl⟩ := mem_ωZ_iff.mp hj
      have hij' : i' ≠ j' := fun hh => hij (by rw [hh])
      have hante' : ∀ z ∈ a, ∃ y ∈ L η,
          SatIn (L η) (Function.update (Function.update (SeqVal v) i' z) j' y) φ := by
        intro z hz
        obtain ⟨y, hy, q, hq, hu, hasn, hmem⟩ := hante z hz
        refine ⟨y, hy, ?_⟩
        have hqseq := hu.1
        obtain ⟨-, hqcov⟩ := isAsn_code_iff.mp hasn
        have hs := (satCode_correct hsat φ q hqseq hqcov (hUcl q hqseq)).mp hmem
        rwa [isUpd2_seqVal hemp hij' hvseq hu] at hs
      have hP : Delta0Def (fv φ) (fun D u => Sat D u φ) :=
        ⟨φ, hφ, subset_rfl, fun _ _ _ _ => Iff.rfl⟩
      have hvalD : ValD (· ∈ L η) (((fv φ).erase i').erase j') (SeqVal v) :=
        fun k _ => seqVal_mem hvseq hemp k
      obtain ⟨b, hb, hbspec⟩ :=
        hadm.collection (fv φ) _ hP i' j' hij' (SeqVal v) hvalD a ha hante'
      refine ⟨b, hb, ?_⟩
      intro z hz
      obtain ⟨y, hyb, hsy⟩ := hbspec z hz
      have hzL : z ∈ L η := (L_transitive η).subset_of_mem ha hz
      have hyL : y ∈ L η := (L_transitive η).subset_of_mem hb hyb
      obtain ⟨q, hqL, hqseq, hqdom, hqval⟩ :=
        exists_upd2_in_L hlim hωle hvseq hij' hzL hyL (fvSup φ)
      have hqcov : ∀ k ∈ fv φ, InDomZ q (natZ k) := fun k hk => hqdom k (lt_fvSup hk)
      refine ⟨y, hyb, q, hqL, isUpd2_of_seqVal hij' hqseq hvseq hqval,
        isAsn_code_iff.mpr ⟨hqseq, hqcov⟩, ?_⟩
      rw [satCode_correct hsat φ q hqseq hqcov (hUcl q hqseq), hqval]
      exact hsy

end BM4.ST
