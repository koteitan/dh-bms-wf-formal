/-
  Part III, §11: the internal Σ̂₁ predicate `AdmKP(η)` expressing that `η` is admissible
  (Definition 11.1) and its correctness inside an admissible `L θ` (Lemma 11.2).

  This is the *verbatim* form of the paper's definition: internal admissibility is expressed by
  the truth, inside the coded structure `M = L η`, of every axiom of Kripke–Platek set theory —
  the predicate `KPTrue` below asks, exactly as the paper does, that `⟨d, ∅⟩` belong to the truth
  part `S` of a satisfaction code for `M` for every code `d` recognised by `KPAxCode`.  Truth at
  the *empty* assignment is enough because `KPAxCode` recognises only codes of sentences (the
  schema instances are recognised in universally closed form).  (The variant `AdmP` of
  `Bm4.SetTheory.AdmP` replaces this by the ad hoc `CollTrue`, which spells out Δ₀-collection by
  hand.)
-/
import Bm4.SetTheory.KPSat
import Bm4.SetTheory.AdmP
import Bm4.SetTheory.LCodeEx

universe u

namespace BM4.ST

open Fm

/-! ### Definition 11.1: the internal predicate -/

set_option linter.unusedVariables false in
/-- All axioms of KP are true in the structure `M` described by the satisfaction code `S`:
every code `d ∈ h` recognised by `KPAxCode` is satisfied by the **empty** assignment.

This is the paper's `∀ d ∈ ω (KPAx(d) → ⟨d, ∅⟩ ∈ S)` verbatim.  It is the right reading because
`KPAxCode` recognises only codes of **sentences** (`fv_eq_empty_of_kpAxCode`): for the three
schemas what is recognised is the universal closure of an instance, not the open instance.  (Had
the open instances been recognised, truth at `∅` would only have given the parameter-free
instances of Δ₀-collection — for example `Fm.fv (collAx (Fm.mem 5 6) 0 1 7 8) = {5, 6}` — which
is strictly weaker than the `Delta0Collection (L η)` that `IsAdmissible η` asks for.)

`pair d ∅ ∈ S` is Δ₀: `∅` is reached by bounded quantifiers inside the pair itself
(`delta0_kpairEmptyMem`).

`M` and `U` are no longer mentioned; they are kept so that `AdmKP` and `delta0_kpTrue` read as
before. -/
def KPTrue (h w M U S : ZFSet.{u}) : Prop :=
  ∀ d ∈ h, KPAxCode h w d → ZFSet.pair d ∅ ∈ S

/-- **Definition 11.1**: `η` is admissible, internally, via the truth of the KP axioms.

This is literally the paper's definition: the two Δ₀ conjuncts `ω ∈ η` and `∀ ζ ∈ η, ζ + 1 ∈ η`
that `AdmP` carries are *not* part of it.  They are recovered inside `admKP_iff` from the truth
of the KP axioms in `L η`; see `omega_lt_of_kpTrue` and `isSuccLimit_of_kpTrue`. -/
def AdmKP (D : ZFSet.{u} → Prop) (h w η : ZFSet.{u}) : Prop :=
  ∃ M, D M ∧ ∃ c, D c ∧ ∃ U, D U ∧ ∃ S, D S ∧
    LCode h w η M c ∧ SatCode h w M U S ∧ KPTrue h w M U S

/-! ### Δ₀-definability -/

set_option linter.unusedVariables false in
/-- `pair d ∅ ∈ S` is Δ₀: the pair and its components bound every quantifier, and `∅` is found
inside the pair as the second component of `{d, ∅}`. -/
theorem delta0_kpairEmptyMem (S d : ℕ) (hSd : S ≠ d) :
    Delta0Def.{u} {S, d} (fun _ v => ZFSet.pair (v d) ∅ ∈ v S) := by
  set m := S + d + 1 with hm
  -- `p := m`, `r := m+1`, `e := m+2`
  have h0 := (delta0_isNatZ 0 (m + 2)).and
    (delta0_isKPair m d (m + 2) (by omega) (by omega))
  have h1 := h0.bex (m + 2) (m + 1) (by omega)
  have h2 := h1.bex (m + 1) m (by omega)
  have h3 := h2.bex m S (by omega)
  refine (h3.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨p, hp, r, -, e, -, he0, rfl⟩
      rw [he0] at hp
      exact hp
    · intro H
      exact ⟨_, H, _, upair_mem_pair _ _, (∅ : ZFSet.{u}), mem_upair_right _ _, rfl, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

set_option linter.unusedVariables false in
theorem delta0_kpTrue (h w M U S : ℕ) (hhw : h ≠ w) (hhM : h ≠ M) (hhU : h ≠ U) (hhS : h ≠ S)
    (hwM : w ≠ M) (hwU : w ≠ U) (hwS : w ≠ S) (hMU : M ≠ U) (hMS : M ≠ S) (hUS : U ≠ S) :
    Delta0Def {h, w, M, U, S} (fun _ v => KPTrue (v h) (v w) (v M) (v U) (v S)) := by
  set m := h + w + M + U + S + 1 with hm
  -- `d := m`
  have a1 := delta0_kpAxCode h w m hhw (by omega) (by omega)
  have a2 := delta0_kpairEmptyMem S m (by omega)
  have b3 := a1.imp a2
  have b4 := b3.ball m h (by omega)
  refine (b4.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    rfl
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢
    omega

theorem sigmaDef_admKP (h w x : ℕ) (hhw : h ≠ w) (hhx : h ≠ x) (hwx : w ≠ x) :
    SigmaDef 1 {h, w, x} (fun D v => AdmKP.{u} D (v h) (v w) (v x)) := by
  set m := h + w + x + 1 with hm
  -- `M := m`, `c := m+1`, `U := m+2`, `S := m+3`
  have hlc := delta0_lcode h w x m (m + 1) hhw hhx (by omega) (by omega) hwx (by omega)
    (by omega) (by omega) (by omega) (by omega)
  have hsc := delta0_satCode h w m (m + 2) (m + 3) hhw (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hkt := delta0_kpTrue h w m (m + 2) (m + 3) hhw (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have core := hlc.and (hsc.and hkt)
  have e1 := (core.sigma 1).ex (m + 3) le_rfl
  have e2 := e1.ex (m + 2) le_rfl
  have e3 := e2.ex (m + 1) le_rfl
  have e4 := e3.ex m le_rfl
  refine (e4.congr ?_).mono ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    simp only [AdmKP]
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union] at hk ⊢
    omega


/-! ### The empty assignment

`KPTrue` speaks of the empty assignment only, so the empty sequence has to be an assignment over
`M` and to lie in the domain `U` of the satisfaction code. -/

/-- The empty set is a (zero-length) assignment over any `A`. -/
theorem isSeqA_empty (A : ZFSet.{u}) : IsSeqA ωZ.{u} A ∅ :=
  ⟨⟨fun p hp => absurd hp (ZFSet.notMem_empty p),
      fun _ _ _ hb => absurd hb (ZFSet.notMem_empty _)⟩,
    ⟨∅, natZ_mem_ωZ 0, fun a => ⟨fun ha => absurd ha (ZFSet.notMem_empty a),
      fun ⟨_, hb⟩ => absurd hb (ZFSet.notMem_empty _)⟩⟩,
    fun _ _ hp => absurd hp (ZFSet.notMem_empty _)⟩


/-! ### `ω < η` and the limit property from the truth of the KP axioms

Definition 11.1 carries neither `ω < η` nor "`η` is a limit", so the proof of Lemma 11.2 has to
produce both from the truth of the KP axioms in `L η`.  This section is that step. -/

/-- "Every KP axiom is true in `L η` under every valuation into `L η`" — the `hall` hypothesis of
`isAdmissible_of_kpTrue`. -/
def KPSatL (η : Ordinal.{u}) : Prop :=
  ∀ φ : Fm, KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} φ) →
    ∀ v : ℕ → ZFSet.{u}, (∀ n, v n ∈ L η) → SatIn (L η) v φ

/-- The infinity axiom, unpacked: `L η` contains a non-empty set with no ∈-maximal element. -/
theorem infAx_content {η : Ordinal.{u}} (hemp : (∅ : ZFSet.{u}) ∈ L η) (hall : KPSatL.{u} η) :
    ∃ x ∈ L η, (∃ u, u ∈ x) ∧ ∀ u ∈ x, ∃ z ∈ x, u ∈ z := by
  have hT := L_transitive η
  have h := hall infAx kpAxCode_inf (fun _ => ∅) (fun _ => hemp)
  simp only [infAx, SatIn] at h
  obtain ⟨x, hxL, hx⟩ := sat_ex.mp h
  obtain ⟨hne, hstep⟩ := sat_and.mp hx
  obtain ⟨u0, hu0L, hu0⟩ := sat_ex.mp hne
  simp (disch := omega) only [sat_mem, Function.update_self, Function.update_of_ne] at hu0
  refine ⟨x, hxL, ⟨u0, hu0⟩, ?_⟩
  rw [sat_ball_of_ne (show (1 : ℕ) ≠ 0 by decide)] at hstep
  intro u hu
  have h1 := hstep u (hT.subset_of_mem hxL hu)
    (by simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hu)
  rw [sat_bex_of_ne (show (2 : ℕ) ≠ 0 by decide)] at h1
  obtain ⟨z, hzL, hzx, hz⟩ := h1
  simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hzx
  simp (disch := omega) only [sat_mem, Function.update_self, Function.update_of_ne] at hz
  exact ⟨z, hzx, hz⟩

/-- **`ω < η`.**  The witness of the infinity axiom in `L η` has no ∈-maximal element, hence has
elements of arbitrarily large finite rank, hence rank `≥ ω`; and its rank is `< η`. -/
theorem omega_lt_of_kpTrue {η : Ordinal.{u}} (hpos : (0 : Ordinal.{u}) < η)
    (hall : KPSatL.{u} η) : Ordinal.omega0 < η := by
  obtain ⟨x, hxL, ⟨u0, hu0⟩, hstep⟩ := infAx_content (empty_mem_L hpos) hall
  have key : ∀ n : ℕ, ∃ u ∈ x, (n : Ordinal.{u}) ≤ u.rank := by
    intro n
    induction n with
    | zero => exact ⟨u0, hu0, by simp⟩
    | succ n ih =>
      obtain ⟨u, hu, hun⟩ := ih
      obtain ⟨z, hz, huz⟩ := hstep u hu
      refine ⟨z, hz, ?_⟩
      have hlt : u.rank < z.rank := ZFSet.rank_lt_of_mem huz
      have hle : ((n : Ordinal.{u}) + 1) ≤ z.rank := Order.add_one_le_iff.mpr (hun.trans_lt hlt)
      simpa [Nat.cast_succ] using hle
  have hrank : ∀ n : ℕ, (n : Ordinal.{u}) ≤ x.rank := by
    intro n
    obtain ⟨u, hu, hun⟩ := key n
    exact hun.trans (ZFSet.rank_lt_of_mem hu).le
  exact (Ordinal.omega0_le.mpr hrank).trans_lt (rank_lt_of_mem_L hxL)

/-- The pairing axiom, unpacked. -/
theorem pairAx_content {η : Ordinal.{u}} (hemp : (∅ : ZFSet.{u}) ∈ L η) (hall : KPSatL.{u} η) :
    ∀ a ∈ L η, ∀ b ∈ L η, ∃ z ∈ L η, a ∈ z ∧ b ∈ z := by
  have h := hall pairAx kpAxCode_pair (fun _ => ∅) (fun _ => hemp)
  simp only [pairAx, SatIn, sat_all, sat_ex, sat_and, sat_mem] at h
  intro a ha b hb
  obtain ⟨z, hzL, h1, h2⟩ := h a ha b hb
  simp (disch := omega) only [Function.update_self, Function.update_of_ne] at h1 h2
  exact ⟨z, hzL, h1, h2⟩

/-- The union axiom, unpacked. -/
theorem unionAx_content {η : Ordinal.{u}} (hemp : (∅ : ZFSet.{u}) ∈ L η) (hall : KPSatL.{u} η) :
    ∀ A ∈ L η, ∃ Y ∈ L η, ∀ u ∈ A, ∀ t ∈ u, t ∈ Y := by
  have hT := L_transitive η
  have h := hall unionAx kpAxCode_union (fun _ => ∅) (fun _ => hemp)
  simp only [unionAx, SatIn, sat_all] at h
  intro A hA
  obtain ⟨Y, hYL, hY⟩ := sat_ex.mp (h A hA)
  refine ⟨Y, hYL, ?_⟩
  rw [sat_ball_of_ne (show (2 : ℕ) ≠ 0 by decide)] at hY
  intro u hu t ht
  have huL : u ∈ L η := hT.subset_of_mem hA hu
  have h1 := hY u huL
    (by simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using hu)
  rw [sat_ball_of_ne (show (3 : ℕ) ≠ 2 by decide)] at h1
  have h2 := h1 t (hT.subset_of_mem huL ht)
    (by simpa (disch := omega) only [Function.update_self, Function.update_of_ne] using ht)
  simpa (disch := omega) only [sat_mem, Function.update_self, Function.update_of_ne] using h2

/-- Δ₀-separation, unpacked, for an instance formula in the two variables `0` (the element being
separated) and `1` (the parameter).  Such an instance is a *sentence*, so no hypothesis on the
valuation is needed. -/
theorem sepAx_content {η : Ordinal.{u}} (hemp : (∅ : ZFSet.{u}) ∈ L η) (hall : KPSatL.{u} η)
    {φ : Fm} (hφ : Fm.IsDelta0 φ) (hvars : ∀ k ∈ Fm.vars φ, k < 2) :
    ∀ p ∈ L η, ∀ A ∈ L η, ∃ B ∈ L η, ∀ t ∈ L η,
      (t ∈ B ↔ t ∈ A ∧ SatIn (L η) (fun n => if n = 0 then t else p) φ) := by
  -- `sepAx φ 0 1 2 3` is already a sentence here, but the recognizer asks for a closure, so we
  -- take the (in fact redundant) closure over its free variables and strip it again
  have hcode : KPAxCode (L Ordinal.omega0) ωZ
      (Fm.code.{u} (Fm.alls (Fm.fv (sepAx φ 0 1 2 3)).toList (sepAx φ 0 1 2 3))) :=
    kpAxCode_sep hφ (notFree_of_vars_lt hvars (by omega))
      (notFree_of_vars_lt hvars (by omega))
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      _ (subset_toList_toFinset _)
  have h := sat_of_alls (D := (· ∈ L η)) (fun _ => hemp)
    (hall _ hcode (fun _ => ∅) (fun _ => hemp))
  simp only [sepAx, sat_all, sat_ex, sat_iff, sat_and, sat_mem] at h
  intro p hp A hA
  obtain ⟨B, hBL, hB⟩ := h p hp A hA
  refine ⟨B, hBL, ?_⟩
  intro t ht
  have hBt := hB t ht
  simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hBt
  rw [hBt]
  refine and_congr Iff.rfl (sat_congr ?_)
  intro k hk
  have hk2 : k < 2 := hvars k (Fm.fv_subset_vars φ hk)
  interval_cases k <;>
    simp (disch := omega) only [Function.update_self, Function.update_of_ne] <;> simp

/-- **`η` is a limit.**  For `ζ < η`: pairing gives a set containing `ζ`, separation cuts it down
to `{ζ}`, pairing and union give a set containing `ζ ∪ {ζ}`, and separation cuts that down to
`ζ ∪ {ζ} = (ζ+1)ᶻ`; hence `ζ + 1 < η`.  `η ≠ 0` comes from `ω < η`. -/
theorem isSuccLimit_of_kpTrue {η : Ordinal.{u}} (hpos : (0 : Ordinal.{u}) < η)
    (hall : KPSatL.{u} η) : Order.IsSuccLimit η := by
  have hemp : (∅ : ZFSet.{u}) ∈ L η := empty_mem_L hpos
  have hT := L_transitive η
  have hω := omega_lt_of_kpTrue hpos hall
  rw [Ordinal.isSuccLimit_iff]
  refine ⟨(Ordinal.omega0_pos.trans hω).ne', Order.isSuccPrelimit_iff_succ_lt.mpr ?_⟩
  intro ξ hξ
  rw [Order.succ_eq_add_one, ← toZFSet_mem_L_iff, Ordinal.toZFSet_add_one]
  have hcL : ξ.toZFSet ∈ L η := (toZFSet_mem_L_iff η ξ).mpr hξ
  set c : ZFSet.{u} := ξ.toZFSet with hc
  -- step 1: `{c} ∈ L η`
  obtain ⟨z, hzL, hcz, -⟩ := pairAx_content hemp hall c hcL c hcL
  obtain ⟨B, hBL, hB⟩ :=
    sepAx_content hemp hall (Fm.IsDelta0.eq 0 1) (by decide) c hcL z hzL
  have hBeq : B = ({c} : ZFSet.{u}) := by
    ext t
    rw [ZFSet.mem_singleton]
    constructor
    · intro htB
      have h1 := (hB t (hT.subset_of_mem hBL htB)).mp htB
      simpa using h1.2
    · rintro rfl
      exact (hB c hcL).mpr ⟨hcz, by simp⟩
  rw [hBeq] at hBL
  -- step 2: a set `Y` containing `c ∪ {c}`
  obtain ⟨z2, hz2L, hcz2, hscz2⟩ := pairAx_content hemp hall c hcL ({c} : ZFSet.{u}) hBL
  obtain ⟨Y, hYL, hY⟩ := unionAx_content hemp hall z2 hz2L
  have hsub : ∀ t, t ∈ insert c c → t ∈ Y := by
    intro t ht
    rw [ZFSet.mem_insert_iff] at ht
    rcases ht with rfl | ht
    · exact hY _ hscz2 _ (ZFSet.mem_singleton.mpr rfl)
    · exact hY _ hcz2 _ ht
  -- step 3: separate `c ∪ {c}` out of `Y`
  obtain ⟨B2, hB2L, hB2⟩ := sepAx_content hemp hall
    ((Fm.IsDelta0.mem 0 1).or (Fm.IsDelta0.eq 0 1)) (by decide) c hcL Y hYL
  have hB2eq : B2 = insert c c := by
    ext t
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro htB
      have h1 := (hB2 t (hT.subset_of_mem hB2L htB)).mp htB
      have h2 := h1.2
      simp only [SatIn, sat_or, sat_mem, sat_eq] at h2
      simpa using h2.symm
    · intro ht
      have htY : t ∈ Y := hsub t (ZFSet.mem_insert_iff.mpr ht)
      have htL : t ∈ L η := by
        rcases ht with rfl | ht
        · exact hcL
        · exact hT.subset_of_mem hcL ht
      refine (hB2 t htL).mpr ⟨htY, ?_⟩
      simp only [SatIn, sat_or, sat_mem, sat_eq]
      simpa using ht.symm
  rw [hB2eq] at hB2L
  exact hB2L


/-! ### Lemma 11.2: correctness inside an admissible `L θ` -/

/-- **Lemma 11.2**: `AdmKP` is correct inside an admissible `L θ`. -/
theorem admKP_iff {θ η : Ordinal.{u}} (hθ : IsAdmissible θ) (hη : η < θ) :
    AdmKP (· ∈ L θ) (L Ordinal.omega0.{u}) ωZ.{u} η.toZFSet ↔ IsAdmissible η := by
  constructor
  · rintro ⟨M, hM, c, hcM, U, hU, S, hS, hlc, hsat, hkp⟩
    have hMeq : M = L η := lcode_sound hlc
    subst hMeq
    have hUcl : ∀ q : ZFSet.{u}, IsSeqA ωZ (L η) q → q ∈ U :=
      fun _ hq => seq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl hq
    have h0seq : IsSeqA ωZ.{u} (L η) ∅ := isSeqA_empty _
    have h0U : (∅ : ZFSet.{u}) ∈ U := hUcl ∅ h0seq
    -- the recognised codes are sentences, so the empty assignment is appropriate for them
    have hsent : ∀ φ : Fm, KPAxCode (L Ordinal.omega0) ωZ (Fm.code.{u} φ) →
        SatIn (L η) (SeqVal ∅) φ := by
      intro φ hc
      have hfv : Fm.fv φ = ∅ := fv_eq_empty_of_kpAxCode hc rfl
      have hcov : ∀ k ∈ Fm.fv φ, InDomZ (∅ : ZFSet.{u}) (natZ k) :=
        fun k hk => absurd (hfv ▸ hk) (Finset.notMem_empty k)
      have hmem := hkp (Fm.code.{u} φ) (Fm.code_mem_Lω φ) hc
      rw [satCode_correct hsat φ ∅ h0seq hcov h0U] at hmem
      exact hmem
    have hpos : (0 : Ordinal.{u}) < η := by
      rcases eq_or_ne η 0 with rfl | hne
      · have hmem := hsent infAx kpAxCode_inf
        simp only [infAx, SatIn] at hmem
        obtain ⟨x, hxL, -⟩ := sat_ex.mp hmem
        rw [L_zero] at hxL
        exact absurd hxL (ZFSet.notMem_empty _)
      · exact pos_iff_ne_zero.mpr hne
    have hall : KPSatL.{u} η := by
      intro φ hc v hv
      have hfv : Fm.fv φ = ∅ := fv_eq_empty_of_kpAxCode hc rfl
      exact (sat_congr (fun k hk => absurd (hfv ▸ hk) (Finset.notMem_empty k))).mp (hsent φ hc)
    exact isAdmissible_of_kpTrue (omega_lt_of_kpTrue hpos hall)
      (isSuccLimit_of_kpTrue hpos hall) hall
  · intro hadm
    have hpos : (0 : Ordinal.{u}) < η := hadm.pos
    have hemp : (∅ : ZFSet.{u}) ∈ L η := empty_mem_L hpos
    obtain ⟨M0, hM0, c0, hc0, hlc⟩ := lcode_exists_in_L hθ hη
    have hMeq : M0 = L η := lcode_sound hlc
    subst hMeq
    obtain ⟨U, hU, S, hS, hsat⟩ :=
      satCode_exists_in_L hθ (L_mem_L hη)
    have h0seq : IsSeqA ωZ.{u} (L η) ∅ := isSeqA_empty _
    have h0U : (∅ : ZFSet.{u}) ∈ U :=
      seq_mem_of_puCl hsat.trans hsat.A_mem hsat.w_mem hsat.pucl h0seq
    refine ⟨L η, L_mem_L hη, c0, hc0, U, hU, S, hS, hlc, hsat, ?_⟩
    intro d hd hdcode
    obtain ⟨φ, rfl⟩ := exists_fm_of_kpAxCode hdcode
    have hfv : Fm.fv φ = ∅ := fv_eq_empty_of_kpAxCode hdcode rfl
    have hcov : ∀ k ∈ Fm.fv φ, InDomZ (∅ : ZFSet.{u}) (natZ k) :=
      fun k hk => absurd (hfv ▸ hk) (Finset.notMem_empty k)
    rw [satCode_correct hsat φ ∅ h0seq hcov h0U]
    exact satIn_kpAx hadm hdcode φ rfl (SeqVal ∅) (fun n => seqVal_mem h0seq hemp n)

end BM4.ST
