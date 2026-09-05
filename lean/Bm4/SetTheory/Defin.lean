/-
  Part III: a shallow embedding of Lévy definability. A predicate on (domain, valuation) pairs is
  Δ₀ / Σ̂q / Π̂q definable if some formula of that class expresses it over every nonempty
  transitive domain. Closure lemmas replace the paper's "this is obviously Δ₀" claims.
-/
import Bm4.SetTheory.Fm

universe u

namespace BM4.ST

open Fm

/-- Predicates on (domain, valuation). -/
abbrev Pred := (ZFSet.{u} → Prop) → (ℕ → ZFSet.{u}) → Prop

/-- Nonempty transitive domains. -/
def GoodDom (D : ZFSet.{u} → Prop) : Prop := (∃ x, D x) ∧ TransDom D

theorem goodDom_univ : GoodDom (fun _ : ZFSet.{u} => True) := ⟨⟨∅, trivial⟩, transDom_univ⟩

theorem goodDom_mem {W : ZFSet.{u}} (hW : W.IsTransitive) (hne : ∃ x, x ∈ W) : GoodDom (· ∈ W) :=
  ⟨hne, transDom_mem hW⟩

/-- The valuation takes values in `D` on `s`. -/
def ValD (D : ZFSet.{u} → Prop) (s : Finset ℕ) (v : ℕ → ZFSet.{u}) : Prop := ∀ i ∈ s, D (v i)

theorem ValD.mono {D : ZFSet.{u} → Prop} {s t : Finset ℕ} (h : s ⊆ t) {v : ℕ → ZFSet.{u}}
    (hv : ValD D t v) : ValD D s v := fun i hi => hv i (h hi)

theorem ValD.update {D : ZFSet.{u} → Prop} {s : Finset ℕ} {v : ℕ → ZFSet.{u}} {i : ℕ}
    (hv : ValD D (s.erase i) v) {x : ZFSet.{u}} (hx : D x) : ValD D s (Function.update v i x) := by
  intro k hk
  by_cases hki : k = i
  · subst hki; simpa
  · rw [Function.update_of_ne hki]; exact hv k (Finset.mem_erase.mpr ⟨hki, hk⟩)

/-- Δ₀-definability with support `s`. -/
def Delta0Def (s : Finset ℕ) (P : Pred.{u}) : Prop :=
  ∃ φ : Fm, IsDelta0 φ ∧ fv φ ⊆ s ∧
    ∀ D v, GoodDom D → ValD D s v → (Sat D v φ ↔ P D v)

/-- Σ̂q-definability with support `s`. -/
def SigmaDef (q : ℕ) (s : Finset ℕ) (P : Pred.{u}) : Prop :=
  ∃ φ : Fm, IsSigma q φ ∧ fv φ ⊆ s ∧
    ∀ D v, GoodDom D → ValD D s v → (Sat D v φ ↔ P D v)

/-- Π̂q-definability with support `s`. -/
def PiDef (q : ℕ) (s : Finset ℕ) (P : Pred.{u}) : Prop :=
  ∃ φ : Fm, IsPi q φ ∧ fv φ ⊆ s ∧
    ∀ D v, GoodDom D → ValD D s v → (Sat D v φ ↔ P D v)

/-! ### Basic closure -/

namespace Delta0Def

variable {s t : Finset ℕ} {P Q : Pred.{u}}

theorem congr (h : Delta0Def s P) (hPQ : ∀ D v, GoodDom D → ValD D s v → (P D v ↔ Q D v)) :
    Delta0Def s Q := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  exact ⟨φ, hφ, hfv, fun D v hD hv => (hsat D v hD hv).trans (hPQ D v hD hv)⟩

theorem mono (h : Delta0Def s P) (hst : s ⊆ t) : Delta0Def t P := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  exact ⟨φ, hφ, hfv.trans hst, fun D v hD hv => hsat D v hD (hv.mono hst)⟩

theorem falsum : Delta0Def ∅ (fun _ _ => False) :=
  ⟨Fm.falsum, IsDelta0.falsum, by simp [fv], fun _ _ _ _ => Iff.rfl⟩

theorem top : Delta0Def ∅ (fun _ _ => True) :=
  ⟨Fm.top, IsDelta0.top, by simp [Fm.top, Fm.not, fv], fun _ _ _ _ => by simp⟩

theorem mem (i j : ℕ) : Delta0Def {i, j} (fun _ v => v i ∈ v j) :=
  ⟨Fm.mem i j, IsDelta0.mem i j, by simp [fv], fun _ _ _ _ => Iff.rfl⟩

theorem eq (i j : ℕ) : Delta0Def {i, j} (fun _ v => v i = v j) :=
  ⟨Fm.eq i j, IsDelta0.eq i j, by simp [fv], fun _ _ _ _ => Iff.rfl⟩

theorem imp (hP : Delta0Def s P) (hQ : Delta0Def t Q) :
    Delta0Def (s ∪ t) (fun D v => P D v → Q D v) := by
  obtain ⟨φ, hφ, hfvφ, hφs⟩ := hP
  obtain ⟨ψ, hψ, hfvψ, hψs⟩ := hQ
  refine ⟨Fm.imp φ ψ, hφ.imp hψ, by simp only [fv]; exact Finset.union_subset_union hfvφ hfvψ, ?_⟩
  intro D v hD hv
  rw [sat_imp, hφs D v hD (hv.mono Finset.subset_union_left),
    hψs D v hD (hv.mono Finset.subset_union_right)]

theorem not (hP : Delta0Def s P) : Delta0Def s (fun D v => ¬ P D v) := by
  have := hP.imp falsum
  rwa [Finset.union_empty] at this

theorem and (hP : Delta0Def s P) (hQ : Delta0Def t Q) :
    Delta0Def (s ∪ t) (fun D v => P D v ∧ Q D v) :=
  (hP.imp hQ.not).not.congr (fun _ _ _ _ => by tauto)

theorem or (hP : Delta0Def s P) (hQ : Delta0Def t Q) :
    Delta0Def (s ∪ t) (fun D v => P D v ∨ Q D v) :=
  (hP.not.imp hQ).congr (fun _ _ _ _ => by tauto)

theorem iff (hP : Delta0Def s P) (hQ : Delta0Def t Q) :
    Delta0Def (s ∪ t) (fun D v => P D v ↔ Q D v) :=
  (((hP.imp hQ).and (hQ.imp hP)).congr (fun _ _ _ _ => by tauto)).mono (by
    intro x hx; simp only [Finset.mem_union] at hx ⊢; tauto)

/-- Bounded universal quantification `∀ i ∈ j, Q`. -/
theorem ball (i j : ℕ) (hij : i ≠ j) (hQ : Delta0Def s Q) :
    Delta0Def (insert j (s.erase i)) (fun D v => ∀ x ∈ v j, Q D (Function.update v i x)) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hQ
  refine ⟨Fm.ball i j φ, IsDelta0.ball hij hφ, ?_, ?_⟩
  · rw [fv_ball]
    intro x hx
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
    rcases hx with ⟨hxi, (rfl | rfl) | hx⟩
    · exact absurd rfl hxi
    · exact Or.inl rfl
    · exact Or.inr ⟨hxi, hfv hx⟩
  · intro D v hD hv
    rw [sat_ball_of_ne hij]
    have hvj : D (v j) := hv j (by simp)
    constructor
    · intro H x hx
      rw [← hsat D _ hD (ValD.update (hv.mono (Finset.subset_insert _ _)) (hD.2 _ hvj x hx))]
      exact H x (hD.2 _ hvj x hx) hx
    · intro H x hxD hx
      rw [hsat D _ hD (ValD.update (hv.mono (Finset.subset_insert _ _)) hxD)]
      exact H x hx

/-- Bounded existential quantification `∃ i ∈ j, Q`. -/
theorem bex (i j : ℕ) (hij : i ≠ j) (hQ : Delta0Def s Q) :
    Delta0Def (insert j (s.erase i)) (fun D v => ∃ x ∈ v j, Q D (Function.update v i x)) :=
  (ball i j hij hQ.not).not.congr (fun _ _ _ _ => by push Not; rfl)

/-- Definable predicates only depend on the values of the support. -/
theorem congr_val (h : Delta0Def s P) {D : ZFSet.{u} → Prop} (hD : GoodDom D) {v w : ℕ → ZFSet.{u}}
    (hv : ValD D s v) (hw : ValD D s w) (hvw : ∀ i ∈ s, v i = w i) : P D v ↔ P D w := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  rw [← hsat D v hD hv, ← hsat D w hD hw]
  exact sat_congr (fun x hx => hvw x (hfv hx))

/-- Δ₀ predicates are absolute: their value does not depend on the (good) domain. -/
theorem absolute (hP : Delta0Def s P) {D : ZFSet.{u} → Prop} (hD : GoodDom D) {v : ℕ → ZFSet.{u}}
    (hv : ValD D s v) : P D v ↔ P (fun _ => True) v := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  rw [← hsat D v hD hv, ← hsat _ v goodDom_univ (fun _ _ => trivial)]
  exact hφ.sat_iff_satV hD.2 (fun x hx => hv x (hfv hx))

end Delta0Def

/-! ### Σ̂ / Π̂ closure -/

theorem Delta0Def.sigma {s : Finset ℕ} {P : Pred.{u}} (h : Delta0Def s P) (q : ℕ) : SigmaDef q s P := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  obtain ⟨φ', hφ', hfv', hequiv⟩ := (IsSigma.zero hφ).pad (Nat.zero_le q)
  exact ⟨φ', hφ', hfv'.symm ▸ hfv, fun D v hD hv => (hequiv D v hD.1).trans (hsat D v hD hv)⟩

theorem Delta0Def.pi {s : Finset ℕ} {P : Pred.{u}} (h : Delta0Def s P) (q : ℕ) : PiDef q s P := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  obtain ⟨φ', hφ', hfv', hequiv⟩ := (IsPi.zero hφ).pad (Nat.zero_le q)
  exact ⟨φ', hφ', hfv'.symm ▸ hfv, fun D v hD hv => (hequiv D v hD.1).trans (hsat D v hD hv)⟩

namespace SigmaDef

variable {q : ℕ} {s t : Finset ℕ} {P Q : Pred.{u}}

theorem congr (h : SigmaDef q s P) (hPQ : ∀ D v, GoodDom D → ValD D s v → (P D v ↔ Q D v)) :
    SigmaDef q s Q := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  exact ⟨φ, hφ, hfv, fun D v hD hv => (hsat D v hD hv).trans (hPQ D v hD hv)⟩

theorem mono (h : SigmaDef q s P) (hst : s ⊆ t) : SigmaDef q t P := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  exact ⟨φ, hφ, hfv.trans hst, fun D v hD hv => hsat D v hD (hv.mono hst)⟩

theorem congr_val (h : SigmaDef q s P) {D : ZFSet.{u} → Prop} (hD : GoodDom D) {v w : ℕ → ZFSet.{u}}
    (hv : ValD D s v) (hw : ValD D s w) (hvw : ∀ i ∈ s, v i = w i) : P D v ↔ P D w := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  rw [← hsat D v hD hv, ← hsat D w hD hw]
  exact sat_congr (fun x hx => hvw x (hfv hx))

theorem pad (h : SigmaDef q s P) {q' : ℕ} (hq : q ≤ q') : SigmaDef q' s P := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  obtain ⟨φ', hφ', hfv', hequiv⟩ := hφ.pad hq
  exact ⟨φ', hφ', hfv'.symm ▸ hfv, fun D v hD hv => (hequiv D v hD.1).trans (hsat D v hD hv)⟩

theorem and (hP : SigmaDef q s P) (hQ : SigmaDef q t Q) :
    SigmaDef q (s ∪ t) (fun D v => P D v ∧ Q D v) := by
  obtain ⟨φ, hφ, hfvφ, hφs⟩ := hP
  obtain ⟨ψ, hψ, hfvψ, hψs⟩ := hQ
  obtain ⟨χ, hχ, hfvχ, hsat⟩ := hφ.and_exists hψ
  refine ⟨χ, hχ, by rw [hfvχ]; exact Finset.union_subset_union hfvφ hfvψ, ?_⟩
  intro D v hD hv
  rw [hsat D v hD.1, hφs D v hD (hv.mono Finset.subset_union_left),
    hψs D v hD (hv.mono Finset.subset_union_right)]

theorem not (hP : SigmaDef q s P) : PiDef q s (fun D v => ¬ P D v) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  obtain ⟨ψ, hψ, hfvψ, hequiv⟩ := hφ.exists_neg
  exact ⟨ψ, hψ, hfvψ.symm ▸ hfv, fun D v hD hv => (hequiv D v).trans (by rw [hsat D v hD hv])⟩

/-- Unbounded existential quantification keeps Σ̂q for `q ≥ 1`. -/
theorem ex (i : ℕ) (hq : 1 ≤ q) (hP : SigmaDef q s P) :
    SigmaDef q (s.erase i) (fun D v => ∃ x, D x ∧ P D (Function.update v i x)) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  cases hφ with
  | zero => omega
  | @succ q' l hl hnd ψ hψ =>
    by_cases hil : i ∈ l
    · -- `i` already occurs in the block, so prefixing it would violate Definition 12.1;
      -- but then `i` is not free and the extra quantifier is vacuous over a nonempty domain.
      have hi : i ∉ fv (exs l ψ) := notMem_fv_exs_of_mem hil
      refine ⟨exs l ψ, IsSigma.succ l hl hnd hψ, ?_, ?_⟩
      · intro x hx
        exact Finset.mem_erase.mpr ⟨fun h => hi (h ▸ hx), hfv hx⟩
      · intro D v hD hv
        constructor
        · intro h
          obtain ⟨x₀, hx₀⟩ := hD.1
          exact ⟨x₀, hx₀, (hsat D _ hD (hv.update hx₀)).mp
            ((sat_update_of_notMem (v := v) hi x₀).mpr h)⟩
        · rintro ⟨x, hx, h⟩
          exact (sat_update_of_notMem (v := v) hi x).mp ((hsat D _ hD (hv.update hx)).mpr h)
    · refine ⟨exs (i :: l) _, IsSigma.succ (i :: l) (by simp)
        (List.nodup_cons.mpr ⟨hil, hnd⟩) hψ, ?_, ?_⟩
      · intro x hx
        rw [fv_exs] at hx
        simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons, not_or] at hx
        rw [fv_exs] at hfv
        exact Finset.mem_erase.mpr
          ⟨hx.2.1, hfv (Finset.mem_sdiff.mpr ⟨hx.1, by simpa using hx.2.2⟩)⟩
      · intro D v hD hv
        rw [exs_cons, sat_ex]
        apply exists_congr; intro x; apply and_congr_right; intro hx
        exact hsat D _ hD (hv.update hx)

end SigmaDef

namespace PiDef

variable {q : ℕ} {s t : Finset ℕ} {P Q : Pred.{u}}

theorem congr (h : PiDef q s P) (hPQ : ∀ D v, GoodDom D → ValD D s v → (P D v ↔ Q D v)) :
    PiDef q s Q := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  exact ⟨φ, hφ, hfv, fun D v hD hv => (hsat D v hD hv).trans (hPQ D v hD hv)⟩

theorem mono (h : PiDef q s P) (hst : s ⊆ t) : PiDef q t P := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  exact ⟨φ, hφ, hfv.trans hst, fun D v hD hv => hsat D v hD (hv.mono hst)⟩

theorem congr_val (h : PiDef q s P) {D : ZFSet.{u} → Prop} (hD : GoodDom D) {v w : ℕ → ZFSet.{u}}
    (hv : ValD D s v) (hw : ValD D s w) (hvw : ∀ i ∈ s, v i = w i) : P D v ↔ P D w := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  rw [← hsat D v hD hv, ← hsat D w hD hw]
  exact sat_congr (fun x hx => hvw x (hfv hx))

theorem pad (h : PiDef q s P) {q' : ℕ} (hq : q ≤ q') : PiDef q' s P := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := h
  obtain ⟨φ', hφ', hfv', hequiv⟩ := hφ.pad hq
  exact ⟨φ', hφ', hfv'.symm ▸ hfv, fun D v hD hv => (hequiv D v hD.1).trans (hsat D v hD hv)⟩

theorem and (hP : PiDef q s P) (hQ : PiDef q t Q) :
    PiDef q (s ∪ t) (fun D v => P D v ∧ Q D v) := by
  obtain ⟨φ, hφ, hfvφ, hφs⟩ := hP
  obtain ⟨ψ, hψ, hfvψ, hψs⟩ := hQ
  obtain ⟨χ, hχ, hfvχ, hsat⟩ := hφ.and_exists hψ
  refine ⟨χ, hχ, by rw [hfvχ]; exact Finset.union_subset_union hfvφ hfvψ, ?_⟩
  intro D v hD hv
  rw [hsat D v hD.1, hφs D v hD (hv.mono Finset.subset_union_left),
    hψs D v hD (hv.mono Finset.subset_union_right)]

theorem not (hP : PiDef q s P) : SigmaDef q s (fun D v => ¬ P D v) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  obtain ⟨ψ, hψ, hfvψ, hequiv⟩ := hφ.exists_neg
  exact ⟨ψ, hψ, hfvψ.symm ▸ hfv, fun D v hD hv => (hequiv D v).trans (by rw [hsat D v hD hv])⟩

/-- Unbounded universal quantification keeps Π̂q for `q ≥ 1`. -/
theorem all (i : ℕ) (hq : 1 ≤ q) (hP : PiDef q s P) :
    PiDef q (s.erase i) (fun D v => ∀ x, D x → P D (Function.update v i x)) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  cases hφ with
  | zero => omega
  | @succ q' l hl hnd ψ hψ =>
    by_cases hil : i ∈ l
    · have hi : i ∉ fv (alls l ψ) := notMem_fv_alls_of_mem hil
      refine ⟨alls l ψ, IsPi.succ l hl hnd hψ, ?_, ?_⟩
      · intro x hx
        exact Finset.mem_erase.mpr ⟨fun h => hi (h ▸ hx), hfv hx⟩
      · intro D v hD hv
        constructor
        · intro h x hx
          exact (hsat D _ hD (hv.update hx)).mp ((sat_update_of_notMem (v := v) hi x).mpr h)
        · intro h
          obtain ⟨x₀, hx₀⟩ := hD.1
          exact (sat_update_of_notMem (v := v) hi x₀).mp
            ((hsat D _ hD (hv.update hx₀)).mpr (h x₀ hx₀))
    · refine ⟨alls (i :: l) _, IsPi.succ (i :: l) (by simp)
        (List.nodup_cons.mpr ⟨hil, hnd⟩) hψ, ?_, ?_⟩
      · intro x hx
        rw [fv_alls] at hx
        simp only [Finset.mem_sdiff, List.mem_toFinset, List.mem_cons, not_or] at hx
        rw [fv_alls] at hfv
        exact Finset.mem_erase.mpr
          ⟨hx.2.1, hfv (Finset.mem_sdiff.mpr ⟨hx.1, by simpa using hx.2.2⟩)⟩
      · intro D v hD hv
        rw [alls_cons, sat_all]
        apply forall_congr'; intro x; apply imp_congr_right; intro hx
        exact hsat D _ hD (hv.update hx)

end PiDef

/-- `∃ i, P` with `P` Π̂q is Σ̂(q+1). -/
theorem PiDef.ex {q : ℕ} {s : Finset ℕ} {P : Pred.{u}} (i : ℕ) (hP : PiDef q s P) :
    SigmaDef (q + 1) (s.erase i) (fun D v => ∃ x, D x ∧ P D (Function.update v i x)) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  refine ⟨exs [i] φ, IsSigma.succ [i] (by simp) (by simp) hφ, ?_, ?_⟩
  · intro x hx
    rw [fv_exs] at hx
    simp only [Finset.mem_sdiff, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at hx
    exact Finset.mem_erase.mpr ⟨hx.2, hfv hx.1⟩
  · intro D v hD hv
    simp only [exs_cons, exs_nil, sat_ex]
    apply exists_congr; intro x; apply and_congr_right; intro hx
    exact hsat D _ hD (hv.update hx)

/-- `∀ i, P` with `P` Σ̂q is Π̂(q+1). -/
theorem SigmaDef.all {q : ℕ} {s : Finset ℕ} {P : Pred.{u}} (i : ℕ) (hP : SigmaDef q s P) :
    PiDef (q + 1) (s.erase i) (fun D v => ∀ x, D x → P D (Function.update v i x)) := by
  obtain ⟨φ, hφ, hfv, hsat⟩ := hP
  refine ⟨alls [i] φ, IsPi.succ [i] (by simp) (by simp) hφ, ?_, ?_⟩
  · intro x hx
    rw [fv_alls] at hx
    simp only [Finset.mem_sdiff, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
      Finset.mem_singleton] at hx
    exact Finset.mem_erase.mpr ⟨hx.2, hfv hx.1⟩
  · intro D v hD hv
    simp only [alls_cons, alls_nil, sat_all]
    apply forall_congr'; intro x; apply imp_congr_right; intro hx
    exact hsat D _ hD (hv.update hx)

theorem SigmaDef.or {q : ℕ} {s t : Finset ℕ} {P Q : Pred.{u}} (hP : SigmaDef q s P)
    (hQ : SigmaDef q t Q) : SigmaDef q (s ∪ t) (fun D v => P D v ∨ Q D v) :=
  (hP.not.and hQ.not).not.congr (fun _ _ _ _ => by tauto)

theorem PiDef.or {q : ℕ} {s t : Finset ℕ} {P Q : Pred.{u}} (hP : PiDef q s P)
    (hQ : PiDef q t Q) : PiDef q (s ∪ t) (fun D v => P D v ∨ Q D v) :=
  (hP.not.and hQ.not).not.congr (fun _ _ _ _ => by tauto)

/-- `P → Q` with `P` Π̂q and `Q` Σ̂q is Σ̂q. -/
theorem PiDef.imp_sigma {q : ℕ} {s t : Finset ℕ} {P Q : Pred.{u}} (hP : PiDef q s P)
    (hQ : SigmaDef q t Q) : SigmaDef q (s ∪ t) (fun D v => P D v → Q D v) :=
  (hP.not.or hQ).congr (fun _ _ _ _ => by tauto)

/-- `P → Q` with `P` Σ̂q and `Q` Π̂q is Π̂q. -/
theorem SigmaDef.imp_pi {q : ℕ} {s t : Finset ℕ} {P Q : Pred.{u}} (hP : SigmaDef q s P)
    (hQ : PiDef q t Q) : PiDef q (s ∪ t) (fun D v => P D v → Q D v) :=
  (hP.not.or hQ).congr (fun _ _ _ _ => by tauto)

/-- Bounded existential quantification in front of a Σ̂q predicate (`q ≥ 1`). -/
theorem SigmaDef.bex {q : ℕ} {s : Finset ℕ} {P : Pred.{u}} (i j : ℕ) (hij : i ≠ j) (hq : 1 ≤ q)
    (hP : SigmaDef q s P) :
    SigmaDef q (insert j (s.erase i)) (fun D v => ∃ x ∈ v j, P D (Function.update v i x)) := by
  have h1 : SigmaDef q (insert i (insert j (s.erase i)))
      (fun D v => v i ∈ v j ∧ P D v) := by
    have := ((Delta0Def.mem i j).sigma q).and hP
    refine this.mono ?_
    intro x hx
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase] at hx ⊢
    rcases hx with (rfl | rfl) | hx
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · by_cases hxi : x = i
      · exact Or.inl hxi
      · exact Or.inr (Or.inr ⟨hxi, hx⟩)
  have h2 := h1.ex i hq
  refine h2.congr ?_ |>.mono ?_
  · intro D v hD hv
    constructor
    · rintro ⟨x, hx, hmem, hP⟩
      refine ⟨x, ?_, hP⟩
      rwa [Function.update_self, Function.update_of_ne hij.symm] at hmem
    · rintro ⟨x, hmem, hP⟩
      have hvj : D (v j) := hv j (Finset.mem_erase.mpr ⟨hij.symm, by simp⟩)
      refine ⟨x, hD.2 _ hvj x hmem, ?_, hP⟩
      rwa [Function.update_self, Function.update_of_ne hij.symm]
  · intro x hx
    simp only [Finset.mem_erase, Finset.mem_insert] at hx ⊢
    tauto

/-- Bounded universal quantification in front of a Π̂q predicate (`q ≥ 1`). -/
theorem PiDef.ball {q : ℕ} {s : Finset ℕ} {P : Pred.{u}} (i j : ℕ) (hij : i ≠ j) (hq : 1 ≤ q)
    (hP : PiDef q s P) :
    PiDef q (insert j (s.erase i)) (fun D v => ∀ x ∈ v j, P D (Function.update v i x)) := by
  have := (hP.not.bex i j hij hq).not
  refine this.congr ?_
  intro D v hD hv
  push Not
  rfl

end BM4.ST
