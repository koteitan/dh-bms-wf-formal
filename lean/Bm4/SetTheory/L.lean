/-
  Part III, B2: the constructible hierarchy `L : Ordinal → ZFSet`, via definable power sets.
-/
import Bm4.SetTheory.Fm

open Classical

universe u

namespace BM4.ST

open Fm

/-- `X` is a subset of `M` definable over `(M, ∈)` with parameters from `M`: there are a formula
`φ`, a variable `i` and a valuation `v` (with the other free variables in `M`) such that
`X = {x ∈ M | M ⊨ φ[v, i ↦ x]}`. -/
def DefinableOver (M X : ZFSet.{u}) : Prop :=
  X ⊆ M ∧ ∃ (φ : Fm) (i : ℕ) (v : ℕ → ZFSet.{u}), (∀ j ∈ (fv φ).erase i, v j ∈ M) ∧
    ∀ x, x ∈ X ↔ x ∈ M ∧ SatIn M (Function.update v i x) φ

/-- The definable power set `Def M`. -/
noncomputable def Def (M : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (DefinableOver M) (ZFSet.powerset M)

theorem mem_Def {M X : ZFSet.{u}} : X ∈ Def M ↔ DefinableOver M X := by
  unfold Def
  rw [ZFSet.mem_sep, ZFSet.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem subset_of_mem_Def {M X : ZFSet.{u}} (h : X ∈ Def M) : X ⊆ M := (mem_Def.mp h).1

/-- `M` itself is definable over `M` (by `x = x`). -/
theorem self_mem_Def (M : ZFSet.{u}) : M ∈ Def M := by
  rw [mem_Def]
  refine ⟨subset_rfl, Fm.eq 0 0, 0, fun _ => ∅, fun j hj => by simp [fv] at hj, ?_⟩
  intro x
  simp [SatIn]

/-- Every element of a transitive `M` is definable over `M` (by `x ∈ a`). -/
theorem mem_Def_of_mem {M : ZFSet.{u}} (hM : M.IsTransitive) {a : ZFSet.{u}} (ha : a ∈ M) :
    a ∈ Def M := by
  rw [mem_Def]
  refine ⟨hM.subset_of_mem ha, Fm.mem 0 1, 0, fun _ => a, fun j hj => by simpa using ha, ?_⟩
  intro x
  simp only [SatIn, sat_mem, Function.update_self, Function.update_of_ne (show (1 : ℕ) ≠ 0 by decide)]
  exact ⟨fun h => ⟨hM.subset_of_mem ha h, h⟩, fun h => h.2⟩

theorem subset_Def {M : ZFSet.{u}} (hM : M.IsTransitive) : M ⊆ Def M :=
  fun _ ha => mem_Def_of_mem hM ha

theorem Def_transitive {M : ZFSet.{u}} (hM : M.IsTransitive) : (Def M).IsTransitive := by
  intro X hX y hy
  exact subset_Def hM (subset_of_mem_Def hX hy)

/-- The constructible hierarchy. -/
noncomputable def L (o : Ordinal.{u}) : ZFSet.{u} :=
  Ordinal.limitRecOn o ∅ (fun _ M => Def M)
    (fun o _ ih => ZFSet.sUnion (ZFSet.range (fun x : Set.Iio o => ih x.1 x.2)))

theorem L_zero : L (0 : Ordinal.{u}) = ∅ := Ordinal.limitRecOn_zero _ _ _

theorem L_succ (o : Ordinal.{u}) : L (o + 1) = Def (L o) := by
  unfold L
  rw [← Order.succ_eq_add_one, Ordinal.limitRecOn_succ]

theorem L_limit {o : Ordinal.{u}} (h : Order.IsSuccLimit o) :
    L o = ZFSet.sUnion (ZFSet.range (fun x : Set.Iio o => L x.1)) := by
  unfold L
  rw [Ordinal.limitRecOn_limit _ _ _ _ h]

theorem mem_L_limit {o : Ordinal.{u}} (h : Order.IsSuccLimit o) {x : ZFSet.{u}} :
    x ∈ L o ↔ ∃ o' < o, x ∈ L o' := by
  rw [L_limit h, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hx⟩
    rw [ZFSet.mem_range] at hy
    obtain ⟨⟨o', ho'⟩, rfl⟩ := hy
    exact ⟨o', ho', hx⟩
  · rintro ⟨o', ho', hx⟩
    exact ⟨L o', ZFSet.mem_range.mpr ⟨⟨o', ho'⟩, rfl⟩, hx⟩

theorem L_transitive (o : Ordinal.{u}) : (L o).IsTransitive := by
  induction o using Ordinal.limitRecOn with
  | zero => rw [L_zero]; exact ZFSet.isTransitive_empty
  | add_one o ih => rw [L_succ]; exact Def_transitive ih
  | limit o hlim ih =>
    intro x hx y hy
    rw [mem_L_limit hlim] at hx ⊢
    obtain ⟨o', ho', hx⟩ := hx
    exact ⟨o', ho', ih o' ho' x hx hy⟩

theorem L_subset_L_succ (o : Ordinal.{u}) : L o ⊆ L (o + 1) := by
  rw [L_succ]; exact subset_Def (L_transitive o)

theorem L_mono {o₁ o₂ : Ordinal.{u}} (h : o₁ ≤ o₂) : L o₁ ⊆ L o₂ := by
  induction o₂ using Ordinal.limitRecOn with
  | zero =>
    have : o₁ = 0 := Ordinal.le_zero.mp h
    subst this; exact fun _ hx => hx
  | add_one o ih =>
    rcases le_or_gt o₁ o with h' | h'
    · exact (ih h').trans (L_subset_L_succ o)
    · have : o₁ = o + 1 := le_antisymm h (by rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt h')
      subst this; exact fun _ hx => hx
  | limit o hlim ih =>
    rcases lt_or_eq_of_le h with h' | h'
    · intro x hx
      rw [mem_L_limit hlim]
      exact ⟨o₁, h', hx⟩
    · subst h'; exact fun _ hx => hx

theorem L_mem_L_succ (o : Ordinal.{u}) : L o ∈ L (o + 1) := by
  rw [L_succ]; exact self_mem_Def _

theorem L_mem_L {o₁ o₂ : Ordinal.{u}} (h : o₁ < o₂) : L o₁ ∈ L o₂ :=
  L_mono (by rw [← Order.succ_eq_add_one]; exact Order.succ_le_of_lt h) (L_mem_L_succ o₁)

theorem L_nonempty {o : Ordinal.{u}} (h : 0 < o) : ∃ x, x ∈ L o :=
  ⟨L 0, L_mem_L h⟩

/-! ### Ranks and ordinals in `L` -/

theorem rank_Def_le {M : ZFSet.{u}} : (Def M).rank ≤ M.rank + 1 := by
  rw [ZFSet.rank_le_iff]
  intro X hX
  exact Order.lt_succ_iff.mpr (ZFSet.rank_mono (subset_of_mem_Def hX))

theorem rank_L_le (o : Ordinal.{u}) : (L o).rank ≤ o := by
  induction o using Ordinal.limitRecOn with
  | zero => rw [L_zero]; simp
  | add_one o ih => rw [L_succ]; exact rank_Def_le.trans (add_le_add_left ih 1)
  | limit o hlim ih =>
    rw [ZFSet.rank_le_iff]
    intro x hx
    rw [mem_L_limit hlim] at hx
    obtain ⟨o', ho', hx⟩ := hx
    exact (ZFSet.rank_lt_of_mem hx).trans_le ((ih o' ho').trans ho'.le)

theorem rank_lt_of_mem_L {o : Ordinal.{u}} {x : ZFSet.{u}} (hx : x ∈ L o) : x.rank < o :=
  (ZFSet.rank_lt_of_mem hx).trans_le (rank_L_le o)

/-- The Δ₀ formula `transF x y z`: "`x` is transitive" (`∀ y ∈ x, ∀ z ∈ y, z ∈ x`). -/
def transF (x y z : ℕ) : Fm := ball y x (ball z y (Fm.mem z x))

theorem transF_delta0 {x y z : ℕ} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    IsDelta0 (transF x y z) :=
  IsDelta0.ball hxy.symm (IsDelta0.ball hyz.symm (IsDelta0.mem _ _))

theorem fv_transF (x y z : ℕ) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    fv (transF x y z) = {x} := by
  simp only [transF, fv_ball, fv]
  ext w
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hwy, (rfl | rfl) | ⟨hwz, (rfl | rfl) | (rfl | rfl)⟩⟩ <;> simp_all
  · rintro rfl; simp [hxy, hxz]

theorem satV_transF {x y z : ℕ} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (v : ℕ → ZFSet.{u}) :
    SatV v (transF x y z) ↔ (v x).IsTransitive := by
  simp only [SatV, transF]
  rw [sat_ball_of_ne hxy.symm]
  simp only [true_imp_iff]
  constructor
  · intro H a ha
    have := H a ha
    rw [sat_ball_of_ne hyz.symm] at this
    simp only [Function.update_self, true_imp_iff, sat_mem] at this
    intro b hb
    have := this b hb
    simpa only [Function.update_self, Function.update_of_ne hxz, Function.update_of_ne hxy] using this
  · intro H a ha
    rw [sat_ball_of_ne hyz.symm]
    simp only [Function.update_self, true_imp_iff, sat_mem]
    intro b hb
    simpa only [Function.update_self, Function.update_of_ne hxz, Function.update_of_ne hxy] using H a ha hb

/-- The Δ₀ formula "`0` is an ordinal": transitive with transitive elements. -/
def ordF : Fm := Fm.and (transF 0 1 2) (ball 1 0 (transF 1 2 3))

theorem ordF_delta0 : IsDelta0 ordF :=
  (transF_delta0 (by decide) (by decide) (by decide)).and
    (IsDelta0.ball (by decide) (transF_delta0 (by decide) (by decide) (by decide)))

theorem fv_ordF : fv ordF = {0} := by
  simp only [ordF, fv_and, fv_ball, fv_transF 0 1 2 (by decide) (by decide) (by decide),
    fv_transF 1 2 3 (by decide) (by decide) (by decide)]
  decide

theorem satV_ordF (v : ℕ → ZFSet.{u}) : SatV v ordF ↔ (v 0).IsOrdinal := by
  simp only [SatV, ordF, sat_and]
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  apply and_congr
  · exact satV_transF (by decide) (by decide) (by decide) v
  · rw [sat_ball_of_ne (by decide)]
    simp only [true_imp_iff]
    apply forall_congr'; intro a; apply imp_congr_right; intro _
    rw [show (Sat (fun _ => True) (Function.update v 1 a) (transF 1 2 3) ↔ _) from
      satV_transF (by decide) (by decide) (by decide) _]
    simp

/-- The ordinals in `L o` are exactly the ordinals `< o`. -/
theorem toZFSet_mem_L_iff (o ξ : Ordinal.{u}) : ξ.toZFSet ∈ L o ↔ ξ < o := by
  induction o using Ordinal.limitRecOn generalizing ξ with
  | zero => rw [L_zero]; simp
  | add_one o ih =>
    constructor
    · intro h
      have := rank_lt_of_mem_L h
      rwa [Ordinal.rank_toZFSet] at this
    · intro h
      rcases lt_or_eq_of_le (Order.lt_add_one_iff.mp h) with h' | h'
      · exact L_subset_L_succ o ((ih ξ).mpr h')
      · subst h'
        rw [L_succ, mem_Def]
        refine ⟨?_, ordF, 0, fun _ => ∅, fun j hj => by simp [fv_ordF] at hj, ?_⟩
        · intro x hx
          rw [Ordinal.mem_toZFSet_iff] at hx
          obtain ⟨a, ha, rfl⟩ := hx
          exact (ih a).mpr ha
        · intro x
          rw [Ordinal.mem_toZFSet_iff]
          constructor
          · rintro ⟨a, ha, rfl⟩
            refine ⟨(ih a).mpr ha, ?_⟩
            rw [ordF_delta0.satIn_iff_satV (L_transitive ξ), satV_ordF]
            · simpa using ZFSet.isOrdinal_toZFSet a
            · intro j hj; rw [fv_ordF] at hj; simp at hj; subst hj; simpa using (ih a).mpr ha
          · rintro ⟨hx, hsat⟩
            rw [ordF_delta0.satIn_iff_satV (L_transitive ξ), satV_ordF] at hsat
            · simp only [Function.update_self] at hsat
              exact ⟨x.rank, rank_lt_of_mem_L hx, hsat.toZFSet_rank_eq⟩
            · intro j hj; rw [fv_ordF] at hj; simp at hj; subst hj; simpa using hx
  | limit o hlim ih =>
    rw [mem_L_limit hlim]
    constructor
    · rintro ⟨o', ho', h⟩
      exact ((ih o' ho' ξ).mp h).trans ho'
    · intro h
      exact ⟨ξ + 1, hlim.add_one_lt h, (ih _ (hlim.add_one_lt h) ξ).mpr (Order.lt_add_one_iff.mpr le_rfl)⟩

end BM4.ST
