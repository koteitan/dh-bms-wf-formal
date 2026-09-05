/-
  Part III, B1: formulas of set theory with named variables, satisfaction relative to a
  domain predicate, Δ₀ formulas and absoluteness, the strict alternating block hierarchy
  Σ̂q / Π̂q (Definition 12.1), dualization and padding (Lemma 12.2).
-/
import Mathlib

universe u

namespace BM4.ST

/-- Formulas of the language `{∈}` with variables `ℕ`. -/
inductive Fm : Type
  | falsum : Fm
  | eq : ℕ → ℕ → Fm
  | mem : ℕ → ℕ → Fm
  | imp : Fm → Fm → Fm
  | all : ℕ → Fm → Fm
  deriving DecidableEq

namespace Fm

/-! ### Derived connectives -/

def not (φ : Fm) : Fm := imp φ falsum
def top : Fm := not falsum
def or (φ ψ : Fm) : Fm := imp (not φ) ψ
def and (φ ψ : Fm) : Fm := not (imp φ (not ψ))
def iff (φ ψ : Fm) : Fm := and (imp φ ψ) (imp ψ φ)
def ex (i : ℕ) (φ : Fm) : Fm := not (all i (not φ))
/-- `∀ i ∈ j, φ`. -/
def ball (i j : ℕ) (φ : Fm) : Fm := all i (imp (mem i j) φ)
/-- `∃ i ∈ j, φ`. -/
def bex (i j : ℕ) (φ : Fm) : Fm := not (ball i j (not φ))

/-! ### Satisfaction -/

/-- Satisfaction of `φ` under the valuation `v`, with quantifiers ranging over `D`.
`Sat (· ∈ W)` is satisfaction relativized to `W`; `Sat (fun _ => True)` is satisfaction in the
universe `V`. -/
def Sat (D : ZFSet.{u} → Prop) : (ℕ → ZFSet.{u}) → Fm → Prop
  | _, falsum => False
  | v, eq i j => v i = v j
  | v, mem i j => v i ∈ v j
  | v, imp φ ψ => Sat D v φ → Sat D v ψ
  | v, all i φ => ∀ x, D x → Sat D (Function.update v i x) φ

/-- Satisfaction in the universe. -/
abbrev SatV (v : ℕ → ZFSet.{u}) (φ : Fm) : Prop := Sat (fun _ => True) v φ

/-- Satisfaction in the set `W` (quantifiers relativized to `W`). -/
abbrev SatIn (W : ZFSet.{u}) (v : ℕ → ZFSet.{u}) (φ : Fm) : Prop := Sat (· ∈ W) v φ

variable {D : ZFSet.{u} → Prop} {v : ℕ → ZFSet.{u}}

@[simp] theorem sat_falsum : Sat D v falsum ↔ False := Iff.rfl
@[simp] theorem sat_eq {i j : ℕ} : Sat D v (eq i j) ↔ v i = v j := Iff.rfl
@[simp] theorem sat_mem {i j : ℕ} : Sat D v (mem i j) ↔ v i ∈ v j := Iff.rfl
@[simp] theorem sat_imp {φ ψ : Fm} : Sat D v (imp φ ψ) ↔ (Sat D v φ → Sat D v ψ) := Iff.rfl
@[simp] theorem sat_all {i : ℕ} {φ : Fm} :
    Sat D v (all i φ) ↔ ∀ x, D x → Sat D (Function.update v i x) φ := Iff.rfl
@[simp] theorem sat_not {φ : Fm} : Sat D v (not φ) ↔ ¬ Sat D v φ := Iff.rfl
@[simp] theorem sat_top : Sat D v top ↔ True := by simp [top]
@[simp] theorem sat_or {φ ψ : Fm} : Sat D v (or φ ψ) ↔ Sat D v φ ∨ Sat D v ψ := by
  simp [or]; tauto
@[simp] theorem sat_and {φ ψ : Fm} : Sat D v (and φ ψ) ↔ Sat D v φ ∧ Sat D v ψ := by
  simp [and]
@[simp] theorem sat_iff {φ ψ : Fm} : Sat D v (iff φ ψ) ↔ (Sat D v φ ↔ Sat D v ψ) := by
  simp [iff]; tauto
@[simp] theorem sat_ex {i : ℕ} {φ : Fm} :
    Sat D v (ex i φ) ↔ ∃ x, D x ∧ Sat D (Function.update v i x) φ := by
  simp [ex]
@[simp] theorem sat_ball {i j : ℕ} {φ : Fm} :
    Sat D v (ball i j φ) ↔
      ∀ x, D x → x ∈ Function.update v i x j → Sat D (Function.update v i x) φ := by
  simp [ball]
@[simp] theorem sat_bex {i j : ℕ} {φ : Fm} :
    Sat D v (bex i j φ) ↔
      ∃ x, D x ∧ x ∈ Function.update v i x j ∧ Sat D (Function.update v i x) φ := by
  simp [bex]

theorem sat_ball_of_ne {i j : ℕ} (h : i ≠ j) {φ : Fm} :
    Sat D v (ball i j φ) ↔ ∀ x, D x → x ∈ v j → Sat D (Function.update v i x) φ := by
  rw [sat_ball]
  simp [Function.update_of_ne h.symm]

theorem sat_bex_of_ne {i j : ℕ} (h : i ≠ j) {φ : Fm} :
    Sat D v (bex i j φ) ↔ ∃ x, D x ∧ x ∈ v j ∧ Sat D (Function.update v i x) φ := by
  rw [sat_bex]
  simp [Function.update_of_ne h.symm]

/-! ### Variables -/

/-- Free variables. -/
def fv : Fm → Finset ℕ
  | falsum => ∅
  | eq i j => {i, j}
  | mem i j => {i, j}
  | imp φ ψ => fv φ ∪ fv ψ
  | all i φ => (fv φ).erase i

/-- All variables (free or bound). -/
def vars : Fm → Finset ℕ
  | falsum => ∅
  | eq i j => {i, j}
  | mem i j => {i, j}
  | imp φ ψ => vars φ ∪ vars ψ
  | all i φ => insert i (vars φ)

theorem fv_subset_vars : ∀ φ : Fm, fv φ ⊆ vars φ
  | falsum => by simp [fv, vars]
  | eq i j => by simp [fv, vars]
  | mem i j => by simp [fv, vars]
  | imp φ ψ => by
    simp only [fv, vars]
    exact Finset.union_subset_union (fv_subset_vars φ) (fv_subset_vars ψ)
  | all i φ => by
    simp only [fv, vars]
    exact (Finset.erase_subset _ _).trans ((fv_subset_vars φ).trans (Finset.subset_insert _ _))

@[simp] theorem fv_not (φ : Fm) : fv (not φ) = fv φ := by simp [not, fv]
@[simp] theorem fv_and (φ ψ : Fm) : fv (and φ ψ) = fv φ ∪ fv ψ := by simp [and, not, fv]
@[simp] theorem fv_or (φ ψ : Fm) : fv (or φ ψ) = fv φ ∪ fv ψ := by simp [or, not, fv]
@[simp] theorem fv_ex (i : ℕ) (φ : Fm) : fv (ex i φ) = (fv φ).erase i := by simp [ex, not, fv]
theorem fv_ball (i j : ℕ) (φ : Fm) : fv (ball i j φ) = ({i, j} ∪ fv φ).erase i := by
  simp [ball, fv]
theorem fv_bex (i j : ℕ) (φ : Fm) : fv (bex i j φ) = ({i, j} ∪ fv φ).erase i := by
  simp [bex, ball, not, fv]

/-- Satisfaction only depends on the values of the free variables. -/
theorem sat_congr {φ : Fm} : ∀ {v w : ℕ → ZFSet.{u}}, (∀ x ∈ fv φ, v x = w x) →
    (Sat D v φ ↔ Sat D w φ) := by
  induction φ with
  | falsum => intro v w _; rfl
  | eq i j => intro v w h; simp only [sat_eq, fv] at *; rw [h i (by simp), h j (by simp)]
  | mem i j => intro v w h; simp only [sat_mem, fv] at *; rw [h i (by simp), h j (by simp)]
  | imp φ ψ ihφ ihψ =>
    intro v w h
    simp only [fv, Finset.mem_union] at h
    rw [sat_imp, sat_imp, ihφ (fun x hx => h x (Or.inl hx)), ihψ (fun x hx => h x (Or.inr hx))]
  | all i φ ih =>
    intro v w h
    simp only [sat_all]
    apply forall_congr'; intro x; apply imp_congr_right; intro _
    apply ih
    intro y hy
    by_cases hyi : y = i
    · subst hyi; simp
    · rw [Function.update_of_ne hyi, Function.update_of_ne hyi]
      exact h y (by simp [fv, Finset.mem_erase, hyi, hy])

/-- A variable not occurring in `φ` can be updated freely. -/
theorem sat_update_of_notMem {φ : Fm} {i : ℕ} (hi : i ∉ fv φ) (x : ZFSet.{u}) :
    Sat D (Function.update v i x) φ ↔ Sat D v φ :=
  sat_congr (fun y hy => Function.update_of_ne (fun h => hi (by rw [← h]; exact hy)) _ _)

/-- Vacuous quantification over a nonempty domain. -/
theorem sat_ex_of_notMem {φ : Fm} {i : ℕ} (hi : i ∉ fv φ) (hD : ∃ x, D x) :
    Sat D v (ex i φ) ↔ Sat D v φ := by
  rw [sat_ex]
  constructor
  · rintro ⟨x, _, h⟩; exact (sat_update_of_notMem hi x).mp h
  · intro h; obtain ⟨x, hx⟩ := hD; exact ⟨x, hx, (sat_update_of_notMem hi x).mpr h⟩

theorem sat_all_of_notMem {φ : Fm} {i : ℕ} (hi : i ∉ fv φ) (hD : ∃ x, D x) :
    Sat D v (all i φ) ↔ Sat D v φ := by
  rw [sat_all]
  constructor
  · intro h; obtain ⟨x, hx⟩ := hD; exact (sat_update_of_notMem hi x).mp (h x hx)
  · intro h x _; exact (sat_update_of_notMem hi x).mpr h

/-! ### Renaming -/

/-- Rename all variables (free and bound) along `f`. -/
def rename (f : ℕ → ℕ) : Fm → Fm
  | falsum => falsum
  | eq i j => eq (f i) (f j)
  | mem i j => mem (f i) (f j)
  | imp φ ψ => imp (rename f φ) (rename f ψ)
  | all i φ => all (f i) (rename f φ)

theorem sat_rename {f : ℕ → ℕ} (hf : Function.Injective f) {φ : Fm} :
    ∀ {v : ℕ → ZFSet.{u}}, Sat D v (rename f φ) ↔ Sat D (v ∘ f) φ := by
  induction φ with
  | falsum => intro v; rfl
  | eq i j => intro v; rfl
  | mem i j => intro v; rfl
  | imp φ ψ ihφ ihψ => intro v; simp only [rename, sat_imp, ihφ, ihψ]
  | all i φ ih =>
    intro v
    simp only [rename, sat_all, ih]
    apply forall_congr'; intro x; apply imp_congr_right; intro _
    rw [Function.update_comp_eq_of_injective _ hf]

theorem fv_rename (f : ℕ → ℕ) (hf : Function.Injective f) : ∀ φ : Fm, fv (rename f φ) = (fv φ).image f
  | falsum => by simp [rename, fv]
  | eq i j => by simp [rename, fv]
  | mem i j => by simp [rename, fv]
  | imp φ ψ => by simp [rename, fv, fv_rename f hf φ, fv_rename f hf ψ, Finset.image_union]
  | all i φ => by
    simp only [rename, fv, fv_rename f hf φ]
    rw [Finset.image_erase hf]

theorem vars_rename (f : ℕ → ℕ) : ∀ φ : Fm, vars (rename f φ) = (vars φ).image f
  | falsum => by simp [rename, vars]
  | eq i j => by simp [rename, vars]
  | mem i j => by simp [rename, vars]
  | imp φ ψ => by simp [rename, vars, vars_rename f φ, vars_rename f ψ, Finset.image_union]
  | all i φ => by simp [rename, vars, vars_rename f φ, Finset.image_insert]

@[simp] theorem rename_not (f : ℕ → ℕ) (φ : Fm) : rename f (not φ) = not (rename f φ) := rfl
@[simp] theorem rename_and (f : ℕ → ℕ) (φ ψ : Fm) :
    rename f (and φ ψ) = and (rename f φ) (rename f ψ) := rfl
@[simp] theorem rename_ex (f : ℕ → ℕ) (i : ℕ) (φ : Fm) :
    rename f (ex i φ) = ex (f i) (rename f φ) := rfl
@[simp] theorem rename_ball (f : ℕ → ℕ) (i j : ℕ) (φ : Fm) :
    rename f (ball i j φ) = ball (f i) (f j) (rename f φ) := rfl

/-! ### Δ₀ formulas -/

inductive IsDelta0 : Fm → Prop
  | falsum : IsDelta0 falsum
  | eq (i j : ℕ) : IsDelta0 (eq i j)
  | mem (i j : ℕ) : IsDelta0 (mem i j)
  | imp {φ ψ : Fm} : IsDelta0 φ → IsDelta0 ψ → IsDelta0 (imp φ ψ)
  | ball {i j : ℕ} (h : i ≠ j) {φ : Fm} : IsDelta0 φ → IsDelta0 (ball i j φ)

namespace IsDelta0

theorem not {φ : Fm} (h : IsDelta0 φ) : IsDelta0 (Fm.not φ) := h.imp falsum
theorem top : IsDelta0 Fm.top := falsum.not
theorem or {φ ψ : Fm} (hφ : IsDelta0 φ) (hψ : IsDelta0 ψ) : IsDelta0 (Fm.or φ ψ) := hφ.not.imp hψ
theorem and {φ ψ : Fm} (hφ : IsDelta0 φ) (hψ : IsDelta0 ψ) : IsDelta0 (Fm.and φ ψ) :=
  (hφ.imp hψ.not).not
theorem iff {φ ψ : Fm} (hφ : IsDelta0 φ) (hψ : IsDelta0 ψ) : IsDelta0 (Fm.iff φ ψ) :=
  (hφ.imp hψ).and (hψ.imp hφ)
theorem bex {i j : ℕ} (h : i ≠ j) {φ : Fm} (hφ : IsDelta0 φ) : IsDelta0 (Fm.bex i j φ) :=
  (ball h hφ.not).not

theorem rename {f : ℕ → ℕ} (hf : Function.Injective f) {φ : Fm} (h : IsDelta0 φ) :
    IsDelta0 (Fm.rename f φ) := by
  induction h with
  | falsum => exact falsum
  | eq i j => exact eq _ _
  | mem i j => exact mem _ _
  | imp _ _ ih₁ ih₂ => exact ih₁.imp ih₂
  | ball hij _ ih => exact ball (fun h => hij (hf h)) ih

end IsDelta0

/-- A transitive domain predicate. -/
def TransDom (D : ZFSet.{u} → Prop) : Prop := ∀ x, D x → ∀ y ∈ x, D y

theorem transDom_univ : TransDom (fun _ : ZFSet.{u} => True) := fun _ _ _ _ => trivial

theorem transDom_mem {W : ZFSet.{u}} (hW : W.IsTransitive) : TransDom (· ∈ W) :=
  fun _ hx _ hy => hW.subset_of_mem hx hy

/-- **Δ₀-absoluteness**: for a transitive domain `D` and a valuation of the free variables in `D`,
satisfaction over `D` and in the universe agree. -/
theorem IsDelta0.sat_iff_satV {φ : Fm} (h : IsDelta0 φ) {D : ZFSet.{u} → Prop} (hD : TransDom D) :
    ∀ {v : ℕ → ZFSet.{u}}, (∀ x ∈ fv φ, D (v x)) → (Sat D v φ ↔ SatV v φ) := by
  induction h with
  | falsum => intro v _; rfl
  | eq i j => intro v _; rfl
  | mem i j => intro v _; rfl
  | imp _ _ ih₁ ih₂ =>
    intro v hv
    simp only [fv, Finset.mem_union] at hv
    exact imp_congr (ih₁ (fun x hx => hv x (Or.inl hx))) (ih₂ (fun x hx => hv x (Or.inr hx)))
  | @ball i j hij φ _ ih =>
    intro v hv
    have hvj : D (v j) := hv j (by simp [fv_ball, hij.symm])
    simp only [SatV] at ih ⊢
    rw [sat_ball_of_ne hij, sat_ball_of_ne hij]
    constructor
    · intro H x _ hx
      have hxD : D x := hD _ hvj x hx
      rw [← ih]
      · exact H x hxD hx
      · intro y hy
        by_cases hyi : y = i
        · subst hyi; simpa
        · rw [Function.update_of_ne hyi]
          exact hv y (by simp [fv_ball, Finset.mem_erase, hyi, hy])
    · intro H x hxD hx
      rw [ih]
      · exact H x trivial hx
      · intro y hy
        by_cases hyi : y = i
        · subst hyi; simpa
        · rw [Function.update_of_ne hyi]
          exact hv y (by simp [fv_ball, Finset.mem_erase, hyi, hy])

/-- Δ₀-absoluteness for a transitive set `W`. -/
theorem IsDelta0.satIn_iff_satV {φ : Fm} (h : IsDelta0 φ) {W : ZFSet.{u}} (hW : W.IsTransitive)
    {v : ℕ → ZFSet.{u}} (hv : ∀ x ∈ fv φ, v x ∈ W) : SatIn W v φ ↔ SatV v φ :=
  h.sat_iff_satV (transDom_mem hW) hv

/-- Δ₀-absoluteness between two transitive sets `W₁ ⊆ W₂`. -/
theorem IsDelta0.satIn_iff_satIn {φ : Fm} (h : IsDelta0 φ) {W₁ W₂ : ZFSet.{u}}
    (h₁ : W₁.IsTransitive) (h₂ : W₂.IsTransitive) (h₁₂ : W₁ ⊆ W₂) {v : ℕ → ZFSet.{u}}
    (hv : ∀ x ∈ fv φ, v x ∈ W₁) : SatIn W₁ v φ ↔ SatIn W₂ v φ := by
  rw [h.satIn_iff_satV h₁ hv, h.satIn_iff_satV h₂ (fun x hx => h₁₂ (hv x hx))]

/-! ### Quantifier blocks and the alternating hierarchy (Definition 12.1) -/

/-- `∃ l, φ` for a list of variables. -/
def exs : List ℕ → Fm → Fm
  | [], φ => φ
  | i :: l, φ => ex i (exs l φ)

/-- `∀ l, φ` for a list of variables. -/
def alls : List ℕ → Fm → Fm
  | [], φ => φ
  | i :: l, φ => all i (alls l φ)

@[simp] theorem exs_nil (φ : Fm) : exs [] φ = φ := rfl
@[simp] theorem exs_cons (i : ℕ) (l : List ℕ) (φ : Fm) : exs (i :: l) φ = ex i (exs l φ) := rfl
@[simp] theorem alls_nil (φ : Fm) : alls [] φ = φ := rfl
@[simp] theorem alls_cons (i : ℕ) (l : List ℕ) (φ : Fm) : alls (i :: l) φ = all i (alls l φ) := rfl

theorem exs_append (l₁ l₂ : List ℕ) (φ : Fm) : exs (l₁ ++ l₂) φ = exs l₁ (exs l₂ φ) := by
  induction l₁ with
  | nil => rfl
  | cons i l ih => simp [ih]

theorem alls_append (l₁ l₂ : List ℕ) (φ : Fm) : alls (l₁ ++ l₂) φ = alls l₁ (alls l₂ φ) := by
  induction l₁ with
  | nil => rfl
  | cons i l ih => simp [ih]

theorem rename_exs (f : ℕ → ℕ) (l : List ℕ) (φ : Fm) :
    rename f (exs l φ) = exs (l.map f) (rename f φ) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [ih]

theorem rename_alls (f : ℕ → ℕ) (l : List ℕ) (φ : Fm) :
    rename f (alls l φ) = alls (l.map f) (rename f φ) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [rename, ih]

theorem fv_exs (l : List ℕ) (φ : Fm) : fv (exs l φ) = (fv φ) \ l.toFinset := by
  induction l with
  | nil => simp
  | cons i l ih => rw [exs_cons, fv_ex, ih]; ext x; simp <;> tauto

theorem fv_alls (l : List ℕ) (φ : Fm) : fv (alls l φ) = (fv φ) \ l.toFinset := by
  induction l with
  | nil => simp
  | cons i l ih => rw [alls_cons]; simp only [fv]; rw [ih]; ext x; simp <;> tauto

mutual
/-- Σ̂q: `q = 0` is Δ₀; `Σ̂(q+1)` is a nonempty existential block followed by a Π̂q formula. -/
inductive IsSigma : ℕ → Fm → Prop
  | zero {φ : Fm} : IsDelta0 φ → IsSigma 0 φ
  | succ {q : ℕ} (l : List ℕ) (hl : l ≠ []) (hnd : l.Nodup) {ψ : Fm} :
      IsPi q ψ → IsSigma (q + 1) (exs l ψ)
/-- Π̂q, dually. -/
inductive IsPi : ℕ → Fm → Prop
  | zero {φ : Fm} : IsDelta0 φ → IsPi 0 φ
  | succ {q : ℕ} (l : List ℕ) (hl : l ≠ []) (hnd : l.Nodup) {ψ : Fm} :
      IsSigma q ψ → IsPi (q + 1) (alls l ψ)
end

mutual
theorem IsSigma.rename {f : ℕ → ℕ} (hf : Function.Injective f) :
    ∀ {q : ℕ} {φ : Fm}, IsSigma q φ → IsSigma q (Fm.rename f φ)
  | _, _, .zero h => .zero (h.rename hf)
  | _, _, .succ l hl hnd h => by
    rw [rename_exs]
    exact .succ (l.map f) (by simpa using hl) (hnd.map hf) (IsPi.rename hf h)
theorem IsPi.rename {f : ℕ → ℕ} (hf : Function.Injective f) :
    ∀ {q : ℕ} {φ : Fm}, IsPi q φ → IsPi q (Fm.rename f φ)
  | _, _, .zero h => .zero (h.rename hf)
  | _, _, .succ l hl hnd h => by
    rw [rename_alls]
    exact .succ (l.map f) (by simpa using hl) (hnd.map hf) (IsSigma.rename hf h)
end

/-! ### Dualization (Lemma 12.2 (2)) -/

/-- Semantic equivalence in every domain. -/
def Equiv (φ ψ : Fm) : Prop := ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), Sat D v φ ↔ Sat D v ψ

theorem sat_exs_congr {χ χ' : Fm} (h : ∀ v : ℕ → ZFSet.{u}, Sat D v χ ↔ Sat D v χ') (l : List ℕ) :
    ∀ v : ℕ → ZFSet.{u}, Sat D v (exs l χ) ↔ Sat D v (exs l χ') := by
  induction l with
  | nil => exact h
  | cons i l ih =>
    intro v
    simp only [exs_cons, sat_ex]
    apply exists_congr; intro x; apply and_congr_right; intro _
    exact ih _

theorem sat_alls_congr {χ χ' : Fm} (h : ∀ v : ℕ → ZFSet.{u}, Sat D v χ ↔ Sat D v χ') (l : List ℕ) :
    ∀ v : ℕ → ZFSet.{u}, Sat D v (alls l χ) ↔ Sat D v (alls l χ') := by
  induction l with
  | nil => exact h
  | cons i l ih =>
    intro v
    simp only [alls_cons, sat_all]
    apply forall_congr'; intro x; apply imp_congr_right; intro _
    exact ih _

theorem not_sat_exs (l : List ℕ) (φ : Fm) :
    ∀ v : ℕ → ZFSet.{u}, ¬ Sat D v (exs l φ) ↔ Sat D v (alls l (not φ)) := by
  induction l with
  | nil => intro v; rfl
  | cons i l ih =>
    intro v
    simp only [exs_cons, alls_cons, sat_ex, sat_all, not_exists, not_and]
    apply forall_congr'; intro x; apply imp_congr_right; intro _
    exact ih _

theorem not_sat_alls (l : List ℕ) (φ : Fm) :
    ∀ v : ℕ → ZFSet.{u}, ¬ Sat D v (alls l φ) ↔ Sat D v (exs l (not φ)) := by
  induction l with
  | nil => intro v; rfl
  | cons i l ih =>
    intro v
    simp only [exs_cons, alls_cons, sat_ex, sat_all]
    rw [not_forall]
    apply exists_congr; intro x
    rw [_root_.not_imp]
    apply and_congr_right; intro _
    exact ih _

mutual
/-- Every Σ̂q formula has a Π̂q formula (with the same free variables) equivalent to its negation. -/
theorem IsSigma.exists_neg : ∀ {q : ℕ} {φ : Fm}, IsSigma q φ →
    ∃ ψ, IsPi q ψ ∧ fv ψ = fv φ ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), Sat D v ψ ↔ ¬ Sat D v φ
  | _, _, .zero h => ⟨_, .zero h.not, fv_not _, fun _ _ => Iff.rfl⟩
  | _, _, .succ l hl hnd h => by
    obtain ⟨χ, hχ, hfv, hequiv⟩ := IsPi.exists_neg h
    refine ⟨alls l χ, .succ l hl hnd hχ, by rw [fv_alls, fv_exs, hfv], fun D v => ?_⟩
    rw [not_sat_exs]
    exact sat_alls_congr (hequiv D) l v
/-- Every Π̂q formula has a Σ̂q formula (with the same free variables) equivalent to its negation. -/
theorem IsPi.exists_neg : ∀ {q : ℕ} {φ : Fm}, IsPi q φ →
    ∃ ψ, IsSigma q ψ ∧ fv ψ = fv φ ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), Sat D v ψ ↔ ¬ Sat D v φ
  | _, _, .zero h => ⟨_, .zero h.not, fv_not _, fun _ _ => Iff.rfl⟩
  | _, _, .succ l hl hnd h => by
    obtain ⟨χ, hχ, hfv, hequiv⟩ := IsSigma.exists_neg h
    refine ⟨exs l χ, .succ l hl hnd hχ, by rw [fv_exs, fv_alls, hfv], fun D v => ?_⟩
    rw [not_sat_alls]
    exact sat_exs_congr (hequiv D) l v
end

/-! ### Padding (Lemma 12.2 (3)) -/

/-- A variable not in `s`. -/
def fresh (s : Finset ℕ) : ℕ := if h : s.Nonempty then s.max' h + 1 else 0

theorem fresh_notMem (s : Finset ℕ) : fresh s ∉ s := by
  unfold fresh
  split_ifs with h
  · intro hmem
    have := s.le_max' _ hmem
    omega
  · intro hmem
    exact h ⟨_, hmem⟩

/-- Semantic equivalence over nonempty domains, with the same free variables. -/
def EquivNE (φ ψ : Fm) : Prop :=
  fv φ = fv ψ ∧ ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), (∃ x, D x) → (Sat D v φ ↔ Sat D v ψ)

mutual
theorem IsSigma.pad_succ : ∀ {q : ℕ} {φ : Fm}, IsSigma q φ →
    ∃ φ', IsSigma (q + 1) φ' ∧ EquivNE.{u} φ' φ
  | _, φ, .zero h =>
    ⟨ex (fresh (fv φ)) φ, .succ [fresh (fv φ)] (by simp) (by simp) (.zero h),
      by rw [fv_ex, Finset.erase_eq_of_notMem (fresh_notMem _)],
      fun D v hD => sat_ex_of_notMem (fresh_notMem _) hD⟩
  | _, _, .succ l hl hnd h => by
    obtain ⟨ψ', hψ', hfv, hequiv⟩ := IsPi.pad_succ h
    exact ⟨exs l ψ', .succ l hl hnd hψ', by rw [fv_exs, fv_exs, hfv],
      fun D v hD => sat_exs_congr (fun v => hequiv D v hD) l v⟩
theorem IsPi.pad_succ : ∀ {q : ℕ} {φ : Fm}, IsPi q φ →
    ∃ φ', IsPi (q + 1) φ' ∧ EquivNE.{u} φ' φ
  | _, φ, .zero h =>
    ⟨all (fresh (fv φ)) φ, .succ [fresh (fv φ)] (by simp) (by simp) (.zero h),
      by simp only [fv]; rw [Finset.erase_eq_of_notMem (fresh_notMem _)],
      fun D v hD => sat_all_of_notMem (fresh_notMem _) hD⟩
  | _, _, .succ l hl hnd h => by
    obtain ⟨ψ', hψ', hfv, hequiv⟩ := IsSigma.pad_succ h
    exact ⟨alls l ψ', .succ l hl hnd hψ', by rw [fv_alls, fv_alls, hfv],
      fun D v hD => sat_alls_congr (fun v => hequiv D v hD) l v⟩
end

theorem EquivNE.refl (φ : Fm) : EquivNE.{u} φ φ := ⟨rfl, fun _ _ _ => Iff.rfl⟩
theorem EquivNE.trans {φ ψ χ : Fm} (h₁ : EquivNE.{u} φ ψ) (h₂ : EquivNE.{u} ψ χ) :
    EquivNE.{u} φ χ :=
  ⟨h₁.1.trans h₂.1, fun D v hD => (h₁.2 D v hD).trans (h₂.2 D v hD)⟩

theorem IsSigma.pad {q q' : ℕ} (hq : q ≤ q') {φ : Fm} (h : IsSigma q φ) :
    ∃ φ', IsSigma q' φ' ∧ EquivNE.{u} φ' φ := by
  induction hq with
  | refl => exact ⟨φ, h, EquivNE.refl φ⟩
  | step _ ih =>
    obtain ⟨ψ, hψ, hequiv⟩ := ih
    obtain ⟨ψ', hψ', hequiv'⟩ := hψ.pad_succ
    exact ⟨ψ', hψ', hequiv'.trans hequiv⟩

theorem IsPi.pad {q q' : ℕ} (hq : q ≤ q') {φ : Fm} (h : IsPi q φ) :
    ∃ φ', IsPi q' φ' ∧ EquivNE.{u} φ' φ := by
  induction hq with
  | refl => exact ⟨φ, h, EquivNE.refl φ⟩
  | step _ ih =>
    obtain ⟨ψ, hψ, hequiv⟩ := ih
    obtain ⟨ψ', hψ', hequiv'⟩ := hψ.pad_succ
    exact ⟨ψ', hψ', hequiv'.trans hequiv⟩

/-- A Σ̂₁ formula is equivalent to a Π̂₂ formula (`∃x̄ δ ↔ ∀w ∃x̄ δ`). -/
theorem IsSigma.exists_pi_two {φ : Fm} (h : IsSigma 1 φ) :
    ∃ φ', IsPi 2 φ' ∧ EquivNE.{u} φ' φ :=
  ⟨all (fresh (fv φ)) φ, .succ [fresh (fv φ)] (by simp) (by simp) h,
    by simp only [fv]; rw [Finset.erase_eq_of_notMem (fresh_notMem _)],
    fun D v hD => sat_all_of_notMem (fresh_notMem _) hD⟩

/-! ### Merging conjunctions (Lemma 12.2 (4)) -/

/-- Renaming the bound variables of `φ` above `N`, keeping the free variables (all `< N`). -/
def shiftBound (N : ℕ) (φ : Fm) : ℕ → ℕ := fun i => if i ∈ fv φ then i else i + N

theorem shiftBound_injective {N : ℕ} {φ : Fm} (hN : ∀ i ∈ fv φ, i < N) :
    Function.Injective (shiftBound N φ) := by
  intro i j hij
  unfold shiftBound at hij
  split_ifs at hij with hi hj hj
  · exact hij
  · have := hN i hi; omega
  · have := hN j hj; omega
  · omega

theorem shiftBound_fv {N : ℕ} {φ : Fm} (hN : ∀ i ∈ fv φ, i < N) :
    fv (rename (shiftBound N φ) φ) = fv φ := by
  rw [fv_rename _ (shiftBound_injective hN)]
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩; simpa [shiftBound, hi]
  · intro hx; exact ⟨x, hx, by simp [shiftBound, hx]⟩

theorem shiftBound_vars {N : ℕ} {φ : Fm} (hN : ∀ i ∈ fv φ, i < N) :
    ∀ i ∈ vars (rename (shiftBound N φ) φ), i ∈ fv φ ∨ N ≤ i := by
  intro i hi
  rw [vars_rename] at hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  unfold shiftBound
  split_ifs with hj
  · exact Or.inl hj
  · right; omega

theorem sat_shiftBound {N : ℕ} {φ : Fm} (hN : ∀ i ∈ fv φ, i < N) (D : ZFSet.{u} → Prop)
    (v : ℕ → ZFSet.{u}) : Sat D v (rename (shiftBound N φ) φ) ↔ Sat D v φ := by
  rw [sat_rename (shiftBound_injective hN)]
  apply sat_congr
  intro x hx
  simp [shiftBound, hx]

/-- Bound variables of an `exs` block are not free in the whole formula. -/
theorem notMem_fv_exs_of_mem {l : List ℕ} {ψ : Fm} {i : ℕ} (hi : i ∈ l) : i ∉ fv (exs l ψ) := by
  rw [fv_exs]; simp [hi]

theorem notMem_fv_alls_of_mem {l : List ℕ} {ψ : Fm} {i : ℕ} (hi : i ∈ l) : i ∉ fv (alls l ψ) := by
  rw [fv_alls]; simp [hi]

theorem mem_vars_of_mem_exs {l : List ℕ} {ψ : Fm} {i : ℕ} (hi : i ∈ l) : i ∈ vars (exs l ψ) := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    simp only [exs_cons, ex, not, vars] at *
    rcases List.mem_cons.mp hi with rfl | h
    · simp
    · simp [ih h]

theorem mem_vars_of_mem_alls {l : List ℕ} {ψ : Fm} {i : ℕ} (hi : i ∈ l) : i ∈ vars (alls l ψ) := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    simp only [alls_cons, vars] at *
    rcases List.mem_cons.mp hi with rfl | h
    · simp
    · simp [ih h]

theorem fv_subset_vars_exs (l : List ℕ) (ψ : Fm) : fv ψ ⊆ vars (exs l ψ) := by
  induction l with
  | nil => exact fv_subset_vars ψ
  | cons j l ih => simp only [exs_cons, ex, not, vars]; exact ih.trans (by simp)

theorem fv_subset_vars_alls (l : List ℕ) (ψ : Fm) : fv ψ ⊆ vars (alls l ψ) := by
  induction l with
  | nil => exact fv_subset_vars ψ
  | cons j l ih => simp only [alls_cons, vars]; exact ih.trans (by simp)

/-- Merging two existential blocks whose variables do not interfere. -/
theorem sat_exs_and_exs {l₁ l₂ : List ℕ} {A B : Fm} (h₁ : ∀ i ∈ l₁, i ∉ fv B)
    (h₂ : ∀ i ∈ l₂, i ∉ fv A) (D : ZFSet.{u} → Prop) :
    ∀ v : ℕ → ZFSet.{u}, Sat D v (exs (l₁ ++ l₂) (and A B)) ↔ Sat D v (exs l₁ A) ∧ Sat D v (exs l₂ B) := by
  induction l₁ with
  | nil =>
    intro v
    simp only [List.nil_append, exs_nil]
    induction l₂ generalizing v with
    | nil => simp
    | cons i l ih =>
      simp only [exs_cons, sat_ex]
      have hi : i ∉ fv A := h₂ i (by simp)
      constructor
      · rintro ⟨x, hx, h⟩
        rw [ih (fun j hj => h₂ j (by simp [hj]))] at h
        exact ⟨(sat_update_of_notMem hi x).mp h.1, x, hx, h.2⟩
      · rintro ⟨hA, x, hx, hB⟩
        refine ⟨x, hx, ?_⟩
        rw [ih (fun j hj => h₂ j (by simp [hj]))]
        exact ⟨(sat_update_of_notMem hi x).mpr hA, hB⟩
  | cons i l ih =>
    intro v
    simp only [List.cons_append, exs_cons, sat_ex]
    have hi : i ∉ fv (exs l₂ B) := by
      rw [fv_exs]; intro h; exact h₁ i (by simp) (Finset.mem_sdiff.mp h).1
    constructor
    · rintro ⟨x, hx, h⟩
      rw [ih (fun j hj => h₁ j (by simp [hj]))] at h
      exact ⟨⟨x, hx, h.1⟩, (sat_update_of_notMem hi x).mp h.2⟩
    · rintro ⟨⟨x, hx, hA⟩, hB⟩
      refine ⟨x, hx, ?_⟩
      rw [ih (fun j hj => h₁ j (by simp [hj]))]
      exact ⟨hA, (sat_update_of_notMem hi x).mpr hB⟩

theorem sat_alls_and_alls {l₁ l₂ : List ℕ} {A B : Fm} (h₁ : ∀ i ∈ l₁, i ∉ fv B)
    (h₂ : ∀ i ∈ l₂, i ∉ fv A) (D : ZFSet.{u} → Prop) (hD : ∃ x, D x) :
    ∀ v : ℕ → ZFSet.{u}, Sat D v (alls (l₁ ++ l₂) (and A B)) ↔ Sat D v (alls l₁ A) ∧ Sat D v (alls l₂ B) := by
  induction l₁ with
  | nil =>
    intro v
    simp only [List.nil_append, alls_nil]
    induction l₂ generalizing v with
    | nil => simp
    | cons i l ih =>
      simp only [alls_cons, sat_all]
      have hi : i ∉ fv A := h₂ i (by simp)
      constructor
      · intro h
        obtain ⟨x₀, hx₀⟩ := hD
        refine ⟨?_, fun x hx => ?_⟩
        · have := (ih (fun j hj => h₂ j (by simp [hj])) _).mp (h x₀ hx₀)
          exact (sat_update_of_notMem hi x₀).mp this.1
        · exact ((ih (fun j hj => h₂ j (by simp [hj])) _).mp (h x hx)).2
      · rintro ⟨hA, hB⟩ x hx
        rw [ih (fun j hj => h₂ j (by simp [hj]))]
        exact ⟨(sat_update_of_notMem hi x).mpr hA, hB x hx⟩
  | cons i l ih =>
    intro v
    simp only [List.cons_append, alls_cons, sat_all]
    have hi : i ∉ fv (alls l₂ B) := by
      rw [fv_alls]; intro h; exact h₁ i (by simp) (Finset.mem_sdiff.mp h).1
    constructor
    · intro h
      obtain ⟨x₀, hx₀⟩ := hD
      refine ⟨fun x hx => ?_, ?_⟩
      · exact ((ih (fun j hj => h₁ j (by simp [hj])) _).mp (h x hx)).1
      · have := (ih (fun j hj => h₁ j (by simp [hj])) _).mp (h x₀ hx₀)
        exact (sat_update_of_notMem hi x₀).mp this.2
    · rintro ⟨hA, hB⟩ x hx
      rw [ih (fun j hj => h₁ j (by simp [hj]))]
      exact ⟨hA x hx, (sat_update_of_notMem hi x).mpr hB⟩

/-- Bound on the variables of a formula. -/
def bound (φ : Fm) : ℕ := fresh (vars φ)

theorem lt_bound {φ : Fm} {i : ℕ} (hi : i ∈ vars φ) : i < bound φ := by
  unfold bound fresh
  split_ifs with h
  · have := (vars φ).le_max' _ hi; omega
  · exact absurd ⟨_, hi⟩ h

theorem fv_lt_bound {φ : Fm} {i : ℕ} (hi : i ∈ fv φ) : i < bound φ := lt_bound (fv_subset_vars φ hi)

theorem vars_subset_vars_exs (l : List ℕ) (ψ : Fm) : vars ψ ⊆ vars (exs l ψ) := by
  induction l with
  | nil => exact subset_rfl
  | cons j l ih => simp only [exs_cons, ex, not, vars]; exact ih.trans (by simp)

theorem vars_subset_vars_alls (l : List ℕ) (ψ : Fm) : vars ψ ⊆ vars (alls l ψ) := by
  induction l with
  | nil => exact subset_rfl
  | cons j l ih => simp only [alls_cons, vars]; exact ih.trans (by simp)

/-- Variables of the shifted formula: free ones stay below `N`, bound ones land in `[N, 2N)`. -/
theorem vars_rename_shiftBound {N : ℕ} {φ : Fm} (hN : ∀ i ∈ fv φ, i < N) (hb : bound φ ≤ N) :
    ∀ x ∈ vars (rename (shiftBound N φ) φ), (x ∈ fv φ ∧ x < N) ∨ (N ≤ x ∧ x < 2 * N) := by
  intro x hx
  rw [vars_rename] at hx
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
  have hkb := lt_bound hk
  unfold shiftBound
  split_ifs with hkf
  · exact Or.inl ⟨hkf, hN k hkf⟩
  · right; omega

theorem shiftBound_of_mem_exs {N : ℕ} {l : List ℕ} {A : Fm} {j : ℕ} (hj : j ∈ l) :
    shiftBound N (exs l A) j = j + N := by
  simp [shiftBound, notMem_fv_exs_of_mem (ψ := A) hj]

theorem shiftBound_of_mem_alls {N : ℕ} {l : List ℕ} {A : Fm} {j : ℕ} (hj : j ∈ l) :
    shiftBound N (alls l A) j = j + N := by
  simp [shiftBound, notMem_fv_alls_of_mem (ψ := A) hj]

/-- The combinatorial core of the merge: the two renamed blocks and matrices do not interfere. -/
theorem merge_data_exs {q : ℕ} {l₁ l₂ : List ℕ} {A B : Fm} (_ : IsPi q A) (_ : IsPi q B) :
    let N := bound (exs l₁ A) + bound (exs l₂ B)
    let f := shiftBound N (exs l₁ A)
    let g := shiftBound (2 * N) (exs l₂ B)
    (∀ i ∈ l₁.map f, i ∉ fv (rename g B)) ∧ (∀ i ∈ l₂.map g, i ∉ fv (rename f A)) ∧
    (∀ x ∈ fv (rename f A), x ∉ l₂.map g) ∧ (∀ x ∈ fv (rename g B), x ∉ l₁.map f) ∧
    (∀ i ∈ l₁.map f, i ∉ l₂.map g) := by
  intro N f g
  have hN1 : ∀ i ∈ fv (exs l₁ A), i < N := fun i hi => by have := fv_lt_bound hi; omega
  have hN2 : ∀ i ∈ fv (exs l₂ B), i < 2 * N := fun i hi => by have := fv_lt_bound hi; omega
  have hb1 : bound (exs l₁ A) ≤ N := by omega
  have hb2 : bound (exs l₂ B) ≤ 2 * N := by omega
  -- variables of `rename f A` are `< 2N`; variables of `rename g B` are `< N` or `≥ 2N`
  have hA : ∀ x ∈ vars (rename f A), x < 2 * N := by
    intro x hx
    have hx' : x ∈ vars (rename f (exs l₁ A)) := by
      rw [rename_exs]; exact vars_subset_vars_exs _ _ hx
    rcases vars_rename_shiftBound hN1 hb1 x hx' with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hB : ∀ x ∈ vars (rename g B), x < N ∨ 2 * N ≤ x := by
    intro x hx
    have hx' : x ∈ vars (rename g (exs l₂ B)) := by
      rw [rename_exs]; exact vars_subset_vars_exs _ _ hx
    rcases vars_rename_shiftBound hN2 hb2 x hx' with ⟨hxf, _⟩ | ⟨h, _⟩
    · left; have := fv_lt_bound hxf; omega
    · right; exact h
  have hf : ∀ j ∈ l₁, N ≤ f j ∧ f j < 2 * N := by
    intro j hj
    have : f j = j + N := shiftBound_of_mem_exs hj
    have := lt_bound (mem_vars_of_mem_exs (ψ := A) hj)
    omega
  have hg : ∀ j ∈ l₂, 2 * N ≤ g j := by
    intro j hj
    have : g j = j + 2 * N := shiftBound_of_mem_exs hj
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have := hf j hj
    rcases hB _ (fv_subset_vars _ hmem) with h | h <;> omega
  · intro i hi hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have := hg j hj
    have := hA _ (fv_subset_vars _ hmem)
    omega
  · intro x hx hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
    have := hg j hj
    have := hA _ (fv_subset_vars _ hx)
    omega
  · intro x hx hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
    have := hf j hj
    rcases hB _ (fv_subset_vars _ hx) with h | h <;> omega
  · intro i hi hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    obtain ⟨j', hj', hjj'⟩ := List.mem_map.mp hmem
    have := hf j hj
    have := hg j' hj'
    omega

theorem merge_data_alls {q : ℕ} {l₁ l₂ : List ℕ} {A B : Fm} (_ : IsSigma q A) (_ : IsSigma q B) :
    let N := bound (alls l₁ A) + bound (alls l₂ B)
    let f := shiftBound N (alls l₁ A)
    let g := shiftBound (2 * N) (alls l₂ B)
    (∀ i ∈ l₁.map f, i ∉ fv (rename g B)) ∧ (∀ i ∈ l₂.map g, i ∉ fv (rename f A)) ∧
    (∀ x ∈ fv (rename f A), x ∉ l₂.map g) ∧ (∀ x ∈ fv (rename g B), x ∉ l₁.map f) ∧
    (∀ i ∈ l₁.map f, i ∉ l₂.map g) := by
  intro N f g
  have hN1 : ∀ i ∈ fv (alls l₁ A), i < N := fun i hi => by have := fv_lt_bound hi; omega
  have hN2 : ∀ i ∈ fv (alls l₂ B), i < 2 * N := fun i hi => by have := fv_lt_bound hi; omega
  have hb1 : bound (alls l₁ A) ≤ N := by omega
  have hb2 : bound (alls l₂ B) ≤ 2 * N := by omega
  have hA : ∀ x ∈ vars (rename f A), x < 2 * N := by
    intro x hx
    have hx' : x ∈ vars (rename f (alls l₁ A)) := by
      rw [rename_alls]; exact vars_subset_vars_alls _ _ hx
    rcases vars_rename_shiftBound hN1 hb1 x hx' with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hB : ∀ x ∈ vars (rename g B), x < N ∨ 2 * N ≤ x := by
    intro x hx
    have hx' : x ∈ vars (rename g (alls l₂ B)) := by
      rw [rename_alls]; exact vars_subset_vars_alls _ _ hx
    rcases vars_rename_shiftBound hN2 hb2 x hx' with ⟨hxf, _⟩ | ⟨h, _⟩
    · left; have := fv_lt_bound hxf; omega
    · right; exact h
  have hf : ∀ j ∈ l₁, N ≤ f j ∧ f j < 2 * N := by
    intro j hj
    have : f j = j + N := shiftBound_of_mem_alls hj
    have := lt_bound (mem_vars_of_mem_alls (ψ := A) hj)
    omega
  have hg : ∀ j ∈ l₂, 2 * N ≤ g j := by
    intro j hj
    have : g j = j + 2 * N := shiftBound_of_mem_alls hj
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have := hf j hj
    rcases hB _ (fv_subset_vars _ hmem) with h | h <;> omega
  · intro i hi hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    have := hg j hj
    have := hA _ (fv_subset_vars _ hmem)
    omega
  · intro x hx hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
    have := hg j hj
    have := hA _ (fv_subset_vars _ hx)
    omega
  · intro x hx hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hmem
    have := hf j hj
    rcases hB _ (fv_subset_vars _ hx) with h | h <;> omega
  · intro i hi hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    obtain ⟨j', hj', hjj'⟩ := List.mem_map.mp hmem
    have := hf j hj
    have := hg j' hj'
    omega

/-- Free variables of a merged block. -/
theorem fv_merge {l₁ l₂ : List ℕ} {A B : Fm} (h₁ : ∀ x ∈ fv A, x ∉ l₂) (h₂ : ∀ x ∈ fv B, x ∉ l₁) :
    (fv A ∪ fv B) \ (l₁ ++ l₂).toFinset = (fv A \ l₁.toFinset) ∪ (fv B \ l₂.toFinset) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, List.toFinset_append, List.mem_toFinset]
  constructor
  · rintro ⟨h | h, hn⟩
    · left; exact ⟨h, fun h' => hn (Or.inl h')⟩
    · right; exact ⟨h, fun h' => hn (Or.inr h')⟩
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩)
    · exact ⟨Or.inl h, fun h' => h'.elim hn (h₁ x h)⟩
    · exact ⟨Or.inr h, fun h' => h'.elim (h₂ x h) hn⟩

mutual
/-- Lemma 12.2 (4): the conjunction of two Σ̂q formulas is equivalent (over nonempty domains) to a
single Σ̂q formula. -/
theorem IsSigma.and_exists : ∀ {q : ℕ} {φ ψ : Fm}, IsSigma q φ → IsSigma q ψ →
    ∃ χ, IsSigma q χ ∧ fv χ = fv φ ∪ fv ψ ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), (∃ x, D x) →
        (Sat D v χ ↔ Sat D v φ ∧ Sat D v ψ)
  | _, φ, ψ, .zero hφ, .zero hψ => ⟨and φ ψ, .zero (hφ.and hψ), by simp, fun _ _ _ => sat_and⟩
  | _, _, _, .succ (q := q) l₁ hl₁ hnd₁ (ψ := A) hA, .succ l₂ hl₂ hnd₂ (ψ := B) hB => by
    obtain ⟨d1, d2, d3, d4, d5⟩ := merge_data_exs hA hB
    set N := bound (exs l₁ A) + bound (exs l₂ B) with hN
    set f := shiftBound N (exs l₁ A) with hf_def
    set g := shiftBound (2 * N) (exs l₂ B) with hg_def
    have hN1 : ∀ i ∈ fv (exs l₁ A), i < N := fun i hi => by have := fv_lt_bound hi; omega
    have hN2 : ∀ i ∈ fv (exs l₂ B), i < 2 * N := fun i hi => by have := fv_lt_bound hi; omega
    have hf := shiftBound_injective hN1
    have hg := shiftBound_injective hN2
    obtain ⟨C, hC, hCfv, hCsat⟩ := IsPi.and_exists (hA.rename hf) (hB.rename hg)
    have hndm : (l₁.map f ++ l₂.map g).Nodup :=
      List.nodup_append.mpr ⟨hnd₁.map hf, hnd₂.map hg,
        fun a ha b hb heq => d5 a ha (by rw [heq]; exact hb)⟩
    refine ⟨exs (l₁.map f ++ l₂.map g) C, .succ _ (by simp [hl₁]) hndm hC, ?_, ?_⟩
    · have e1 : fv (exs (l₁.map f) (rename f A)) = fv (exs l₁ A) := by
        rw [← rename_exs]; exact shiftBound_fv hN1
      have e2 : fv (exs (l₂.map g) (rename g B)) = fv (exs l₂ B) := by
        rw [← rename_exs]; exact shiftBound_fv hN2
      rw [fv_exs, hCfv, ← e1, ← e2, fv_exs, fv_exs]
      exact fv_merge d3 d4
    · intro D v hD
      rw [sat_exs_congr (fun v => (hCsat D v hD).trans sat_and.symm), sat_exs_and_exs d1 d2 D v,
        ← rename_exs, ← rename_exs, sat_shiftBound hN1, sat_shiftBound hN2]
theorem IsPi.and_exists : ∀ {q : ℕ} {φ ψ : Fm}, IsPi q φ → IsPi q ψ →
    ∃ χ, IsPi q χ ∧ fv χ = fv φ ∪ fv ψ ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), (∃ x, D x) →
        (Sat D v χ ↔ Sat D v φ ∧ Sat D v ψ)
  | _, φ, ψ, .zero hφ, .zero hψ => ⟨and φ ψ, .zero (hφ.and hψ), by simp, fun _ _ _ => sat_and⟩
  | _, _, _, .succ (q := q) l₁ hl₁ hnd₁ (ψ := A) hA, .succ l₂ hl₂ hnd₂ (ψ := B) hB => by
    obtain ⟨d1, d2, d3, d4, d5⟩ := merge_data_alls hA hB
    set N := bound (alls l₁ A) + bound (alls l₂ B) with hN
    set f := shiftBound N (alls l₁ A) with hf_def
    set g := shiftBound (2 * N) (alls l₂ B) with hg_def
    have hN1 : ∀ i ∈ fv (alls l₁ A), i < N := fun i hi => by have := fv_lt_bound hi; omega
    have hN2 : ∀ i ∈ fv (alls l₂ B), i < 2 * N := fun i hi => by have := fv_lt_bound hi; omega
    have hf := shiftBound_injective hN1
    have hg := shiftBound_injective hN2
    obtain ⟨C, hC, hCfv, hCsat⟩ := IsSigma.and_exists (hA.rename hf) (hB.rename hg)
    have hndm : (l₁.map f ++ l₂.map g).Nodup :=
      List.nodup_append.mpr ⟨hnd₁.map hf, hnd₂.map hg,
        fun a ha b hb heq => d5 a ha (by rw [heq]; exact hb)⟩
    refine ⟨alls (l₁.map f ++ l₂.map g) C, .succ _ (by simp [hl₁]) hndm hC, ?_, ?_⟩
    · have e1 : fv (alls (l₁.map f) (rename f A)) = fv (alls l₁ A) := by
        rw [← rename_alls]; exact shiftBound_fv hN1
      have e2 : fv (alls (l₂.map g) (rename g B)) = fv (alls l₂ B) := by
        rw [← rename_alls]; exact shiftBound_fv hN2
      rw [fv_alls, hCfv, ← e1, ← e2, fv_alls, fv_alls]
      exact fv_merge d3 d4
    · intro D v hD
      rw [sat_alls_congr (fun v => (hCsat D v hD).trans sat_and.symm),
        sat_alls_and_alls d1 d2 D hD v, ← rename_alls, ← rename_alls, sat_shiftBound hN1,
        sat_shiftBound hN2]
end

/-! ### Merging disjunctions and finite families (Lemma 12.2 (4)) -/

/-- Lemma 12.2 (4): the disjunction of two Σ̂q formulas is equivalent (over nonempty domains) to a
single Σ̂q formula.  Obtained from the conjunction case by dualizing twice. -/
theorem IsSigma.or_exists {q : ℕ} {φ ψ : Fm} (hφ : IsSigma q φ) (hψ : IsSigma q ψ) :
    ∃ χ, IsSigma q χ ∧ fv χ = fv φ ∪ fv ψ ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), (∃ x, D x) →
        (Sat D v χ ↔ Sat D v φ ∨ Sat D v ψ) := by
  obtain ⟨φ', hφ', hfvφ, hsatφ⟩ := IsSigma.exists_neg.{u} hφ
  obtain ⟨ψ', hψ', hfvψ, hsatψ⟩ := IsSigma.exists_neg.{u} hψ
  obtain ⟨χ, hχ, hfvχ, hsatχ⟩ := IsPi.and_exists.{u} hφ' hψ'
  obtain ⟨χ', hχ', hfvχ', hsatχ'⟩ := IsPi.exists_neg.{u} hχ
  refine ⟨χ', hχ', by rw [hfvχ', hfvχ, hfvφ, hfvψ], fun D v hD => ?_⟩
  rw [hsatχ' D v, hsatχ D v hD, hsatφ D v, hsatψ D v]
  tauto

/-- Lemma 12.2 (4): the disjunction of two Π̂q formulas is equivalent (over nonempty domains) to a
single Π̂q formula. -/
theorem IsPi.or_exists {q : ℕ} {φ ψ : Fm} (hφ : IsPi q φ) (hψ : IsPi q ψ) :
    ∃ χ, IsPi q χ ∧ fv χ = fv φ ∪ fv ψ ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), (∃ x, D x) →
        (Sat D v χ ↔ Sat D v φ ∨ Sat D v ψ) := by
  obtain ⟨φ', hφ', hfvφ, hsatφ⟩ := IsPi.exists_neg.{u} hφ
  obtain ⟨ψ', hψ', hfvψ, hsatψ⟩ := IsPi.exists_neg.{u} hψ
  obtain ⟨χ, hχ, hfvχ, hsatχ⟩ := IsSigma.and_exists.{u} hφ' hψ'
  obtain ⟨χ', hχ', hfvχ', hsatχ'⟩ := IsSigma.exists_neg.{u} hχ
  refine ⟨χ', hχ', by rw [hfvχ', hfvχ, hfvφ, hfvψ], fun D v hD => ?_⟩
  rw [hsatχ' D v, hsatχ D v hD, hsatφ D v, hsatψ D v]
  tauto

/-- The free variables of a finite family of formulas. -/
def fvList : List Fm → Finset ℕ
  | [] => ∅
  | φ :: L => fv φ ∪ fvList L

@[simp] theorem fvList_nil : fvList [] = ∅ := rfl
@[simp] theorem fvList_cons (φ : Fm) (L : List Fm) : fvList (φ :: L) = fv φ ∪ fvList L := rfl

@[simp] theorem fv_top : fv top = ∅ := by simp [top, not, fv]

/-- Lemma 12.2 (4), finite family: the conjunction of finitely many Σ̂q formulas is equivalent
(over nonempty domains) to a single Σ̂q formula. -/
theorem IsSigma.andList_exists {q : ℕ} : ∀ (L : List Fm), (∀ φ ∈ L, IsSigma q φ) →
    ∃ χ, IsSigma q χ ∧ fv χ = fvList L ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), (∃ x, D x) →
        (Sat D v χ ↔ ∀ φ ∈ L, Sat D v φ) := by
  intro L
  induction L with
  | nil =>
    intro _
    obtain ⟨χ, hχ, hfv, hsat⟩ := IsSigma.pad.{u} (Nat.zero_le q) (IsSigma.zero IsDelta0.top)
    exact ⟨χ, hχ, by rw [hfv, fv_top, fvList_nil], fun D v hD => by rw [hsat D v hD]; simp⟩
  | cons φ L ih =>
    intro h
    obtain ⟨χ₀, hχ₀, hfv₀, hsat₀⟩ := ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))
    obtain ⟨χ, hχ, hfv, hsat⟩ := IsSigma.and_exists.{u} (h φ (List.mem_cons_self ..)) hχ₀
    refine ⟨χ, hχ, by rw [hfv, hfv₀, fvList_cons], fun D v hD => ?_⟩
    rw [hsat D v hD, hsat₀ D v hD]
    simp

/-- Lemma 12.2 (4), finite family: the disjunction of finitely many Σ̂q formulas is equivalent
(over nonempty domains) to a single Σ̂q formula. -/
theorem IsSigma.orList_exists {q : ℕ} : ∀ (L : List Fm), (∀ φ ∈ L, IsSigma q φ) →
    ∃ χ, IsSigma q χ ∧ fv χ = fvList L ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), (∃ x, D x) →
        (Sat D v χ ↔ ∃ φ ∈ L, Sat D v φ) := by
  intro L
  induction L with
  | nil =>
    intro _
    obtain ⟨χ, hχ, hfv, hsat⟩ := IsSigma.pad.{u} (Nat.zero_le q) (IsSigma.zero IsDelta0.falsum)
    exact ⟨χ, hχ, by rw [hfv, fvList_nil]; rfl, fun D v hD => by rw [hsat D v hD]; simp⟩
  | cons φ L ih =>
    intro h
    obtain ⟨χ₀, hχ₀, hfv₀, hsat₀⟩ := ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))
    obtain ⟨χ, hχ, hfv, hsat⟩ := IsSigma.or_exists.{u} (h φ (List.mem_cons_self ..)) hχ₀
    refine ⟨χ, hχ, by rw [hfv, hfv₀, fvList_cons], fun D v hD => ?_⟩
    rw [hsat D v hD, hsat₀ D v hD]
    simp

/-- Lemma 12.2 (4), finite family: the conjunction of finitely many Π̂q formulas is equivalent
(over nonempty domains) to a single Π̂q formula. -/
theorem IsPi.andList_exists {q : ℕ} : ∀ (L : List Fm), (∀ φ ∈ L, IsPi q φ) →
    ∃ χ, IsPi q χ ∧ fv χ = fvList L ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), (∃ x, D x) →
        (Sat D v χ ↔ ∀ φ ∈ L, Sat D v φ) := by
  intro L
  induction L with
  | nil =>
    intro _
    obtain ⟨χ, hχ, hfv, hsat⟩ := IsPi.pad.{u} (Nat.zero_le q) (IsPi.zero IsDelta0.top)
    exact ⟨χ, hχ, by rw [hfv, fv_top, fvList_nil], fun D v hD => by rw [hsat D v hD]; simp⟩
  | cons φ L ih =>
    intro h
    obtain ⟨χ₀, hχ₀, hfv₀, hsat₀⟩ := ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))
    obtain ⟨χ, hχ, hfv, hsat⟩ := IsPi.and_exists.{u} (h φ (List.mem_cons_self ..)) hχ₀
    refine ⟨χ, hχ, by rw [hfv, hfv₀, fvList_cons], fun D v hD => ?_⟩
    rw [hsat D v hD, hsat₀ D v hD]
    simp

/-- Lemma 12.2 (4), finite family: the disjunction of finitely many Π̂q formulas is equivalent
(over nonempty domains) to a single Π̂q formula. -/
theorem IsPi.orList_exists {q : ℕ} : ∀ (L : List Fm), (∀ φ ∈ L, IsPi q φ) →
    ∃ χ, IsPi q χ ∧ fv χ = fvList L ∧
      ∀ (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u}), (∃ x, D x) →
        (Sat D v χ ↔ ∃ φ ∈ L, Sat D v φ) := by
  intro L
  induction L with
  | nil =>
    intro _
    obtain ⟨χ, hχ, hfv, hsat⟩ := IsPi.pad.{u} (Nat.zero_le q) (IsPi.zero IsDelta0.falsum)
    exact ⟨χ, hχ, by rw [hfv, fvList_nil]; rfl, fun D v hD => by rw [hsat D v hD]; simp⟩
  | cons φ L ih =>
    intro h
    obtain ⟨χ₀, hχ₀, hfv₀, hsat₀⟩ := ih (fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ))
    obtain ⟨χ, hχ, hfv, hsat⟩ := IsPi.or_exists.{u} (h φ (List.mem_cons_self ..)) hχ₀
    refine ⟨χ, hχ, by rw [hfv, hfv₀, fvList_cons], fun D v hD => ?_⟩
    rw [hsat D v hD, hsat₀ D v hD]
    simp

end Fm

end BM4.ST
