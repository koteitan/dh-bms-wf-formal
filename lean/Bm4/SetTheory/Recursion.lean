/-
  Part III (§10, Lemma 10.3 in semantic form): Σ1-recursion along ordinals in an admissible `L θ`.
-/
import Bm4.SetTheory.Recur

universe u

namespace BM4.ST

open Fm

/-- Graph of `F` below `ξ`: the set of pairs `⟨ζ, F ζ⟩` for `ζ < ξ`. -/
noncomputable def graphBelow (F : Ordinal.{u} → ZFSet.{u}) (ξ : Ordinal.{u}) : ZFSet.{u} :=
  ZFSet.range (fun ζ : Set.Iio ξ => ZFSet.pair ζ.1.toZFSet (F ζ.1))

theorem mem_graphBelow {F : Ordinal.{u} → ZFSet.{u}} {ξ : Ordinal.{u}} {p : ZFSet.{u}} :
    p ∈ graphBelow F ξ ↔ ∃ ζ < ξ, p = ZFSet.pair ζ.toZFSet (F ζ) := by
  unfold graphBelow
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨⟨ζ, hζ⟩, rfl⟩; exact ⟨ζ, hζ, rfl⟩
  · rintro ⟨ζ, hζ, rfl⟩; exact ⟨⟨ζ, hζ⟩, rfl⟩

theorem graphBelow_zero (F : Ordinal.{u} → ZFSet.{u}) : graphBelow F 0 = ∅ := by
  ext p; simp [mem_graphBelow]

theorem graphBelow_succ (F : Ordinal.{u} → ZFSet.{u}) (ξ : Ordinal.{u}) :
    graphBelow F (ξ + 1) = insert (ZFSet.pair ξ.toZFSet (F ξ)) (graphBelow F ξ) := by
  ext p
  rw [ZFSet.mem_insert_iff, mem_graphBelow, mem_graphBelow]
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    rcases lt_or_eq_of_le (Order.lt_add_one_iff.mp hζ) with h | rfl
    · exact Or.inr ⟨ζ, h, rfl⟩
    · exact Or.inl rfl
  · rintro (rfl | ⟨ζ, hζ, rfl⟩)
    · exact ⟨ξ, Order.lt_add_one_iff.mpr le_rfl, rfl⟩
    · exact ⟨ζ, hζ.trans (Order.lt_add_one_iff.mpr le_rfl), rfl⟩

theorem graphBelow_isFunc (F : Ordinal.{u} → ZFSet.{u}) (ξ : Ordinal.{u}) : IsFunc (graphBelow F ξ) := by
  constructor
  · intro p hp
    obtain ⟨ζ, _, rfl⟩ := mem_graphBelow.mp hp
    exact ⟨_, _, rfl⟩
  · intro a b b' hb hb'
    obtain ⟨ζ, _, h⟩ := mem_graphBelow.mp hb
    obtain ⟨ζ', _, h'⟩ := mem_graphBelow.mp hb'
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective h
    obtain ⟨hζ, rfl⟩ := ZFSet.pair_injective h'
    rw [Ordinal.toZFSet_injective hζ]

theorem graphBelow_isDom (F : Ordinal.{u} → ZFSet.{u}) (ξ : Ordinal.{u}) :
    IsDom (graphBelow F ξ) ξ.toZFSet := by
  intro a
  rw [Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨ζ, hζ, rfl⟩; exact ⟨F ζ, mem_graphBelow.mpr ⟨ζ, hζ, rfl⟩⟩
  · rintro ⟨b, hb⟩
    obtain ⟨ζ, hζ, h⟩ := mem_graphBelow.mp hb
    obtain ⟨rfl, _⟩ := ZFSet.pair_injective h
    exact ⟨ζ, hζ, rfl⟩

theorem pair_mem_graphBelow_iff {F : Ordinal.{u} → ZFSet.{u}} {ξ ζ : Ordinal.{u}} {y : ZFSet.{u}} :
    ZFSet.pair ζ.toZFSet y ∈ graphBelow F ξ ↔ ζ < ξ ∧ y = F ζ := by
  rw [mem_graphBelow]
  constructor
  · rintro ⟨ζ', hζ', h⟩
    obtain ⟨h1, rfl⟩ := ZFSet.pair_injective h
    rw [Ordinal.toZFSet_injective h1]
    exact ⟨Ordinal.toZFSet_injective h1 ▸ hζ', rfl⟩
  · rintro ⟨hζ, rfl⟩; exact ⟨ζ, hζ, rfl⟩

/-- The restriction of a function-set `g` to a domain `d`. -/
def IsRestrict (g d g' : ZFSet.{u}) : Prop :=
  ∀ p, p ∈ g' ↔ p ∈ g ∧ ∃ a ∈ d, ∃ b, p = ZFSet.pair a b

theorem isRestrict_graphBelow {F : Ordinal.{u} → ZFSet.{u}} {ξ ζ : Ordinal.{u}} (h : ζ ≤ ξ) :
    IsRestrict (graphBelow F ξ) ζ.toZFSet (graphBelow F ζ) := by
  intro p
  rw [mem_graphBelow, mem_graphBelow]
  constructor
  · rintro ⟨ζ', hζ', rfl⟩
    exact ⟨⟨ζ', hζ'.trans_le h, rfl⟩, _, Ordinal.mem_toZFSet_iff.mpr ⟨ζ', hζ', rfl⟩, _, rfl⟩
  · rintro ⟨⟨ζ', hζ', rfl⟩, a, ha, b, hab⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_injective hab
    obtain ⟨ζ'', hζ'', h''⟩ := Ordinal.mem_toZFSet_iff.mp ha
    rw [Ordinal.toZFSet_injective h''] at hζ''
    exact ⟨ζ', hζ'', rfl⟩

theorem isRestrict_unique {g d g₁ g₂ : ZFSet.{u}} (h₁ : IsRestrict g d g₁) (h₂ : IsRestrict g d g₂) :
    g₁ = g₂ := by
  ext p; rw [h₁ p, h₂ p]

/-- Δ0-definability of restriction. -/
theorem delta0_isRestrict (g d g' : ℕ) (hgd : g ≠ d) (hgg' : g ≠ g') (hdg' : d ≠ g') :
    Delta0Def {g, d, g'} (fun _ v => IsRestrict (v g) (v d) (v g')) := by
  set m := g + d + g' + 1 with hm
  -- `∀ p ∈ g', p ∈ g ∧ ∃ a ∈ d, ∃ q ∈ p, ∃ b ∈ q, p = pair a b`
  have a1 := delta0_isKPair m (m + 1) (m + 3) (by omega) (by omega)
  have a2 := a1.bex (m + 3) (m + 2) (by omega)
  have a3 := a2.bex (m + 2) m (by omega)
  have a4 := a3.bex (m + 1) d (by omega)
  have a5 := (Delta0Def.mem m g).and a4
  have h1 := a5.ball m g' (by omega)
  -- `∀ p ∈ g, ∀ a ∈ d, ∀ q ∈ p, ∀ b ∈ q, p = pair a b → p ∈ g'`
  have b1 := (delta0_isKPair m (m + 1) (m + 3) (by omega) (by omega)).imp (Delta0Def.mem m g')
  have b2 := b1.ball (m + 3) (m + 2) (by omega)
  have b3 := b2.ball (m + 2) m (by omega)
  have b4 := b3.ball (m + 1) d (by omega)
  have h2 := b4.ball m g (by omega)
  refine ((h1.and h2).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨H1, H2⟩ p
      constructor
      · intro hp
        obtain ⟨hpg, a, ha, q, _, b, _, rfl⟩ := H1 p hp
        exact ⟨hpg, a, ha, b, rfl⟩
      · rintro ⟨hpg, a, ha, b, rfl⟩
        exact H2 _ hpg a ha _ (upair_mem_pair a b) b (mem_upair_right a b) rfl
    · intro H
      refine ⟨fun p hp => ?_, ?_⟩
      · obtain ⟨hpg, a, ha, b, rfl⟩ := (H p).mp hp
        exact ⟨hpg, a, ha, _, upair_mem_pair a b, b, mem_upair_right a b, rfl⟩
      · intro p hp a ha q _ b _ hpab
        subst hpab
        exact (H _).mpr ⟨hp, a, ha, b, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Partial approximations -/

/-- A partial approximation of the recursion up to `ζ`: `g` is a function with domain `ζ`, and
for each `ζ' ∈ ζ`, with `g'` the restriction of `g` to `ζ'` and `y = g(ζ')`, the step relation
(matrix `Q`, witness block `l`, witnesses in `b`) holds at `(ζ', g', y)`. The variables `0, 1, 2`
carry `ζ', g', y`. -/
def PA (Q : Pred.{u}) (l : List ℕ) (D : ZFSet.{u} → Prop) (v : ℕ → ZFSet.{u})
    (ζ g b : ZFSet.{u}) : Prop :=
  IsFunc g ∧ IsDom g ζ ∧ ∀ ζ' ∈ ζ, ∃ g' ∈ b, ∃ y ∈ b, IsRestrict g ζ' g' ∧ ZFSet.pair ζ' y ∈ g ∧
    ExsIn b l (Q D) (Function.update (Function.update (Function.update v 0 ζ') 1 g') 2 y)

/-- Δ0-definability of `PA` in the variables `zζ, zg, zb` (fresh) and the parameters of `Q`. -/
theorem delta0_PA {s : Finset ℕ} {Q : Pred.{u}} (hQ : Delta0Def s Q) (l : List ℕ)
    (hl0 : 0 ∉ l) (hl1 : 1 ∉ l) (hl2 : 2 ∉ l) (zζ zg zb : ℕ)
    (hζ : ∀ k ∈ s, k < zζ) (hζl : ∀ k ∈ l, k < zζ) (h3 : 3 ≤ zζ)
    (hg : zg = zζ + 1) (hb : zb = zζ + 2) :
    Delta0Def (insert zζ (insert zg (insert zb s)))
      (fun D w => PA Q l D w (w zζ) (w zg) (w zb)) := by
  have hsz : zζ ∉ s := fun h => by have := hζ _ h; omega
  have hsg : zg ∉ s := fun h => by have := hζ _ h; omega
  have hsb : zb ∉ s := fun h => by have := hζ _ h; omega
  have hlb : zb ∉ l := fun h => by have := hζl _ h; omega
  -- the matrix at `(0, 1, 2)` with witnesses in `zb`
  have c1 := delta0_isRestrict zg 0 1 (by omega) (by omega) (by omega)
  have c2 := delta0_funVal zg 0 2 (by omega) (by omega) (by omega)
  have c3 := delta0Def_exsIn hQ zb hsb l hlb
  have c4 := (c1.and c2).and c3
  have c5 := c4.bex 2 zb (by omega)
  have c6 := c5.bex 1 zb (by omega)
  have c7 := c6.ball 0 zζ (by omega)
  have h := ((delta0_isFunc zg).and (delta0_isDom zg zζ (by omega))).and c7
  refine (h.congr ?_).mono ?_
  · intro D w _ _
    simp only [PA]
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    simp only [and_assoc]
  · intro k hk
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton] at hk ⊢
    by_cases hks : k ∈ s
    · simp [hks]
    · simp only [hks, or_false, false_or, and_false, false_and] at hk ⊢
      omega

/-- The valuation with `0 ↦ ζ, 1 ↦ g, 2 ↦ y`. -/
def upd3 (v : ℕ → ZFSet.{u}) (ζ g y : ZFSet.{u}) : ℕ → ZFSet.{u} :=
  Function.update (Function.update (Function.update v 0 ζ) 1 g) 2 y

theorem upd3_apply_of_ge {v : ℕ → ZFSet.{u}} {ζ g y : ZFSet.{u}} {k : ℕ} (hk : 3 ≤ k) :
    upd3 v ζ g y k = v k := by
  unfold upd3
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega)]

/-- The conjunction with a part independent of the block variables can be pulled out of `ExsIn`. -/
theorem exsIn_and_of_indep {b : ZFSet.{u}} {A B : (ℕ → ZFSet.{u}) → Prop}
    (hA : ∀ w i y, i ∈ l → (A (Function.update w i y) ↔ A w)) :
    ∀ (v : ℕ → ZFSet.{u}), ExsIn b l (fun w => A w ∧ B w) v ↔ A v ∧ ExsIn b l B v := by
  induction l with
  | nil => intro v; rfl
  | cons i l ih =>
    intro v
    simp only [ExsIn]
    constructor
    · rintro ⟨y, hy, h⟩
      rw [ih (fun w i' y' hi' => hA w i' y' (by simp [hi']))] at h
      exact ⟨(hA v i y (by simp)).mp h.1, y, hy, h.2⟩
    · rintro ⟨hAv, y, hy, h⟩
      refine ⟨y, hy, ?_⟩
      rw [ih (fun w i' y' hi' => hA w i' y' (by simp [hi']))]
      exact ⟨(hA v i y (by simp)).mpr hAv, h⟩

/-- Uniqueness of partial approximations: any partial approximation up to `ξ` (with witnesses in
`L θ`) is the graph of `F` below `ξ`, provided `F` is the unique solution of the step relation. -/
theorem PA_unique {θ : Ordinal.{u}} {Q : Pred.{u}} {l : List ℕ} {v : ℕ → ZFSet.{u}}
    {F : Ordinal.{u} → ZFSet.{u}}
    (huniq : ∀ ξ < θ, graphBelow F ξ ∈ L θ → ∀ y ∈ L θ,
      ExsD (· ∈ L θ) l (Q (· ∈ L θ)) (upd3 v ξ.toZFSet (graphBelow F ξ) y) → y = F ξ) :
    ∀ ξ < θ, ∀ g b, (∀ z ∈ b, z ∈ L θ) → PA Q l (· ∈ L θ) v ξ.toZFSet g b → g = graphBelow F ξ := by
  intro ξ
  induction ξ using Ordinal.induction with
  | _ ξ ih =>
  intro hξ g b hb ⟨hfun, hdom, hstep⟩
  -- values of `g` are the values of `F`
  have hval : ∀ ξ' < ξ, ∀ y, ZFSet.pair ξ'.toZFSet y ∈ g → y = F ξ' := by
    intro ξ' hξ' y hy
    obtain ⟨g', hg', y', hy', hres, hpair, hexs⟩ :=
      hstep ξ'.toZFSet (Ordinal.mem_toZFSet_iff.mpr ⟨ξ', hξ', rfl⟩)
    -- `g'` is a partial approximation up to `ξ'`
    have hPA' : PA Q l (· ∈ L θ) v ξ'.toZFSet g' b := by
      refine ⟨?_, ?_, ?_⟩
      · constructor
        · intro p hp; exact hfun.1 p ((hres p).mp hp).1
        · intro a c c' hc hc'
          exact hfun.2 a c c' ((hres _).mp hc).1 ((hres _).mp hc').1
      · intro a
        constructor
        · intro ha
          have haξ : a ∈ ξ.toZFSet := by
            obtain ⟨a', ha', rfl⟩ := Ordinal.mem_toZFSet_iff.mp ha
            exact Ordinal.mem_toZFSet_iff.mpr ⟨a', ha'.trans hξ', rfl⟩
          obtain ⟨c, hc⟩ := (hdom a).mp haξ
          exact ⟨c, (hres _).mpr ⟨hc, a, ha, c, rfl⟩⟩
        · rintro ⟨c, hc⟩
          obtain ⟨_, a', ha', c', hac⟩ := (hres _).mp hc
          obtain ⟨rfl, _⟩ := ZFSet.pair_injective hac
          exact ha'
      · intro ζ'' hζ''
        have hζ''ξ : ζ'' ∈ ξ.toZFSet := by
          obtain ⟨a', ha', rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ''
          exact Ordinal.mem_toZFSet_iff.mpr ⟨a', ha'.trans hξ', rfl⟩
        obtain ⟨g'', hg'', y'', hy'', hres'', hpair'', hexs''⟩ := hstep ζ'' hζ''ξ
        refine ⟨g'', hg'', y'', hy'', ?_, ?_, hexs''⟩
        · intro p
          rw [hres'' p, hres p]
          constructor
          · rintro ⟨hp, a, ha, c, rfl⟩
            obtain ⟨a', ha', rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ''
            obtain ⟨a'', ha'', rfl⟩ := Ordinal.mem_toZFSet_iff.mp ha
            exact ⟨⟨hp, _, Ordinal.mem_toZFSet_iff.mpr ⟨a'', ha''.trans ha', rfl⟩, c, rfl⟩,
              _, Ordinal.mem_toZFSet_iff.mpr ⟨a'', ha'', rfl⟩, c, rfl⟩
          · rintro ⟨⟨hp, _⟩, a, ha, c, rfl⟩
            exact ⟨hp, a, ha, c, rfl⟩
        · exact (hres _).mpr ⟨hpair'', _, hζ'', _, rfl⟩
    have hg'eq : g' = graphBelow F ξ' := ih ξ' hξ' (hξ'.trans hξ) g' b hb hPA'
    -- `y'` is the value `F ξ'`
    have hy'eq : y' = F ξ' := by
      apply huniq ξ' (hξ'.trans hξ) (by rw [← hg'eq]; exact hb g' hg') y' (hb y' hy')
      rw [← hg'eq]
      exact exsIn_imp_exsD hb l _ _ hexs
    -- `y = y'` by functionality
    rw [hfun.2 _ y y' hy hpair, hy'eq]
  ext p
  rw [mem_graphBelow]
  constructor
  · intro hp
    obtain ⟨a, y, rfl⟩ := hfun.1 p hp
    have ha : a ∈ ξ.toZFSet := (hdom a).mpr ⟨y, hp⟩
    obtain ⟨ξ', hξ', rfl⟩ := Ordinal.mem_toZFSet_iff.mp ha
    exact ⟨ξ', hξ', by rw [hval ξ' hξ' y hp]⟩
  · rintro ⟨ξ', hξ', rfl⟩
    obtain ⟨y, hy⟩ := (hdom _).mp (Ordinal.mem_toZFSet_iff.mpr ⟨ξ', hξ', rfl⟩)
    rw [← hval ξ' hξ' y hy]
    exact hy

theorem exsD_and_of_indep {D : ZFSet.{u} → Prop} {A B : (ℕ → ZFSet.{u}) → Prop} {l : List ℕ}
    (hA : ∀ w i y, i ∈ l → (A (Function.update w i y) ↔ A w)) :
    ∀ (v : ℕ → ZFSet.{u}), ExsD D l (fun w => A w ∧ B w) v ↔ A v ∧ ExsD D l B v := by
  induction l with
  | nil => intro v; rfl
  | cons i l ih =>
    intro v
    simp only [ExsD]
    constructor
    · rintro ⟨y, hy, h⟩
      rw [ih (fun w i' y' hi' => hA w i' y' (by simp [hi']))] at h
      exact ⟨(hA v i y (by simp)).mp h.1, y, hy, h.2⟩
    · rintro ⟨hAv, y, hy, h⟩
      refine ⟨y, hy, ?_⟩
      rw [ih (fun w i' y' hi' => hA w i' y' (by simp [hi']))]
      exact ⟨(hA v i y (by simp)).mpr hAv, h⟩

/-- `PA` only depends on the parameter valuation outside `{0,1,2} ∪ l` (for a matrix depending on
`s` only). -/
theorem PA_congr_v {Q : Pred.{u}} {s : Finset ℕ} {l : List ℕ} {D : ZFSet.{u} → Prop}
    (hQ : ∀ w w', (∀ k ∈ s, w k = w' k) → (Q D w ↔ Q D w')) {v v' : ℕ → ZFSet.{u}}
    (hvv' : ∀ k ∈ s, k ∉ l → 3 ≤ k → v k = v' k) (ζ g b : ZFSet.{u}) :
    PA Q l D v ζ g b ↔ PA Q l D v' ζ g b := by
  unfold PA
  apply and_congr_right; intro _; apply and_congr_right; intro _
  apply forall_congr'; intro ζ'; apply imp_congr_right; intro _
  apply exists_congr; intro g'; apply and_congr_right; intro _
  apply exists_congr; intro y; apply and_congr_right; intro _
  apply and_congr_right; intro _; apply and_congr_right; intro _
  apply exsIn_congr_outside hQ l
  intro k hk hkl
  show upd3 v ζ' g' y k = upd3 v' ζ' g' y k
  rcases lt_or_ge k 3 with hk3 | hk3
  · unfold upd3
    interval_cases k <;> simp
  · rw [upd3_apply_of_ge hk3, upd3_apply_of_ge hk3]
    exact hvv' k hk hkl hk3

/-- **Σ1-recursion in an admissible `L θ`** (Lemma 10.3, semantic form). Let `F` be a function
on ordinals which, at every `ξ < θ`, is the unique solution `y` of a Σ1 step relation
`∃ l, Q(ξ, graph F below ξ, y)` (matrix `Q` Δ₀, witnesses in `L θ`), with `F ξ ∈ L θ` whenever
the graph below `ξ` is in `L θ`. Then all graphs below `ξ < θ` lie in `L θ`. -/
theorem sigma1_recursion {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {s : Finset ℕ} {Q : Pred.{u}}
    (hQ : Delta0Def s Q) (l : List ℕ) (hl0 : 0 ∉ l) (hl1 : 1 ∉ l) (hl2 : 2 ∉ l)
    {v : ℕ → ZFSet.{u}} (hv : ∀ k ∈ s, k ∉ l → 3 ≤ k → v k ∈ L θ)
    (F : Ordinal.{u} → ZFSet.{u})
    (hstep : ∀ ξ < θ, graphBelow F ξ ∈ L θ → F ξ ∈ L θ ∧
      ExsD (· ∈ L θ) l (Q (· ∈ L θ)) (upd3 v ξ.toZFSet (graphBelow F ξ) (F ξ)))
    (huniq : ∀ ξ < θ, ∀ y ∈ L θ,
      ExsD (· ∈ L θ) l (Q (· ∈ L θ)) (upd3 v ξ.toZFSet (graphBelow F ξ) y) → y = F ξ) :
    ∀ ξ < θ, graphBelow F ξ ∈ L θ := by
  set W := L θ with hW
  have hT := L_transitive θ
  have hlim := hθ.isSuccLimit
  have hWgood : GoodDom (· ∈ W) := hθ.goodDom
  have hord : ∀ ξ < θ, ξ.toZFSet ∈ W := fun ξ hξ => (toZFSet_mem_L_iff θ ξ).mpr hξ
  -- the formula version of `Q`
  obtain ⟨φ, hφ, hfv, hsat⟩ := hQ
  set Q' : Pred.{u} := fun D w => Sat D w φ with hQ'
  have hQ'def : Delta0Def s Q' := ⟨φ, hφ, hfv, fun _ _ _ _ => Iff.rfl⟩
  have hQQ' : ∀ w, ValD (· ∈ W) s w → (Q (· ∈ W) w ↔ Q' (· ∈ W) w) :=
    fun w hw => (hsat _ w hWgood hw).symm
  have hQ'cong : ∀ D w w', (∀ k ∈ s, w k = w' k) → (Q' D w ↔ Q' D w') :=
    fun D w w' hww' => sat_congr (fun k hk => hww' k (hfv hk))
  -- normalized parameter valuation
  set v₀ : ℕ → ZFSet.{u} := fun k => if k < 3 ∨ k ∈ l then ∅ else v k with hv₀
  have hv₀W : ∀ k, v₀ k ∈ W ∨ (k ∈ s → v₀ k ∈ W) := fun k => by
    by_cases h : k < 3 ∨ k ∈ l
    · left; simp only [v₀, h, if_true]; exact empty_mem_L_of_limit hlim
    · right; intro hk; simp only [v₀, h, if_false]; push Not at h; exact hv k hk h.2 h.1
  have hv₀s : ∀ k ∈ s, v₀ k ∈ W := fun k hk => (hv₀W k).elim id (fun h => h hk)
  have hvv₀ : ∀ k, k ∉ l → 3 ≤ k → v k = v₀ k := fun k hkl hk3 => by
    simp [v₀, hkl, show ¬ k < 3 by omega]
  have hupd3 : ∀ ζ g y, ∀ k, k ∉ l → upd3 v ζ g y k = upd3 v₀ ζ g y k := by
    intro ζ g y k hkl
    rcases lt_or_ge k 3 with hk3 | hk3
    · unfold upd3; interval_cases k <;> simp
    · rw [upd3_apply_of_ge hk3, upd3_apply_of_ge hk3]; exact hvv₀ k hkl hk3
  -- the step and uniqueness hypotheses for `Q'` and `v₀`
  have hstep' : ∀ ξ < θ, graphBelow F ξ ∈ W → F ξ ∈ W ∧
      ExsD (· ∈ W) l (Q' (· ∈ W)) (upd3 v₀ ξ.toZFSet (graphBelow F ξ) (F ξ)) := by
    intro ξ hξ hg
    obtain ⟨hF, h⟩ := hstep ξ hξ hg
    refine ⟨hF, ?_⟩
    rw [← exsD_congr_outside (hQ'cong _) l _ _ (fun k _ hkl => hupd3 _ _ _ k hkl)]
    rw [← exsD_congr_valD hQQ' l]
    · exact h
    · intro k hk hkl
      rcases lt_or_ge k 3 with hk3 | hk3
      · unfold upd3; interval_cases k <;> simp [hord ξ hξ, hg, hF]
      · rw [upd3_apply_of_ge hk3]; exact hv k hk hkl hk3
  have huniq' : ∀ ξ < θ, graphBelow F ξ ∈ W → ∀ y ∈ W,
      ExsD (· ∈ W) l (Q' (· ∈ W)) (upd3 v₀ ξ.toZFSet (graphBelow F ξ) y) → y = F ξ := by
    intro ξ hξ hg y hy h
    apply huniq ξ hξ y hy
    rw [← exsD_congr_outside (hQ'cong _) l _ _ (fun k _ hkl => hupd3 _ _ _ k hkl)] at h
    rw [exsD_congr_valD hQQ' l]
    · exact h
    · intro k hk hkl
      rcases lt_or_ge k 3 with hk3 | hk3
      · unfold upd3; interval_cases k <;> simp [hord ξ hξ, hg, hy]
      · rw [upd3_apply_of_ge hk3]; exact hv k hk hkl hk3
  -- fresh variables
  set M : ℕ := s.sup id + l.sum + 3 with hM
  have hMs : ∀ k ∈ s, k < M := fun k hk => by
    have := Finset.le_sup (f := id) hk; simp only [id] at this; omega
  have hMl : ∀ k ∈ l, k < M := fun k hk => by have := List.le_sum_of_mem hk; omega
  have hPA := delta0_PA hQ'def l hl0 hl1 hl2 M (M + 1) (M + 2) hMs hMl (by omega) rfl rfl
  -- main induction
  intro ξ
  induction ξ using Ordinal.limitRecOn with
  | zero => intro _; rw [graphBelow_zero]; exact empty_mem_L_of_limit hlim
  | add_one ξ ih =>
    intro hξ1
    have hξ : ξ < θ := (Order.lt_add_one_iff.mpr le_rfl).trans hξ1
    have hg := ih hξ
    rw [graphBelow_succ]
    exact insert_mem_L_of_limit hlim (kpair_mem_L_of_limit hlim (hord ξ hξ) (hstep ξ hξ hg).1) hg
  | limit lam hlamlim ih =>
    intro hlam
    -- Step A: for each `ζ₀ < λ`, a witness set `b` making the graph below `ζ₀` a partial approximation
    have stepA : ∀ ζ₀ < lam, ∃ b ∈ W, PA Q' l (· ∈ W) v₀ ζ₀.toZFSet (graphBelow F ζ₀) b := by
      intro ζ₀ hζ₀
      have hζ₀θ : ζ₀ < θ := hζ₀.trans hlam
      have hg₀ : graphBelow F ζ₀ ∈ W := ih ζ₀ hζ₀ hζ₀θ
      -- the matrix with the restriction and value conditions
      set Q₂ : Pred.{u} := fun D w =>
        (IsRestrict (w (M + 1)) (w 0) (w 1) ∧ ZFSet.pair (w 0) (w 2) ∈ w (M + 1)) ∧ Q' D w with hQ₂
      have hQ₂def : Delta0Def ((({M + 1, 0, 1} ∪ {M + 1, 0, 2}) ∪ s)) Q₂ :=
        ((delta0_isRestrict (M + 1) 0 1 (by omega) (by omega) (by omega)).and
          (delta0_funVal (M + 1) 0 2 (by omega) (by omega) (by omega))).and hQ'def
      set w₀ : ℕ → ZFSet.{u} := Function.update (Function.update v₀ M ζ₀.toZFSet) (M + 1) (graphBelow F ζ₀)
        with hw₀
      have hindep : ∀ (w : ℕ → ZFSet.{u}) i y, i ∈ l →
          ((IsRestrict (Function.update w i y (M + 1)) (Function.update w i y 0)
              (Function.update w i y 1) ∧
            ZFSet.pair (Function.update w i y 0) (Function.update w i y 2) ∈
              Function.update w i y (M + 1)) ↔
          (IsRestrict (w (M + 1)) (w 0) (w 1) ∧ ZFSet.pair (w 0) (w 2) ∈ w (M + 1))) := by
        intro w i y hi
        have h0 : i ≠ 0 := fun h => hl0 (h ▸ hi)
        have h1 : i ≠ 1 := fun h => hl1 (h ▸ hi)
        have h2 : i ≠ 2 := fun h => hl2 (h ▸ hi)
        have hM1 : i ≠ M + 1 := fun h => by have := hMl i hi; omega
        rw [Function.update_of_ne h0.symm, Function.update_of_ne h1.symm,
          Function.update_of_ne h2.symm, Function.update_of_ne hM1.symm]
      have hvW : ∀ k ∈ (({M + 1, 0, 1} ∪ {M + 1, 0, 2}) ∪ s), k ∉ (1 :: 2 :: l) → k ≠ 0 → w₀ k ∈ W := by
        intro k hk hkl hk0
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hk
        have hk1 : k ≠ 1 := fun h => hkl (by simp [h])
        have hk2 : k ≠ 2 := fun h => hkl (by simp [h])
        have hkl' : k ∉ l := fun h => hkl (by simp [h])
        rcases hk with ((h | h | h) | (h | h | h)) | hk
        · rw [h]; simp [w₀, hg₀]
        · exact absurd h hk0
        · exact absurd h hk1
        · rw [h]; simp [w₀, hg₀]
        · exact absurd h hk0
        · exact absurd h hk2
        · have hkM : k ≠ M := fun h => by have := hMs k hk; omega
          have hkM1 : k ≠ M + 1 := fun h => by have := hMs k hk; omega
          simp only [w₀, Function.update_of_ne hkM1, Function.update_of_ne hkM]
          exact hv₀s k hk
      have haW : w₀ M ∈ W := by
        simp [w₀, Function.update_of_ne (show M ≠ M + 1 by omega), hord ζ₀ hζ₀θ]
      have hwit : ∀ ζ' ∈ w₀ M, ExsD (· ∈ W) (1 :: 2 :: l) (Q₂ (· ∈ W)) (Function.update w₀ 0 ζ') := by
        intro ζ' hζ'
        rw [show w₀ M = ζ₀.toZFSet by simp [w₀, Function.update_of_ne (show M ≠ M + 1 by omega)]] at hζ'
        obtain ⟨ξ', hξ', rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ'
        have hξ'θ : ξ' < θ := hξ'.trans hζ₀θ
        have hg' : graphBelow F ξ' ∈ W := ih ξ' (hξ'.trans hζ₀) hξ'θ
        obtain ⟨hF', hexs'⟩ := hstep' ξ' hξ'θ hg'
        refine ⟨graphBelow F ξ', hg', F ξ', hF', ?_⟩
        rw [exsD_and_of_indep hindep]
        refine ⟨?_, ?_⟩
        · simp only [Function.update_self, Function.update_of_ne (show (2 : ℕ) ≠ 0 by decide),
            Function.update_of_ne (show (1 : ℕ) ≠ 0 by decide),
            Function.update_of_ne (show (2 : ℕ) ≠ 1 by decide)]
          rw [Function.update_of_ne (show M + 1 ≠ 2 by omega),
            Function.update_of_ne (show M + 1 ≠ 1 by omega),
            Function.update_of_ne (show M + 1 ≠ 0 by omega)]
          simp only [w₀, Function.update_self]
          exact ⟨isRestrict_graphBelow hξ'.le, pair_mem_graphBelow_iff.mpr ⟨hξ', rfl⟩⟩
        · rw [exsD_congr_outside (hQ'cong _) l _ _ ?_]
          · exact hexs'
          · intro k hk hkl
            have hkM : k ≠ M := fun h => by have := hMs k hk; omega
            have hkM1 : k ≠ M + 1 := fun h => by have := hMs k hk; omega
            rcases lt_or_ge k 3 with hk3 | hk3
            · show upd3 w₀ _ _ _ k = upd3 v₀ _ _ _ k
              unfold upd3; interval_cases k <;> simp
            · show upd3 w₀ _ _ _ k = upd3 v₀ _ _ _ k
              rw [upd3_apply_of_ge hk3, upd3_apply_of_ge hk3]
              try simp only [w₀, Function.update_of_ne hkM1, Function.update_of_ne hkM]
      obtain ⟨b, hb, hcoll⟩ := sigma1_collection hθ hQ₂def (1 :: 2 :: l) 0 M (by omega)
        (by simp [hl0]) (by simp; exact ⟨by omega, by omega, fun h => by have := hMl M h; omega⟩)
        (v := w₀) hvW haW hwit
      refine ⟨b, hb, graphBelow_isFunc F ζ₀, graphBelow_isDom F ζ₀, ?_⟩
      intro ζ' hζ'
      obtain ⟨g', hg', y, hy, hexs⟩ := hcoll ζ' (by
        simpa [w₀, Function.update_of_ne (show M ≠ M + 1 by omega)] using hζ')
      rw [exsIn_and_of_indep hindep] at hexs
      obtain ⟨⟨hres, hpair⟩, hexs⟩ := hexs
      simp only [Function.update_self, Function.update_of_ne (show (2 : ℕ) ≠ 0 by decide),
        Function.update_of_ne (show (1 : ℕ) ≠ 0 by decide),
        Function.update_of_ne (show (2 : ℕ) ≠ 1 by decide)] at hres hpair
      rw [Function.update_of_ne (show M + 1 ≠ 2 by omega),
        Function.update_of_ne (show M + 1 ≠ 1 by omega),
        Function.update_of_ne (show M + 1 ≠ 0 by omega)] at hres hpair
      simp only [w₀, Function.update_self] at hres hpair
      refine ⟨g', hg', y, hy, hres, hpair, ?_⟩
      rw [exsIn_congr_outside (hQ'cong _) l _ _ ?_] at hexs
      · exact hexs
      · intro k hk hkl
        have hkM : k ≠ M := fun h => by have := hMs k hk; omega
        have hkM1 : k ≠ M + 1 := fun h => by have := hMs k hk; omega
        rcases lt_or_ge k 3 with hk3 | hk3
        · show upd3 w₀ ζ' g' y k = upd3 v₀ ζ' g' y k
          unfold upd3; interval_cases k <;> simp
        · show upd3 w₀ ζ' g' y k = upd3 v₀ ζ' g' y k
          rw [upd3_apply_of_ge hk3, upd3_apply_of_ge hk3]
          try simp only [w₀, Function.update_of_ne hkM1, Function.update_of_ne hkM]
    -- absoluteness of `PA` between the universe and `W`
    have hQ'abs : ∀ w', ValD (· ∈ W) s w' → (Q' (fun _ => True) w' ↔ Q' (· ∈ W) w') :=
      fun w' hw' => (hφ.sat_iff_satV (transDom_mem hT) (fun k hk => hw' k (hfv hk))).symm
    have hPAabs : ∀ (w' : ℕ → ZFSet.{u}), (∀ k ∈ s, k ∉ l → 3 ≤ k → w' k ∈ W) →
        ∀ ζ₀ ∈ W, ∀ g b, (∀ z ∈ b, z ∈ W) →
        (PA Q' l (fun _ => True) w' ζ₀ g b ↔ PA Q' l (· ∈ W) w' ζ₀ g b) := by
      intro w' hw' ζ₀ hζ₀ g b hb
      unfold PA
      apply and_congr_right; intro _; apply and_congr_right; intro _
      apply forall_congr'; intro ζ'; apply imp_congr_right; intro hζ'
      apply exists_congr; intro g'; apply and_congr_right; intro hg'
      apply exists_congr; intro y; apply and_congr_right; intro hy
      apply and_congr_right; intro _; apply and_congr_right; intro _
      apply exsIn_congr_valD hb hQ'abs l
      intro k hk hkl
      have hζ'W : ζ' ∈ W := hT.subset_of_mem hζ₀ hζ'
      show upd3 w' ζ' g' y k ∈ W
      rcases lt_or_ge k 3 with hk3 | hk3
      · unfold upd3; interval_cases k <;> simp [hζ'W, hb g' hg', hb y hy]
      · rw [upd3_apply_of_ge hk3]; exact hw' k hk hkl hk3
    -- Step B: collect the partial approximations for all `ζ₀ < lam`
    set PAP : Pred.{u} := fun D w => PA Q' l D w (w M) (w (M + 1)) (w (M + 2)) with hPAP
    set w₁ : ℕ → ZFSet.{u} := Function.update v₀ (M + 3) lam.toZFSet with hw₁
    have hw₁s : ∀ k ∈ s, w₁ k = v₀ k := fun k hk => by
      have := hMs k hk; simp [hw₁, Function.update_of_ne (show k ≠ M + 3 by omega)]
    have hvW₁ : ∀ k ∈ insert M (insert (M + 1) (insert (M + 2) s)), k ∉ [M + 1, M + 2] → k ≠ M →
        w₁ k ∈ W := by
      intro k hk hkl hkM
      simp only [Finset.mem_insert] at hk
      rcases hk with rfl | rfl | rfl | hk
      · exact absurd rfl hkM
      · exact absurd (by simp) hkl
      · exact absurd (by simp) hkl
      · rw [hw₁s k hk]; exact hv₀s k hk
    have haW₁ : w₁ (M + 3) ∈ W := by simp [hw₁, hord lam hlam]
    have hwit₁ : ∀ ζ₀ ∈ w₁ (M + 3), ExsD (· ∈ W) [M + 1, M + 2] (PAP (· ∈ W)) (Function.update w₁ M ζ₀) := by
      intro ζ₀ hζ₀
      rw [show w₁ (M + 3) = lam.toZFSet by simp [hw₁]] at hζ₀
      obtain ⟨ξ₀, hξ₀, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ₀
      obtain ⟨b, hb, hPAb⟩ := stepA ξ₀ hξ₀
      refine ⟨graphBelow F ξ₀, ih ξ₀ hξ₀ (hξ₀.trans hlam), b, hb, ?_⟩
      simp only [ExsD, hPAP]
      simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      rw [PA_congr_v (hQ'cong _) (v' := v₀)]
      · exact hPAb
      · intro k hk hkl hk3
        have := hMs k hk
        simp (disch := omega) only [Function.update_of_ne]
        exact hw₁s k hk
    obtain ⟨B, hB, hcollB⟩ := sigma1_collection hθ hPA [M + 1, M + 2] M (M + 3) (by omega)
      (by simp) (by simp) (v := w₁) hvW₁ haW₁ hwit₁
    have hBW : ∀ z ∈ B, z ∈ W := fun z hz => hT.subset_of_mem hB hz
    -- from the collected set: for every `ξ₀ < lam` a partial approximation `g ∈ B` with witnesses `b ∈ B`
    have hcollB' : ∀ ξ₀ < lam, ∃ g ∈ B, ∃ b ∈ B, PA Q' l (· ∈ W) v₀ ξ₀.toZFSet g b := by
      intro ξ₀ hξ₀
      have hmem : ξ₀.toZFSet ∈ w₁ (M + 3) := by
        simp only [hw₁, Function.update_self]; exact Ordinal.mem_toZFSet_iff.mpr ⟨ξ₀, hξ₀, rfl⟩
      obtain ⟨g, hg, b, hb, hPAb⟩ := hcollB _ hmem
      refine ⟨g, hg, b, hb, ?_⟩
      simp only [ExsIn, hPAP] at hPAb
      try simp (disch := omega) only [Function.update_self, Function.update_of_ne] at hPAb
      rw [PA_congr_v (hQ'cong _) (v' := v₀)] at hPAb
      · exact hPAb
      · intro k hk hkl hk3
        have := hMs k hk
        simp (disch := omega) only [Function.update_of_ne]
        exact hw₁s k hk
    -- Step C: the union of the partial approximations in `B`
    set PC : Pred.{u} := fun D w => ∃ y ∈ w (M + 3), ∃ x ∈ Function.update w M y (M + 4),
      PAP D (Function.update (Function.update w M y) (M + 2) x) with hPC
    have hPCdef : Delta0Def (insert (M + 3) ((insert (M + 4)
        ((insert M (insert (M + 1) (insert (M + 2) s))).erase (M + 2))).erase M)) PC :=
      (hPA.bex (M + 2) (M + 4) (by omega)).bex M (M + 3) (by omega)
    set v₂ : ℕ → ZFSet.{u} := Function.update (Function.update v₀ (M + 3) lam.toZFSet) (M + 4) B with hv₂
    have hv₂val : ValD (· ∈ W) ((insert (M + 3) ((insert (M + 4)
        ((insert M (insert (M + 1) (insert (M + 2) s))).erase (M + 2))).erase M)).erase (M + 1)) v₂ := by
      intro k hk
      simp only [Finset.mem_erase, Finset.mem_insert] at hk
      rcases hk with ⟨h1, h2 | ⟨h3, h4 | ⟨h5, h6 | h6 | h6 | h6⟩⟩⟩
      · subst h2
        simp only [hv₂, Function.update_of_ne (show M + 3 ≠ M + 4 by omega), Function.update_self]
        exact hord lam hlam
      · subst h4
        simp only [hv₂, Function.update_self]
        exact hB
      · exact absurd h6 h3
      · exact absurd h6 h1
      · exact absurd h6 h5
      · have := hMs k h6
        simp (disch := omega) only [hv₂, Function.update_of_ne]
        exact hv₀s k h6
    have hG := sep_mem_L_of_limit hlim hPCdef (M + 1) hv₂val hB
    set G : ZFSet.{u} := ZFSet.sep (fun x => PC (fun _ => True) (Function.update v₂ (M + 1) x)) B with hGdef
    -- membership in `G`
    have hmemG : ∀ g, g ∈ G ↔ g ∈ B ∧ ∃ ξ₀ < lam, ∃ b ∈ B, PA Q' l (· ∈ W) v₀ ξ₀.toZFSet g b := by
      intro g
      simp only [hGdef, ZFSet.mem_sep]
      apply and_congr_right; intro hgB
      simp only [hPC, hPAP, hv₂]
      simp (disch := omega) only [Function.update_self, Function.update_of_ne]
      constructor
      · rintro ⟨ζ₀, hζ₀, b, hb, hPAg⟩
        obtain ⟨ξ₀, hξ₀, rfl⟩ := Ordinal.mem_toZFSet_iff.mp hζ₀
        refine ⟨ξ₀, hξ₀, b, hb, ?_⟩
        rw [PA_congr_v (hQ'cong _) (v' := v₀)] at hPAg
        · rw [← hPAabs v₀ (fun k hk hkl hk3 => hv₀s k hk) _ (hord ξ₀ (hξ₀.trans hlam)) g b (fun z hz => hT.subset_of_mem (hBW b hb) hz)]
          exact hPAg
        · intro k hk hkl hk3
          have := hMs k hk
          simp (disch := omega) only [Function.update_of_ne]
      · rintro ⟨ξ₀, hξ₀, b, hb, hPAg⟩
        refine ⟨ξ₀.toZFSet, Ordinal.mem_toZFSet_iff.mpr ⟨ξ₀, hξ₀, rfl⟩, b, hb, ?_⟩
        rw [PA_congr_v (hQ'cong _) (v' := v₀)]
        · rw [hPAabs v₀ (fun k hk hkl hk3 => hv₀s k hk) _ (hord ξ₀ (hξ₀.trans hlam)) g b (fun z hz => hT.subset_of_mem (hBW b hb) hz)]
          exact hPAg
        · intro k hk hkl hk3
          have := hMs k hk
          simp (disch := omega) only [Function.update_of_ne]
    -- the union of `G` is the graph below `lam`
    have hunion : graphBelow F lam = ZFSet.sUnion G := by
      ext p
      rw [ZFSet.mem_sUnion, mem_graphBelow]
      constructor
      · rintro ⟨ξ', hξ', rfl⟩
        have hξ₀ : ξ' + 1 < lam := hlamlim.add_one_lt hξ'
        obtain ⟨g, hg, b, hb, hPAg⟩ := hcollB' (ξ' + 1) hξ₀
        have hgeq : g = graphBelow F (ξ' + 1) :=
          PA_unique huniq' (ξ' + 1) (hξ₀.trans hlam) g b (fun z hz => hT.subset_of_mem (hBW b hb) hz) hPAg
        refine ⟨g, (hmemG g).mpr ⟨hg, ξ' + 1, hξ₀, b, hb, hPAg⟩, ?_⟩
        rw [hgeq]
        exact pair_mem_graphBelow_iff.mpr ⟨Order.lt_add_one_iff.mpr le_rfl, rfl⟩
      · rintro ⟨g, hg, hp⟩
        obtain ⟨_, ξ₀, hξ₀, b, hb, hPAg⟩ := (hmemG g).mp hg
        have hgeq : g = graphBelow F ξ₀ :=
          PA_unique huniq' ξ₀ (hξ₀.trans hlam) g b (fun z hz => hT.subset_of_mem (hBW b hb) hz) hPAg
        rw [hgeq, mem_graphBelow] at hp
        obtain ⟨ξ', hξ', rfl⟩ := hp
        exact ⟨ξ', hξ'.trans hξ₀, rfl⟩
    rw [hunion]
    exact sUnion_mem_L_of_limit hlim hG

/-- **Lemma 10.3** in the paper's existence-and-uniqueness form.  Under the hypotheses of
`sigma1_recursion`, for every `η` with `η + 1 < θ` there is *exactly one* set `G ∈ L θ` which is
a function with domain `η + 1` and satisfies the recursion equation `Φ(ξ, G ↾ ξ, G ξ)` at every
`ξ ≤ η`; it is the graph of `F` on `η + 1`. -/
theorem sigma1_recursion_existsUnique {θ : Ordinal.{u}} (hθ : IsAdmissible θ) {s : Finset ℕ}
    {Q : Pred.{u}} (hQ : Delta0Def s Q) (l : List ℕ) (hl0 : 0 ∉ l) (hl1 : 1 ∉ l) (hl2 : 2 ∉ l)
    {v : ℕ → ZFSet.{u}} (hv : ∀ k ∈ s, k ∉ l → 3 ≤ k → v k ∈ L θ)
    (F : Ordinal.{u} → ZFSet.{u})
    (hstep : ∀ ξ < θ, graphBelow F ξ ∈ L θ → F ξ ∈ L θ ∧
      ExsD (· ∈ L θ) l (Q (· ∈ L θ)) (upd3 v ξ.toZFSet (graphBelow F ξ) (F ξ)))
    (huniq : ∀ ξ < θ, ∀ y ∈ L θ,
      ExsD (· ∈ L θ) l (Q (· ∈ L θ)) (upd3 v ξ.toZFSet (graphBelow F ξ) y) → y = F ξ)
    {η : Ordinal.{u}} (hη : η + 1 < θ) :
    ∃! G : ZFSet.{u}, G ∈ L θ ∧ IsFunc G ∧ IsDom G (η + 1).toZFSet ∧
      ∀ ξ ≤ η, ∀ g y, IsRestrict G ξ.toZFSet g → ZFSet.pair ξ.toZFSet y ∈ G →
        ExsD (· ∈ L θ) l (Q (· ∈ L θ)) (upd3 v ξ.toZFSet g y) := by
  have hT := L_transitive θ
  have hsucc : η < η + 1 := Order.lt_add_one_iff.mpr le_rfl
  have hηθ : η < θ := hsucc.trans hη
  have hgraph : ∀ ξ < θ, graphBelow F ξ ∈ L θ :=
    sigma1_recursion hθ hQ l hl0 hl1 hl2 hv F hstep huniq
  refine ⟨graphBelow F (η + 1),
    ⟨hgraph _ hη, graphBelow_isFunc F _, graphBelow_isDom F _, ?_⟩, ?_⟩
  · intro ξ hξ g y hres hpair
    have hξθ : ξ < θ := hξ.trans_lt hηθ
    have hgeq : g = graphBelow F ξ :=
      isRestrict_unique hres (isRestrict_graphBelow (hξ.trans hsucc.le))
    have hyeq : y = F ξ := (pair_mem_graphBelow_iff.mp hpair).2
    rw [hgeq, hyeq]
    exact (hstep ξ hξθ (hgraph ξ hξθ)).2
  · rintro G ⟨hGL, hGf, hGd, hGrec⟩
    have key : ∀ ξ : Ordinal.{u}, ξ ≤ η → ∀ y, ZFSet.pair ξ.toZFSet y ∈ G → y = F ξ := by
      intro ξ
      induction ξ using Ordinal.induction with
      | _ ξ ih =>
      intro hξ y hy
      have hξθ : ξ < θ := hξ.trans_lt hηθ
      have hGval : ∀ ζ < ξ, ZFSet.pair ζ.toZFSet (F ζ) ∈ G := by
        intro ζ hζ
        obtain ⟨b, hb⟩ := (hGd ζ.toZFSet).mp
          (Ordinal.mem_toZFSet_iff.mpr ⟨ζ, (hζ.trans_le hξ).trans hsucc, rfl⟩)
        rw [← ih ζ hζ (hζ.trans_le hξ).le b hb]
        exact hb
      have hres : IsRestrict G ξ.toZFSet (graphBelow F ξ) := by
        intro p
        constructor
        · intro hp
          obtain ⟨ζ, hζ, rfl⟩ := mem_graphBelow.mp hp
          exact ⟨hGval ζ hζ, ζ.toZFSet, Ordinal.mem_toZFSet_iff.mpr ⟨ζ, hζ, rfl⟩, _, rfl⟩
        · rintro ⟨hp, a, ha, b, rfl⟩
          obtain ⟨ζ, hζ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp ha
          rw [ih ζ hζ (hζ.trans_le hξ).le b hp]
          exact mem_graphBelow.mpr ⟨ζ, hζ, rfl⟩
      have hpL : ZFSet.pair ξ.toZFSet y ∈ L θ := hT.subset_of_mem hGL hy
      have hyL : y ∈ L θ :=
        hT.subset_of_mem (hT.subset_of_mem hpL (upair_mem_pair _ _)) (mem_upair_right _ _)
      exact huniq ξ hξθ y hyL (hGrec ξ hξ _ y hres hy)
    ext p
    constructor
    · intro hp
      obtain ⟨a, b, rfl⟩ := hGf.1 p hp
      obtain ⟨ζ, hζ, rfl⟩ := Ordinal.mem_toZFSet_iff.mp ((hGd a).mpr ⟨b, hp⟩)
      rw [key ζ (Order.lt_add_one_iff.mp hζ) b hp]
      exact mem_graphBelow.mpr ⟨ζ, hζ, rfl⟩
    · intro hp
      obtain ⟨ζ, hζ, rfl⟩ := mem_graphBelow.mp hp
      obtain ⟨b, hb⟩ := (hGd ζ.toZFSet).mp (Ordinal.mem_toZFSet_iff.mpr ⟨ζ, hζ, rfl⟩)
      rw [← key ζ (Order.lt_add_one_iff.mp hζ) b hb]
      exact hb

end BM4.ST
