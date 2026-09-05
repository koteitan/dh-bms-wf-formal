/-
  Part III, B4 (basics): naturals and `ω` as ZFC sets, closure of limit levels `L θ` under
  insert / union / finite sets, and Δ₀-definability of the basic set-theoretic predicates
  (pairs, functions, domains, updates) used for coding.
-/
import Bm4.SetTheory.Adm

universe u

namespace BM4.ST

open Fm

/-! ### A. Naturals and ω -/

/-- The von Neumann natural `n`. -/
def natZ : ℕ → ZFSet.{u}
  | 0 => ∅
  | n + 1 => insert (natZ n) (natZ n)

theorem natZ_eq_toZFSet (n : ℕ) : natZ.{u} n = (n : Ordinal.{u}).toZFSet := by
  induction n with
  | zero => simp [natZ, Ordinal.toZFSet_zero]
  | succ n ih => rw [natZ, Nat.cast_succ, Ordinal.toZFSet_add_one, ih]

theorem natZ_injective : Function.Injective natZ.{u} := by
  intro m n h
  rw [natZ_eq_toZFSet, natZ_eq_toZFSet] at h
  exact_mod_cast Ordinal.toZFSet_injective h

theorem natZ_mem_ωZ (n : ℕ) : natZ.{u} n ∈ ωZ.{u} := by
  rw [natZ_eq_toZFSet, ωZ, Ordinal.toZFSet_mem_toZFSet_iff]
  exact Ordinal.nat_lt_omega0 n

theorem mem_ωZ_iff {x : ZFSet.{u}} : x ∈ ωZ ↔ ∃ n, x = natZ n := by
  rw [ωZ, Ordinal.mem_toZFSet_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp ha
    exact ⟨n, (natZ_eq_toZFSet n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n, Ordinal.nat_lt_omega0 n, (natZ_eq_toZFSet n).symm⟩

theorem natZ_mem_L {θ : Ordinal.{u}} (h : Ordinal.omega0 < θ) (n : ℕ) : natZ n ∈ L θ := by
  rw [natZ_eq_toZFSet, toZFSet_mem_L_iff]
  exact (Ordinal.nat_lt_omega0 n).trans h

theorem ωZ_mem_L {θ : Ordinal.{u}} (h : Ordinal.omega0 < θ) : ωZ ∈ L θ :=
  (toZFSet_mem_L_iff θ _).mpr h

theorem natZ_mem_natZ_iff {m n : ℕ} : natZ.{u} m ∈ natZ n ↔ m < n := by
  rw [natZ_eq_toZFSet, natZ_eq_toZFSet, Ordinal.toZFSet_mem_toZFSet_iff]
  exact_mod_cast Iff.rfl

/-! ### B. Closure of limit levels -/

theorem insert_eq_sUnion (a b : ZFSet.{u}) : insert a b = ZFSet.sUnion ({{a}, b} : ZFSet.{u}) := by
  ext x
  rw [ZFSet.mem_insert_iff, ZFSet.mem_sUnion]
  constructor
  · rintro (rfl | hx)
    · exact ⟨{x}, by simp, by simp⟩
    · exact ⟨b, by simp, hx⟩
  · rintro ⟨z, hz, hx⟩
    rw [ZFSet.mem_pair] at hz
    rcases hz with rfl | rfl
    · exact Or.inl (ZFSet.mem_singleton.mp hx)
    · exact Or.inr hx

theorem insert_mem_L_of_limit {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) {a b : ZFSet.{u}}
    (ha : a ∈ L θ) (hb : b ∈ L θ) : insert a b ∈ L θ := by
  rw [insert_eq_sUnion]
  exact sUnion_mem_L_of_limit hθ (pair_mem_L_of_limit hθ (singleton_mem_L_of_limit hθ ha) hb)

theorem union_mem_L_of_limit {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) {a b : ZFSet.{u}}
    (ha : a ∈ L θ) (hb : b ∈ L θ) : a ∪ b ∈ L θ := by
  rw [← ZFSet.sUnion_pair]
  exact sUnion_mem_L_of_limit hθ (pair_mem_L_of_limit hθ ha hb)

theorem empty_mem_L_of_limit {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) : (∅ : ZFSet.{u}) ∈ L θ := by
  rw [← L_zero]
  exact L_mem_L hθ.bot_lt

/-- The set of the elements of a list. -/
def ofList : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | a :: l => insert a (ofList l)

theorem mem_ofList {x : ZFSet.{u}} : ∀ {l : List ZFSet.{u}}, x ∈ ofList l ↔ x ∈ l
  | [] => by simp [ofList]
  | a :: l => by simp [ofList, ZFSet.mem_insert_iff, mem_ofList]

theorem ofList_mem_L_of_limit {θ : Ordinal.{u}} (hθ : Order.IsSuccLimit θ) :
    ∀ (l : List ZFSet.{u}), (∀ x ∈ l, x ∈ L θ) → ofList l ∈ L θ
  | [], _ => empty_mem_L_of_limit hθ
  | a :: l, hl => by
    rw [ofList]
    exact insert_mem_L_of_limit hθ (hl a (by simp))
      (ofList_mem_L_of_limit hθ l (fun x hx => hl x (by simp [hx])))

/-! ### C. Δ₀-definable predicates -/

/-- Transport along an equality of supports. -/
theorem Delta0Def.of_eq {s t : Finset ℕ} {P : Pred.{u}} (h : Delta0Def s P) (hst : s = t) :
    Delta0Def t P := hst ▸ h

theorem delta0_subset (x y : ℕ) (hxy : x ≠ y) : Delta0Def {x, y} (fun _ v => v x ⊆ v y) := by
  have h := (Delta0Def.mem (x + y + 1) y).ball (x + y + 1) x (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp only [Function.update_self, Function.update_of_ne (show y ≠ x + y + 1 by omega)]
    exact ⟨fun H z hz => H z hz, fun H z hz => H hz⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]; omega

theorem delta0_isEmpty (x : ℕ) : Delta0Def.{u} {x} (fun _ v => v x = ∅) := by
  have h := (Delta0Def.falsum.{u}).ball (x + 1) x (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    constructor
    · intro H
      ext z
      simp only [ZFSet.notMem_empty, iff_false]
      exact fun hz => H z hz
    · intro H z hz
      rw [H] at hz
      exact ZFSet.notMem_empty z hz
  · ext k; simp

theorem delta0_isSingleton (s a : ℕ) (h : s ≠ a) : Delta0Def {s, a} (fun _ v => v s = {v a}) := by
  have h1 := ((Delta0Def.eq (s + a + 1) a).ball (s + a + 1) s (by omega)).and (Delta0Def.mem a s)
  refine (h1.congr ?_).of_eq ?_
  · intro D v _ _
    simp only [Function.update_self, Function.update_of_ne (show a ≠ s + a + 1 by omega)]
    constructor
    · rintro ⟨H1, H2⟩
      ext z
      rw [ZFSet.mem_singleton]
      exact ⟨fun hz => H1 z hz, fun hz => hz ▸ H2⟩
    · intro H
      rw [H]
      exact ⟨fun z hz => ZFSet.mem_singleton.mp hz, ZFSet.mem_singleton.mpr rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isUPair (p a b : ℕ) (hpa : p ≠ a) (hpb : p ≠ b) :
    Delta0Def {p, a, b} (fun _ v => v p = {v a, v b}) := by
  set m := p + a + b + 1 with hm
  have h1 := (((Delta0Def.eq m a).or (Delta0Def.eq m b)).ball m p (by omega)).and
    ((Delta0Def.mem a p).and (Delta0Def.mem b p))
  refine (h1.congr ?_).of_eq ?_
  · intro D v _ _
    simp only [Function.update_self, Function.update_of_ne (show a ≠ m by omega),
      Function.update_of_ne (show b ≠ m by omega)]
    constructor
    · rintro ⟨H1, H2, H3⟩
      ext z
      rw [ZFSet.mem_pair]
      constructor
      · exact H1 z
      · rintro (rfl | rfl)
        · exact H2
        · exact H3
    · intro H
      rw [H]
      refine ⟨fun z hz => ZFSet.mem_pair.mp hz, ?_, ?_⟩ <;> simp
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isKPair (z a b : ℕ) (hza : z ≠ a) (hzb : z ≠ b) :
    Delta0Def {z, a, b} (fun _ v => v z = ZFSet.pair (v a) (v b)) := by
  set m := z + a + b + 1 with hm
  -- `∀ w ∈ z, w = {a} ∨ w = {a, b}`
  have h1 := ((delta0_isSingleton m a (by omega)).or (delta0_isUPair m a b (by omega) (by omega))).ball
    m z (by omega)
  -- `∃ w ∈ z, w = {a}` and `∃ w ∈ z, w = {a, b}`
  have h2 := (delta0_isSingleton m a (by omega)).bex m z (by omega)
  have h3 := (delta0_isUPair m a b (by omega) (by omega)).bex m z (by omega)
  refine ((h1.and (h2.and h3)).congr ?_).of_eq ?_
  · intro D v _ _
    simp only [Function.update_self, Function.update_of_ne (show a ≠ m by omega),
      Function.update_of_ne (show b ≠ m by omega)]
    constructor
    · rintro ⟨H1, ⟨w1, hw1, rfl⟩, ⟨w2, hw2, rfl⟩⟩
      ext y
      rw [ZFSet.pair, ZFSet.mem_pair]
      constructor
      · exact H1 y
      · rintro (rfl | rfl)
        · exact hw1
        · exact hw2
    · intro H
      rw [H]
      refine ⟨fun y hy => ?_, ⟨_, ?_, rfl⟩, ⟨_, ?_, rfl⟩⟩
      · rw [ZFSet.pair, ZFSet.mem_pair] at hy; exact hy
      · simp [ZFSet.pair]
      · simp [ZFSet.pair]
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isInsert (w a b : ℕ) (hwa : w ≠ a) (hwb : w ≠ b) :
    Delta0Def {w, a, b} (fun _ v => v w = insert (v a) (v b)) := by
  set m := w + a + b + 1 with hm
  have h1 := (((Delta0Def.eq m a).or (Delta0Def.mem m b)).ball m w (by omega)).and
    ((Delta0Def.mem a w).and ((Delta0Def.mem m w).ball m b (by omega)))
  refine (h1.congr ?_).of_eq ?_
  · intro D v _ _
    simp only [Function.update_self, Function.update_of_ne (show a ≠ m by omega),
      Function.update_of_ne (show b ≠ m by omega), Function.update_of_ne (show w ≠ m by omega)]
    constructor
    · rintro ⟨H1, H2, H3⟩
      ext z
      rw [ZFSet.mem_insert_iff]
      exact ⟨H1 z, fun h => h.elim (fun h => h ▸ H2) (H3 z)⟩
    · intro H
      rw [H]
      exact ⟨fun z hz => ZFSet.mem_insert_iff.mp hz, ZFSet.mem_insert _ _,
        fun z hz => ZFSet.mem_insert_iff.mpr (Or.inr hz)⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isSucc (y x : ℕ) (hyx : y ≠ x) : Delta0Def {y, x} (fun _ v => v y = insert (v x) (v x)) :=
  (delta0_isInsert y x x hyx hyx).of_eq (by ext k; simp)

theorem delta0_isTransitive (x : ℕ) : Delta0Def {x} (fun _ v => (v x).IsTransitive) := by
  have h := (((Delta0Def.mem (x + 2) x).ball (x + 2) (x + 1) (by omega)).ball (x + 1) x (by omega))
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp only [Function.update_self, Function.update_of_ne (show x ≠ x + 1 by omega),
      Function.update_of_ne (show x ≠ x + 2 by omega),
      Function.update_of_ne (show x + 1 ≠ x + 2 by omega)]
    exact ⟨fun H y hy z hz => H y hy z hz, fun H y hy z hz => H y hy hz⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]; omega

theorem delta0_isOrdinal (x : ℕ) : Delta0Def {x} (fun _ v => (v x).IsOrdinal) := by
  have h := (delta0_isTransitive x).and ((delta0_isTransitive (x + 1)).ball (x + 1) x (by omega))
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp only [Function.update_self]
    rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isSUnion (w a : ℕ) (hwa : w ≠ a) :
    Delta0Def {w, a} (fun _ v => v w = ZFSet.sUnion (v a)) := by
  set m := w + a + 1 with hm
  -- `∀ z ∈ w, ∃ y ∈ a, z ∈ y` and `∀ y ∈ a, ∀ z ∈ y, z ∈ w`
  have h1 := ((Delta0Def.mem m (m + 1)).bex (m + 1) a (by omega)).ball m w (by omega)
  have h2 := ((Delta0Def.mem (m + 1) w).ball (m + 1) m (by omega)).ball m a (by omega)
  refine ((h1.and h2).congr ?_).of_eq ?_
  · intro D v _ _
    simp only [Function.update_self, Function.update_of_ne (show a ≠ m by omega),
      Function.update_of_ne (show w ≠ m by omega), Function.update_of_ne (show w ≠ m + 1 by omega),
      Function.update_of_ne (show m ≠ m + 1 by omega)]
    constructor
    · rintro ⟨H1, H2⟩
      ext z
      rw [ZFSet.mem_sUnion]
      exact ⟨H1 z, fun ⟨y, hy, hz⟩ => H2 y hy z hz⟩
    · intro H
      rw [H]
      exact ⟨fun z hz => ZFSet.mem_sUnion.mp hz, fun y hy z hz => ZFSet.mem_sUnion.mpr ⟨y, hy, hz⟩⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

theorem delta0_isUnion (w a b : ℕ) (hwa : w ≠ a) (hwb : w ≠ b) :
    Delta0Def {w, a, b} (fun _ v => v w = v a ∪ v b) := by
  set m := w + a + b + 1 with hm
  have h1 := (((Delta0Def.mem m a).or (Delta0Def.mem m b)).ball m w (by omega)).and
    (((Delta0Def.mem m w).ball m a (by omega)).and ((Delta0Def.mem m w).ball m b (by omega)))
  refine (h1.congr ?_).of_eq ?_
  · intro D v _ _
    simp only [Function.update_self, Function.update_of_ne (show a ≠ m by omega),
      Function.update_of_ne (show b ≠ m by omega), Function.update_of_ne (show w ≠ m by omega)]
    constructor
    · rintro ⟨H1, H2, H3⟩
      ext z
      rw [ZFSet.mem_union]
      exact ⟨H1 z, fun h => h.elim (H2 z) (H3 z)⟩
    · intro H
      rw [H]
      exact ⟨fun z hz => ZFSet.mem_union.mp hz, fun z hz => ZFSet.mem_union.mpr (Or.inl hz),
        fun z hz => ZFSet.mem_union.mpr (Or.inr hz)⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-! ### Functions as sets of Kuratowski pairs -/

theorem singleton_mem_pair (a b : ZFSet.{u}) : ({a} : ZFSet.{u}) ∈ ZFSet.pair a b := by
  simp [ZFSet.pair]

theorem upair_mem_pair (a b : ZFSet.{u}) : ({a, b} : ZFSet.{u}) ∈ ZFSet.pair a b := by
  simp [ZFSet.pair]

theorem mem_upair_right (a b : ZFSet.{u}) : b ∈ ({a, b} : ZFSet.{u}) := by simp

theorem mem_upair_left (a b : ZFSet.{u}) : a ∈ ({a, b} : ZFSet.{u}) := by simp

theorem delta0_funVal (f a b : ℕ) (hfa : f ≠ a) (hfb : f ≠ b) (hab : a ≠ b) :
    Delta0Def {f, a, b} (fun _ v => ZFSet.pair (v a) (v b) ∈ v f) := by
  set m := f + a + b + 1 with hm
  have h := (delta0_isKPair m a b (by omega) (by omega)).bex m f (by omega)
  refine (h.congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨p, hp, rfl⟩; exact hp
    · intro H; exact ⟨_, H, rfl⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]; omega

/-- `f` is a function: a set of Kuratowski pairs, single-valued. -/
def IsFunc (f : ZFSet.{u}) : Prop :=
  (∀ p ∈ f, ∃ a b, p = ZFSet.pair a b) ∧
    ∀ a b b', ZFSet.pair a b ∈ f → ZFSet.pair a b' ∈ f → b = b'

theorem delta0_isFunc (f : ℕ) : Delta0Def {f} (fun _ v => IsFunc (v f)) := by
  set m := f + 1 with hm
  -- `∀ p ∈ f, ∃ q ∈ p, ∃ a ∈ q, ∃ q' ∈ p, ∃ b ∈ q', p = pair a b`
  have a1 := delta0_isKPair m (m + 2) (m + 4) (by omega) (by omega)
  have a2 := a1.bex (m + 4) (m + 3) (by omega)
  have a3 := a2.bex (m + 3) m (by omega)
  have a4 := a3.bex (m + 2) (m + 1) (by omega)
  have a5 := a4.bex (m + 1) m (by omega)
  have h1 := a5.ball m f (by omega)
  -- `∀ p ∈ f, ∀ q ∈ p, ∀ a ∈ q, ∀ q' ∈ p, ∀ b ∈ q', p = pair a b →
  --    ∀ p2 ∈ f, ∀ q2 ∈ p2, ∀ b' ∈ q2, p2 = pair a b' → b = b'`
  have b1 := (delta0_isKPair (m + 5) (m + 2) (m + 7) (by omega) (by omega)).imp
    (Delta0Def.eq (m + 4) (m + 7))
  have b2 := b1.ball (m + 7) (m + 6) (by omega)
  have b3 := b2.ball (m + 6) (m + 5) (by omega)
  have b4 := b3.ball (m + 5) f (by omega)
  have b5 := a1.imp b4
  have b6 := b5.ball (m + 4) (m + 3) (by omega)
  have b7 := b6.ball (m + 3) m (by omega)
  have b8 := b7.ball (m + 2) (m + 1) (by omega)
  have b9 := b8.ball (m + 1) m (by omega)
  have h2 := b9.ball m f (by omega)
  refine ((h1.and h2).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨H1, H2⟩
      refine ⟨fun p hp => ?_, fun a b b' hab hab' => ?_⟩
      · obtain ⟨q, _, a, _, q', _, b, _, hpab⟩ := H1 p hp
        exact ⟨a, b, hpab⟩
      · exact H2 _ hab _ (singleton_mem_pair a b) a (ZFSet.mem_singleton.mpr rfl) _
          (upair_mem_pair a b) b (mem_upair_right a b) rfl _ hab' _ (upair_mem_pair a b') b'
          (mem_upair_right a b') rfl
    · rintro ⟨H1, H2⟩
      refine ⟨fun p hp => ?_, ?_⟩
      · obtain ⟨a, b, rfl⟩ := H1 p hp
        exact ⟨_, singleton_mem_pair a b, a, ZFSet.mem_singleton.mpr rfl, _, upair_mem_pair a b,
          b, mem_upair_right a b, rfl⟩
      · intro p hp q _ a _ q' _ b _ hpab p2 hp2 q2 _ b' _ hp2ab
        subst hpab; subst hp2ab
        exact H2 a b b' hp hp2
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `d` is the domain of `f`. -/
def IsDom (f d : ZFSet.{u}) : Prop := ∀ a, a ∈ d ↔ ∃ b, ZFSet.pair a b ∈ f

theorem delta0_isDom (f d : ℕ) (hfd : f ≠ d) : Delta0Def {f, d} (fun _ v => IsDom (v f) (v d)) := by
  set m := f + d + 1 with hm
  -- `∀ a ∈ d, ∃ p ∈ f, ∃ q ∈ p, ∃ b ∈ q, p = pair a b`
  have a1 := delta0_isKPair (m + 1) m (m + 3) (by omega) (by omega)
  have a2 := a1.bex (m + 3) (m + 2) (by omega)
  have a3 := a2.bex (m + 2) (m + 1) (by omega)
  have a4 := a3.bex (m + 1) f (by omega)
  have h1 := a4.ball m d (by omega)
  -- `∀ p ∈ f, ∀ q ∈ p, ∀ a ∈ q, ∀ q' ∈ p, ∀ b ∈ q', p = pair a b → a ∈ d`
  have b1 := (delta0_isKPair m (m + 2) (m + 4) (by omega) (by omega)).imp
    (Delta0Def.mem (m + 2) d)
  have b2 := b1.ball (m + 4) (m + 3) (by omega)
  have b3 := b2.ball (m + 3) m (by omega)
  have b4 := b3.ball (m + 2) (m + 1) (by omega)
  have b5 := b4.ball (m + 1) m (by omega)
  have h2 := b5.ball m f (by omega)
  refine ((h1.and h2).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨H1, H2⟩ a
      constructor
      · intro ha
        obtain ⟨p, hp, q, _, b, _, rfl⟩ := H1 a ha
        exact ⟨b, hp⟩
      · rintro ⟨b, hb⟩
        exact H2 _ hb _ (singleton_mem_pair a b) a (ZFSet.mem_singleton.mpr rfl) _
          (upair_mem_pair a b) b (mem_upair_right a b) rfl
    · intro H
      refine ⟨fun a ha => ?_, ?_⟩
      · obtain ⟨b, hb⟩ := (H a).mp ha
        exact ⟨_, hb, _, upair_mem_pair a b, b, mem_upair_right a b, rfl⟩
      · intro p hp q _ a _ q' _ b _ hpab
        subst hpab
        exact (H a).mpr ⟨b, hp⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `r` is the range of `f`. -/
def IsRan (f r : ZFSet.{u}) : Prop := ∀ b, b ∈ r ↔ ∃ a, ZFSet.pair a b ∈ f

theorem delta0_isRan (f r : ℕ) (hfr : f ≠ r) : Delta0Def {f, r} (fun _ v => IsRan (v f) (v r)) := by
  set m := f + r + 1 with hm
  -- `∀ b ∈ r, ∃ p ∈ f, ∃ q ∈ p, ∃ a ∈ q, p = pair a b`
  have a1 := delta0_isKPair (m + 1) (m + 3) m (by omega) (by omega)
  have a2 := a1.bex (m + 3) (m + 2) (by omega)
  have a3 := a2.bex (m + 2) (m + 1) (by omega)
  have a4 := a3.bex (m + 1) f (by omega)
  have h1 := a4.ball m r (by omega)
  -- `∀ p ∈ f, ∀ q ∈ p, ∀ a ∈ q, ∀ q' ∈ p, ∀ b ∈ q', p = pair a b → b ∈ r`
  have b1 := (delta0_isKPair m (m + 2) (m + 4) (by omega) (by omega)).imp
    (Delta0Def.mem (m + 4) r)
  have b2 := b1.ball (m + 4) (m + 3) (by omega)
  have b3 := b2.ball (m + 3) m (by omega)
  have b4 := b3.ball (m + 2) (m + 1) (by omega)
  have b5 := b4.ball (m + 1) m (by omega)
  have h2 := b5.ball m f (by omega)
  refine ((h1.and h2).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨H1, H2⟩ b
      constructor
      · intro hb
        obtain ⟨p, hp, q, _, a, _, rfl⟩ := H1 b hb
        exact ⟨a, hp⟩
      · rintro ⟨a, ha⟩
        exact H2 _ ha _ (singleton_mem_pair a b) a (ZFSet.mem_singleton.mpr rfl) _
          (upair_mem_pair a b) b (mem_upair_right a b) rfl
    · intro H
      refine ⟨fun b hb => ?_, ?_⟩
      · obtain ⟨a, ha⟩ := (H b).mp hb
        exact ⟨_, ha, _, upair_mem_pair a b, a, mem_upair_left a b, rfl⟩
      · intro p hp q _ a _ q' _ b _ hpab
        subst hpab
        exact (H b).mpr ⟨a, hp⟩
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

/-- `b` is `a` with the value at `i` replaced by `x` (functions as sets of pairs). -/
def IsUpdate (a i x b : ZFSet.{u}) : Prop :=
  ∀ p, p ∈ b ↔ (p ∈ a ∧ ∀ y, p ≠ ZFSet.pair i y) ∨ p = ZFSet.pair i x

/-- The bounded form of `∀ y, p ≠ pair i y`. -/
theorem forall_ne_pair_iff_bounded (p i : ZFSet.{u}) :
    (∀ y, p ≠ ZFSet.pair i y) ↔ ∀ q ∈ p, ∀ y ∈ q, p ≠ ZFSet.pair i y := by
  constructor
  · intro H q _ y _; exact H y
  · intro H y hpy
    subst hpy
    exact H _ (upair_mem_pair i y) y (mem_upair_right i y) rfl

theorem delta0_isUpdate (a i x b : ℕ) (hai : a ≠ i) (hax : a ≠ x) (hab : a ≠ b) (hix : i ≠ x)
    (hib : i ≠ b) (hxb : x ≠ b) :
    Delta0Def {a, i, x, b} (fun _ v => IsUpdate (v a) (v i) (v x) (v b)) := by
  set m := a + i + x + b + 1 with hm
  -- `∀ q ∈ p, ∀ y ∈ q, p ≠ pair i y` (with `p = m`)
  have n1 := (delta0_isKPair m i (m + 2) (by omega) (by omega)).not
  have n2 := n1.ball (m + 2) (m + 1) (by omega)
  have hne := n2.ball (m + 1) m (by omega)
  -- `∀ p ∈ b, (p ∈ a ∧ ne) ∨ p = pair i x`
  have c1 := ((Delta0Def.mem m a).and hne).or (delta0_isKPair m i x (by omega) (by omega))
  have h1 := c1.ball m b (by omega)
  -- `∀ p ∈ a, ne → p ∈ b`
  have h2 := (hne.imp (Delta0Def.mem m b)).ball m a (by omega)
  -- `pair i x ∈ b`
  have h3 := delta0_funVal b i x (by omega) (by omega) hix
  refine (((h1.and h2).and h3).congr ?_).of_eq ?_
  · intro D v _ _
    simp (disch := omega) only [Function.update_self, Function.update_of_ne]
    constructor
    · rintro ⟨⟨H1, H2⟩, H3⟩ p
      constructor
      · intro hp
        rcases H1 p hp with ⟨hpa, hne⟩ | hpx
        · exact Or.inl ⟨hpa, (forall_ne_pair_iff_bounded p (v i)).mpr hne⟩
        · exact Or.inr hpx
      · rintro (⟨hpa, hne⟩ | rfl)
        · exact H2 p hpa ((forall_ne_pair_iff_bounded p (v i)).mp hne)
        · exact H3
    · intro H
      refine ⟨⟨fun p hp => ?_, fun p hpa hne => ?_⟩, (H _).mpr (Or.inr rfl)⟩
      · rcases (H p).mp hp with ⟨hpa, hne⟩ | hpx
        · exact Or.inl ⟨hpa, (forall_ne_pair_iff_bounded p (v i)).mp hne⟩
        · exact Or.inr hpx
      · exact (H p).mpr (Or.inl ⟨hpa, (forall_ne_pair_iff_bounded p (v i)).mpr hne⟩)
  · ext k; simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton,
      Finset.mem_union]; omega

end BM4.ST
