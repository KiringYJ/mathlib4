/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Yi-Jing Tseng
-/
module

public import Mathlib.Order.Sublattice

/-!
# Generalized Boolean subalgebras

A generalized Boolean subalgebra contains bottom and is closed under binary suprema, binary
infima, and relative difference. Its elements inherit a generalized Boolean algebra structure.
The generalized Boolean subalgebras of a fixed algebra form a complete lattice, with infima
given by intersections.
-/

@[expose] public section

open Function Set

variable {ι : Sort*} {α : Type*}

variable (α) in
/-- A generalized Boolean subalgebra is a sublattice containing bottom and closed under relative
difference. -/
structure GeneralizedBooleanSubalgebra [GeneralizedBooleanAlgebra α] extends Sublattice α where
  bot_mem' : ⊥ ∈ carrier
  sdiff_mem' {a b} : a ∈ carrier → b ∈ carrier → a \ b ∈ carrier

namespace GeneralizedBooleanSubalgebra

variable [GeneralizedBooleanAlgebra α] {L M : GeneralizedBooleanSubalgebra α}
  {s t : Set α} {a b : α}

initialize_simps_projections GeneralizedBooleanSubalgebra (carrier → coe, as_prefix coe)

instance instSetLike : SetLike (GeneralizedBooleanSubalgebra α) α where
  coe L := L.carrier
  coe_injective L M h := by obtain ⟨⟨_, _⟩, _⟩ := L; congr

instance : PartialOrder (GeneralizedBooleanSubalgebra α) :=
  .ofSetLike (GeneralizedBooleanSubalgebra α) α

lemma coe_inj : (L : Set α) = M ↔ L = M := SetLike.coe_set_eq

@[simp] lemma supClosed (L : GeneralizedBooleanSubalgebra α) : SupClosed (L : Set α) :=
  L.supClosed'
@[simp] lemma infClosed (L : GeneralizedBooleanSubalgebra α) : InfClosed (L : Set α) :=
  L.infClosed'
@[simp] lemma isSublattice (L : GeneralizedBooleanSubalgebra α) : IsSublattice (L : Set α) :=
  ⟨L.supClosed, L.infClosed⟩

@[simp] lemma bot_mem : ⊥ ∈ L := L.bot_mem'
lemma sup_mem (ha : a ∈ L) (hb : b ∈ L) : a ⊔ b ∈ L := L.supClosed ha hb
lemma inf_mem (ha : a ∈ L) (hb : b ∈ L) : a ⊓ b ∈ L := L.infClosed ha hb
lemma sdiff_mem (ha : a ∈ L) (hb : b ∈ L) : a \ b ∈ L := L.sdiff_mem' ha hb

@[simp] lemma mem_carrier : a ∈ L.carrier ↔ a ∈ L := .rfl
@[simp] lemma mem_toSublattice : a ∈ L.toSublattice ↔ a ∈ L := .rfl
@[simp] lemma coe_toSublattice (L : GeneralizedBooleanSubalgebra α) :
    (L.toSublattice : Set α) = L := rfl
@[simp] lemma mem_mk {L : Sublattice α} (h_bot h_sdiff) :
    a ∈ mk L h_bot h_sdiff ↔ a ∈ L := .rfl
@[simp] lemma coe_mk (L : Sublattice α) (h_bot h_sdiff) :
    (mk L h_bot h_sdiff : Set α) = L := rfl
@[simp] lemma mk_le_mk {L M : Sublattice α} (hL_bot hL_sdiff hM_bot hM_sdiff) :
    mk L hL_bot hL_sdiff ≤ mk M hM_bot hM_sdiff ↔ L ≤ M := .rfl
@[simp] lemma mk_lt_mk {L M : Sublattice α} (hL_bot hL_sdiff hM_bot hM_sdiff) :
    mk L hL_bot hL_sdiff < mk M hM_bot hM_sdiff ↔ L < M := .rfl

/-- Two generalized Boolean subalgebras are equal if they have the same elements. -/
@[ext] lemma ext : (∀ a, a ∈ L ↔ a ∈ M) → L = M := SetLike.ext

/-- Construct a generalized Boolean subalgebra from bottom, supremum, and relative-difference
closure. Infimum closure follows from `a ⊓ b = a \ (a \ b)`. -/
def ofBotSupSDiff (s : Set α) (hbot : ⊥ ∈ s) (hsup : SupClosed s)
    (hsdiff : ∀ ⦃a b⦄, a ∈ s → b ∈ s → a \ b ∈ s) : GeneralizedBooleanSubalgebra α where
  carrier := s
  bot_mem' := hbot
  supClosed' := hsup
  infClosed' := fun _ ha _ hb ↦ by
    simpa only [_root_.sdiff_sdiff_right_self] using hsdiff ha (hsdiff ha hb)
  sdiff_mem' := fun ha hb ↦ hsdiff ha hb

@[simp, norm_cast] lemma coe_ofBotSupSDiff (s : Set α) (hbot hsup hsdiff) :
    (ofBotSupSDiff s hbot hsup hsdiff : Set α) = s := rfl

@[simp] lemma mem_ofBotSupSDiff (hbot hsup hsdiff) :
    a ∈ ofBotSupSDiff s hbot hsup hsdiff ↔ a ∈ s := .rfl

/-- Copy a generalized Boolean subalgebra with a definitionally different carrier. -/
protected def copy (L : GeneralizedBooleanSubalgebra α) (s : Set α) (hs : s = L) :
    GeneralizedBooleanSubalgebra α where
  toSublattice := L.toSublattice.copy s <| by subst hs; rfl
  bot_mem' := by subst hs; exact L.bot_mem'
  sdiff_mem' := by subst hs; exact L.sdiff_mem'

@[simp, norm_cast] lemma coe_copy (L : GeneralizedBooleanSubalgebra α) (s : Set α) (hs) :
    (L.copy s hs : Set α) = s := rfl

lemma copy_eq (L : GeneralizedBooleanSubalgebra α) (s : Set α) (hs) : L.copy s hs = L :=
  SetLike.coe_injective hs

/-- A generalized Boolean subalgebra inherits bottom. -/
instance instBotCoe : Bot L where bot := ⟨⊥, bot_mem⟩

/-- A generalized Boolean subalgebra inherits suprema. -/
instance instSupCoe : Max L where max a b := ⟨a ⊔ b, sup_mem a.2 b.2⟩

/-- A generalized Boolean subalgebra inherits infima. -/
instance instInfCoe : Min L where min a b := ⟨a ⊓ b, inf_mem a.2 b.2⟩

/-- A generalized Boolean subalgebra inherits relative difference. -/
instance instSDiffCoe : SDiff L where sdiff a b := ⟨a \ b, sdiff_mem a.2 b.2⟩

@[simp, norm_cast] lemma val_bot : (⊥ : L) = (⊥ : α) := rfl
@[simp, norm_cast] lemma val_sup (a b : L) : a ⊔ b = (a : α) ⊔ b := rfl
@[simp, norm_cast] lemma val_inf (a b : L) : a ⊓ b = (a : α) ⊓ b := rfl
@[simp, norm_cast] lemma val_sdiff (a b : L) : a \ b = (a : α) \ b := rfl

@[simp] lemma mk_bot : (⟨⊥, bot_mem⟩ : L) = ⊥ := rfl
@[simp] lemma mk_sup_mk (a b : α) (ha hb) :
    (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, sup_mem ha hb⟩ := rfl
@[simp] lemma mk_inf_mk (a b : α) (ha hb) :
    (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, inf_mem ha hb⟩ := rfl
@[simp] lemma mk_sdiff_mk (a b : α) (ha hb) :
    (⟨a, ha⟩ \ ⟨b, hb⟩ : L) = ⟨a \ b, sdiff_mem ha hb⟩ := rfl

instance (L : GeneralizedBooleanSubalgebra α) : PartialOrder L :=
  PartialOrder.lift _ Subtype.coe_injective

/-- A generalized Boolean subalgebra inherits a generalized Boolean algebra structure. -/
instance instGeneralizedBooleanAlgebraCoe (L : GeneralizedBooleanSubalgebra α) :
    GeneralizedBooleanAlgebra L :=
  Subtype.coe_injective.generalizedBooleanAlgebra _ .rfl .rfl val_sup val_inf val_bot val_sdiff

@[simp, norm_cast] lemma disjoint_coe {a b : L} :
    Disjoint (a : α) (b : α) ↔ Disjoint a b := by
  rw [disjoint_iff, disjoint_iff, ← val_inf, ← val_bot, Subtype.coe_inj]

/-- The natural lattice homomorphism from a generalized Boolean subalgebra to its ambient
algebra. -/
def subtype (L : GeneralizedBooleanSubalgebra α) : LatticeHom L α where
  toFun := ((↑) : L → α)
  map_sup' := val_sup
  map_inf' := val_inf

@[simp, norm_cast] lemma coe_subtype (L : GeneralizedBooleanSubalgebra α) :
    L.subtype = ((↑) : L → α) := rfl

lemma subtype_apply (L : GeneralizedBooleanSubalgebra α) (a : L) : L.subtype a = a := rfl

lemma subtype_injective (L : GeneralizedBooleanSubalgebra α) : Injective L.subtype :=
  Subtype.coe_injective

@[simp] lemma subtype_bot : L.subtype ⊥ = ⊥ := rfl
@[simp] lemma subtype_sdiff (a b : L) : L.subtype (a \ b) = L.subtype a \ L.subtype b := rfl

/-- The inclusion homomorphism between nested generalized Boolean subalgebras. -/
def inclusion (h : L ≤ M) : LatticeHom L M where
  toFun := Set.inclusion h
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

@[simp] lemma coe_inclusion (h : L ≤ M) : inclusion h = Set.inclusion h := rfl
lemma inclusion_apply (h : L ≤ M) (a : L) : inclusion h a = Set.inclusion h a := rfl
lemma inclusion_injective (h : L ≤ M) : Injective (inclusion h) := Set.inclusion_injective h

@[simp] lemma inclusion_bot (h : L ≤ M) : inclusion h ⊥ = ⊥ := rfl
@[simp] lemma inclusion_sdiff (h : L ≤ M) (a b : L) :
    inclusion h (a \ b) = inclusion h a \ inclusion h b := rfl
@[simp] lemma inclusion_rfl (L : GeneralizedBooleanSubalgebra α) :
    inclusion (L := L) le_rfl = .id L := rfl
@[simp] lemma subtype_comp_inclusion (h : L ≤ M) :
    M.subtype.comp (inclusion h) = L.subtype := rfl

/-- Pull a generalized Boolean subalgebra back to the elements of another one. When `L ≤ M`,
this regards `L` as a generalized Boolean subalgebra of `M`. -/
def comapSubtype (L M : GeneralizedBooleanSubalgebra α) : GeneralizedBooleanSubalgebra M where
  carrier := Subtype.val ⁻¹' L
  bot_mem' := bot_mem
  supClosed' := fun _ ha _ hb ↦ sup_mem ha hb
  infClosed' := fun _ ha _ hb ↦ inf_mem ha hb
  sdiff_mem' := fun ha hb ↦ sdiff_mem ha hb

@[simp, norm_cast] lemma coe_comapSubtype (L M : GeneralizedBooleanSubalgebra α) :
    (L.comapSubtype M : Set M) = Subtype.val ⁻¹' L := rfl

@[simp] lemma mem_comapSubtype {a : M} : a ∈ L.comapSubtype M ↔ (a : α) ∈ L := .rfl

lemma comapSubtype_mono (M : GeneralizedBooleanSubalgebra α) :
    Monotone (fun L : GeneralizedBooleanSubalgebra α ↦ L.comapSubtype M) :=
  fun _ _ h _ ha ↦ h ha

lemma comapSubtype_le_comapSubtype_iff {N : GeneralizedBooleanSubalgebra α} (hL : L ≤ M) :
    L.comapSubtype M ≤ N.comapSubtype M ↔ L ≤ N :=
  ⟨fun h a ha ↦ h (x := ⟨a, hL ha⟩) ha, fun h ↦ comapSubtype_mono M h⟩

lemma comapSubtype_lt_comapSubtype_iff {N : GeneralizedBooleanSubalgebra α}
    (hL : L ≤ M) (hN : N ≤ M) : L.comapSubtype M < N.comapSubtype M ↔ L < N := by
  simp only [lt_iff_le_not_ge, comapSubtype_le_comapSubtype_iff hL,
    comapSubtype_le_comapSubtype_iff hN]

/-- The whole ambient algebra is a generalized Boolean subalgebra. -/
instance instTop : Top (GeneralizedBooleanSubalgebra α) where
  top.carrier := univ
  top.bot_mem' := mem_univ _
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ
  top.sdiff_mem' _ _ := mem_univ _

/-- The generalized Boolean subalgebra consisting only of bottom. -/
instance instBot : Bot (GeneralizedBooleanSubalgebra α) where
  bot.carrier := {⊥}
  bot.bot_mem' := mem_singleton _
  bot.supClosed' := supClosed_singleton
  bot.infClosed' := infClosed_singleton
  bot.sdiff_mem' := by simp

/-- The infimum of two generalized Boolean subalgebras is their intersection. -/
instance instInf : Min (GeneralizedBooleanSubalgebra α) where
  min L M :=
    { carrier := L ∩ M
      bot_mem' := ⟨bot_mem, bot_mem⟩
      supClosed' := L.supClosed.inter M.supClosed
      infClosed' := L.infClosed.inter M.infClosed
      sdiff_mem' := fun ha hb ↦ ⟨sdiff_mem ha.1 hb.1, sdiff_mem ha.2 hb.2⟩ }

/-- The infimum of generalized Boolean subalgebras is their intersection. -/
instance instInfSet : InfSet (GeneralizedBooleanSubalgebra α) where
  sInf S :=
    { carrier := ⋂ L ∈ S, L
      bot_mem' := mem_iInter₂.2 fun _ _ ↦ bot_mem
      supClosed' := supClosed_sInter <| forall_mem_range.2 fun L ↦ supClosed_sInter <|
        forall_mem_range.2 fun _ ↦ L.supClosed
      infClosed' := infClosed_sInter <| forall_mem_range.2 fun L ↦ infClosed_sInter <|
        forall_mem_range.2 fun _ ↦ L.infClosed
      sdiff_mem' := fun ha hb ↦ mem_iInter₂.2 fun L hL ↦
        sdiff_mem (mem_iInter₂.1 ha L hL) (mem_iInter₂.1 hb L hL) }

instance instInhabited : Inhabited (GeneralizedBooleanSubalgebra α) := ⟨⊥⟩

/-- The top generalized Boolean subalgebra is order-isomorphic to its ambient algebra. -/
def topEquiv : (⊤ : GeneralizedBooleanSubalgebra α) ≃o α where
  toEquiv := Equiv.Set.univ _
  map_rel_iff' := .rfl

@[simp, norm_cast] lemma coe_top : (⊤ : GeneralizedBooleanSubalgebra α) = (univ : Set α) := rfl
@[simp, norm_cast] lemma coe_bot : (⊥ : GeneralizedBooleanSubalgebra α) = ({⊥} : Set α) := rfl
@[simp, norm_cast] lemma coe_inf (L M : GeneralizedBooleanSubalgebra α) :
    ((L ⊓ M : GeneralizedBooleanSubalgebra α) : Set α) = (L : Set α) ∩ M := rfl
@[simp, norm_cast] lemma coe_sInf (S : Set (GeneralizedBooleanSubalgebra α)) :
    ((sInf S : GeneralizedBooleanSubalgebra α) : Set α) = ⋂ L ∈ S, (L : Set α) := rfl
@[simp, norm_cast] lemma coe_iInf (f : ι → GeneralizedBooleanSubalgebra α) :
    ((⨅ i, f i : GeneralizedBooleanSubalgebra α) : Set α) = ⋂ i, (f i : Set α) := by simp [iInf]
@[simp, norm_cast] lemma coe_eq_univ : L = (univ : Set α) ↔ L = ⊤ := by
  rw [← coe_top, coe_inj]

@[simp] lemma mem_bot : a ∈ (⊥ : GeneralizedBooleanSubalgebra α) ↔ a = ⊥ := mem_singleton_iff
@[simp] lemma mem_top : a ∈ (⊤ : GeneralizedBooleanSubalgebra α) := mem_univ _
@[simp] lemma mem_inf : a ∈ L ⊓ M ↔ a ∈ L ∧ a ∈ M := .rfl
@[simp] lemma mem_sInf {S : Set (GeneralizedBooleanSubalgebra α)} :
    a ∈ sInf S ↔ ∀ L ∈ S, a ∈ L := by
  rw [← SetLike.mem_coe]; simp
@[simp] lemma mem_iInf {f : ι → GeneralizedBooleanSubalgebra α} :
    a ∈ ⨅ i, f i ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe]; simp

/-- Generalized Boolean subalgebras form a complete lattice under inclusion. -/
instance instCompleteLattice : CompleteLattice (GeneralizedBooleanSubalgebra α) where
  bot := ⊥
  bot_le _ _ ha := by obtain rfl := mem_bot.1 ha; exact bot_mem
  top := ⊤
  le_top _ _ _ := mem_top
  inf := (· ⊓ ·)
  le_inf _ _ _ hM hN _ ha := ⟨hM ha, hN ha⟩
  inf_le_left _ _ _ := And.left
  inf_le_right _ _ _ := And.right
  __ := completeLatticeOfInf (GeneralizedBooleanSubalgebra α)
    fun _ ↦ IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf

/-- The smallest generalized Boolean subalgebra containing a set. -/
def closure (s : Set α) : GeneralizedBooleanSubalgebra α := sInf {L | s ⊆ L}

lemma mem_closure : a ∈ closure s ↔ ∀ ⦃L : GeneralizedBooleanSubalgebra α⦄, s ⊆ L → a ∈ L :=
  mem_sInf

@[simp] lemma subset_closure : s ⊆ closure s := fun _ ha ↦ mem_closure.2 fun _ hL ↦ hL ha

@[simp] lemma closure_le : closure s ≤ L ↔ s ⊆ L :=
  ⟨subset_closure.trans, fun h ↦ sInf_le h⟩

lemma closure_mono (hst : s ⊆ t) : closure s ≤ closure t :=
  closure_le.2 (hst.trans subset_closure)

@[simp] lemma closure_eq (L : GeneralizedBooleanSubalgebra α) : closure (L : Set α) = L :=
  le_antisymm (closure_le.2 Subset.rfl) subset_closure

/-- To prove a property of elements of a generated generalized Boolean subalgebra, prove it for
the generators and bottom, and show that it is preserved under suprema and relative difference. -/
@[elab_as_elim]
lemma closure_bot_sup_sdiff_induction {p : ∀ g ∈ closure s, Prop}
    (mem : ∀ x hx, p x (subset_closure hx)) (bot : p ⊥ bot_mem)
    (sup : ∀ x hx y hy, p x hx → p y hy → p (x ⊔ y) (sup_mem hx hy))
    (sdiff : ∀ x hx y hy, p x hx → p y hy → p (x \ y) (sdiff_mem hx hy))
    {x} (hx : x ∈ closure s) : p x hx :=
  let L : GeneralizedBooleanSubalgebra α :=
    ofBotSupSDiff {x | ∃ hx, p x hx} ⟨_, bot⟩
      (fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ ↦ ⟨_, sup _ _ _ _ ha hb⟩)
      (fun {_ _} ⟨_, ha⟩ ⟨_, hb⟩ ↦ ⟨_, sdiff _ _ _ _ ha hb⟩)
  closure_le (L := L).mpr (fun y hy ↦ ⟨subset_closure hy, mem y hy⟩) hx |>.elim fun _ ↦ id

end GeneralizedBooleanSubalgebra
