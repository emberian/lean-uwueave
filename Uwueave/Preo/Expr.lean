/-
# Uwueave.Preo.Expr — typed expressions, exact read sets, and safe analyses.

`preo` currently accepts ordinary Lean terms for invariants and derivations.
That is a good escape hatch, but an opaque term has no structure from which an
elaborator can honestly infer its field dependencies or whether it preserves a
merge.  This module supplies the missing semantic foundation without changing
the surface language yet.

The design is deliberately small and first-order:

* `Ty` is the value universe needed by derivations and queries today: booleans,
  naturals, products, and options;
* `Var` is a typed de Bruijn field reference into a heterogeneous `Schema`, and
  `Env` is the corresponding heterogeneous environment;
* `Term Γ t` is intrinsically typed.  Ill-typed negation, arithmetic, and
  projection are unrepresentable;
* every term has a structural list of positional `Hole`s.  A field read records
  its exact tree position.  An opaque leaf must declare an in-range dependency
  list and prove that agreement there determines its result (extra conservative
  reads are permitted; out-of-range vacuity is not);
* `eval_ext` proves that the computed dependency set is sufficient;
* `MergeSafe` and `MonotoneSafe` are proof-carrying positive analyses.
  `certifyMergeSafe`/`certifyMonotone` recognize only constructors whose laws
  are structurally sound.  An opaque leaf is never accepted automatically,
  even if its hidden function happens to be a homomorphism; an author may add
  it only by supplying the missing equation explicitly.

`Raw.infer` is the surface hook used by `typed derive` in Preoscript.  It
rejects malformed syntax and raw opaque nodes; `Raw.certifyMergeSafe` returns a
typed term together with its proof, never a Boolean claim detached from
evidence.  `Program` retains the raw spelling, the inferred typed term, and the
exact inference equation, so downstream cache and result adapters consume one
kernel-checked value rather than repeating inference.

## Honest boundary

The first-order `Ty` universe is intentional: arbitrary Lean computations
remain available through ordinary `derive`, while raw `custom` is refused
because it carries neither an implementation nor a locality proof.  A caller
can construct `Term.custom` directly only with those missing ingredients and
must supply any positive algebraic law.  The automatic analyses are sound and
deliberately incomplete; `none` means "not established by this syntax", not
"semantically false".
-/
import Uwueave.JoinHom

namespace Uwueave.Preo.Expr

/-! ## 1. A genuinely typed field environment -/

/-- The closed value universe of the structural query fragment. -/
inductive Ty where
  | bool
  | nat
  | pair (left right : Ty)
  | option (elem : Ty)
  deriving DecidableEq, Repr

/-- Lean interpretation of a query type. -/
def Ty.denote : Ty → Type
  | .bool => Bool
  | .nat => Nat
  | .pair a b => a.denote × b.denote
  | .option a => Option a.denote

/-- Executable equality for every first-order value type.  Keeping this
structural lets runtime/result adapters form singleton answer sets without a
classical oracle. -/
def Ty.decEq : (t : Ty) → DecidableEq t.denote
  | .bool => Bool.decEq
  | .nat => Nat.decEq
  | .pair a b => fun x y =>
      match a.decEq x.1 y.1 with
      | isTrue hx =>
          match b.decEq x.2 y.2 with
          | isTrue hy => isTrue (Prod.ext hx hy)
          | isFalse hy => isFalse (fun h => hy (congrArg Prod.snd h))
      | isFalse hx => isFalse (fun h => hx (congrArg Prod.fst h))
  | .option a => fun x y =>
      match x, y with
      | none, none => isTrue rfl
      | none, some _ => isFalse (by intro h; cases h)
      | some _, none => isFalse (by intro h; cases h)
      | some x, some y =>
          match a.decEq x y with
          | isTrue h => isTrue (congrArg Option.some h)
          | isFalse h => isFalse (fun hs => h (Option.some.inj hs))

instance (t : Ty) : DecidableEq t.denote := t.decEq

/-- The canonical evidence merge for each first-order query type: disjunction,
maximum, componentwise merge, and `none`-as-bottom option merge. -/
def Ty.merge : (t : Ty) → t.denote → t.denote → t.denote
  | .bool, x, y => x || y
  | .nat, x, y => Nat.max x y
  | .pair a b, x, y => (a.merge x.1 y.1, b.merge x.2 y.2)
  | .option _, none, y => y
  | .option _, x, none => x
  | .option a, some x, some y => some (a.merge x y)

theorem Ty.merge_comm : ∀ (t : Ty) (x y : t.denote), t.merge x y = t.merge y x
  | .bool, x, y => Bool.or_comm x y
  | .nat, x, y => Nat.max_comm x y
  | .pair a b, (xa, xb), (ya, yb) => by
      simp only [Ty.merge]
      rw [a.merge_comm xa ya, b.merge_comm xb yb]
  | .option a, none, none => rfl
  | .option a, none, some y => rfl
  | .option a, some x, none => rfl
  | .option a, some x, some y => by
      simp only [Ty.merge]
      rw [a.merge_comm x y]

theorem Ty.merge_assoc : ∀ (t : Ty) (x y z : t.denote),
    t.merge (t.merge x y) z = t.merge x (t.merge y z)
  | .bool, x, y, z => Bool.or_assoc x y z
  | .nat, x, y, z => Nat.max_assoc x y z
  | .pair a b, (xa, xb), (ya, yb), (za, zb) => by
      simp only [Ty.merge]
      rw [a.merge_assoc xa ya za, b.merge_assoc xb yb zb]
  | .option a, none, none, none => rfl
  | .option a, none, none, some z => rfl
  | .option a, none, some y, none => rfl
  | .option a, none, some y, some z => rfl
  | .option a, some x, none, none => rfl
  | .option a, some x, none, some z => rfl
  | .option a, some x, some y, none => rfl
  | .option a, some x, some y, some z => by
      simp only [Ty.merge]
      rw [a.merge_assoc x y z]

theorem Ty.merge_idem : ∀ (t : Ty) (x : t.denote), t.merge x x = x
  | .bool, x => Bool.or_self x
  | .nat, x => Nat.max_self x
  | .pair a b, (x, y) => by
      simp only [Ty.merge]
      rw [a.merge_idem x, b.merge_idem y]
  | .option a, none => rfl
  | .option a, some x => by
      simp only [Ty.merge]
      rw [a.merge_idem x]

/-- A declaration schema is a heterogeneous list of field types. -/
abbrev Schema := List Ty

/-- A typed field position.  `Var Γ t` can point only at a field of type `t`. -/
inductive Var : Schema → Ty → Type where
  | here : Var (t :: Γ) t
  | there : Var Γ t → Var (u :: Γ) t

/-- Erase the field type, retaining its de Bruijn position for dependency
reporting and comparison with surface field order. -/
def Var.index : Var Γ t → Nat
  | .here => 0
  | .there v => v.index + 1

/-- A typed heterogeneous environment for a schema. -/
inductive Env : Schema → Type where
  | nil : Env []
  | cons : t.denote → Env Γ → Env (t :: Γ)

/-- Typed lookup cannot fail. -/
def Env.get : Env Γ → Var Γ t → t.denote
  | .cons x _, .here => x
  | .cons _ xs, .there v => xs.get v

/-- Pointwise merge of heterogeneous environments. -/
def Env.merge : Env Γ → Env Γ → Env Γ
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (Ty.merge _ x y) (merge xs ys)

theorem Env.merge_comm : ∀ (x y : Env Γ), merge x y = merge y x
  | .nil, .nil => rfl
  | .cons x xs, .cons y ys => by
      simp only [merge]
      rw [Ty.merge_comm, merge_comm xs ys]

theorem Env.merge_assoc : ∀ (x y z : Env Γ),
    merge (merge x y) z = merge x (merge y z)
  | .nil, .nil, .nil => rfl
  | .cons x xs, .cons y ys, .cons z zs => by
      simp only [merge]
      rw [Ty.merge_assoc, merge_assoc xs ys zs]

theorem Env.merge_idem : ∀ (x : Env Γ), merge x x = x
  | .nil => rfl
  | .cons x xs => by
      simp only [merge]
      rw [Ty.merge_idem, merge_idem xs]

@[simp] theorem Env.get_merge (x y : Env Γ) (v : Var Γ t) :
    (merge x y).get v = Ty.merge t (x.get v) (y.get v) := by
  induction v with
  | here => cases x <;> cases y <;> rfl
  | there v ih =>
      cases x with
      | cons _ xs =>
        cases y with
        | cons _ ys => exact ih xs ys

/-- Equality of two environments at one erased position.  Out-of-range
positions are false; every dependency produced by a typed term is in range. -/
def Env.AgreeAt : Env Γ → Env Γ → Nat → Prop
  | .nil, .nil, _ => False
  | .cons x _, .cons y _, 0 => x = y
  | .cons _ xs, .cons _ ys, n + 1 => AgreeAt xs ys n

/-- Agreement on a finite dependency list.  Duplicates are harmless. -/
def Env.AgreeOn (dependencies : List Nat) (x y : Env Γ) : Prop :=
  ∀ n, n ∈ dependencies → AgreeAt x y n

theorem congrArgTwo {A B C : Sort _} (f : A → B → C)
    {a a' : A} {b b' : B} (ha : a = a') (hb : b = b') :
    f a b = f a' b' := by
  cases ha
  cases hb
  rfl

theorem Env.get_eq_of_agreeAt (v : Var Γ t) (x y : Env Γ)
    (h : AgreeAt x y v.index) : x.get v = y.get v := by
  induction v with
  | here => cases x <;> cases y <;> exact h
  | there v ih =>
      cases x with
      | cons _ xs =>
        cases y with
        | cons _ ys => exact ih xs ys h

/-! ## 2. Typed terms and exact dependencies -/

/-- An opaque/custom query.  Its implementation is available to evaluation,
but it must declare a finite, schema-bounded dependency set and prove locality
on that set. The list may conservatively contain extra reads; it cannot use an
impossible out-of-range agreement premise. No algebraic property is stored or
inferred here. -/
structure CustomNode (Γ : Schema) (t : Ty) where
  name : String
  run : Env Γ → t.denote
  dependencies : List Nat
  /-- Declared reads must name actual schema slots. Without this field an
  out-of-range dependency would make `AgreeOn` false and let `respects` pass
  vacuously, which is not a locality certificate. -/
  dependenciesInRange : ∀ n, n ∈ dependencies → n < Γ.length
  respects : ∀ x y, Env.AgreeOn dependencies x y → run x = run y

/-- Intrinsically typed derivation/query expressions. -/
inductive Term (Γ : Schema) : Ty → Type where
  | litBool (value : Bool) : Term Γ .bool
  | litNat (value : Nat) : Term Γ .nat
  | var (field : Var Γ t) : Term Γ t
  | pair (left : Term Γ a) (right : Term Γ b) : Term Γ (.pair a b)
  | fst (pair : Term Γ (.pair a b)) : Term Γ a
  | snd (pair : Term Γ (.pair a b)) : Term Γ b
  | none : Term Γ (.option a)
  | some (value : Term Γ a) : Term Γ (.option a)
  | isSome (value : Term Γ (.option a)) : Term Γ .bool
  | boolOr (left right : Term Γ .bool) : Term Γ .bool
  | boolAnd (left right : Term Γ .bool) : Term Γ .bool
  | boolNot (value : Term Γ .bool) : Term Γ .bool
  | natMax (left right : Term Γ .nat) : Term Γ .nat
  | natAdd (left right : Term Γ .nat) : Term Γ .nat
  | natSucc (value : Term Γ .nat) : Term Γ .nat
  | natEq (left right : Term Γ .nat) : Term Γ .bool
  | custom (value : CustomNode Γ t) : Term Γ t

/-- Denotation of a typed term. -/
def Term.eval : Term Γ t → Env Γ → t.denote
  | .litBool b, _ => b
  | .litNat n, _ => n
  | .var v, env => env.get v
  | .pair a b, env => (a.eval env, b.eval env)
  | .fst p, env => (p.eval env).1
  | .snd p, env => (p.eval env).2
  | .none, _ => Option.none
  | .some a, env => Option.some (a.eval env)
  | .isSome a, env => (a.eval env).isSome
  | .boolOr a b, env => a.eval env || b.eval env
  | .boolAnd a b, env => a.eval env && b.eval env
  | .boolNot a, env => !a.eval env
  | .natMax a b, env => Nat.max (a.eval env) (b.eval env)
  | .natAdd a b, env => Nat.add (a.eval env) (b.eval env)
  | .natSucc a, env => Nat.succ (a.eval env)
  | .natEq a b, env => Nat.beq (a.eval env) (b.eval env)
  | .custom o, env => o.run env

/-- Whether a positional hole is a visible field read or a dependency declared
by an opaque leaf. -/
inductive HoleKind where
  | field
  | opaque
  deriving DecidableEq, Repr

/-- One dependency occurrence.  `path` is a child-index path from the root and
`field` is the erased schema position.  All dependencies of one opaque leaf
share its path and are distinguished by `kind = opaque`. -/
structure Hole where
  path : List Nat
  field : Nat
  kind : HoleKind
  deriving DecidableEq, Repr

def Hole.prefix (child : Nat) (hole : Hole) : Hole :=
  { hole with path := child :: hole.path }

def prefixHoles (child : Nat) (holes : List Hole) : List Hole :=
  holes.map (Hole.prefix child)

@[simp] theorem fields_prefixHoles (child : Nat) (holes : List Hole) :
    (prefixHoles child holes).map Hole.field = holes.map Hole.field := by
  induction holes with
  | nil => rfl
  | cons h hs ih => simp [prefixHoles, Hole.prefix]

/-- Positional dependency occurrences.  Child `0` is the only child of unary
nodes and the left child of binary nodes; child `1` is the right child. -/
def Term.holes : Term Γ t → List Hole
  | .litBool _ | .litNat _ | .none => []
  | .var v => [{ path := [], field := v.index, kind := .field }]
  | .pair a b | .boolOr a b | .boolAnd a b | .natMax a b
  | .natAdd a b | .natEq a b => prefixHoles 0 a.holes ++ prefixHoles 1 b.holes
  | .fst p | .snd p | .some p | .isSome p | .boolNot p | .natSucc p =>
      prefixHoles 0 p.holes
  | .custom o => o.dependencies.map fun n =>
      { path := [], field := n, kind := .opaque }

/-- The structural dependency/read set, with duplicates retained so positions
are never silently erased. -/
def Term.reads (term : Term Γ t) : List Nat := term.holes.map Hole.field

@[simp] theorem Term.reads_litBool (b : Bool) : (litBool ( Γ := Γ) b).reads = [] := rfl
@[simp] theorem Term.reads_litNat (n : Nat) : (litNat ( Γ := Γ) n).reads = [] := rfl
@[simp] theorem Term.reads_var (v : Var Γ t) : (var v).reads = [v.index] := rfl
@[simp] theorem Term.reads_pair (a : Term Γ s) (b : Term Γ t) :
    (pair a b).reads = a.reads ++ b.reads := by
  simp [Term.reads, Term.holes]
@[simp] theorem Term.reads_custom (o : CustomNode Γ t) :
    (custom o).reads = o.dependencies := by
  simp [Term.reads, Term.holes, List.map_map, Function.comp_def]

theorem Env.agreeOn_append_left {a b : List Nat} {x y : Env Γ}
    (h : AgreeOn (a ++ b) x y) : AgreeOn a x y := by
  intro n hn
  exact h n (List.mem_append_left _ hn)

theorem Env.agreeOn_append_right {a b : List Nat} {x y : Env Γ}
    (h : AgreeOn (a ++ b) x y) : AgreeOn b x y := by
  intro n hn
  exact h n (List.mem_append_right _ hn)

/-- **Dependency soundness.** Two environments agreeing at every structurally
reported dependency evaluate to the same result.  This includes opaque leaves
only because their constructors require exactly this evidence. -/
theorem Term.eval_ext (term : Term Γ t) (x y : Env Γ)
    (h : Env.AgreeOn term.reads x y) : term.eval x = term.eval y := by
  induction term with
  | litBool | litNat | none => simp [Term.eval]
  | var v =>
      simpa [Term.eval] using
        Env.get_eq_of_agreeAt v x y (h v.index (by simp))
  | pair a b iha ihb =>
      have hall : Env.AgreeOn (a.reads ++ b.reads) x y := by
        simpa [Term.reads, Term.holes] using h
      simpa only [Term.eval] using congrArgTwo Prod.mk
        (iha (Env.agreeOn_append_left hall))
        (ihb (Env.agreeOn_append_right hall))
  | fst p ih =>
      have hp : Env.AgreeOn p.reads x y := by
        simpa [Term.reads, Term.holes] using h
      simpa only [Term.eval] using congrArg Prod.fst (ih hp)
  | snd p ih =>
      have hp : Env.AgreeOn p.reads x y := by
        simpa [Term.reads, Term.holes] using h
      simpa only [Term.eval] using congrArg Prod.snd (ih hp)
  | some p ih =>
      have hp : Env.AgreeOn p.reads x y := by
        simpa [Term.reads, Term.holes] using h
      simpa only [Term.eval] using congrArg Option.some (ih hp)
  | isSome p ih =>
      have hp : Env.AgreeOn p.reads x y := by
        simpa [Term.reads, Term.holes] using h
      simpa only [Term.eval] using congrArg Option.isSome (ih hp)
  | boolNot p ih =>
      have hp : Env.AgreeOn p.reads x y := by
        simpa [Term.reads, Term.holes] using h
      simpa only [Term.eval] using congrArg Bool.not (ih hp)
  | natSucc p ih =>
      have hp : Env.AgreeOn p.reads x y := by
        simpa [Term.reads, Term.holes] using h
      simpa only [Term.eval] using congrArg Nat.succ (ih hp)
  | boolOr a b iha ihb =>
      have ha : Env.AgreeOn a.reads x y := by
        exact Env.agreeOn_append_left (by simpa [Term.reads, Term.holes] using h)
      have hb : Env.AgreeOn b.reads x y := by
        exact Env.agreeOn_append_right (by simpa [Term.reads, Term.holes] using h)
      simpa only [Term.eval] using congrArgTwo Bool.or (iha ha) (ihb hb)
  | boolAnd a b iha ihb =>
      have ha : Env.AgreeOn a.reads x y :=
        Env.agreeOn_append_left (by simpa [Term.reads, Term.holes] using h)
      have hb : Env.AgreeOn b.reads x y :=
        Env.agreeOn_append_right (by simpa [Term.reads, Term.holes] using h)
      simpa only [Term.eval] using congrArgTwo Bool.and (iha ha) (ihb hb)
  | natMax a b iha ihb =>
      have ha : Env.AgreeOn a.reads x y :=
        Env.agreeOn_append_left (by simpa [Term.reads, Term.holes] using h)
      have hb : Env.AgreeOn b.reads x y :=
        Env.agreeOn_append_right (by simpa [Term.reads, Term.holes] using h)
      simpa only [Term.eval] using congrArgTwo Nat.max (iha ha) (ihb hb)
  | natAdd a b iha ihb =>
      have ha : Env.AgreeOn a.reads x y :=
        Env.agreeOn_append_left (by simpa [Term.reads, Term.holes] using h)
      have hb : Env.AgreeOn b.reads x y :=
        Env.agreeOn_append_right (by simpa [Term.reads, Term.holes] using h)
      simpa only [Term.eval] using congrArgTwo Nat.add (iha ha) (ihb hb)
  | natEq a b iha ihb =>
      have ha : Env.AgreeOn a.reads x y :=
        Env.agreeOn_append_left (by simpa [Term.reads, Term.holes] using h)
      have hb : Env.AgreeOn b.reads x y :=
        Env.agreeOn_append_right (by simpa [Term.reads, Term.holes] using h)
      simpa only [Term.eval] using congrArgTwo Nat.beq (iha ha) (ihb hb)
  | custom o =>
      apply o.respects x y
      simpa using h

/-- Every positional occurrence contributes its field to the dependency set. -/
theorem Term.hole_implies_dependency (term : Term Γ t) (hole : Hole)
    (h : hole ∈ term.holes) : hole.field ∈ term.reads := by
  exact List.mem_map_of_mem h

/-- The dependency list is *exactly* the erasure of positional holes, not a
second analysis that may drift from them. -/
theorem Term.dependency_iff_positional_hole (term : Term Γ t) (field : Nat) :
    field ∈ term.reads ↔
      ∃ hole, hole ∈ term.holes ∧ hole.field = field := by
  simp [Term.reads]

/-! ## 3. Proof-carrying algebraic analysis -/

/-- A term preserves the canonical environment merge. -/
def PreservesMerge (term : Term Γ t) : Prop :=
  ∀ x y, term.eval (Env.merge x y) = Ty.merge t (term.eval x) (term.eval y)

/-- A term is monotone for the orders induced by the canonical merges. -/
def Monotone (term : Term Γ t) : Prop :=
  ∀ x y, Env.merge x y = y → Ty.merge t (term.eval x) (term.eval y) = term.eval y

theorem preservesMerge_implies_monotone {term : Term Γ t}
    (h : PreservesMerge term) : Monotone term := by
  intro x y hxy
  rw [← h x y, hxy]

theorem bool_or_interchange (a b c d : Bool) :
    ((a || b) || (c || d)) = ((a || c) || (b || d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem nat_max_interchange (a b c d : Nat) :
    Nat.max (Nat.max a b) (Nat.max c d) =
      Nat.max (Nat.max a c) (Nat.max b d) := by
  ac_rfl

theorem option_isSome_merge (t : Ty) (x y : Option t.denote) :
    (Ty.merge (.option t) x y).isSome = (x.isSome || y.isSome) := by
  cases x <;> cases y <;> rfl

theorem bool_and_mono (a b c d : Bool)
    (hab : (a || b) = b) (hcd : (c || d) = d) :
    ((a && c) || (b && d)) = (b && d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

theorem nat_le_of_max_eq_right {a b : Nat} (h : Nat.max a b = b) : a ≤ b := by
  calc
    a ≤ Nat.max a b := Nat.le_max_left a b
    _ = b := h

/-- The syntactic fragment known to preserve merge.  The opaque constructor is
available only with an explicit semantic equation; the automatic certifier
below never constructs it. -/
inductive MergeSafe : {t : Ty} → Term Γ t → Type where
  | litBool (b : Bool) : MergeSafe (.litBool b)
  | litNat (n : Nat) : MergeSafe (.litNat n)
  | var (v : Var Γ t) : MergeSafe (.var v)
  | pair : MergeSafe a → MergeSafe b → MergeSafe (.pair a b)
  | fst : MergeSafe p → MergeSafe (.fst p)
  | snd : MergeSafe p → MergeSafe (.snd p)
  | none : MergeSafe (Term.none ( Γ := Γ) (a := a))
  | some : MergeSafe a → MergeSafe (.some a)
  | isSome : MergeSafe a → MergeSafe (.isSome a)
  | boolOr : MergeSafe a → MergeSafe b → MergeSafe (.boolOr a b)
  | natMax : MergeSafe a → MergeSafe b → MergeSafe (.natMax a b)
  | natSucc : MergeSafe a → MergeSafe (.natSucc a)
  | custom (o : CustomNode Γ t) : PreservesMerge (.custom o) → MergeSafe (.custom o)

theorem MergeSafe.sound {term : Term Γ t} (safe : MergeSafe term) :
    PreservesMerge term := by
  intro x y
  induction safe with
  | litBool b => simpa [Term.eval] using (Ty.merge_idem .bool b).symm
  | litNat n => simpa [Term.eval] using (Ty.merge_idem .nat n).symm
  | var v =>
      change (Env.merge x y).get v = Ty.merge _ (x.get v) (y.get v)
      exact Env.get_merge x y v
  | pair ha hb iha ihb =>
      simp only [Term.eval, Ty.merge]
      rw [iha, ihb]
  | fst hp ih =>
      simpa [Term.eval, Ty.merge] using congrArg Prod.fst ih
  | snd hp ih =>
      simpa [Term.eval, Ty.merge] using congrArg Prod.snd ih
  | none => simp [Term.eval, Ty.merge]
  | some ha ih =>
      simp only [Term.eval, Ty.merge]
      rw [ih]
  | isSome ha ih =>
      simp only [Term.eval]
      rw [ih]
      exact option_isSome_merge _ _ _
  | boolOr ha hb iha ihb =>
      simp only [Term.eval, Ty.merge]
      rw [iha, ihb]
      exact bool_or_interchange _ _ _ _
  | natMax ha hb iha ihb =>
      simp only [Term.eval, Ty.merge]
      rw [iha, ihb]
      exact nat_max_interchange _ _ _ _
  | natSucc ha ih =>
      simp only [Term.eval, Ty.merge]
      rw [ih]
      exact (Nat.succ_max_succ _ _).symm
  | custom o h => exact h x y

/-- Automatic, proof-producing merge classifier.  `boolAnd`, `natAdd`,
negation, equality, and every opaque term return `none`; some are monotone but
not structurally merge-preserving, and opaque code has no inspectable syntax. -/
def certifyMergeSafe : (term : Term Γ t) → Option (MergeSafe term)
  | .litBool b => some (.litBool b)
  | .litNat n => some (.litNat n)
  | .var v => some (.var v)
  | .pair a b =>
      match certifyMergeSafe a, certifyMergeSafe b with
      | some ha, some hb => some (.pair ha hb)
      | _, _ => none
  | .fst p => (certifyMergeSafe p).map .fst
  | .snd p => (certifyMergeSafe p).map .snd
  | .none => some .none
  | .some a => (certifyMergeSafe a).map .some
  | .isSome a => (certifyMergeSafe a).map .isSome
  | .boolOr a b =>
      match certifyMergeSafe a, certifyMergeSafe b with
      | some ha, some hb => some (.boolOr ha hb)
      | _, _ => none
  | .natMax a b =>
      match certifyMergeSafe a, certifyMergeSafe b with
      | some ha, some hb => some (.natMax ha hb)
      | _, _ => none
  | .natSucc a => (certifyMergeSafe a).map .natSucc
  | .boolAnd _ _ | .boolNot _ | .natAdd _ _ | .natEq _ _ | .custom _ => none

/-- The larger structurally monotone fragment.  Conjunction and addition are
recognized here but not by `MergeSafe`: independently merging their inputs can
create cross terms. -/
inductive MonotoneSafe : {t : Ty} → Term Γ t → Type where
  | ofMergeSafe : MergeSafe term → MonotoneSafe term
  | boolAnd : MonotoneSafe a → MonotoneSafe b → MonotoneSafe (.boolAnd a b)
  | natAdd : MonotoneSafe a → MonotoneSafe b → MonotoneSafe (.natAdd a b)

theorem MonotoneSafe.sound {term : Term Γ t} (safe : MonotoneSafe term) :
    Monotone term := by
  induction safe with
  | ofMergeSafe h => exact preservesMerge_implies_monotone h.sound
  | boolAnd ha hb iha ihb =>
      intro x y hxy
      have hleft := iha x y hxy
      have hright := ihb x y hxy
      exact bool_and_mono _ _ _ _ hleft hright
  | natAdd ha hb iha ihb =>
      intro x y hxy
      apply Nat.max_eq_right
      exact Nat.add_le_add
        (nat_le_of_max_eq_right (iha x y hxy))
        (nat_le_of_max_eq_right (ihb x y hxy))

/-- Automatic, proof-producing monotonicity classifier. -/
def certifyMonotone : (term : Term Γ t) → Option (MonotoneSafe term)
  | .boolAnd a b =>
      match certifyMonotone a, certifyMonotone b with
      | some ha, some hb => some (.boolAnd ha hb)
      | _, _ => none
  | .natAdd a b =>
      match certifyMonotone a, certifyMonotone b with
      | some ha, some hb => some (.natAdd ha hb)
      | _, _ => none
  | term => (certifyMergeSafe term).map .ofMergeSafe

/-! ## 4. A raw surface boundary that fails closed -/

/-- Untyped surface expressions.  `opaque` is only a name here: constructing a
typed opaque term requires its implementation, dependency list, and locality
proof, so raw inference refuses it. -/
inductive Raw where
  | litBool (value : Bool)
  | litNat (value : Nat)
  | field (index : Nat)
  | pair (left right : Raw)
  | fst (pair : Raw)
  | snd (pair : Raw)
  | none (elem : Ty)
  | some (value : Raw)
  | isSome (value : Raw)
  | boolOr (left right : Raw)
  | boolAnd (left right : Raw)
  | boolNot (value : Raw)
  | natMax (left right : Raw)
  | natAdd (left right : Raw)
  | natSucc (value : Raw)
  | natEq (left right : Raw)
  | custom (name : String)
  deriving Repr

/-- A field found by erased position, repackaged with its type. -/
def Var.at? : (Γ : Schema) → Nat → Option (Σ t, Var Γ t)
  | [], _ => Option.none
  | _ :: _, 0 => Option.some ⟨_, .here⟩
  | _ :: Γ, n + 1 =>
      match at? Γ n with
      | Option.none => Option.none
      | Option.some ⟨t, v⟩ => Option.some ⟨t, .there v⟩

/-- An existentially typed checked expression. -/
structure Checked (Γ : Schema) where
  type : Ty
  term : Term Γ type

def Checked.asBool : Checked Γ → Option (Term Γ .bool)
  | ⟨.bool, term⟩ => Option.some term
  | _ => Option.none

def Checked.asNat : Checked Γ → Option (Term Γ .nat)
  | ⟨.nat, term⟩ => Option.some term
  | _ => Option.none

def Raw.infer (Γ : Schema) : Raw → Option (Checked Γ)
  | .litBool b => Option.some ⟨.bool, .litBool b⟩
  | .litNat n => Option.some ⟨.nat, .litNat n⟩
  | .field n =>
      match Var.at? Γ n with
      | Option.none => Option.none
      | Option.some ⟨t, v⟩ => Option.some ⟨t, .var v⟩
  | .pair a b =>
      match infer Γ a, infer Γ b with
      | Option.some ⟨ta, a⟩, Option.some ⟨tb, b⟩ =>
          Option.some ⟨.pair ta tb, .pair a b⟩
      | _, _ => Option.none
  | .fst p =>
      match infer Γ p with
      | Option.some ⟨.pair a _, p⟩ => Option.some ⟨a, .fst p⟩
      | _ => Option.none
  | .snd p =>
      match infer Γ p with
      | Option.some ⟨.pair _ b, p⟩ => Option.some ⟨b, .snd p⟩
      | _ => Option.none
  | .none a => Option.some ⟨.option a, .none⟩
  | .some a =>
      match infer Γ a with
      | Option.some ⟨t, a⟩ => Option.some ⟨.option t, .some a⟩
      | Option.none => Option.none
  | .isSome a =>
      match infer Γ a with
      | Option.some ⟨.option _, a⟩ => Option.some ⟨.bool, .isSome a⟩
      | _ => Option.none
  | .boolOr a b =>
      match (infer Γ a).bind Checked.asBool, (infer Γ b).bind Checked.asBool with
      | Option.some a, Option.some b => Option.some ⟨.bool, .boolOr a b⟩
      | _, _ => Option.none
  | .boolAnd a b =>
      match (infer Γ a).bind Checked.asBool, (infer Γ b).bind Checked.asBool with
      | Option.some a, Option.some b => Option.some ⟨.bool, .boolAnd a b⟩
      | _, _ => Option.none
  | .boolNot a =>
      match (infer Γ a).bind Checked.asBool with
      | Option.some a => Option.some ⟨.bool, .boolNot a⟩
      | Option.none => Option.none
  | .natMax a b =>
      match (infer Γ a).bind Checked.asNat, (infer Γ b).bind Checked.asNat with
      | Option.some a, Option.some b => Option.some ⟨.nat, .natMax a b⟩
      | _, _ => Option.none
  | .natAdd a b =>
      match (infer Γ a).bind Checked.asNat, (infer Γ b).bind Checked.asNat with
      | Option.some a, Option.some b => Option.some ⟨.nat, .natAdd a b⟩
      | _, _ => Option.none
  | .natSucc a =>
      match (infer Γ a).bind Checked.asNat with
      | Option.some a => Option.some ⟨.nat, .natSucc a⟩
      | Option.none => Option.none
  | .natEq a b =>
      match (infer Γ a).bind Checked.asNat, (infer Γ b).bind Checked.asNat with
      | Option.some a, Option.some b => Option.some ⟨.bool, .natEq a b⟩
      | _, _ => Option.none
  | .custom _ => Option.none

/-- A successful surface compilation.  Keeping the exact `Raw.infer`
equation in the value is the trust boundary: a `Program` cannot pair arbitrary
raw syntax with an unrelated typed term. -/
structure Program (Γ : Schema) where
  raw : Raw
  success : (raw.infer Γ).isSome = true

namespace Program

/-- The checked term is obtained from `Raw.infer` itself; it is not a second
author-supplied field. -/
def checked (program : Program Γ) : Checked Γ :=
  (program.raw.infer Γ).get program.success

abbrev type (program : Program Γ) : Ty := program.checked.type

abbrev term (program : Program Γ) : Term Γ program.type :=
  program.checked.term

/-- Evaluation exposed for runtime/status adapters. -/
def eval (program : Program Γ) (env : Env Γ) : program.type.denote :=
  program.term.eval env

/-- Exact positional holes from the checked term. -/
def holes (program : Program Γ) : List Hole := program.term.holes

/-- Exact reads, definitionally the field erasure of `holes`. -/
def reads (program : Program Γ) : List Nat := program.term.reads

/-- Proof-carrying positive merge analysis.  `none` is an honest non-answer. -/
def mergeSafe? (program : Program Γ) : Option (MergeSafe program.term) :=
  certifyMergeSafe program.term

/-- Proof-carrying positive monotonicity analysis.  `none` is an honest
non-answer and is never interpreted as a refutation. -/
def monotoneSafe? (program : Program Γ) : Option (MonotoneSafe program.term) :=
  certifyMonotone program.term

theorem reads_eq_hole_fields (program : Program Γ) :
    program.reads = program.holes.map Hole.field := rfl

theorem inferred (program : Program Γ) :
    program.raw.infer Γ = Option.some program.checked := by
  have hs := program.success
  cases h : program.raw.infer Γ with
  | none => simp [h] at hs
  | some value => simp [Program.checked, h]

end Program

/-- Compile raw syntax to one checked program.  Failure is data and no typed
term or analysis is produced. -/
def Raw.compile? (Γ : Schema) (raw : Raw) : Option (Program Γ) :=
  if h : (raw.infer Γ).isSome = true then
    Option.some { raw := raw, success := h }
  else
    Option.none

theorem Raw.compile?_isSome (Γ : Schema) (raw : Raw) :
    (raw.compile? Γ).isSome = (raw.infer Γ).isSome := by
  cases h : raw.infer Γ <;> simp [Raw.compile?, h]

/-- A compiled value always exposes the very term returned by inference; this
rules out attaching certificates to unsupported raw syntax. -/
theorem Program.infer_eq (program : Program Γ) :
    program.raw.infer Γ = Option.some program.checked := program.inferred

/-- A successful raw positive analysis contains both the typed term and the
proof that it preserves merge. -/
structure CertifiedMergeSafe (Γ : Schema) where
  type : Ty
  term : Term Γ type
  safe : MergeSafe term

def Raw.certifyMergeSafe (Γ : Schema) (raw : Raw) : Option (CertifiedMergeSafe Γ) :=
  match raw.infer Γ with
  | Option.none => Option.none
  | Option.some ⟨t, term⟩ =>
      match Expr.certifyMergeSafe term with
      | Option.none => Option.none
      | Option.some safe => Option.some ⟨t, term, safe⟩

/-! ## 5. Falsifiability witnesses -/

/-- Reading only the first field of a two-field schema. -/
def firstOnly : Term [.bool, .bool] .bool := .var .here

def outsideLeft : Env [.bool, .bool] := .cons true (.cons false .nil)
def outsideRight : Env [.bool, .bool] := .cons true (.cons true .nil)

/-- Values that differ only outside the dependency set are indistinguishable. -/
theorem outside_dependency_is_indistinguishable :
    outsideLeft ≠ outsideRight ∧ firstOnly.eval outsideLeft = firstOnly.eval outsideRight := by
  constructor
  · intro h
    have htail := congrArg (fun env : Env [.bool, .bool] => env.get (.there .here)) h
    exact Bool.noConfusion htail
  · rfl

/-- Negated membership: learning that the member is present changes `not
present` from true to false. -/
def negatedMembership : Term [.bool] .bool := .boolNot (.var .here)

def absentEnv : Env [.bool] := .cons false .nil
def presentEnv : Env [.bool] := .cons true .nil

theorem negatedMembership_not_monotone : ¬ Monotone negatedMembership := by
  intro h
  have hle : Env.merge absentEnv presentEnv = presentEnv := rfl
  have bad := h absentEnv presentEnv hle
  exact Bool.noConfusion bad

theorem negatedMembership_not_classified_monotone :
    certifyMonotone negatedMembership = none := rfl

/-- A malformed raw term is rejected before analysis. -/
def malformedNotNat : Raw := .boolNot (.litNat 7)

theorem malformed_not_classified :
    Raw.certifyMergeSafe [] malformedNotNat = none := rfl

theorem raw_custom_not_classified :
    Raw.certifyMergeSafe [] (.custom "unchecked") = none := rfl

/-- A semantically ordinary field read hidden behind an opaque node.  Its
locality proof makes evaluation sound, but the automatic algebraic analyses
still refuse to inspect it. -/
def hiddenFirst : CustomNode [.nat] .nat where
  name := "hidden-first"
  run := fun env => env.get .here
  dependencies := [0]
  dependenciesInRange := by simp
  respects := by
    intro x y h
    apply Env.get_eq_of_agreeAt .here x y
    exact h 0 (by simp)

def hiddenFirstTerm : Term [.nat] .nat := .custom hiddenFirst

theorem opaque_not_auto_mergeSafe : certifyMergeSafe hiddenFirstTerm = none := rfl
theorem opaque_not_auto_monotone : certifyMonotone hiddenFirstTerm = none := rfl

/-- The escape hatch is proof-carrying: the same opaque node can be admitted
only after the author supplies its merge equation. -/
theorem hiddenFirst_preservesMerge : PreservesMerge hiddenFirstTerm := by
  intro x y
  exact Env.get_merge x y .here

def hiddenFirst_explicitlySafe : MergeSafe hiddenFirstTerm :=
  .custom hiddenFirst hiddenFirst_preservesMerge

/-- Positional analysis distinguishes the two children while dependency
erasure retains exactly the two field indices. -/
def pairedFields : Term [.bool, .nat] (.pair .bool .nat) :=
  .pair (.var .here) (.var (.there .here))

theorem pairedFields_holes : pairedFields.holes =
    [{ path := [0], field := 0, kind := .field },
     { path := [1], field := 1, kind := .field }] := rfl

theorem pairedFields_reads : pairedFields.reads = [0, 1] := rfl

/-- Addition is a useful sharp edge: it is structurally monotone but does not
preserve independent max-merges, so the two analyses intentionally disagree. -/
def summedFields : Term [.nat, .nat] .nat :=
  .natAdd (.var .here) (.var (.there .here))

def sumLeft : Env [.nat, .nat] := .cons (1 : Nat) (.cons (0 : Nat) .nil)
def sumRight : Env [.nat, .nat] := .cons (0 : Nat) (.cons (1 : Nat) .nil)

theorem summedFields_not_preservesMerge : ¬ PreservesMerge summedFields := by
  intro h
  have bad := h sumLeft sumRight
  simp [summedFields, sumLeft, sumRight, Term.eval, Env.get, Env.merge, Ty.merge] at bad
  exact (by decide : (2 : Nat) ≠ 1) bad

theorem summedFields_not_classified_mergeSafe :
    certifyMergeSafe summedFields = none := rfl

theorem summedFields_classified_monotone :
    ∃ safe : MonotoneSafe summedFields, certifyMonotone summedFields = some safe := by
  exact ⟨MonotoneSafe.natAdd
    (MonotoneSafe.ofMergeSafe (MergeSafe.var .here))
    (MonotoneSafe.ofMergeSafe (MergeSafe.var (.there .here))), rfl⟩

end Uwueave.Preo.Expr
