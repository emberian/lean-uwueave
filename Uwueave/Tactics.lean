/-
# Uwueave.Tactics — the verdict, automated; and the idioms, named.

Two things live here, and they share a doctrine: **a tactic that can produce a
wrong verdict is worse than no tactic.** Every route below either closes the
goal with a kernel-checked term or throws — none of them can report "free" on
an invariant that clashes, because none of them *reports* anything: they
either build the proof or fail.

## §A. `classify` — the verdict tactic

Given `IConfluent I` or `¬ IConfluent I`, `classify` tries, in order:

  1. **selection** (`Catalog.selection_iconfluent`) — if the carrier's merge
     always returns one of its arguments (`SelectionMerge`), *every* invariant
     is I-confluent. Covers `LWW`, `Nat`-under-max, and anything else that
     gets a `SelectionMerge` instance. Works over **infinite** carriers.
  2. **one-key selection** (`key_selection_iconfluent`) — if the invariant
     reads a keyed map at exactly one key and the *value* lattice selects
     (`CLSet`, `GCounter`, any `K → LWW`), it is free. Also infinite.
  3. **monotone closure** (`Catalog.gset_monotone_iconfluent`) — for grow-only
     sets, discharge the upward-closure side condition with a short script.
  4. **exhaustive decision** — over a carrier with a `FinEnum` instance (a
     list plus a *proof* that it contains everything) and a decidable
     invariant, `IConfluent I` is `Decidable`, and `decide` settles it either
     way. This is the only route that also proves the **negative**.
  5. **clash search** — for `¬ IConfluent I`: search a pool of concrete probe
     states for a pair `x, y` with `I x`, `I y`, `¬ I (x ⊔ y)`, then emit
     `not_iconfluent_of_clash x y (by decide) (by decide) (by decide)`.

### What `classify` covers — precisely

* **Positive verdicts** are available for: any invariant over a
  `SelectionMerge` carrier (infinite carriers included); conjunctions thereof;
  monotone invariants over `GSet α` for any `α`; and *arbitrary* decidable
  invariants over a carrier with `FinEnum` (`Bool`, `Fin n`, products of
  those, and function spaces `A → B` out of a finite `A`).
* **Negative verdicts** need only a decidable invariant and a probe that
  clashes — the carrier may be infinite (`GSet Nat`, `PNCounter Bool`,
  `LWW × LWW` all work off the default probe pools).
* **NOT covered**, and `classify` says so rather than guessing: invariants
  with unbounded quantifiers over an infinite type (`∀ m n : Nat, …` is not
  decidable, so no route applies — `Catalog.gset_atMostOne_not_iconfluent` is
  out of reach and must stay hand-proved); carriers with neither `FinEnum`
  nor a `SelectionMerge` nor a probe pool that happens to contain a clash;
  and `Segmented.SegmentedIConfluent`, which is a different judgement.

### How it fails

Loudly, always, and with the clash when it has one:

* asked for `IConfluent I` and a clash exists → the error *names the two
  states*, so the failure is the bug report;
* asked for `¬ IConfluent I` and no clash is in the pool → the error says how
  many probes were tried and how many of them even satisfied `I` (a pool where
  *nothing* satisfies `I` is the commonest cause, and it looks nothing like
  "the invariant is confluent");
* no route applies → the error lists what was tried and names the missing
  instance.

`classify` never closes a goal by any route other than a term the kernel
checks. `Probes` — the search pool — carries **no** completeness obligation
precisely because it is only ever used to *find* a clash, and a found clash is
a refutation whatever else is in the pool; `FinEnum`, which underwrites the
positive verdict, carries a completeness *proof*.

## §B. The idiom tactics

Four proof shapes are copy-pasted across the tree; each gets a name here, and
each is demonstrated below on a goal that exists verbatim in another file.

  * `clash x, y` — the concrete-witness refutation
    (`intro h; exact absurd (h x y _ _) (by decide)`).
  * `mem_union h [defs]` — "this merged set holds exactly these elements",
    the `simp [defs, gset_mem_merge] at h; rcases; cases; simp_all` shape.
  * `view_unique mem, t` — "the view is exactly `{t}`", the
    `constructor; intro ⟨_,_⟩; rcases; subst; decide` shape.
  * `iconf_intro` / `merge_unfold` — the opener, without the hand-written
    `show (x a || y a) = true` that pins the encoding into the proof.
-/
import Uwueave.Catalog
import Uwueave.Segmented
import Uwueave.ORSet
import Uwueave.Undo
import Lean

namespace Uwueave.Tactics

open Uwueave Uwueave.Catalog

universe u v

/-! ## §1. Finite carriers — enumeration with a completeness proof.

`FinEnum` is what licenses a *positive* verdict by exhaustion: a list, plus
the theorem that nothing is missing. Without the second field an exhaustive
`decide` would be a vacuous check over whatever the list happened to hold. -/

/-- A carrier with a listing of **all** its elements. The `complete` field is
the whole point: it is what makes `decide` over `enum` a proof about the type
rather than about the list. -/
class FinEnum (S : Type u) where
  /-- Every element of `S`, listed. -/
  enum : List S
  /-- …and nothing is missing. -/
  complete : ∀ s : S, s ∈ enum

instance : FinEnum Bool where
  enum := [false, true]
  complete b := by cases b <;> simp

instance : FinEnum Unit where
  enum := [()]
  complete u := by cases u; simp

instance (n : Nat) : FinEnum (Fin n) where
  enum := List.finRange n
  complete := List.mem_finRange

instance {A : Type u} {B : Type v} [FinEnum A] [FinEnum B] : FinEnum (A × B) where
  enum := (FinEnum.enum (S := A)).flatMap fun a => (FinEnum.enum (S := B)).map fun b => (a, b)
  complete p := by
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨p.1, FinEnum.complete p.1, p.2, FinEnum.complete p.2, rfl⟩

/-- All functions `A → B` that agree with `base` off `l`, tabulated. The
enumeration of a function space is the one construction here that is not a
one-liner; `mem_funsOn` is its correctness. -/
def funsOn {A : Type u} {B : Type v} [DecidableEq A]
    (l : List A) (bs : List B) (base : A → B) : List (A → B) :=
  match l with
  | [] => [base]
  | a :: l' =>
      (funsOn l' bs base).flatMap fun f => bs.map fun b => fun a' => if a' = a then b else f a'

/-- **Tabulation is complete on `l`**: any `g` whose values on `l` come from
`bs` is matched on `l` by some tabulated function. -/
theorem mem_funsOn {A : Type u} {B : Type v} [DecidableEq A]
    (l : List A) (bs : List B) (base : A → B) (g : A → B) (hg : ∀ a, g a ∈ bs) :
    ∃ f ∈ funsOn l bs base, ∀ a ∈ l, f a = g a := by
  induction l with
  | nil => exact ⟨base, by simp [funsOn], by simp⟩
  | cons a l' ih =>
      obtain ⟨f, hf, hfa⟩ := ih
      refine ⟨fun a' => if a' = a then g a else f a', ?_, ?_⟩
      · simp only [funsOn, List.mem_flatMap, List.mem_map]
        exact ⟨f, hf, g a, hg a, rfl⟩
      · intro a'' h''
        by_cases hc : a'' = a
        · simp [hc]
        · simp only [if_neg hc]
          rcases List.mem_cons.mp h'' with h | h
          · exact absurd h hc
          · exact hfa a'' h

instance instFinEnumFun {A : Type u} {B : Type v}
    [DecidableEq A] [FinEnum A] [FinEnum B] [Inhabited B] : FinEnum (A → B) where
  enum := funsOn (FinEnum.enum (S := A)) (FinEnum.enum (S := B)) (fun _ => default)
  complete g := by
    obtain ⟨f, hf, hfa⟩ := mem_funsOn (FinEnum.enum (S := A)) (FinEnum.enum (S := B))
      (fun _ => default) g (fun a => FinEnum.complete (g a))
    have hfg : f = g := funext fun a => hfa a (FinEnum.complete a)
    exact hfg ▸ hf

/-! ## §2. The judgement is decidable on a finite carrier. -/

/-- **`IConfluent` is decidable over a `FinEnum` carrier with a decidable
invariant** — and decidable *both ways*, which is why this single instance
serves the free verdict and the refutation alike. `decide` on it is a kernel
computation over the enumeration; the `complete` field is what turns "no clash
in the list" into "no clash at all". -/
instance instDecidableIConfluent {S : Type u} [MergeState S] [FinEnum S]
    (I : Invariant S) [DecidablePred I] : Decidable (IConfluent I) :=
  decidable_of_iff
    (∀ x ∈ FinEnum.enum (S := S), ∀ y ∈ FinEnum.enum (S := S), I x → I y → I (x ⊔ y))
    ⟨fun h x y => h x (FinEnum.complete x) y (FinEnum.complete y),
     fun h x _ y _ => h x y⟩

/-! ## §3. Refutation by witness — and the probe pools that find one. -/

/-- **The refutation lemma.** Two legal states whose merge is illegal *are* the
counterexample; `escalation_witness` (`Confluence.lean`) is the converse. This
is the term every negative route emits. -/
theorem not_iconfluent_of_clash {S : Type u} [MergeState S] {I : Invariant S} {x y : S}
    (hx : I x) (hy : I y) (hbad : ¬ I (x ⊔ y)) : ¬ IConfluent I :=
  fun h => hbad (h x y hx hy)

/-- **A pool of concrete states to look for a clash in — a heuristic, and
deliberately unproved.** There is no completeness field and there must not be
one: the pool is only ever used to *find* a clash, and any clash found is a
genuine refutation no matter what else the pool holds or omits. A pool that
finds nothing yields no verdict at all — `classify` says so.

Supply your own with `classify using <list>` when the defaults are too coarse
(they carry small values; a budget of 10 needs states with a 10 in them). -/
class Probes (S : Type u) where
  /-- Candidate states. No completeness obligation — see the class doc. -/
  probes : List S

/-- A function given by a lookup table, `default` off the table. Probe pools of
function-typed states are built from these rather than from `funsOn`, for one
reason: a clash is reported by printing the state, and `table [(0, true)]` is
legible where a nest of tabulating `if`s is not. `Probes` carries no proof
obligation, so it is free to choose the readable spelling; `FinEnum`, which
does, keeps `funsOn`. -/
def table {A : Type u} {B : Type v} [DecidableEq A] [Inhabited B]
    (kvs : List (A × B)) : A → B := fun a =>
  match kvs.find? (fun p => p.1 = a) with
  | some p => p.2
  | none => default

/-- Every assignment of `vals` to `keys`, as tables. -/
def tables {A : Type u} {B : Type v} [DecidableEq A] [Inhabited B]
    (keys : List A) (vals : List B) : List (A → B) :=
  (go keys).map table
where
  /-- Every key/value assignment over `keys`. -/
  go : List A → List (List (A × B))
    | [] => [[]]
    | a :: as => (go as).flatMap fun rest => vals.map fun v => (a, v) :: rest

instance : Probes Bool := ⟨[false, true]⟩

/-- Deliberately tiny. Probe pools multiply: `Probes Nat` of size `k` makes
`Bool → Nat` of size `k²` and `PNCounter Bool` of size `k⁴`. -/
instance : Probes Nat := ⟨[0, 1]⟩

instance {A : Type u} {B : Type v} [Probes A] [Probes B] : Probes (A × B) :=
  ⟨(Probes.probes (S := A)).flatMap fun a => (Probes.probes (S := B)).map fun b => (a, b)⟩

/-- Functions out of a finite domain: every table over the whole domain. -/
instance {A : Type u} {B : Type v} [DecidableEq A] [FinEnum A] [Probes B] [Inhabited B] :
    Probes (A → B) :=
  ⟨tables (FinEnum.enum (S := A)) (Probes.probes (S := B))⟩

/-- Functions out of `Nat` — an infinite domain, so the pool is the
**small-support** states: anything can happen on keys `0,1,2`, and the default
value holds everywhere else. Enough for the standard grow-only-set clashes
(`{0}` vs `{1}`, `{0,1}` vs `{0,2}`), and honestly incomplete. -/
instance instProbesNatFun {B : Type v} [Probes B] [Inhabited B] : Probes (Nat → B) :=
  ⟨tables [0, 1, 2] (Probes.probes (S := B))⟩

instance : Probes LWW :=
  ⟨(Probes.probes (S := Nat)).flatMap fun t =>
    (Probes.probes (S := Nat)).map fun v => ⟨t, v⟩⟩

/-! ## §4. Selection lattices — the route that beats an infinite carrier.

`Catalog.selection_iconfluent` says a merge that *picks a side* preserves every
invariant. Registering that fact as a class turns it into a route `classify`
can take without enumerating anything. -/

/-- A merge that always returns one of its arguments. Every invariant over
such a carrier is I-confluent (`Catalog.selection_iconfluent`). -/
class SelectionMerge (S : Type u) [MergeState S] where
  /-- The join picks a side. -/
  selects : ∀ x y : S, x ⊔ y = x ∨ x ⊔ y = y

instance : SelectionMerge LWW := ⟨LWW.join_selects⟩

instance : SelectionMerge Nat := ⟨fun x y => by
  show Nat.max x y = x ∨ Nat.max x y = y
  rw [nat_max_def]
  split
  · exact Or.inr rfl
  · exact Or.inl rfl⟩

/-- **A one-key invariant over a pointwise selection lattice is I-confluent.**
The merged map's value at `k` is one of the two replicas' values at `k`, and
that replica was legal. This is the general law behind
`ORSet.clset_present_iconfluent`, `ORSet.clset_absent_iconfluent` and
`Catalog.gcounter_lowerBound_iconfluent` — three proofs of one fact, each
re-deriving `Nat.max`'s selection by hand.

⚠ Read the quantifier: **one** key. The cross-key invariant is
`ORSet.clset_cross_element_not_iconfluent`, and it is false — pointwise
selection lattices compose into non-selection lattices. -/
theorem key_selection_iconfluent {K : Type u} {V : Type v} [MergeState V] [SelectionMerge V]
    (k : K) (P : V → Prop) : IConfluent (S := K → V) (fun f => P (f k)) := by
  intro x y hx hy
  show P ((x ⊔ y) k)
  rw [pi_merge_apply]
  rcases SelectionMerge.selects (x k) (y k) with h | h
  · rw [h]; exact hx
  · rw [h]; exact hy

/-! ## §5. `classify` — the tactic.

The meta code below **steers**; it never concludes. Every verdict it reaches is
re-derived as a term the kernel checks (`decide`, or
`not_iconfluent_of_clash x y (by decide) (by decide) (by decide)` on witnesses
the search proposed). A bug in the search can therefore only produce a
*failure*, never a false "free". -/

namespace Classify

open Lean Meta Elab Tactic

/-- `IConfluent I` ↦ `(S, MergeState instance, I)`. -/
def iconfArgs? (e : Expr) : Option (Expr × Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``Uwueave.IConfluent 3 then
    let a := e.getAppArgs
    some (a[0]!, a[1]!, a[2]!)
  else
    none

/-- `¬ P` in either spelling ↦ `P`. -/
def negArg? (e : Expr) : Option Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Not 1 then
    some e.appArg!
  else
    match e with
    | .forallE _ d b _ => if b.consumeMData.isConstOf ``False then some d else none
    | _ => none

/-- Evaluate a closed decidable proposition. Used **only to steer the search**;
the verdict it suggests is always re-proved by a kernel-checked term. -/
def expose (p : Expr) (fuel : Nat := 3) : MetaM Expr := do
  match fuel with
  | 0 => withDefault <| whnf p
  | n + 1 =>
      let e ← withDefault <| whnf p
      match negArg? e with
      | some q => mkAppM ``Not #[← expose q n]
      | none => return e

def decideHolds (p : Expr) : MetaM Bool := do
  let d ←
    try mkDecide p
    catch _ =>
      try mkDecide (← expose p)
      catch _ =>
        throwError m!"classify: the invariant is not decidable at a concrete state:" ++
          indentExpr p ++ m!"\n" ++
          m!"The clash search evaluates the invariant on probes, so it needs \
            `DecidablePred I` — an unbounded `∀ n : Nat, …` is not one. Prove this goal \
            by hand, or restate the invariant over a bounded domain."
  let r ← withDefault <| whnf d
  return r.isConstOf ``Bool.true

/-- `mkDecideProof`, retried through one `whnf` — a named invariant
(`Segmented.BudgetInv`) is not unfolded by instance synthesis, so `Decidable`
is only found after the head is exposed. The resulting proof is at a
definitionally equal type, which is what the application check wants. -/
def decideProof (p : Expr) : MetaM Expr := do
  try mkDecideProof p catch _ => mkDecideProof (← expose p)

/-- Walk a list expression down its spine, leaving the *elements* unreduced —
so a reported clash reads as the states were written, not as their normal
forms. -/
partial def listElems (e : Expr) : MetaM (Array Expr) := do
  let e ← withDefault <| whnf e
  match e.getAppFnArgs with
  | (``List.cons, #[_, h, t]) => return #[h] ++ (← listElems t)
  | (``List.nil, _) => return #[]
  | _ => throwError "classify: the probe pool did not reduce to a list literal:{indentExpr e}"

/-- The probe pool for carrier `S`: an explicit `using` list, else a `Probes`
instance, else a `FinEnum` enumeration. -/
def getPool (S : Expr) (explicit? : Option Expr) : MetaM (Array Expr × String) := do
  if let some e := explicit? then
    return ((← listElems e), "the `using` list")
  match ← trySynthInstance (← mkAppM ``Probes #[S]) with
  | .some inst =>
      return ((← listElems (← mkAppOptM ``Probes.probes #[S, inst])), "the `Probes` pool")
  | _ =>
    match ← trySynthInstance (← mkAppM ``FinEnum #[S]) with
    | .some inst =>
        return ((← listElems (← mkAppOptM ``FinEnum.enum #[S, inst])), "the `FinEnum` enumeration")
    | _ =>
        throwError "classify: no probe pool for{indentExpr S}\n\
          Give one with `classify using <list of states>`, or register a \
          `Probes`/`FinEnum` instance."

/-- The maximum pool size the pairwise search will walk. Beyond it the search
refuses rather than hangs. -/
def poolCap : Nat := 64

/-- Search a pool for a clash: two states satisfying `I` whose merge does not.
Returns the states, or the pool census (`legal`, `total`) that found none. -/
def findClash (S inst I : Expr) (pool : Array Expr) :
    MetaM (Except (Nat × Nat) (Expr × Expr)) := do
  if pool.size > poolCap then
    throwError "classify: probe pool has {pool.size} states, over the cap of {poolCap} — \
      the pairwise search would not terminate usefully. Narrow it with `classify using <list>`."
  let mut legal : Array Expr := #[]
  for x in pool do
    if ← decideHolds (mkAppN I #[x]).headBeta then
      legal := legal.push x
  for x in legal do
    for y in legal do
      let m ← mkAppOptM ``Uwueave.MergeState.merge #[S, inst, x, y]
      unless ← decideHolds (mkAppN I #[m]).headBeta do
        return .ok (x, y)
  return .error (legal.size, pool.size)

/-- Build `not_iconfluent_of_clash` on a found pair, with all three side
conditions discharged by `decide` — kernel-checked, so a wrong witness is a
build error, never a wrong verdict. -/
def clashProof (S inst I x y : Expr) : MetaM Expr := do
  let m ← mkAppOptM ``Uwueave.MergeState.merge #[S, inst, x, y]
  let px ← decideProof (mkAppN I #[x]).headBeta
  let py ← decideProof (mkAppN I #[y]).headBeta
  let pbad ← decideProof (← mkAppM ``Not #[(mkAppN I #[m]).headBeta])
  mkAppOptM ``Uwueave.Tactics.not_iconfluent_of_clash #[S, inst, I, x, y, px, py, pbad]

/-- Run a tactic script, reporting whether it closed the goal; restores state
on failure so the next route starts clean. -/
def tryRoute (stx : TSyntax `tactic) : TacticM Bool := do
  let s ← saveState
  try
    evalTactic stx
    if (← getUnsolvedGoals).isEmpty then
      return true
    else
      s.restore
      return false
  catch _ =>
    s.restore
    return false

/-- **The one-key selection route.** If the invariant reads the map at exactly
one key and the value lattice selects, `key_selection_iconfluent` closes it.

This one is meta code rather than an `exact` because `fun f => ?P (f ?k)` is
not a higher-order *pattern* — `?P` is applied to `f k`, not to a bound
variable, so unification cannot guess it and `apply` fails. Abstraction can:
find an occurrence `s k` in the body, `kabstract` it, and check that nothing
else mentions `s`. That last check is what makes the route sound for one key
and refuse for two (`ORSet.clset_cross_element_not_iconfluent` is the
cross-key invariant, and it is *false*). -/
def tryKeySelection (S I : Expr) : TacticM Bool := do
  let goal ← getMainGoal
  try
    let Sw ← whnf S
    let .forallE _ K V _ := Sw | return false
    if V.hasLooseBVars then return false
    let some (k, P) ← lambdaTelescope I fun args body => do
        unless args.size == 1 do return none
        let s := args[0]!
        let isRead := fun (e : Expr) => e.isApp && e.appFn! == s
        -- A named invariant (`CLPresent s a`) hides the read behind a `def`;
        -- expose the head once before giving up.
        let (body, occ?) ←
          match body.find? isRead with
          | some occ => pure (body, some occ)
          | none => do
              let body' ← whnf body
              pure (body', body'.find? isRead)
        let some occ := occ? | return none
        let key := occ.appArg!
        if key.containsFVar s.fvarId! then return none
        let abst ← kabstract body occ
        let P := Expr.lam `v V abst .default
        if P.containsFVar s.fvarId! then return none
        return some (key, P)
      | return false
    let e ← mkAppOptM ``Uwueave.Tactics.key_selection_iconfluent #[K, V, none, none, k, P]
    unless ← isDefEq (← goal.getType) (← inferType e) do return false
    goal.assign e
    replaceMainGoal []
    return true
  catch _ => return false

/-- The syntactic positive routes, in order of cost. Each either closes the
goal or leaves it untouched. -/
def positiveRoutes : List (String × TSyntax `tactic) := Id.run do
  return [
    ("selection lattice (Catalog.selection_iconfluent)",
      Unhygienic.run `(tactic|
        exact Uwueave.Catalog.selection_iconfluent Uwueave.Tactics.SelectionMerge.selects _)),
    ("monotone closure (Catalog.gset_monotone_iconfluent)",
      Unhygienic.run `(tactic|
        (apply Uwueave.Catalog.gset_monotone_iconfluent
         intro s t hst hI
         first
           | exact hst _ hI
           | exact fun a ha => hst a (hI a ha)
           | exact ⟨hst _ hI.1, hst _ hI.2⟩
           | simp_all))),
    ("exhaustive decision over FinEnum",
      Unhygienic.run `(tactic| decide))]

/-- Render a probe for a human. A generated probe arrives as an unevaluated
`table ((fun v => …) x)`; reducing *the table's list* (and nothing else) turns
it into `table [(0, true), (1, false)]`, which is a state you can read. Display
only, and total: on any surprise the raw term is printed. -/
def normalizeProbe (e : Expr) (fuel : Nat := 4) : MetaM Expr := do
  match fuel with
  | 0 => return e
  | n + 1 =>
      let e ← whnfCore e
      if e.isAppOfArity ``Uwueave.Tactics.table 5 then
        let args := e.getAppArgs
        return mkAppN e.getAppFn (args.set! 4 (← withDefault <| Meta.reduce args[4]!))
      else if e.isAppOfArity ``Prod.mk 4 then
        let args := e.getAppArgs
        return mkAppN e.getAppFn
          #[args[0]!, args[1]!, ← normalizeProbe args[2]! n, ← normalizeProbe args[3]! n]
      else
        return e

/-- `indentExpr` on a probe, made legible. -/
def display (e : Expr) : MetaM MessageData := do
  try return indentExpr (← normalizeProbe e) catch _ => return indentExpr e

/-- Report a clash as an error. This is the failure mode the tactic exists to
have: the counterexample *is* the answer to the question that was asked. -/
def throwClash (positive : Bool) (source : String) (x y : Expr) : TacticM α := do
  let head := if positive then
    "classify: this invariant is NOT I-confluent — it cannot be proved free."
  else
    "classify: internal error — clash found but the goal is not a refutation."
  throwError m!"{head}\nClash found in {source}:" ++
    m!"\n  x ={← display x}\n  y ={← display y}\n" ++
    m!"Both satisfy the invariant; their merge does not. That pair is the bug \
      report — it is the scenario users will hit, and the test an implementation \
      must decide a policy for. State `¬ IConfluent …` and prove it with \
      `classify`, or `clash x, y`."

end Classify

/-- **The verdict tactic.** On `IConfluent I` it tries the selection, one-key
selection, monotone-closure and exhaustive-decision routes; on `¬ IConfluent I`
it searches a probe pool for a clash and emits the witness refutation. It
closes the goal with a kernel-checked term or it fails — loudly, naming the
clash when it found one. Covered fragment and failure modes: the file header.

`classify using <list>` supplies a probe pool explicitly (the defaults carry
small values; a budget of 10 needs states with a 10 in them). -/
syntax "classify" (" using " term)? : tactic

open Lean Meta Elab Tactic Classify in
elab_rules : tactic
  | `(tactic| classify $[using $poolStx]?) => withMainContext do
  let goal ← instantiateMVars (← (← getMainGoal).getType)
  let goal ← whnfR goal
  -- The carrier, so the `using` pool elaborates at `List S` rather than blind:
  -- an unannotated `fun _ => 2` otherwise leaves its domain a metavariable and
  -- the invariant becomes undecidable at it for no reason the user can see.
  let carrier? : Option Expr :=
    match iconfArgs? goal with
    | some (S, _, _) => some S
    | none => (negArg? goal).bind fun inner => (iconfArgs? inner).map (·.1)
  let explicit? ← match poolStx with
    | some stx => do
        let expected? ← match carrier? with
          | some S => pure (some (← mkAppM ``List #[S]))
          | none => pure none
        let e ← Term.elabTerm stx expected?
        Term.synthesizeSyntheticMVars
        pure (some (← instantiateMVars e))
    | none => pure none
  if let some (S, inst, I) := iconfArgs? goal then
    -- Positive: try each route; a route that closes the goal is the verdict.
    if ← tryRoute (positiveRoutes.head!).2 then
      return
    if ← tryKeySelection S I then
      return
    for (_, stx) in positiveRoutes.tail! do
      if ← tryRoute stx then
        return
    -- No route worked. Say why, with the clash if there is one.
    let (pool, source) ← getPool S explicit?
    match ← findClash S inst I pool with
    | .ok (x, y) => throwClash true source x y
    | .error (legal, total) =>
        throwError "classify: no route applies to{indentExpr goal}\n\
          Tried: selection lattice, one-key selection, monotone closure, \
          exhaustive decision over `FinEnum`.\n\
          No clash either — {legal} of {total} states in {source} satisfy the \
          invariant, and no pair of them clashes. This is NOT a verdict: the \
          pool is a heuristic, not an enumeration. Register a `FinEnum` \
          instance for the carrier to get a decision, widen the pool with \
          `classify using <list>`, or prove it by hand."
  else if let some inner := negArg? goal then
    let inner ← whnfR inner
    let some (S, inst, I) := iconfArgs? inner
      | throwError "classify: expected `IConfluent I` or `¬ IConfluent I`, got{indentExpr goal}"
    -- Refutation: exhaustive decision first (it is a proof), then clash search.
    if explicit?.isNone then
      if ← tryRoute (Unhygienic.run `(tactic| decide)) then
        return
    let (pool, source) ← getPool S explicit?
    match ← findClash S inst I pool with
    | .ok (x, y) =>
        let prf ← clashProof S inst I x y
        (← getMainGoal).assign prf
        replaceMainGoal []
    | .error (legal, total) =>
        throwError "classify: no clash found, and therefore NO VERDICT.\n\
          {legal} of {total} states in {source} satisfy the invariant, and no \
          pair of them clashes.\n\
          This does not mean the invariant is I-confluent — a probe pool is a \
          heuristic. If nothing satisfied the invariant the pool is simply \
          wrong for it (the defaults carry small values). Widen it with \
          `classify using <list>`, register a `FinEnum` instance for a real \
          decision, or prove the positive goal with `classify`."
  else
    throwError "classify: expected `IConfluent I` or `¬ IConfluent I`, got{indentExpr goal}"

/-! ## §6. `classify`, demonstrated.

Each example below is the statement of an existing theorem of this library,
copied verbatim, with the hand proof replaced by one word. -/

section ClassifyDemo

open Uwueave.ORSet

/-- `Catalog.lww_every_invariant_iconfluent` — selection route, infinite
carrier, arbitrary invariant. Original: one term citing two lemmas. -/
example (I : Invariant LWW) : IConfluent I := by classify

/-- `ORSet.clset_present_iconfluent` — one-key selection route over the
pointwise-max lattice. Original: 5 lines (`show`/`rw`/`split`/two cases). -/
example {α : Type} (a : α) : IConfluent (S := CLSet α) (fun s => CLPresent s a) := by
  classify

/-- `ORSet.clset_absent_iconfluent` — same route, same one word. -/
example {α : Type} (a : α) : IConfluent (S := CLSet α) (fun s => s a % 2 = 0) := by
  classify

/-- `Catalog.gcounter_lowerBound_iconfluent` — third instance of the same
route; the tree proves this one by hand with `Nat.le_trans`/`Nat.le_max_left`. -/
example {ι : Type} (i : ι) (k : Nat) : IConfluent (S := GCounter ι) (fun f => k ≤ f i) := by
  classify

/-- `Catalog.gset_mem_iconfluent` — monotone-closure route, over an arbitrary
(infinite) element type. -/
example {α : Type} (a : α) : IConfluent (S := GSet α) (fun s => s a = true) := by classify

/-- Exhaustive-decision route: a finite carrier, an invariant no lemma covers.
`GSet Bool` has four states; `FinEnum` enumerates them *with the proof that
that is all of them*, and `decide` settles the 16 pairs. -/
example : IConfluent (S := GSet Bool) (fun s => s true = true ∨ s false = true) := by
  classify

/-- The exhaustive route decides the **negative** too — same instance, no probe
pool involved. Over `GSet Bool`, "exactly one element" is refuted by decision,
not by search. -/
example : ¬ IConfluent (S := GSet Bool) (fun s => (s true = true) ≠ (s false = true)) := by
  classify

/-- `Catalog.or_breaks_iconfluence` — clash search over the default `GSet Nat`
probes (small-support subsets of `{0,1,2}`). Original: 6 lines. -/
example : ¬ IConfluent (S := GSet Nat)
    (fun s => (s 0 = true ∧ s 1 = false) ∨ (s 1 = true ∧ s 0 = false)) := by classify

/-- `Weave.active_path_not_iconfluent` — the loom's shared active path, found
by the same pool. Original: 6 lines with the witnesses written by hand. -/
example : ¬ IConfluent (S := GSet Nat)
    (fun s => s 0 = true ∧ ((s 1 = true ∧ s 2 = false) ∨ (s 2 = true ∧ s 1 = false))) := by
  classify

/-- `Catalog.pncounter_nonneg_not_iconfluent` — Bailis's motivating example,
found in the 16-state `(Bool → Nat) × (Bool → Nat)` pool. Original: 7 lines. -/
example : ¬ IConfluent (S := PNCounter Bool) (fun c => 0 ≤ net c) := by classify

/-- `Catalog.lww_cross_field_not_iconfluent` — the cross-field register clash.
The search finds a *different* witness than the hand proof's `(2,5)/(1,0),(3,0)`
(the probes only carry `0`s and `1`s), which is the point: any clash refutes. -/
example : ¬ IConfluent (S := LWW × LWW) (fun p => p.1.val ≤ p.2.val) := by classify

/-- The escape hatch, and the honest failure it repairs. `Segmented.BudgetInv 10`
needs states holding a `10`; the default pools carry `0`s and `1`s, so `classify`
alone reports *no verdict* (see the file header — it does not guess). Handing it
the two allocations from `Segmented.budget_not_iconfluent` settles it. -/
private def budgetProbes : List Segmented.QuotaState :=
  [((fun b => if b then 10 else 0), (fun b => if b then 10 else 0)),
   ((fun b => if b then 0 else 10), (fun b => if b then 0 else 10))]

example : ¬ IConfluent (Segmented.BudgetInv 10) := by classify using budgetProbes

/-- `ORSet.clset_cross_element_not_iconfluent` — same escape hatch, second
instance. The clash needs a `3` against a `2` (odd beats even at `max`), and
the default `Probes Nat` carries only `0` and `1`; handed the two states, the
search settles it. Original: 16 lines, the longest refutation in that file. -/
example : ¬ IConfluent (S := CLSet Nat) (fun s => s 0 % 2 = 1 → s 1 % 2 = 1) := by
  classify using [(fun n => if n = 0 then 3 else 1), (fun _ => 2)]

end ClassifyDemo

/-! ## §7. The idiom tactics.

Four shapes the tree repeats. Each is a macro over the same script the hand
proofs run, so nothing new is trusted. -/

/-- Rewrite a goal so the merge is *computed* — `(x ⊔ y) a` becomes
`x a || y a`, `(x ⊔ y).1` becomes `x.1 ⊔ y.1`, and so on. Replaces the
hand-written `show (x a || y a) = true` lines, which pin the encoding of the
merge into every proof that opens with one. -/
macro "merge_unfold" : tactic =>
  `(tactic| first
    | simp only [Uwueave.Catalog.gset_mem_merge, Uwueave.prod_merge_fst,
        Uwueave.prod_merge_snd, Uwueave.pi_merge_apply]
    | skip)

/-- The I-confluence opener: introduce the two replicas and their legality
hypotheses, then compute the merge. `iconf_intro x y hx hy` is
`intro x y hx hy` followed by `merge_unfold`. -/
syntax "iconf_intro" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| iconf_intro $xs*) => `(tactic| (intro $xs*; merge_unfold))

/-- **The concrete-witness refutation.** `clash x, y` proves `¬ IConfluent I`
from a pair you name, discharging `I x`, `I y` and `¬ I (x ⊔ y)` by `decide`.
This is `classify`'s negative route with the search skipped — use it when the
witness is the point (it belongs in the docstring), or when the invariant is
outside any probe pool. -/
macro "clash " x:term ", " y:term : tactic =>
  `(tactic| exact @Uwueave.Tactics.not_iconfluent_of_clash _ _ _ $x $y
      (by decide) (by decide) (by decide))

/-- Case-split a hypothesis that is a (possibly nested) disjunction of
equations, substituting each. Arity is discovered, not declared. -/
syntax "rsubst " term : tactic
macro_rules
  | `(tactic| rsubst $h) =>
    `(tactic|
      focus
        (have hEq := $h
         rcases hEq with hEq | hEq | hEq | hEq | hEq | hEq | hEq | hEq
         all_goals (try subst hEq)))

/-- **"This merged set holds exactly these elements."** Given
`h : (s₁ ⊔ … ⊔ sₙ) w = true` where each `sᵢ` is a singleton `fun w => w == cᵢ`,
close the goal `w = c₁ ∨ … ∨ cₙ`. The bracket takes the *state* definitions to
unfold — never the element definitions: leaving `c₁ …` folded is what keeps
`beq_iff_eq` from decomposing them into component equations, which is the
`cases w; simp_all [c₁]` step the hand proofs each pay per case. -/
syntax "mem_union " ident " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mem_union $h:ident [$ds,*]) =>
    `(tactic| first
      | (simp only [$ds,*, Uwueave.Catalog.gset_mem_merge, Bool.or_eq_true, beq_iff_eq,
            or_assoc] at $h:ident ⊢
         exact $h)
      | (simp only [$ds,*, Uwueave.Catalog.gset_mem_merge, Bool.or_eq_true, beq_iff_eq,
            or_assoc] at $h:ident
         exact $h))

/-- **"The view is exactly `{t}`."** Proves `InView s w ↔ w = t` given the
membership lemma for `s` (`mem_s…`, itself a `mem_union` one-liner) and the
dominating write `t`. Runs the same script the hand proofs run: forward, split
the membership cases and kill each non-`t` one with the domination fact;
backward, substitute and decide. -/
macro "view_unique " mem:term ", " t:term : tactic =>
  `(tactic|
    (constructor
     · intro hview
       obtain ⟨hmem, hnodom⟩ := hview
       rsubst ($mem hmem)
       all_goals (first | rfl | exact absurd (by decide) (hnodom $t (by decide)))
     · intro hIsT
       subst hIsT
       refine ⟨by decide, ?_⟩
       intro w' hw'
       rsubst ($mem hw')
       all_goals decide))

/-! ## §8. The idiom tactics, demonstrated on the tree's real goals.

Every statement below is copied verbatim from another module. Nothing there is
edited — these are the same goals, re-proved by the named tactic, so the
saving is measured rather than asserted. -/

section IdiomDemo

open Uwueave.MVRegister Uwueave.Undo

/-- `Catalog.gset_mem_iconfluent`, opener replaced (was: `intro x y hx hy;
show (x a || y a) = true; simp [hx]`). -/
example {α : Type} (a : α) : IConfluent (S := GSet α) (fun s => s a = true) := by
  iconf_intro x y hx hy
  simp [hx]

/-- `Catalog.escrow_local_bound_iconfluent`, opener replaced. -/
example {ι : Type} (q : ι → Nat) :
    IConfluent (S := Escrow ι) (fun f => ∀ i, f i ≤ q i) := by
  iconf_intro x y hx hy
  intro i
  exact Nat.max_le.mpr ⟨hx i, hy i⟩

/-- `Catalog.lww_cross_field_not_iconfluent` with its own witnesses — the
5-line `intro`/`exact absurd`/`by decide` block becomes the witnesses alone. -/
example : ¬ IConfluent (S := LWW × LWW) (fun p => p.1.val ≤ p.2.val) := by
  clash (⟨2, 5⟩, ⟨2, 5⟩), (⟨1, 0⟩, ⟨3, 0⟩)

/-- `Catalog.pncounter_nonneg_not_iconfluent`, witnesses preserved. -/
example : ¬ IConfluent (S := PNCounter Bool) (fun c => 0 ≤ net c) := by
  clash (fun b => if b then 10 else 0, fun b => if b then 10 else 0),
        (fun b => if b then 10 else 0, fun b => if b then 0 else 10)

/-- `Undo.mem_s01` (8 lines → 1). -/
example {w : Write} (h : s01 w = true) : w = w0 ∨ w = w1 := by
  mem_union h [s01]

/-- `Undo.mem_s01u` (9 lines → 1). -/
example {w : Write} (h : s01u w = true) : w = w0 ∨ w = w1 ∨ w = u1 := by
  mem_union h [s01u, s01]

/-- `Undo.mem_s01ur` (10 lines → 1). -/
example {w : Write} (h : s01ur w = true) : w = w0 ∨ w = w1 ∨ w = u1 ∨ w = r1 := by
  mem_union h [s01ur, s01u, s01]

/-- `Undo.mem_s01uC` (10 lines → 1). -/
example {w : Write} (h : s01uC w = true) : w = w0 ∨ w = w1 ∨ w = u1 ∨ w = wC := by
  mem_union h [s01uC, s01u, s01]

/-- `MVRegister.mem_sAB` (6 lines → 1). -/
example {w : Write} (h : sAB w = true) : w = wA ∨ w = wB := by
  mem_union h [sAB]

/-- `Undo.overwrite_supersedes` (11 lines → 1). -/
example (w : Write) : InView s01 w ↔ w = w1 := by
  view_unique mem_s01, w1

/-- `Undo.undo_restores` (12 lines → 1). -/
example (w : Write) : InView s01u w ↔ w = u1 := by
  view_unique mem_s01u, u1

/-- `Undo.redo_restores` (13 lines → 1). -/
example (w : Write) : InView s01ur w ↔ w = r1 := by
  view_unique mem_s01ur, r1

end IdiomDemo

end Uwueave.Tactics
