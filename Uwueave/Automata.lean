/-
# Uwueave.Automata — replicated automata, run through the library's verdict machinery.

A replicated automaton is a state machine whose copies run at different
replicas, each feeding the input letters that arrive locally, and sync. The
library's usual question — which runs and which invariants survive merging? —
splits the subject into the same tiers as the data types:

  * **§1 Semilattice actions.** Every letter acts by joining a fixed lattice
    element, so a run *is* `Delta.joinAll` over the mapped input word, and
    order-, duplication- and batching-independence of runs are **instances** of
    the delta-shipping laws — one citation each, nothing reproved. This is the
    CALM / LVars class of machines.
  * **§2 Commuting actions.** No lattice at all: pairwise commutation of the
    action family already makes runs order-independent, and idempotence makes
    them duplication-independent. This is the seed of the Mazurkiewicz-trace /
    Zielonka asynchronous-automata connection; the section header says exactly
    what is (deliberately) not formalized.
  * **§3 The automaton as replicated data.** The transition table itself as a
    G-Set of `(state, letter, target)` triples: growth is free for monotone
    invariants, and ⚠ **DFA determinism is NOT I-confluent** — with the concrete
    two-replica clash and the priced exits (LWW-arbitrate the slot, or accept
    the NFA as the visible conflict surface).
  * **§4 Escrowed tokens.** The segmented budget of `Segmented.lean`, re-read
    as a Petri-net escrow: firing = local spend runs free within a token
    allocation; re-allocation is the coordination seam.

Literature:
  * Hellerstein, Alvaro — "Keeping CALM: When Distributed Consistency Is
    Easy", CACM 63(9), 2020. (Monotone ⇒ coordination-free; §1's class.)
  * Kuper, Newton — "LVars: Lattice-based Data Structures for Deterministic
    Parallelism", FHPC 2013. (Join-only writes to lattice variables; §1 again.)
  * Mazurkiewicz — "Concurrent Program Schemes and their Interpretations",
    DAIMI PB-78, Aarhus University, 1977. (Traces: words modulo commutation of
    independent letters.)
  * Zielonka — "Notes on Finite Asynchronous Automata", RAIRO Informatique
    Théorique et Applications 21(2), 1987. (Trace-closed languages are exactly
    those accepted by deadlock-free asynchronous automata.)
  * O'Neil — "The Escrow Transactional Method", ACM TODS 11(4), 1986. (§4's
    seam, in its original transactional clothes.)
-/
import Uwueave.Delta
import Uwueave.Segmented

namespace Uwueave.Automata

open Uwueave Uwueave.Catalog Uwueave.Delta Uwueave.Segmented

universe u v

/-! ## §1. Semilattice-action runs — the CALM / LVars class.

An automaton whose input letters act by joins is a delta-CRDT receiver wearing
automaton clothes: the letter `i` ships the delta `delta i`, and the run is the
receiver's fold. Consequently every convergence property a replicated automaton
could want is *already proved* in `Delta.lean`; this section only instantiates.
That inheritance — monotone/join-only steps need no coordination — is the CALM
theorem's easy direction and the LVars programming model, specialized to runs. -/

section SemilatticeRuns

variable {S : Type u} [MergeState S] {I : Type v}

/-- **A semilattice-action run**: the state reached from `base` by feeding the
input word `l`, where each letter `i` acts by `fun s => s ⊔ delta i`.
Definitionally this is `Delta.joinAll` over the mapped word — a replica running
its input stream IS a delta-CRDT receiver, with `delta i` the delta that letter
`i` ships. Machines of this shape are the CALM / LVars class (see the section
header), and every theorem below is a one-line instance of a `Delta.lean` law. -/
def run (delta : I → S) (base : S) (l : List I) : S :=
  Delta.joinAll base (l.map delta)

/-- The empty word does nothing (`rfl`, exposed for `simp`). -/
@[simp] theorem run_nil (delta : I → S) (base : S) : run delta base [] = base := rfl

/-- One letter steps the base by its join (`rfl`, exposed for `simp`). -/
@[simp] theorem run_cons (delta : I → S) (base : S) (i : I) (l : List I) :
    run delta base (i :: l) = run delta (base ⊔ delta i) l := rfl

/-- A run only moves *up* the lattice: the base is never forgotten. Instance of
`Delta.le_joinAll`. -/
theorem run_extends (delta : I → S) (base : S) (l : List I) :
    base ⊑ run delta base l :=
  Delta.le_joinAll base (l.map delta)

/-- **Order-independence of runs**: permuted input words produce the same
state, so replicas may consume their letters in whatever order the network
delivers them. Instance of `Delta.joinAll_perm`, pushed through `List.map`. -/
theorem run_perm (delta : I → S) {l l' : List I} (h : l.Perm l') (base : S) :
    run delta base l = run delta base l' :=
  Delta.joinAll_perm (h.map delta) base

/-- **Duplication-independence of runs**, adjacent form: feeding a letter twice
in a row is feeding it once. Instance of `Delta.joinAll_dup`. -/
theorem run_dup (delta : I → S) (base : S) (i : I) (l : List I) :
    run delta base (i :: i :: l) = run delta base (i :: l) :=
  Delta.joinAll_dup base (delta i) (l.map delta)

/-- **Duplication-independence of runs**, anywhere form: a letter the rest of
the word already contains adds nothing — at-least-once delivery of inputs is as
good as exactly-once. Instance of `Delta.joinAll_redeliver`. -/
theorem run_redeliver (delta : I → S) {i : I} {l : List I} (h : i ∈ l) (base : S) :
    run delta base (i :: l) = run delta base l :=
  Delta.joinAll_redeliver (List.mem_map.mpr ⟨i, h, rfl⟩) base

/-- **Batching-independence / state sync of runs**: running a concatenated word
equals running the two halves independently from the same base and merging the
resulting states — two replicas may each consume their own input stream and
converge by one state merge. Instance of `Delta.joinAll_append_merge`. -/
theorem run_append_merge (delta : I → S) (base : S) (l₁ l₂ : List I) :
    run delta base (l₁ ++ l₂) = run delta base l₁ ⊔ run delta base l₂ := by
  simp only [run, List.map_append]
  exact Delta.joinAll_append_merge base (l₁.map delta) (l₂.map delta)

/-- **The composite**: two input words with the same *set* of letters — any
order, any duplication, any multiplicity — produce the same state. This is the
automaton reading of strong eventual consistency's safety half: *which* letters
arrived decides the state; *how* they arrived cannot. Instance of
`Delta.same_deltas_same_state`, with the membership hypothesis pushed through
`List.mem_map`. -/
theorem run_same_inputs (delta : I → S) {l l' : List I}
    (h : ∀ i, i ∈ l ↔ i ∈ l') (base : S) :
    run delta base l = run delta base l' :=
  Delta.same_deltas_same_state
    (fun d => by
      simp only [List.mem_map]
      exact ⟨fun ⟨i, hi, hd⟩ => ⟨i, (h i).mp hi, hd⟩,
             fun ⟨i, hi, hd⟩ => ⟨i, (h i).mpr hi, hd⟩⟩)
    base

end SemilatticeRuns

/-! ## §2. The commuting-batch bridge — mini-Zielonka.

The lattice of §1 is sufficient for order-independent runs, not necessary. For
a completely general action family — no merge, no order, bare `S` — pairwise
commutation alone already yields permutation-independence, and idempotence
yields duplication-independence. Independence of letters is what licenses
coordination-free replicated runs.

This is the seed of the Mazurkiewicz-trace / Zielonka asynchronous-automata
connection, and only the seed. What is proved here is the degenerate trace
alphabet in which **all** pairs of letters are independent (a global
commutation hypothesis). Mazurkiewicz's trace theory proper — words modulo an
independence *relation* on a subset of pairs — and Zielonka's theorem
(trace-closed regular languages are exactly those accepted by asynchronous
automata, via his distributed construction) are NOT formalized here; they are
cited as literature in the file header. -/

section CommutingActions

variable {S : Type u} {I : Type v}

/-- **A general-action run**: fold each letter's action over the word, left to
right. No lattice structure is assumed anywhere in this section. -/
def exec (act : I → S → S) (base : S) (l : List I) : S :=
  l.foldl (fun s i => act i s) base

/-- The empty word does nothing (`rfl`, exposed for `simp`). -/
@[simp] theorem exec_nil (act : I → S → S) (base : S) : exec act base [] = base := rfl

/-- One letter acts on the base (`rfl`, exposed for `simp`). -/
@[simp] theorem exec_cons (act : I → S → S) (base : S) (i : I) (l : List I) :
    exec act base (i :: l) = exec act (act i base) l := rfl

/-- **The commuting-batch bridge.** If all pairs of letters commute, runs are
order-independent: permuted input words produce the same state. Induction on
the permutation derivation — `nil`/`cons` ride the fold, `swap` is one
application of the commutation hypothesis, `trans` composes. (Compare
`Delta.joinAll_perm`, which is this theorem with commutation supplied by the
merge laws — see `run_is_exec` below.) -/
theorem exec_perm (act : I → S → S)
    (hcomm : ∀ i j s, act i (act j s) = act j (act i s))
    {l l' : List I} (h : l.Perm l') (base : S) :
    exec act base l = exec act base l' := by
  induction h generalizing base with
  | nil => rfl
  | cons i _ ih => exact ih (act i base)
  | swap i j l =>
    show exec act (act i (act j base)) l = exec act (act j (act i base)) l
    rw [hcomm i j base]
  | trans _ _ ih₁ ih₂ => exact (ih₁ base).trans (ih₂ base)

/-- **The idempotent variant, adjacent form**: if every letter's action is
idempotent, feeding a letter twice in a row is feeding it once. -/
theorem exec_dup (act : I → S → S)
    (hidem : ∀ i s, act i (act i s) = act i s)
    (base : S) (i : I) (l : List I) :
    exec act base (i :: i :: l) = exec act base (i :: l) := by
  show exec act (act i (act i base)) l = exec act (act i base) l
  rw [hidem i base]

/-- **The idempotent variant, anywhere form**: with commutation to carry the
duplicate to its twin and idempotence to collapse them, a letter the rest of
the word already contains adds nothing. -/
theorem exec_redeliver (act : I → S → S)
    (hcomm : ∀ i j s, act i (act j s) = act j (act i s))
    (hidem : ∀ i s, act i (act i s) = act i s)
    {i : I} {l : List I} (h : i ∈ l) (base : S) :
    exec act base (i :: l) = exec act base l := by
  induction h generalizing base with
  | head l => exact exec_dup act hidem base i l
  | tail e _ ih =>
    simp only [exec_cons]
    rw [hcomm e i base]
    exact ih (act e base)

/-- A trailing letter the word already contains is absorbed: commute it to the
front (`exec_perm`), then collapse it (`exec_redeliver`). -/
theorem exec_absorb (act : I → S → S)
    (hcomm : ∀ i j s, act i (act j s) = act j (act i s))
    (hidem : ∀ i s, act i (act i s) = act i s)
    {i : I} {l : List I} (h : i ∈ l) (base : S) :
    exec act base (l ++ [i]) = exec act base l := by
  have hperm : (l ++ [i]).Perm (i :: l) := List.perm_append_comm
  exact (exec_perm act hcomm hperm base).trans (exec_redeliver act hcomm hidem h base)

/-- A whole appended word whose letters all already occur is absorbed, one
trailing letter at a time. -/
theorem exec_absorb_all (act : I → S → S)
    (hcomm : ∀ i j s, act i (act j s) = act j (act i s))
    (hidem : ∀ i s, act i (act i s) = act i s)
    (base : S) {l : List I} :
    ∀ {l' : List I}, (∀ i ∈ l, i ∈ l') → exec act base (l' ++ l) = exec act base l' := by
  induction l with
  | nil => intro l' _; rw [List.append_nil]
  | cons a t ih =>
    intro l' h
    rw [List.append_cons]
    rw [ih (l' := l' ++ [a])
        (fun i hi => List.mem_append.mpr (Or.inl (h i (List.Mem.tail a hi))))]
    exact exec_absorb act hcomm hidem (h a (List.Mem.head t)) base

/-- **The composite, no lattice required**: under commutation and idempotence,
two input words with the same *set* of letters — any order, any duplication,
any multiplicity — produce the same state. This is §1's `run_same_inputs`
(itself `Delta.same_deltas_same_state`) with the semilattice replaced by bare
algebraic hypotheses on the action family. -/
theorem exec_same_letters (act : I → S → S)
    (hcomm : ∀ i j s, act i (act j s) = act j (act i s))
    (hidem : ∀ i s, act i (act i s) = act i s)
    {l l' : List I} (h : ∀ i, i ∈ l ↔ i ∈ l') (base : S) :
    exec act base l = exec act base l' := by
  have h1 : exec act base (l ++ l') = exec act base l :=
    exec_absorb_all act hcomm hidem base (fun i hi => (h i).mpr hi)
  have h2 : exec act base (l' ++ l) = exec act base l' :=
    exec_absorb_all act hcomm hidem base (fun i hi => (h i).mp hi)
  have h3 : exec act base (l ++ l') = exec act base (l' ++ l) :=
    exec_perm act hcomm List.perm_append_comm base
  rw [← h1, h3, h2]

/-! §1 sits inside §2: a join action family is commuting and idempotent *by the
merge laws*, so the semilattice class is the special case of the commuting
class in which independence comes for free from the algebra of ⊔. -/

section LatticeIsCommuting

variable [MergeState S]

/-- Join actions commute — the `hcomm` hypothesis of this section, discharged
once from `merge_comm`/`merge_assoc` for the action family `fun i s => s ⊔ delta i`. -/
theorem join_action_comm (delta : I → S) (i j : I) (s : S) :
    (s ⊔ delta j) ⊔ delta i = (s ⊔ delta i) ⊔ delta j := by
  rw [merge_assoc, merge_comm (delta j) (delta i), ← merge_assoc]

/-- Join actions are idempotent — the `hidem` hypothesis of this section,
discharged once from `merge_assoc`/`merge_idem` for the same family. -/
theorem join_action_idem (delta : I → S) (i : I) (s : S) :
    (s ⊔ delta i) ⊔ delta i = s ⊔ delta i := by
  rw [merge_assoc, merge_idem]

/-- **§1 is a special case of §2**: a semilattice run is the general-action run
of the join family `fun i s => s ⊔ delta i`. With `join_action_comm` and
`join_action_idem`, every §2 theorem re-derives its §1 counterpart. -/
theorem run_is_exec (delta : I → S) (base : S) (l : List I) :
    run delta base l = exec (fun i s => s ⊔ delta i) base l := by
  induction l generalizing base with
  | nil => rfl
  | cons i t ih => exact ih (base ⊔ delta i)

end LatticeIsCommuting

end CommutingActions

/-! ## §3. The automaton as replicated data.

Now the *machine itself* is the replicated object: its transition table is a
grow-only set of `(state, letter, target)` triples, and two replicas sync by
table union. The G-Set machinery of `Catalog.lean` classifies the table's
invariants wholesale — and the classification is a dichotomy worth saying out
loud: **enabledness grows, determinism dies.** What survives replication is
exactly the NFA; the DFA is a coordination artifact. -/

section ReplicatedTable

/-- A replicated transition table: the grow-only set of
`(state, letter, target)` triples over `Nat`-coded states and letters. Adding a
transition is a G-Set insert; syncing two replicas is set union
(`Catalog.gset_mem_merge`). -/
abbrev Transitions : Type := GSet (Nat × Nat × Nat)

/-- A transition either replica has observed survives every merge. Instance of
`Catalog.gset_mem_iconfluent` at the triple alphabet — cited, not reproved. -/
theorem transition_present_iconfluent (e : Nat × Nat × Nat) :
    IConfluent (S := Transitions) (fun δ => δ e = true) :=
  Catalog.gset_mem_iconfluent e

/-- **Grow-only transition-addition is free for monotone invariants**: any
property of the table preserved under adding transitions is I-confluent.
Instance of `Catalog.gset_monotone_iconfluent` — cited, not reproved. -/
theorem transitions_monotone_iconfluent {P : Invariant Transitions}
    (hmono : ∀ δ δ' : Transitions, (∀ e, δ e = true → δ' e = true) → P δ → P δ') :
    IConfluent P :=
  Catalog.gset_monotone_iconfluent hmono

/-- "Letter `a` is enabled at state `q`" — some outgoing transition exists — is
monotone, hence I-confluent: enabledness only grows under sync. A concrete
instance of `transitions_monotone_iconfluent`. -/
theorem enabled_iconfluent (q a : Nat) :
    IConfluent (S := Transitions) (fun δ => ∃ t, δ (q, a, t) = true) :=
  transitions_monotone_iconfluent fun _ _ hsub ⟨t, ht⟩ => ⟨t, hsub (q, a, t) ht⟩

/-- **DFA determinism**: at most one target per `(state, letter)` slot. This is
the `gset_atMostOne_not_iconfluent` uniqueness shape, per slot — which is the
warning that it cannot be free. -/
def Deterministic : Invariant Transitions := fun δ =>
  ∀ q a t₁ t₂, δ (q, a, t₁) = true → δ (q, a, t₂) = true → t₁ = t₂

/-- ⚠ **DFA determinism is NOT I-confluent.** The concrete clash: two replicas
each add a different `a`-transition from the same state `q` — here
`Delta.addDelta (0, 0, 0)` and `Delta.addDelta (0, 0, 1)`: state `0`, letter
`0`, targets `0` versus `1`. Each one-transition table is vacuously
deterministic; their union holds both triples, and instantiating determinism at
the merged table would force `0 = 1`. A ceiling ("at most one target") on a
grow-only table escalates, exactly like `Catalog.gset_atMostOne_not_iconfluent`.

The exits, priced:
  * **Arbitrate the slot** — make each `(q, a)` slot an LWW register and let
    the later write win. Safe slot-by-slot (`Catalog.lww_every_invariant_iconfluent`),
    but ⚠ any invariant *relating two slots* (e.g. "the `a`-loop and the
    `b`-loop agree on a target") is then at risk of a merged interleaving
    neither replica ever had — `Catalog.lww_cross_field_not_iconfluent` is that
    trap, proved.
  * **Accept the NFA** — the merged table is the MV-register stance for
    automata: nondeterminism is the *visible conflict surface*, kept, not
    hidden. Determinize-at-read (the powerset construction) is then a derived
    view over the replicated table, on the pattern of `Move.derived_view_sec`
    (replicate the monotone log, derive the invariant-bearing view); the
    powerset construction itself is standard and not implemented here. -/
theorem determinism_not_iconfluent :
    ¬ IConfluent (S := Transitions) Deterministic := by
  intro h
  have hm := h (Delta.addDelta (0, 0, 0)) (Delta.addDelta (0, 0, 1))
    (fun q a t₁ t₂ h₁ h₂ => by simp [Delta.addDelta] at h₁ h₂; omega)
    (fun q a t₁ t₂ h₁ h₂ => by simp [Delta.addDelta] at h₁ h₂; omega)
  exact absurd (hm 0 0 0 1 (by decide) (by decide)) (by decide)

end ReplicatedTable

/-! ## §4. Escrowed tokens — the Petri-net reading of the segmented budget.

A Petri-net place holding `B` tokens, replicated across two sites, is exactly
the bounded resource `Catalog.pncounter_nonneg_not_iconfluent` says cannot be
free. The escrow reading splits the place into two *local* pools — a per-site
token allocation — and makes **firing a transition = spending from the local
pool**. Everything here is an instantiation or thin wrapper of the `Segmented`
/ `Catalog` escrow machinery (`Segmented.budget_segmented`,
`Catalog.escrow_local_bound_iconfluent`); the Petri vocabulary is the only new
content. Firings never coordinate; moving tokens *between* the pools —
re-allocation — is the seam. -/

section EscrowedTokens

/-- A two-site escrowed token pool: `Segmented.QuotaState` under its Petri
reading. First component: the per-site token allocation (the two local places).
Second component: the per-site consumed count (grow-only, merged by max). -/
abbrev TokenState : Type := Segmented.QuotaState

/-- Token safety at pool size `B`: `Segmented.BudgetInv B` under its Petri
reading — each site has consumed at most its allocation, and the allocation
sums to `B`. Together these bound total consumption by `B`
(`Catalog.escrow_global_bound` is that final summing step). -/
abbrev TokenInv (B : Nat) : Invariant TokenState := Segmented.BudgetInv B

/-- **Fire a transition at site `i`**: consume one token from `i`'s local pool
by bumping its consumed count. The allocation is untouched. -/
def fire (i : Bool) (s : TokenState) : TokenState :=
  (s.1, fun j => if j = i then s.2 j + 1 else s.2 j)

/-- Firing does not move the allocation — the segment projection `Prod.fst` is
fixed, so firings stay inside the fiber `budget_segmented` protects (`rfl`). -/
theorem fire_allocation (i : Bool) (s : TokenState) : (fire i s).1 = s.1 := rfl

/-- Firing consumes exactly one token at the firing site... -/
theorem fire_spends (i : Bool) (s : TokenState) : (fire i s).2 i = s.2 i + 1 := by
  simp [fire]

/-- ...and none at the other site. -/
theorem fire_frame (i j : Bool) (s : TokenState) (h : j ≠ i) :
    (fire i s).2 j = s.2 j := by
  simp [fire, h]

/-- **Local firing preserves token safety**: a site holding an unspent token
(`s.2 i < s.1 i`) may fire without consulting anyone and stay legal. This is
the "firing = local spend" half of the escrow reading. -/
theorem fire_preserves (B : Nat) (i : Bool) (s : TokenState)
    (hroom : s.2 i < s.1 i) (hs : TokenInv B s) : TokenInv B (fire i s) := by
  obtain ⟨⟨ht, hf⟩, hsum⟩ := hs
  cases i with
  | false =>
    refine ⟨⟨?_, ?_⟩, hsum⟩
    · show (if true = false then s.2 true + 1 else s.2 true) ≤ s.1 true
      simp
      omega
    · show (if false = false then s.2 false + 1 else s.2 false) ≤ s.1 false
      simp
      omega
  | true =>
    refine ⟨⟨?_, ?_⟩, hsum⟩
    · show (if true = true then s.2 true + 1 else s.2 true) ≤ s.1 true
      simp
      omega
    · show (if false = true then s.2 false + 1 else s.2 false) ≤ s.1 false
      simp
      omega

/-- **Firings within a fixed allocation are coordination-free**: token safety
is segmented over the allocation, so same-allocation replicas merge legally and
stay in the allocation fiber. Thin wrapper of `Segmented.budget_segmented`
under the Petri names — cited, not reproved. -/
theorem token_firings_segmented (B : Nat) :
    SegmentedIConfluent (S := TokenState) Prod.fst (TokenInv B) :=
  Segmented.budget_segmented B

/-- ⚠ **Re-allocation is the seam**: globally — allocation changes allowed —
token safety is not I-confluent; two legal allocations of the same 10-token
pool merge into an over-allocated one. Thin wrapper of
`Segmented.budget_not_iconfluent` under the Petri names — cited, not reproved.
Moving tokens between pools is where the coordination lives. -/
theorem token_reallocation_not_iconfluent : ¬ IConfluent (TokenInv 10) :=
  Segmented.budget_not_iconfluent

/-- **The Petri punchline, concretely**: from any legal state, two sites that
each hold an unspent token may fire *concurrently* — the merged marking is
still token-safe and the allocation has not moved. `fire_preserves` feeds
`token_firings_segmented`; no other ingredient. -/
theorem concurrent_firings_merge_legal (B : Nat) (i j : Bool) (s : TokenState)
    (hi : s.2 i < s.1 i) (hj : s.2 j < s.1 j) (hs : TokenInv B s) :
    TokenInv B (fire i s ⊔ fire j s) ∧ (fire i s ⊔ fire j s).1 = s.1 :=
  token_firings_segmented B (fire i s) (fire j s) rfl
    (fire_preserves B i s hi hs) (fire_preserves B j s hj hs)

end EscrowedTokens

end Uwueave.Automata
