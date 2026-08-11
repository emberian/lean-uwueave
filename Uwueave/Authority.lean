/-
# Uwueave.Authority — attenuation chains as a grounded causal CRDT.

Local-first *authority*: who may do what, decided without a server. The pieces
are ones this library has already priced, assembled into a capability system:

  * a **grant** `(id, parent, scope)` — "the holder of grant `parent` delegates
    authority `scope` to grant `id`". Grants form a DAG grounded by creation
    order (`parent < id`, the `Sequence.lean` discipline), rooted at the
    sentinel `parent = 0` — issued by the root authority, which holds
    `rootScope`. The replicated state is a grow-only `GSet Grant`.
  * a **revocation** — a grant id in a second grow-only set. Nothing is ever
    deleted; a revocation is monotone information, like fork evidence
    (`Causality.lean`).
  * the **authority anyone actually has** — a *derived view* (`Active`), the
    `Move.lean` pattern: replicate the monotone things, derive the
    invariant-bearing thing.

Three positive results and two refutations:

  1. `wf_iconfluent` — well-formedness (creation order + scope narrowing +
     parent presence) survives every merge: **delegation is coordination-free.**
     Grants can be issued offline, on a plane, in a partition; every sync of
     every schedule is again a well-formed grant DAG.
  2. `chain_scope_descends` + `scope_le_root` (packaged as
     `authority_only_narrows`) — **authority only narrows.** Scope is
     monotonically non-increasing along every delegation chain, and no grant's
     scope exceeds the root's — at every replica, after every merge, with no
     runtime check.
  3. `authority_view_antitone` + `active_monotone_grants` — **revocation is
     fail-closed.** Growing the revocation set never increases anyone's derived
     authority; growing the grant set never decreases it. The derived view's
     instability points only in the safe direction — the security dual of
     `Move.view_not_stable`; the duality is spelled out at
     `authority_view_antitone`.

  ⚠ `sole_admin_not_iconfluent` — "there is at most one root admin" is mutual
     exclusion (`Catalog.or_breaks_iconfluence` in authority clothes) and
     escalates: two partitions each mint their own admin and the merge holds
     both, though each replica was well-formed and sole-ruled.
  ⚠ `duelling_revocations_not_iconfluent` — concurrent revocations compose
     into a state neither admin intended: A revokes B while B revokes A, and
     the fail-closed merge annihilates *both* (`duelling_admins_annihilate`).
     This is the **Duelling Admins** problem of ERA (Dougal, PaPoC 2026); its
     epoch-batched external arbitration — picking a survivor — is exactly the
     coordination this refutation proves you must buy if you want one.

## What is a premise, not a theorem

  * **Grounding and uniqueness are realized cryptographically.** `parent < id`
    models "an issuer exists before what it issues"; in a content-addressed
    deployment `id = hash(parent, scope, …)`, so the ordering holds by
    construction and one id cannot bind two (parent, scope) pairs without a
    hash collision. Here the ordering is part of the invariant and per-id
    uniqueness is an explicit hypothesis (`UniqueGrant`) that the lattice does
    *not* preserve (`wf_unique_not_iconfluent`) — the same discipline as the
    rank remark in `Acyclicity.lean` and `UniqueAnchor` in `Sequence.lean`.
    No `InjectiveHash` typeclass will be added — a design decision: assuming
    injectivity of a finite-codomain hash mis-models collision resistance
    (finite hashes are not injective, by pigeonhole); the honest boundary is
    `UniqueGrant` ("this state exhibits no collision"), with
    `uniqueGrant_violation_extracts_collision` turning any violation into a
    constructive collision witness.
  * **Signatures.** That only `parent`'s holder can mint a grant naming that
    parent is authentication, outside this model entirely.

## Not modeled, honestly

  * **Epochs / arbitration** (ERA): no survivor policy for duelling admins —
    fail-closed kills both duellists, and this file proves that price rather
    than hiding it.
  * **Timed or temporary revocation**, un-revoke, re-grant after revocation.
  * **Structured scopes**: `scope : Nat` under `≤` is a totally-ordered
    miniature of a permission lattice (macaroon caveats and biscuit Datalog
    facts form posets); the proofs use only the order.

Lineage: macaroons (Birgisson et al., NDSS 2014 — HMAC-chained caveats: a
token anyone can *attenuate* and no one can amplify) · biscuits (Couprie —
offline attenuation with Datalog caveats and revocation ids; the design this
file miniaturizes) · the dregg through-line — "a turn is the exercise of an
attenuable proof-carrying token over owned state, leaving a receipt": this
file is that token's attenuation lattice, replicated · ERA (Kegan Dougal,
"ERA: Epoch-Resolved Arbitration for Duelling Admins in Group Management
CRDTs", PaPoC 2026, arXiv:2601.22963; PDF at
ERA, arXiv:2601.22963 — see `docs/BIBLIOGRAPHY.md`) · blocklace
(Almeida–Shapiro 2024 — the grounded hash-DAG substrate; `Acyclicity.lean`).
-/
import Uwueave.Catalog
import Uwueave.Tactics

namespace Uwueave.Authority

open Uwueave Uwueave.Catalog

/-! ## §1. Grants — a grounded delegation DAG, grow-only -/

/-- A grant `(id, parent, scope)`: the holder of grant `parent` delegates
authority `scope` to grant `id`. `parent = 0` is the root sentinel — the grant
was issued by the root authority directly. Creation order (`WF` forces
`parent < id`) structurally excludes `0` from ever being a grant id: a present
`(0, p, σ)` would need `p < 0`. -/
abbrev Grant := Nat × Nat × Nat

/-- The replicated state: the grow-only set of grants ever issued. The
`MergeState` instance is `GSet`'s — union, nothing new to prove. -/
abbrev GrantSet := GSet Grant

example : MergeState GrantSet := inferInstance

/-- Well-formedness relative to the root authority's scope `rootScope`. Every
present grant `(i, p, σ)` has `p < i` (creation order — an issuer is strictly
older than what it issues; rank = id, the grounded discipline of
`Acyclicity.lean`) and **narrows**: either it is root-parented with
`σ ≤ rootScope`, or some present grant carries its parent id and `σ` is at
most that grant's scope. The parent clause is existential — the shape of
`Sequence.WF`'s anchor clause — because the existential is what union
preserves; whether the witness is *unique* per id is deliberately a separate
hypothesis (`UniqueGrant` below). -/
def WF (rootScope : Nat) (s : GrantSet) : Prop :=
  ∀ i p σ : Nat, s (i, p, σ) = true →
    p < i ∧ ((p = 0 ∧ σ ≤ rootScope) ∨ ∃ q σ', s (p, q, σ') = true ∧ σ ≤ σ')

/-- **`WF rootScope` is I-confluent: delegation is coordination-free.** A
grant of the union came from one replica; its creation-order and narrowing
facts are per-element (the `grounded_iconfluent` argument), and its parent's
presence is monotone information, preserved by union (the
`gset_monotone_iconfluent` shape). So grants can be issued offline, in a
partition, on a plane — and every merge of well-formed replicas is a
well-formed grant DAG. This is the headline: attenuation-chain issuance never
needs a coordinator. -/
theorem wf_iconfluent (rootScope : Nat) :
    IConfluent (S := GrantSet) (WF rootScope) := by
  intro x y hx hy i p σ hmem
  cases (Bool.or_eq_true _ _).mp hmem with
  | inl h =>
    obtain ⟨hpi, hnarrow⟩ := hx i p σ h
    refine ⟨hpi, ?_⟩
    rcases hnarrow with hroot | ⟨q, σ', hq, hσ⟩
    · exact Or.inl hroot
    · refine Or.inr ⟨q, σ', ?_, hσ⟩
      show (x (p, q, σ') || y (p, q, σ')) = true
      simp [hq]
  | inr h =>
    obtain ⟨hpi, hnarrow⟩ := hy i p σ h
    refine ⟨hpi, ?_⟩
    rcases hnarrow with hroot | ⟨q, σ', hq, hσ⟩
    · exact Or.inl hroot
    · refine Or.inr ⟨q, σ', ?_, hσ⟩
      show (x (p, q, σ') || y (p, q, σ')) = true
      simp [hq]

/-! ## §2. Chains — authority only narrows -/

/-- A delegation chain, followed *upward*: `Chain s g a` means ancestor entry
`a` is reached from grant `g` by steps through present grants, each step
moving to an entry whose id is the current entry's parent id. Both ends and
every intermediate entry are present in `s`. -/
inductive Chain (s : GrantSet) : Grant → Grant → Prop where
  | delegates {i p σ q σ' : Nat} :
      s (i, p, σ) = true → s (p, q, σ') = true → Chain s (i, p, σ) (p, q, σ')
  | step {g : Grant} {i p σ q σ' : Nat} :
      Chain s g (i, p, σ) → s (p, q, σ') = true → Chain s g (p, q, σ')

/-- The ancestor end of a chain is a present grant. -/
theorem Chain.head_present {s : GrantSet} {g a : Grant} (hc : Chain s g a) :
    s a = true := by
  cases hc with
  | delegates _ hp => exact hp
  | step _ hp => exact hp

/-- Ids strictly decrease along every chain — the delegation DAG is grounded
with rank = id (`Acyclicity.reaches_rank_lt`, transplanted): an ancestor is
strictly older than every grant it transitively issued. `WF` only. -/
theorem chain_id_descends {rootScope : Nat} {s : GrantSet}
    (hwf : WF rootScope s) {g a : Grant} (hc : Chain s g a) : a.1 < g.1 := by
  induction hc with
  | delegates hg _ => exact (hwf _ _ _ hg).1
  | step hc' _ ih => exact Nat.lt_trans (hwf _ _ _ hc'.head_present).1 ih

/-- No grant is its own ancestor: delegation cycles are impossible on a
well-formed state — `grounded_acyclic` in authority clothes, and like it, free
at every merge because `WF` is I-confluent. -/
theorem chain_irrefl {rootScope : Nat} {s : GrantSet}
    (hwf : WF rootScope s) (g : Grant) : ¬ Chain s g g :=
  fun hc => Nat.lt_irrefl g.1 (chain_id_descends hwf hc)

/-- **Corollary of narrowing (general, `WF` only): no grant's scope exceeds
the root's.** Follow the parent witnesses upward; each hop is bounded by the
next scope, the walk strictly descends in id, and it bottoms out at the
sentinel where `σ ≤ rootScope` is direct. However long the delegation chain
and however adversarial the merge schedule, nobody manufactures authority. -/
theorem scope_le_root {rootScope : Nat} {s : GrantSet} (hwf : WF rootScope s)
    (i p σ : Nat) (h : s (i, p, σ) = true) : σ ≤ rootScope := by
  obtain ⟨hpi, hnarrow⟩ := hwf i p σ h
  rcases hnarrow with ⟨-, hσ⟩ | ⟨q, σ', hq, hσ⟩
  · exact hσ
  · exact Nat.le_trans hσ (scope_le_root hwf p q σ' hq)
termination_by i
decreasing_by omega

/-- No id is granted twice (with a different parent or scope). The chain
theorems below need this to pin *which* parent entry a chain step means; the
lattice cannot enforce it (`wf_unique_not_iconfluent`), and a
content-addressed id scheme — `id = hash(parent, scope, …)` — supplies it
cryptographically, one id binding two preimages only via a hash collision.
Same status as `Sequence.UniqueAnchor`: a real hypothesis, an external
discharge. -/
def UniqueGrant (s : GrantSet) : Prop :=
  ∀ i p σ p' σ' : Nat, s (i, p, σ) = true → s (i, p', σ') = true →
    p = p' ∧ σ = σ'

/-- One delegation step narrows: a grant's scope is at most the scope of any
present grant carrying its parent id (`UniqueGrant` makes that entry the
issuer `WF` witnessed). -/
theorem delegation_narrows {rootScope : Nat} {s : GrantSet}
    (hwf : WF rootScope s) (huniq : UniqueGrant s) {i p σ q σ' : Nat}
    (hchild : s (i, p, σ) = true) (hparent : s (p, q, σ') = true) : σ ≤ σ' := by
  obtain ⟨hpi, hnarrow⟩ := hwf i p σ hchild
  rcases hnarrow with ⟨rfl, -⟩ | ⟨q₀, σ₀, hq₀, hσ⟩
  · exact absurd (hwf 0 q σ' hparent).1 (Nat.not_lt_zero q)
  · obtain ⟨-, rfl⟩ := huniq p q₀ σ₀ q σ' hq₀ hparent
    exact hσ

/-- **"Authority only narrows", the general chain form: scope is monotonically
non-increasing along every delegation chain.** Stated under `WF` plus
`UniqueGrant` — the uniqueness is honest load-bearing: without it a chain may
route through a same-id sibling entry that `WF`'s existential never blessed
(see `wf_unique_not_iconfluent` for why the model cannot rule that out, and
the header for the cryptographic premise that does). Induction along the
chain, `Acyclicity.reaches_rank_lt` style. -/
theorem chain_scope_descends {rootScope : Nat} {s : GrantSet}
    (hwf : WF rootScope s) (huniq : UniqueGrant s) {g a : Grant}
    (hc : Chain s g a) : g.2.2 ≤ a.2.2 := by
  induction hc with
  | delegates hg hp => exact delegation_narrows hwf huniq hg hp
  | step hc' hp ih =>
    exact Nat.le_trans ih (delegation_narrows hwf huniq hc'.head_present hp)

/-- Replica A of the duplication pair: a root grant and a delegation under
it. -/
def dupA : GrantSet :=
  fun g => g == ((1 : Nat), (0 : Nat), (5 : Nat))
        || g == ((2 : Nat), (1 : Nat), (3 : Nat))

/-- Replica B of the duplication pair: the *same id* `2` granted from the
root with a different scope. Under content addressing this state pair is
precisely a hash-collision exhibit (one id, two distinct (parent, scope)
preimages); the model permits it. -/
def dupB : GrantSet := fun g => g == ((2 : Nat), (0 : Nat), (4 : Nat))

theorem dupA_wf : WF 9 dupA := by
  intro i p σ h
  simp [dupA] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨by omega, Or.inl ⟨rfl, by omega⟩⟩
  · exact ⟨by omega, Or.inr ⟨0, 5, by decide, by omega⟩⟩

theorem dupB_wf : WF 9 dupB := by
  intro i p σ h
  simp [dupB] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨by omega, Or.inl ⟨rfl, by omega⟩⟩

theorem dupA_unique : UniqueGrant dupA := by
  intro i p σ p' σ' h h'
  simp [dupA] at h h'
  omega

theorem dupB_unique : UniqueGrant dupB := by
  intro i p σ p' σ' h h'
  simp [dupB] at h h'
  omega

/-- ⚠ **`WF ∧ UniqueGrant` is NOT I-confluent.** `dupA` and `dupB` each
satisfy both; their union holds `(2, 1, 3)` and `(2, 0, 4)` — one id, two
grants. This is why `chain_scope_descends` carries `UniqueGrant` as a
hypothesis rather than deriving it from `WF`: within the model the hypothesis
is real, and only a content-addressed id scheme discharges it globally.
Compare `Sequence.wf_unique_anchor_not_iconfluent` — the same ceiling
invariant, there in sequence clothing, here in authority clothing. -/
theorem wf_unique_not_iconfluent :
    ¬ IConfluent (S := GrantSet) (fun s => WF 9 s ∧ UniqueGrant s) := by
  intro h
  obtain ⟨-, huniq⟩ := h dupA dupB ⟨dupA_wf, dupA_unique⟩ ⟨dupB_wf, dupB_unique⟩
  exact absurd (huniq 2 1 3 0 4 (by decide) (by decide)).1 (by decide)

/-- **The collision extractor — the CR-reduction reading of `UniqueGrant`.**
A state violating `UniqueGrant` *constructs* two distinct (parent, scope)
payloads sharing one grant id — when ids are content-derived
(`id = hash(parent, scope, …)`), that is two distinct preimages under one
digest: exactly the adversary's output in the collision-resistance game.

Read at the model boundary: the premise `UniqueGrant s` is **not** "the hash
is injective" — false of every finite-codomain hash, by pigeonhole, so a model
assuming it would assume nonsense — it is "this state exhibits no collision",
and this lemma is the standard computational-CR handoff: any violation is a
constructive collision witness, so an adversary that reaches a violating state
*is* a collision-finder. A deployment discharges the premise computationally —
collision resistance of the hash plus the polynomial bound on how many grants
any execution ever constructs. Compare
`Sequence.uniqueAnchor_violation_extracts_collision` — the same handoff, one
costume over. (Classical unpack of `¬∀`, the `escalation_witness` recipe.) -/
theorem uniqueGrant_violation_extracts_collision {s : GrantSet}
    (h : ¬ UniqueGrant s) :
    ∃ i p σ p' σ' : Nat, (p, σ) ≠ (p', σ')
      ∧ s (i, p, σ) = true ∧ s (i, p', σ') = true := by
  apply Classical.byContradiction
  intro hcon
  apply h
  intro i p σ p' σ' hg hg'
  apply Classical.byContradiction
  intro hne
  exact hcon ⟨i, p, σ, p', σ',
    fun hpair => hne ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩,
    hg, hg'⟩

/-- **The verdict, packaged** (`causal_dag_free`'s shape): issuing attenuated
grants is coordination-free, and every reachable state — every replica, every
merge of every partition schedule — keeps all authority below the root's. The
free, per-element invariant buys the global bound. -/
theorem authority_only_narrows (rootScope : Nat) :
    IConfluent (S := GrantSet) (WF rootScope)
    ∧ ∀ s : GrantSet, WF rootScope s →
        ∀ i p σ : Nat, s (i, p, σ) = true → σ ≤ rootScope :=
  ⟨wf_iconfluent rootScope, fun _ hwf i p σ h => scope_le_root hwf i p σ h⟩

/-! ## §3. The sole admin — mutual exclusion in authority clothes -/

/-- At most one root-parented grant: "there is one admin, appointed by the
root". The bounded-uniqueness shape of `Catalog.gset_atMostOne_not_iconfluent`,
over grants. -/
def SoleAdmin (s : GrantSet) : Prop :=
  ∀ i σ i' σ' : Nat, s (i, 0, σ) = true → s (i', 0, σ') = true → i = i'

/-- Alice's partition mints Alice's admin grant (id 1, full scope). -/
def aliceRoot : GrantSet := fun g => g == ((1 : Nat), (0 : Nat), (9 : Nat))

/-- Bob's partition mints Bob's admin grant (id 2, full scope). -/
def bobRoot : GrantSet := fun g => g == ((2 : Nat), (0 : Nat), (9 : Nat))

theorem aliceRoot_wf : WF 9 aliceRoot := by
  intro i p σ h
  simp [aliceRoot] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨by omega, Or.inl ⟨rfl, by omega⟩⟩

theorem bobRoot_wf : WF 9 bobRoot := by
  intro i p σ h
  simp [bobRoot] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨by omega, Or.inl ⟨rfl, by omega⟩⟩

theorem aliceRoot_sole : SoleAdmin aliceRoot := by
  intro i σ i' σ' h h'
  simp [aliceRoot] at h h'
  omega

theorem bobRoot_sole : SoleAdmin bobRoot := by
  intro i σ i' σ' h h'
  simp [bobRoot] at h h'
  omega

/-- ⚠ **Sole-admin is NOT I-confluent — the duelling-admins clash, entry
side.** Each partition is well-formed and sole-ruled; the merge holds two
admins. Mutual exclusion over grow-only grants is
`Catalog.or_breaks_iconfluence` / `gset_atMostOne_not_iconfluent` again; per
Bailis et al.'s necessity theorem (cited, not re-proved here — what Lean shows
is the clash) no library feature fixes it: electing *the* admin
escalates to coordination, arbitration (ERA's epochs — Dougal, PaPoC 2026 —
are exactly an arbitration policy for this), or compensation. The refutation
pair is the scenario a group-management design must pick a policy for. -/
theorem sole_admin_not_iconfluent :
    ¬ IConfluent (S := GrantSet) (fun s => WF 9 s ∧ SoleAdmin s) := by
  intro h
  obtain ⟨-, hsole⟩ :=
    h aliceRoot bobRoot ⟨aliceRoot_wf, aliceRoot_sole⟩ ⟨bobRoot_wf, bobRoot_sole⟩
  exact absurd (hsole 1 9 2 9 (by decide) (by decide)) (by decide)

/-! ## §4. Revocation, fail-closed — the derived authority view -/

/-- The revocation set: grant ids revoked, grow-only. Merge is union — a
revocation, once issued anywhere, reaches everywhere and never leaves. -/
abbrev Revoked := GSet Nat

example : MergeState Revoked := inferInstance

/-- **Revocation is forever at the state level**: "id `i` is revoked" is
I-confluent — it is `gset_mem_iconfluent` instantiated, not restated, the
fork-evidence pattern (`Causality.fork_evidence_iconfluent`): evidence never
un-happens. The view-level counterpart is `revocation_is_forever` below. -/
theorem revocation_iconfluent (i : Nat) :
    IConfluent (S := Revoked) (fun r => r i = true) :=
  gset_mem_iconfluent i

/-- The derived view: grant `g` is **active** when some chain of present
grants runs from `g` to the root sentinel and no grant on it — `g` included —
is revoked. This is the structural half of authority ("a live, unrevoked
delegation path exists"); the scope half comes from `WF` outside the view
(`active_scope_le_root`). Like every derived view in this library it is a
predicate of the replicated state, recomputed, never itself replicated. -/
inductive Active (s : GrantSet) (r : Revoked) : Grant → Prop where
  | root {i σ : Nat} :
      s (i, 0, σ) = true → r i = false → Active s r (i, 0, σ)
  | step {i p σ q σ' : Nat} :
      s (i, p, σ) = true → r i = false → Active s r (p, q, σ') →
      Active s r (i, p, σ)

/-- An active grant is present. -/
theorem active_present {s : GrantSet} {r : Revoked} {g : Grant}
    (h : Active s r g) : s g = true := by
  cases h with
  | root hs _ => exact hs
  | step hs _ _ => exact hs

/-- An active grant is not itself revoked. -/
theorem active_head_unrevoked {s : GrantSet} {r : Revoked} {g : Grant}
    (h : Active s r g) : r g.1 = false := by
  cases h with
  | root _ hr => exact hr
  | step _ hr _ => exact hr

/-- An active grant is root-parented or has an active parent entry. -/
theorem active_parent {s : GrantSet} {r : Revoked} {g : Grant}
    (h : Active s r g) : g.2.1 = 0 ∨ ∃ q σ', Active s r (g.2.1, q, σ') := by
  cases h with
  | root _ _ => exact Or.inl rfl
  | step _ _ hpar => exact Or.inr ⟨_, _, hpar⟩

/-- **The centerpiece: growing the revocation set never increases anyone's
authority.** If `r ⊆ r'`, everything active under `r'` was already active
under `r`: new revocations only remove; they cannot create authority,
resurrect it, or conjure a delegation path. With `active_monotone_grants`
this pins the derived view's instability to one direction — grants only add,
revocations only subtract.

This is the security dual of `Move.view_not_stable`. There, a grown log
un-happening a move the user watched is the op-log pattern's *price* — a UX
anomaly to design around. Here the same lattice fact — a monotone substrate
whose derived view is not stable under growth — is the *product*: a
revocation issued offline arrives late and retroactively de-authorizes, which
is precisely what fail-closed means. One theorem shape, opposite valence;
which one you are holding depends on whether the unstable view is a document
or a permission. -/
theorem authority_view_antitone {s : GrantSet} {r r' : Revoked}
    (hgrow : ∀ i, r i = true → r' i = true) {g : Grant}
    (h : Active s r' g) : Active s r g := by
  have still : ∀ i : Nat, r' i = false → r i = false := by
    intro i h'
    cases hri : r i with
    | false => rfl
    | true => exact absurd (hgrow i hri) (by simp [h'])
  induction h with
  | root hs hr => exact Active.root hs (still _ hr)
  | step hs hr _ ih => exact Active.step hs (still _ hr) ih

/-- **Revocation is forever at the view level**: a grant dead under `r` stays
dead under every larger revocation set — the fail-closed contrapositive of
`authority_view_antitone`, and the view-level reading of
`revocation_iconfluent`. -/
theorem revocation_is_forever {s : GrantSet} {r r' : Revoked}
    (hgrow : ∀ i, r i = true → r' i = true) {g : Grant}
    (hdead : ¬ Active s r g) : ¬ Active s r' g :=
  fun h => hdead (authority_view_antitone hgrow h)

/-- `authority_view_antitone` at an actual merge: over a fixed grant set,
anything active after syncing in a peer's revocations was active before —
**sync can only revoke, never resurrect**. (The grant component moves the
other way, by `active_monotone_grants`; a full-state sync therefore changes
the view only by adding newly delegated authority and deleting newly revoked
authority, never the reverse of either.) -/
theorem merge_only_revokes {s : GrantSet} (r r' : Revoked) {g : Grant}
    (h : Active s (r ⊔ r') g) : Active s r g :=
  authority_view_antitone
    (fun i hi => by show (r i || r' i) = true; simp [hi]) h

/-- Growing the grant set never deactivates anyone: the positive direction of
the view, monotone as delegation should be. -/
theorem active_monotone_grants {s s' : GrantSet}
    (hgrow : ∀ g : Grant, s g = true → s' g = true) {r : Revoked} {g : Grant}
    (h : Active s r g) : Active s' r g := by
  induction h with
  | root hs hr => exact Active.root (hgrow _ hs) hr
  | step hs hr _ ih => exact Active.step (hgrow _ hs) hr ih

/-- On a well-formed state, active authority is bounded by the root's scope —
§2's bound surfaced at the view: `Active` needs presence
(`active_present`), and presence needs `σ ≤ rootScope` (`scope_le_root`). -/
theorem active_scope_le_root {rootScope : Nat} {s : GrantSet} {r : Revoked}
    (hwf : WF rootScope s) {g : Grant} (h : Active s r g) :
    g.2.2 ≤ rootScope :=
  scope_le_root hwf g.1 g.2.1 g.2.2 (active_present h)

/-- A two-link demonstration state: the root appoints grant 1 (scope 9),
whose holder delegates grant 2 (scope 4). -/
def demoChain : GrantSet :=
  fun g => g == ((1 : Nat), (0 : Nat), (9 : Nat))
        || g == ((2 : Nat), (1 : Nat), (4 : Nat))

theorem demoChain_wf : WF 9 demoChain := by
  intro i p σ h
  simp [demoChain] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact ⟨by omega, Or.inl ⟨rfl, by omega⟩⟩
  · exact ⟨by omega, Or.inr ⟨0, 9, by decide, by omega⟩⟩

example : Chain demoChain (2, 1, 4) (1, 0, 9) :=
  .delegates (by decide) (by decide)

/-- The empty revocation set. -/
def noRevs : Revoked := fun _ => false

/-- Revoke grant 1 — the *issuer*, not the delegate. -/
def revokeIssuer : Revoked := fun i => i == 1

/-- With nothing revoked, the delegate's grant is active — `Active` is
inhabited; the antitone theorems above are about a view with something in
it. -/
theorem demo_delegate_active : Active demoChain noRevs (2, 1, 4) :=
  .step (by decide) rfl (.root (σ := 9) (by decide) rfl)

/-- **Revocation cascades down the chain, fail-closed**: revoking the issuer
(id 1) kills the delegate (id 2) even though id 2 itself is unrevoked — its
only path to the root passes through a revoked grant. The whole subtree under
a revoked grant dies; this is the macaroon/biscuit semantics (a token is
worthless once any link of its chain is), deliberately. -/
theorem demo_cascade_revoked : ¬ Active demoChain revokeIssuer (2, 1, 4) := by
  intro h
  rcases active_parent h with h0 | ⟨q, σ', hpar⟩
  · exact absurd h0 (by decide)
  · have hu := active_head_unrevoked hpar
    simp [revokeIssuer] at hu

/-! ## §5. Duelling admins — what fail-closed does to a duel, and what it
costs. ERA (Dougal, PaPoC 2026) is the literature circling exactly this:
concurrent revocations between equally-permissioned admins have no
coordination-free resolution that keeps a survivor, and a Byzantine admin can
exploit the concurrency; ERA buys a survivor with an external epoch-batching
arbiter. This file takes the other branch of the fork — fail closed, no
survivor — and proves both what that buys (`authority_view_antitone`) and
what it costs (below). -/

/-- Alice's replica: revoke Bob's admin grant (id 2). -/
def aliceRevokesBob : Revoked := fun i => i == 2

/-- Bob's replica: revoke Alice's admin grant (id 1). -/
def bobRevokesAlice : Revoked := fun i => i == 1

/-- ⚠ **"Some admin survives" is NOT I-confluent — the duelling-admins clash,
revocation side.** On Alice's replica Bob is revoked and Alice stands; on
Bob's, the reverse; each replica satisfies "admin 1 or admin 2 is unrevoked".
The merged revocation set holds both, and satisfies neither disjunct —
`Catalog.or_breaks_iconfluence`'s disjunction trap, with revocations as the
lock. Keeping a survivor requires exactly the coordination ERA introduces
(epoch-resolved arbitration); coordination-free, the duel annihilates. -/
theorem duelling_revocations_not_iconfluent :
    ¬ IConfluent (S := Revoked) (fun r => r 1 = false ∨ r 2 = false) := by
  classify

/-- The duel, played out on the derived view: merge the two admins' grants
and the two revocations, and **neither admin is active** — fail-closed
resolves the duel by killing both duellists. Authority can be rebuilt only by
whoever holds the root (a key, in a deployment — the custody question this
model states as premise). That is a defensible policy and a real price; ERA
exists because some systems want a survivor instead. -/
theorem duelling_admins_annihilate :
    ¬ Active (aliceRoot ⊔ bobRoot) (aliceRevokesBob ⊔ bobRevokesAlice) (1, 0, 9)
    ∧ ¬ Active (aliceRoot ⊔ bobRoot) (aliceRevokesBob ⊔ bobRevokesAlice) (2, 0, 9) :=
  ⟨fun h => absurd (active_head_unrevoked h) (by decide),
   fun h => absurd (active_head_unrevoked h) (by decide)⟩

end Uwueave.Authority
