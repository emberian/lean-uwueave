/-
# Uwueave.Cost — how *often* must I coordinate? The frequency, as a quantity.

Every judgement in this library so far is **binary** (`IConfluent`: free, or
escalates) or **seam-shaped** (`SegmentedIConfluent`: free within a fiber of
`σ`, coordinate to cross). Neither answers the question an engineer actually
asks about a workload: *how many times*. `FORCODEX.md` §5.4 poses it as
possibly not existing anywhere —

  > "anything about *cost models* for coordination (everything we have is
  > binary or seam-shaped; nobody seems to have 'how often must I coordinate,
  > given this workload?' as a formal quantity — is that real?)"

— and this file answers: **yes, and here it is, with a lower bound.**

## The quantity

A workload is a finite op stream `w : List Op` over a transition
`step : S → Op → S`. Given a seam `σ : S → Seg`,

    crossings σ step s w  :  Nat

counts the steps along the run of `w` from `s` at which `σ` **changes value**.
Operationally that is exactly the number of coordination events the workload
forces on a replica running it: inside a fiber of `σ` every merge is safe
(`SegmentedIConfluent`), so the only thing a replica must stop and agree about
is leaving the fiber.

## The theorem that makes it more than bookkeeping — §3

`crossings` depends on `σ`, and `σ` is an implementation choice. The result
worth having is the one that does **not**:

    coordination_lower_bound :
      SegmentedIConfluent σ I → ClashBlocks I step s bs →
        bs.length ≤ crossings σ step s bs.flatten

`ClashBlocks I step s bs` chops the stream into blocks whose two endpoints are
each legal but whose **merge is not** — a clash, in the exact sense of
`Confluence.escalation_witness`. The conclusion holds **for every seam `σ` in
every universe** (`coordination_forced`), so the count is forced by the
*specification* — by which states the workload must legally pass through — and
no cleverness in choosing `σ` can beat it. A clash pair is the only thing that
can force two states into different fibers, and it forces it for all `σ` at
once; that is the whole mechanism, and it is why the bound is universal.

The bound is not merely a bound: §6 exhibits a workload where it is **exactly
achieved**. Three re-divisions of a shared budget of 10 cost *three*
coordination events — at least three under every possible segmentation, and
exactly three under the allocation seam. That pair (`budget_cost_is_three`) is
a complete answer to "how often must I coordinate, given this workload?" for
one real workload.

## What landed, section by section

  * **§1–2** the quantity, `run`/`crossings`, its range (`crossings_le_length`:
    at most one crossing per op, so cost lives in `[0, w.length]` and both ends
    are realised below), and the block calculus.
  * **§3** the lower bound (`coordination_lower_bound`, `coordination_forced`).
  * **§4** *monotone segments cost zero*, in both halves: a stream of ops that
    never move `σ` costs 0 (`crossings_eq_zero_of_segmentFree`), and — the
    half that needs `SegmentedIConfluent` — **every interleaving** of two
    replicas running such ops, with syncs at arbitrary points, stays legal and
    stays in the fiber (`interleaving_stays_in_fiber`). Genuinely quantified
    over schedules: the theorem is `∀ sch : List (Event Op)`.
  * **§5** the calibration, and it is the reassuring one: an **inflationary**
    workload (every op an inflation — the CALM/monotone fragment) admits *no*
    clash blocks at all, so the floor it forces is 0
    (`clashBlocks_nil_of_inflationary`). The lower bound bites exactly where
    ops overwrite, which is exactly where the field says coordination lives.
    Both sides of that line are exhibited: `reallocStep_not_inflationary` (the
    op that costs) and `pinStep_inflationary` (the op that cannot).
  * **§6** the budget instance: floor 3, achieved 3. **Tight.**
  * **§7** `SeamAlgebra.linked_segmented`'s saving as a crossing count — and a
    correction to the naive reading of it (below).
  * **§8** amortization, as far as it goes: batching a block into one op takes
    both the floor and the achieved count from 3 to 1
    (`batched_cost_is_one`), because the intermediate allocations stop being
    states anyone occupies.
  * **§9** the honest scope: a two-replica workload where the measure
    **undercounts** (below).

## ⚠ Two findings that correct things this repo already believed

**(i) The link does not lower the floor.** `SeamAlgebra` §7's punchline is that
linking the schema version to the allocation collapses two coordination points
into one. Counted: the same behaviour costs **4** crossings on the unlinked
document under its canonical pair seam and **2** on the linked document under
the version seam (`linked_halves_the_crossings`). But the *forced floor* is
**2 for both** (`unlinked_floor_is_two`, `linked_floor_is_two`). So the link's
saving is real but it is a saving against the *obvious* seam: it makes the
obvious seam optimal, rather than making the document cheaper than it was.
⟨UNDONE⟩ whether 4 is optimal for the unlinked document — a seam reading
"does anyone hold a soon-to-be-illegal record" plausibly reaches 2 there, and
we did not prove it valid.

**(ii) `crossings` is per-stream, and seams are chosen globally — so it
undercounts a concurrent workload.** §9 exhibits it: on the uniqueness ceiling
over `GSet Bool`, the stream `[true]` is free under one valid seam, the stream
`[false]` is free under another, and **no single valid seam frees both**
(`no_seam_frees_both`). Each per-stream count is 0; the workload's true cost is
not. This is not a repairable defect of the definition — it is its domain of
validity, and we state it as scope:

  ⟨TERMINAL for this file⟩ `crossings σ step s w` measures **one stream against
  one already-chosen seam**. The workload-level quantity is a min over valid
  seams of some aggregate over concurrent streams; this file does not define
  that aggregate, and the per-stream minimum is a strict under-estimate of it.

## Non-claims, labelled

  * ⟨UNDONE⟩ **Crossings are not meetings.** A "coordination event" here is a
    seam crossing on one replica's stream. How many peers must attend, and
    whether two replicas crossing "the same" boundary hold one meeting or two,
    is not modelled. §8's batching result is the only amortization proved, and
    it amortizes by *re-blocking the workload*, not by agreeing in advance.
  * ⟨UNDONE⟩ **No liveness, no delivery, no time.** `crossings` counts events,
    never wall-clock; `Liveness.lean`/`Delta.lean` own that axis and are not
    composed with this one.
  * ⟨UNDONE⟩ **`crossings = 0` on a run is weaker than `SegmentFree`.** The
    interleaving theorem (§4) needs the op-level property, which quantifies
    over all legal states; a single run's zero count does not imply it. The
    bridge runs one way only (`crossings_eq_zero_of_segmentFree`).
  * ⟨scope⟩ **`[DecidableEq Seg]`.** `crossings` branches on whether `σ`
    changed, so seams are quantified over *with decidable equality*. Every
    "for every seam" statement below carries that binder. It is not vacuous
    (`Nat`, `Bool`, `Nat × Nat` seams all appear) and it is not free: a seam
    whose codomain is a `Prop`-valued classification is outside the ∀.
  * ⟨scope⟩ Two replicas in §4. The interleaving theorem is stated for a pair;
    nothing here treats N replicas.

## Literature checked — and no exhaustive search is claimed

  * **Whittaker–Hellerstein**, *Interactive Checks for Coordination Avoidance*
    (VLDB'19) — the source of the segmented judgement this file counts. Its
    checks are **per-transaction**: a transaction either passes the interactive
    check or escalates. That is a predicate on each op, not a quantity over a
    stream; the number of checks a *workload* forces is not an object there.
  * **CALM / Bailis et al.** — monotone ⇒ coordination-free is binary by
    construction. §5 is the point of contact: the CALM fragment is exactly the
    fragment on which this file's floor is 0.
  * **ERA** (Dougal, PaPoC'26) — batches arbitration into epochs, which is a
    frequency *mechanism*; the paper prices trust and rollback, not a count
    forced by a workload.
  * **Sal** (Ramesh et al., arXiv 2603.27202) — verifies merge implementations
    against RA-linearizability. Different axis entirely.

We have **not** searched the distributed-systems cost-model literature
exhaustively, and we would not be surprised to be told this quantity exists
under another name (a "coordination complexity", a communication-complexity
lower bound for a replicated object). What we did not find is it stated over
*this* judgement — as a bound forced by segmented I-confluence, universal in
the seam. If it exists, we want the citation.
-/
import Uwueave.SeamAlgebra

namespace Uwueave.Cost

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.Seams Uwueave.SeamAlgebra

universe u v w

/-! ## §1. The quantity — workloads, runs, crossings -/

/-- The state a replica reaches by applying the op stream `w` to `s`, in order.
`step` is the *local* transition: what one op does on one replica. It is
deliberately **not** required to be an inflation — §5 is about exactly that
distinction. -/
def run {S : Type u} {Op : Type w} (step : S → Op → S) (s : S) : List Op → S
  | [] => s
  | o :: w => run step (step s o) w

/-- Running a concatenation is running the halves in sequence. -/
theorem run_append {S : Type u} {Op : Type w} (step : S → Op → S) (s : S)
    (w₁ w₂ : List Op) : run step s (w₁ ++ w₂) = run step (run step s w₁) w₂ := by
  induction w₁ generalizing s with
  | nil => rfl
  | cons o w ih => exact ih (step s o)

/-- **The quantity.** `crossings σ step s w` is the number of ops along the run
of `w` from `s` at which the seam value `σ` changes — the number of times the
replica must leave the fiber it was running free inside, i.e. the number of
coordination events the workload forces on it. -/
def crossings {S : Type u} {Seg : Type v} {Op : Type w} [DecidableEq Seg]
    (σ : S → Seg) (step : S → Op → S) (s : S) : List Op → Nat
  | [] => 0
  | o :: w => (if σ (step s o) = σ s then 0 else 1) + crossings σ step (step s o) w

/-- The empty workload costs nothing. -/
@[simp] theorem crossings_nil {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] (σ : S → Seg) (step : S → Op → S) (s : S) :
    crossings σ step s ([] : List Op) = 0 := rfl

/-- Cost is additive along concatenation: what the second half costs is
measured from the state the first half left behind. -/
theorem crossings_append {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] (σ : S → Seg) (step : S → Op → S) (s : S) (w₁ w₂ : List Op) :
    crossings σ step s (w₁ ++ w₂)
      = crossings σ step s w₁ + crossings σ step (run step s w₁) w₂ := by
  induction w₁ generalizing s with
  | nil => exact (Nat.zero_add _).symm
  | cons o w ih =>
      show (if σ (step s o) = σ s then 0 else 1) + crossings σ step (step s o) (w ++ w₂)
        = ((if σ (step s o) = σ s then 0 else 1) + crossings σ step (step s o) w)
          + crossings σ step (run step (step s o) w) w₂
      rw [ih (step s o), Nat.add_assoc]

/-- Cost never exceeds the op count: one op can move the seam at most once. So
the quantity lives in `[0, w.length]`, and both ends are realised below —
`pinTrue_free_under_seamFalse` at the bottom, `budget_cost_is_three` at the
top. -/
theorem crossings_le_length {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] (σ : S → Seg) (step : S → Op → S) :
    ∀ (s : S) (w : List Op), crossings σ step s w ≤ w.length := by
  intro s w
  induction w generalizing s with
  | nil => exact Nat.le_refl 0
  | cons o w ih =>
      show (if σ (step s o) = σ s then 0 else 1) + crossings σ step (step s o) w
        ≤ w.length + 1
      have h := ih (step s o)
      by_cases hc : σ (step s o) = σ s
      · rw [if_pos hc]; omega
      · rw [if_neg hc]; omega

/-- **A free run never leaves its fiber.** Zero crossings means the seam value
at the end is the seam value at the start — and, by `crossings_append`, at
every intermediate point too. -/
theorem sigma_const_of_crossings_eq_zero {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] {σ : S → Seg} {step : S → Op → S} {s : S} {w : List Op}
    (h : crossings σ step s w = 0) : σ (run step s w) = σ s := by
  induction w generalizing s with
  | nil => rfl
  | cons o w ih =>
      have h' : (if σ (step s o) = σ s then 0 else 1)
          + crossings σ step (step s o) w = 0 := h
      by_cases hc : σ (step s o) = σ s
      · rw [if_pos hc] at h'
        have hrest : crossings σ step (step s o) w = 0 := by omega
        show σ (run step (step s o) w) = σ s
        rw [ih hrest, hc]
      · rw [if_neg hc] at h'
        exact absurd h' (by omega)

/-- The contrapositive, in the form the block calculus consumes: a stream that
ends in a different fiber than it started in costs at least one crossing. -/
theorem one_le_crossings_of_sigma_ne {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] {σ : S → Seg} {step : S → Op → S} {s : S} {w : List Op}
    (h : σ (run step s w) ≠ σ s) : 1 ≤ crossings σ step s w :=
  Nat.pos_of_ne_zero (fun hz => h (sigma_const_of_crossings_eq_zero hz))

/-! ## §2. The block calculus — counting forced changes -/

/-- A block decomposition in which **every block moves the seam**: block `b`
run from `s` ends in a different `σ`-fiber, and the tail is measured from
there. This is the syntactic shape the counting lemma consumes. -/
def BlockChanges {S : Type u} {Seg : Type v} {Op : Type w}
    (σ : S → Seg) (step : S → Op → S) : S → List (List Op) → Prop
  | _, [] => True
  | s, b :: bs => σ (run step s b) ≠ σ s ∧ BlockChanges σ step (run step s b) bs

/-- **The counting lemma.** A stream that decomposes into `n` seam-moving
blocks costs at least `n` crossings. (Blocks are disjoint and cost is additive,
so their individual `≥ 1`s add.) -/
theorem crossings_ge_length {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] {σ : S → Seg} {step : S → Op → S} :
    ∀ (s : S) (bs : List (List Op)), BlockChanges σ step s bs →
      bs.length ≤ crossings σ step s bs.flatten := by
  intro s bs
  induction bs generalizing s with
  | nil => intro _; exact Nat.le_refl 0
  | cons b bs ih =>
      intro h
      have h1 : 1 ≤ crossings σ step s b := one_le_crossings_of_sigma_ne h.1
      have h2 : bs.length ≤ crossings σ step (run step s b) bs.flatten := ih _ h.2
      show bs.length + 1 ≤ crossings σ step s (b ++ bs.flatten)
      rw [crossings_append]
      omega

/-! ## §3. THE LOWER BOUND — coordination forced by the spec, not the seam

A clash pair — two legal states whose merge is illegal — is the *only* thing
that can force two states apart in a seam, and when it does, it does so for
every valid seam at once. That is the leverage: a workload whose trajectory
contains `n` clashing steps costs `n` coordination events under **every**
segmentation anyone could ever choose. -/

/-- A block decomposition in which every block's two endpoints **clash**: each
endpoint is legal on its own, and their merge is not. This is a statement about
the workload and the invariant — no seam appears in it — which is what makes
the bound below a fact about the specification. -/
def ClashBlocks {S : Type u} {Op : Type w} [MergeState S]
    (I : Invariant S) (step : S → Op → S) : S → List (List Op) → Prop
  | _, [] => True
  | s, b :: bs =>
      I s ∧ I (run step s b) ∧ ¬ I (s ⊔ run step s b)
        ∧ ClashBlocks I step (run step s b) bs

/-- **Every valid seam separates every clash block.** If the endpoints of a
block shared a fiber, segmented I-confluence would certify their merge — and
the block says the merge is illegal. So a clash decomposition is a
seam-changing decomposition, for any seam whatsoever. -/
theorem blockChanges_of_clashBlocks {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] {I : Invariant S} {σ : S → Seg} {step : S → Op → S}
    (hseg : SegmentedIConfluent σ I) :
    ∀ (s : S) (bs : List (List Op)), ClashBlocks I step s bs →
      BlockChanges σ step s bs := by
  intro s bs
  induction bs generalizing s with
  | nil => intro _; exact trivial
  | cons b bs ih =>
      intro h
      exact ⟨fun hEq => h.2.2.1 (hseg s (run step s b) hEq.symm h.1 h.2.1).1,
             ih _ h.2.2.2⟩

/-- **THE LOWER BOUND.** A workload whose run passes through `n` successive
clash pairs costs at least `n` coordination events — under the given seam.
`coordination_forced` is the same statement with the seam universally
quantified, which is the reading that matters. -/
theorem coordination_lower_bound {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {I : Invariant S} {σ : S → Seg}
    {step : S → Op → S} {s : S} {bs : List (List Op)}
    (hseg : SegmentedIConfluent σ I) (hcl : ClashBlocks I step s bs) :
    bs.length ≤ crossings σ step s bs.flatten :=
  crossings_ge_length s bs (blockChanges_of_clashBlocks hseg s bs hcl)

/-- **The coordination count is forced by the specification.** The same bound,
now universally quantified over the seam: for **every** segment type in
**every** universe, and every projection onto it that is a valid seam for `I`,
the workload costs at least `bs.length`. No choice of `σ` — no schema
redesign that keeps the invariant — can go below the number of clash pairs the
workload's own trajectory contains.

This is the file's headline. `crossings` depends on an implementation choice;
this floor does not. -/
theorem coordination_forced {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {s : S} {bs : List (List Op)}
    (hcl : ClashBlocks I step s bs) :
    ∀ {Seg : Type v} [DecidableEq Seg] (σ : S → Seg),
      SegmentedIConfluent σ I → bs.length ≤ crossings σ step s bs.flatten :=
  fun _ hseg => coordination_lower_bound hseg hcl

/-! ## §4. Monotone segments cost zero — and every interleaving of them is safe -/

/-- An op is **segment-free** when, from any legal state, it preserves the
invariant and does not move the seam. This is the op-level property; a single
run's zero crossing count is strictly weaker (see the module's non-claims). -/
def SegmentFree {S : Type u} {Seg : Type v} {Op : Type w}
    (σ : S → Seg) (I : Invariant S) (step : S → Op → S) (o : Op) : Prop :=
  ∀ s : S, I s → I (step s o) ∧ σ (step s o) = σ s

/-- **Monotone segments cost zero — the counting half.** A workload built
entirely from segment-free ops has crossing count exactly 0 from any legal
state. -/
theorem crossings_eq_zero_of_segmentFree {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] {σ : S → Seg} {I : Invariant S} {step : S → Op → S} :
    ∀ (s : S) (w : List Op), (∀ o ∈ w, SegmentFree σ I step o) → I s →
      crossings σ step s w = 0 := by
  intro s w
  induction w generalizing s with
  | nil => intro _ _; rfl
  | cons o w ih =>
      intro hall hs
      have ho := hall o List.mem_cons_self s hs
      show (if σ (step s o) = σ s then 0 else 1) + crossings σ step (step s o) w = 0
      rw [if_pos ho.2, ih (step s o) (fun p hp => hall p (List.mem_cons_of_mem o hp)) ho.1]

/-- A scheduling event for two replicas: an op at replica A, an op at replica
B, or a **sync** — the two replicas merge, in both directions. A schedule is a
list of these, so it ranges over every interleaving and every placement of
syncs. -/
inductive Event (Op : Type w) where
  /-- Replica A applies an op locally. -/
  | atA : Op → Event Op
  /-- Replica B applies an op locally. -/
  | atB : Op → Event Op
  /-- The replicas gossip: both take the merge. -/
  | sync : Event Op

/-- One scheduling event applied to the pair of replica states. -/
def evStep {S : Type u} {Op : Type w} [MergeState S] (step : S → Op → S)
    (p : S × S) : Event Op → S × S
  | .atA o => (step p.1 o, p.2)
  | .atB o => (p.1, step p.2 o)
  | .sync => (p.1 ⊔ p.2, p.1 ⊔ p.2)

/-- A whole schedule applied to the pair of replica states. -/
def evRun {S : Type u} {Op : Type w} [MergeState S] (step : S → Op → S)
    (p : S × S) : List (Event Op) → S × S
  | [] => p
  | e :: sch => evRun step (evStep step p e) sch

/-- A scheduling event is free when the op it carries is segment-free; a sync
carries no op and is free unconditionally (that is what the seam buys). -/
def EventFree {S : Type u} {Seg : Type v} {Op : Type w}
    (σ : S → Seg) (I : Invariant S) (step : S → Op → S) : Event Op → Prop
  | .atA o => SegmentFree σ I step o
  | .atB o => SegmentFree σ I step o
  | .sync => True

/-- **Monotone segments cost zero — the confluence half, quantified over every
interleaving.** Two replicas starting legal and in one fiber, running any
schedule at all of segment-free ops and syncs — in any order, with syncs at any
points, any number of times — end legal and still in that fiber, on both sides.

This is where `SegmentedIConfluent` is actually used: it is what makes `sync`
free, and it is what keeps the fiber closed so the next sync is free too. The
statement is `∀ sch`, so no schedule is privileged and no partition schedule is
excluded. -/
theorem interleaving_stays_in_fiber {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] {σ : S → Seg} {I : Invariant S} {step : S → Op → S}
    (hseg : SegmentedIConfluent σ I) :
    ∀ (sch : List (Event Op)) (a b : S), (∀ e ∈ sch, EventFree σ I step e) →
      I a → I b → σ a = σ b →
      I (evRun step (a, b) sch).1 ∧ I (evRun step (a, b) sch).2
        ∧ σ (evRun step (a, b) sch).1 = σ a ∧ σ (evRun step (a, b) sch).2 = σ a := by
  intro sch
  induction sch with
  | nil => intro a b _ ha hb hσ; exact ⟨ha, hb, rfl, hσ.symm⟩
  | cons e sch ih =>
      intro a b hfree ha hb hσ
      have htail : ∀ f ∈ sch, EventFree σ I step f :=
        fun f hf => hfree f (List.mem_cons_of_mem e hf)
      have hhead : EventFree σ I step e := hfree e List.mem_cons_self
      cases e with
      | atA o =>
          have ho : I (step a o) ∧ σ (step a o) = σ a := hhead a ha
          show I (evRun step (step a o, b) sch).1 ∧ I (evRun step (step a o, b) sch).2
            ∧ σ (evRun step (step a o, b) sch).1 = σ a
            ∧ σ (evRun step (step a o, b) sch).2 = σ a
          have hres := ih (step a o) b htail ho.1 hb (by rw [ho.2]; exact hσ)
          exact ⟨hres.1, hres.2.1, by rw [hres.2.2.1, ho.2], by rw [hres.2.2.2, ho.2]⟩
      | atB o =>
          have ho : I (step b o) ∧ σ (step b o) = σ b := hhead b hb
          show I (evRun step (a, step b o) sch).1 ∧ I (evRun step (a, step b o) sch).2
            ∧ σ (evRun step (a, step b o) sch).1 = σ a
            ∧ σ (evRun step (a, step b o) sch).2 = σ a
          exact ih a (step b o) htail ha ho.1 (by rw [ho.2]; exact hσ)
      | sync =>
          have hm := hseg a b hσ ha hb
          show I (evRun step (a ⊔ b, a ⊔ b) sch).1 ∧ I (evRun step (a ⊔ b, a ⊔ b) sch).2
            ∧ σ (evRun step (a ⊔ b, a ⊔ b) sch).1 = σ a
            ∧ σ (evRun step (a ⊔ b, a ⊔ b) sch).2 = σ a
          have hres := ih (a ⊔ b) (a ⊔ b) htail hm.1 hm.1 rfl
          exact ⟨hres.1, hres.2.1, by rw [hres.2.2.1, hm.2], by rw [hres.2.2.2, hm.2]⟩

/-! ## §5. The calibration — the floor is 0 exactly on the monotone fragment

A lower bound that fires everywhere would be worthless. This section shows the
bound is calibrated against the field's own dividing line: on inflationary
(CALM-shaped) workloads it is identically 0, and it can only be positive where
an op overwrites. -/

/-- Every op is an **inflation**: a replica's local step only moves up the
lattice. This is the state-based CRDT discipline, and the lattice-shaped
reading of "monotone". -/
def Inflationary {S : Type u} {Op : Type w} [MergeState S]
    (step : S → Op → S) : Prop := ∀ (s : S) (o : Op), s ⊑ step s o

/-- An inflationary run only moves up: the state after the stream subsumes the
state before it. -/
theorem run_inflationary {S : Type u} {Op : Type w} [MergeState S]
    {step : S → Op → S} (h : Inflationary step) :
    ∀ (s : S) (w : List Op), s ⊑ run step s w := by
  intro s w
  induction w generalizing s with
  | nil => exact leq_refl s
  | cons o w ih => exact leq_trans (h s o) (ih (step s o))

/-- **The floor is 0 on the monotone fragment.** An inflationary workload
admits no clash blocks at all: a block's endpoints are comparable, so their
merge is the later endpoint, which the block itself asserts is legal. The only
clash decomposition is the empty one — the bound of §3 says `0 ≤ crossings`,
which is no constraint.

Read as calibration: `coordination_lower_bound` can only be informative where
ops overwrite, which is exactly where CALM says coordination lives. Read as a
warning: a positive floor is evidence of a non-inflationary op in the workload,
and finding one is the first thing to do about a cost you did not expect. -/
theorem clashBlocks_nil_of_inflationary {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {s : S} {bs : List (List Op)}
    (hinf : Inflationary step) (h : ClashBlocks I step s bs) : bs = [] := by
  cases bs with
  | nil => rfl
  | cons b bs =>
      have hle : s ⊔ run step s b = run step s b := run_inflationary hinf s b
      exact absurd (by rw [hle]; exact h.2.1) h.2.2.1

/-! ## §6. The budget workload — floor 3, achieved 3, TIGHT

`Segmented.lean` proved that a budgeted quota is not I-confluent but is
segmented over the allocation: spends are free, **re-allocation is the
coordination point**. This section counts them. -/

/-- The allocation that hands share `n` (capped at the budget `B`) to device
`true` and the remainder to device `false`. Sums to `B` at every `n`, so every
allocation it produces is budget-legal. -/
def allocOfShare (B n : Nat) : Bool → Nat :=
  fun b => if b then min n B else B - min n B

/-- The re-allocation op: re-divide the budget `B` by handing share `n` to
device `true`, clamping each device's recorded spend to its new quota. This is
the escrow seam's own event, as a local transition. It is **not** an inflation
— a device's quota can go down — which by §5 is what lets it carry a cost. -/
def reallocStep (B : Nat) (s : QuotaState) (n : Nat) : QuotaState :=
  (allocOfShare B n, fun b => min (s.2 b) (allocOfShare B n b))

/-- **The allocation share is a seam.** On budget-legal states the share held
by device `true` determines the whole allocation (the two sum to `B`), so
`Segmented.budget_segmented`'s seam may be read as a single number — which is
what makes crossing counts against it computable. -/
theorem share_segmented (B : Nat) :
    SegmentedIConfluent (S := QuotaState) (fun s => s.1 true) (BudgetInv B) := by
  intro x y hσ hx hy
  have hs : x.1 true = y.1 true := hσ
  have hfull : x.1 = y.1 := by
    funext b
    cases b with
    | false =>
        have h1 : x.1 true + x.1 false = B := hx.2
        have h2 : y.1 true + y.1 false = B := hy.2
        omega
    | true => exact hs
  have h := budget_segmented B x y hfull hx hy
  exact ⟨h.1, congrFun h.2 true⟩

/-- The starting quota state: the whole budget of 10 on device `true`, nothing
spent. -/
def budgetStart : QuotaState := (allocOfShare 10 10, fun _ => 0)

/-- ⚠ **Re-allocation is not an inflation.** Moving the whole budget from
device `true` to device `false` lowers `true`'s quota, so the merge of the old
and new states is neither of them — it is the over-budget pointwise max. By §5
this is exactly what lets the op carry a cost: an inflationary op could not. -/
theorem reallocStep_not_inflationary : ¬ Inflationary (reallocStep 10) := by
  intro h
  have hle : budgetStart ⊔ reallocStep 10 budgetStart 0
      = reallocStep 10 budgetStart 0 := h budgetStart 0
  exact absurd (congrFun (congrArg Prod.fst hle) true) (by decide)

/-- The demo workload: three re-divisions of the budget — everything to device
`false`, then an even split, then three-seven. -/
def budgetW : List Nat := [0, 5, 3]

/-- The demo workload, one re-allocation per block. -/
def budgetBlocks : List (List Nat) := [[0], [5], [3]]

/-- The blocks really are the workload. -/
theorem budgetBlocks_flatten : budgetBlocks.flatten = budgetW := rfl

/-- **Every step of the demo workload is a clash.** Each successive pair of
allocations is legal on its own and merges to an over-budget one — the
`Segmented.budget_not_iconfluent` witness, three times in a row along a single
run. -/
theorem budget_clashBlocks :
    ClashBlocks (BudgetInv 10) (reallocStep 10) budgetStart budgetBlocks := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide
  · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide
  · exact fun h => absurd h.2 (by decide)
  · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide
  · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide
  · exact fun h => absurd h.2 (by decide)
  · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide
  · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide
  · exact fun h => absurd h.2 (by decide)

/-- **How often must I coordinate, given this workload? Exactly three times.**

The first conjunct is the floor: for **every** segment type in every universe
and every valid seam on it, three re-divisions of the budget cost at least
three coordination events. The second is the witness that three is enough: the
allocation-share seam of `share_segmented` pays exactly three.

Floor and achievement meet, so this is not a bound on the workload's
coordination frequency — it **is** the workload's coordination frequency. -/
theorem budget_cost_is_three :
    (∀ {Seg : Type v} [DecidableEq Seg] (σ : QuotaState → Seg),
        SegmentedIConfluent σ (BudgetInv 10) →
        3 ≤ crossings σ (reallocStep 10) budgetStart budgetW)
      ∧ crossings (fun s : QuotaState => s.1 true) (reallocStep 10)
          budgetStart budgetW = 3 := by
  constructor
  · intro Seg _ σ hseg
    have h := coordination_forced (I := BudgetInv 10) budget_clashBlocks σ hseg
    rw [budgetBlocks_flatten] at h
    exact h
  · decide

/-- The achieving seam is a real seam, cited as a term — the second conjunct of
`budget_cost_is_three` is a count against `share_segmented`'s judgement, not
against an arbitrary projection. -/
example : SegmentedIConfluent (S := QuotaState) (fun s => s.1 true) (BudgetInv 10) :=
  share_segmented 10

/-! ## §7. The linked document, counted — and the naive reading corrected

`SeamAlgebra` §7 pairs a versioned store with a budgeted quota and shows that
**linking** them (the schema version dictates the allocation) collapses two
coordination points into one. This section runs the same behaviour through both
documents and counts. The result is not quite the slogan. -/

/-- Ops on the unlinked two-field document: advance the schema version, or
re-divide the budget. Two independent events — which is what "two coordination
points" means. -/
inductive DocOp where
  /-- Advance the schema version by one. -/
  | bump : DocOp
  /-- Re-divide the budget, handing share `n` to device `true`. -/
  | realloc : Nat → DocOp

/-- The unlinked document's local transition. -/
def docStep (p : TwoFieldDoc) : DocOp → TwoFieldDoc
  | .bump => ((p.1.1 + 1, p.1.2), p.2)
  | .realloc n => (p.1, reallocStep 10 p.2 n)

/-- The allocation policy that links the two fields here: version `v` dictates
share `5 * v`. Distinct at every version in play, so each flag day really does
re-divide the budget. (`SeamAlgebra.allocOf` is the file's own policy; it is
constant from version 1 on, which would make the second flag day a no-op for
the quota and hide the very thing we are counting.) -/
def linkAlloc : Nat → (Bool → Nat) := fun v => allocOfShare 10 (5 * v)

/-- The linked well-formedness: store legal, quota legal, and the allocation is
the one the current version dictates — `SeamAlgebra.LinkedInv` at `linkAlloc`. -/
def LinkedWF : Invariant TwoFieldDoc :=
  LinkedInv (SchemaWF tightBound) (BudgetInv 10) Prod.fst Prod.fst linkAlloc

/-- The linked document's local transition — the flag day, as one op: bump the
version and re-allocate to what the new version dictates. There is only one op,
because on the linked document there is only one kind of event. -/
def flagDayStep (p : TwoFieldDoc) (_ : Unit) : TwoFieldDoc :=
  ((p.1.1 + 1, p.1.2),
    (linkAlloc (p.1.1 + 1), fun b => min (p.2.2 b) (linkAlloc (p.1.1 + 1) b)))

/-- The common starting document: version 0, no records, the allocation version
0 dictates, nothing spent. Legal for both well-formedness notions. -/
def docStart : TwoFieldDoc := ((0, fun _ => false), (linkAlloc 0, fun _ => 0))

/-- The unlinked workload: two version bumps and two re-allocations, as four
separate events. -/
def unlinkedW : List DocOp := [.bump, .realloc 5, .bump, .realloc 10]

/-- The linked workload: the same behaviour as two flag days. -/
def linkedW : List Unit := [(), ()]

/-- **The two workloads are the same behaviour.** Same start, same end: version
2, no records, the whole budget on device `true`, nothing spent. Everything
below compares the cost of one behaviour under two schemas, not the cost of two
different things. -/
theorem same_behaviour :
    run docStep docStart unlinkedW = run flagDayStep docStart linkedW := rfl

/-- **The share-projected pair seam segments the unlinked document.** The pair
seam of `SeamAlgebra.twoField_segmented` is `(version, allocation)`; on legal
states the allocation is determined by device `true`'s share, so the seam may
be read as a pair of numbers — the form a crossing count can be taken
against. -/
theorem twoFieldShare_segmented :
    SegmentedIConfluent (S := TwoFieldDoc) (fun p => (p.1.1, p.2.1 true))
      twoFieldInv := by
  intro x y hσ hx hy
  have hσ' : ((x.1.1, x.2.1 true) : Nat × Nat) = (y.1.1, y.2.1 true) := hσ
  have hv : x.1.1 = y.1.1 := congrArg (fun p : Nat × Nat => p.1) hσ'
  have ht : x.2.1 true = y.2.1 true := congrArg (fun p : Nat × Nat => p.2) hσ'
  have halloc : x.2.1 = y.2.1 := by
    funext b
    cases b with
    | false =>
        have h1 : x.2.1 true + x.2.1 false = 10 := hx.2.2
        have h2 : y.2.1 true + y.2.1 false = 10 := hy.2.2
        omega
    | true => exact ht
  have harg : ((x.1.1, x.2.1) : Nat × (Bool → Nat)) = (y.1.1, y.2.1) := by
    rw [hv, halloc]
  have h := twoField_segmented x y harg hx hy
  have h2' : (((x ⊔ y).1.1, (x ⊔ y).2.1) : Nat × (Bool → Nat)) = (x.1.1, x.2.1) := h.2
  refine ⟨h.1, ?_⟩
  have e1 : (x ⊔ y).1.1 = x.1.1 := congrArg (fun p : Nat × (Bool → Nat) => p.1) h2'
  have e2 : (x ⊔ y).2.1 = x.2.1 := congrArg (fun p : Nat × (Bool → Nat) => p.2) h2'
  show ((x ⊔ y).1.1, (x ⊔ y).2.1 true) = (x.1.1, x.2.1 true)
  rw [e1, e2]

/-- **The version alone segments the linked document** — `linked_segmented` at
this instance, with `linkAlloc` as the link. Re-allocation is not a coordination
point of its own; it is something the version change does. -/
theorem linkedWF_segmented :
    SegmentedIConfluent (S := TwoFieldDoc) (fun p => p.1.1) LinkedWF :=
  linked_segmented linkAlloc (schema_segmented tightBound) (budget_segmented 10)

/-- **The count.** The same behaviour costs **four** crossings on the unlinked
document under its canonical pair seam, and **two** on the linked document
under the version seam. This is `SeamAlgebra.linked_segmented`'s saving as a
number: two coordination points, each fired twice, become one fired twice. -/
theorem linked_halves_the_crossings :
    crossings (fun p : TwoFieldDoc => (p.1.1, p.2.1 true)) docStep docStart
        unlinkedW = 4
      ∧ crossings (fun p : TwoFieldDoc => p.1.1) flagDayStep docStart linkedW = 2 :=
  ⟨by decide, by decide⟩

/-- The unlinked workload, blocked at its two re-allocations: a version bump on
an empty store merges harmlessly, so it is the budget events that clash. -/
def unlinkedBlocks : List (List DocOp) :=
  [[.bump, .realloc 5], [.bump, .realloc 10]]

/-- The blocks really are the unlinked workload. -/
theorem unlinkedBlocks_flatten : unlinkedBlocks.flatten = unlinkedW := rfl

/-- The linked workload, blocked one flag day at a time. -/
def linkedBlocks : List (List Unit) := [[()], [()]]

/-- The blocks really are the linked workload. -/
theorem linkedBlocks_flatten : linkedBlocks.flatten = linkedW := rfl

/-- Two clash blocks on the unlinked document: each block's re-allocation makes
its endpoints merge over budget. -/
theorem unlinked_clashBlocks :
    ClashBlocks twoFieldInv docStep docStart unlinkedBlocks := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact ⟨fun _ hn => absurd (show (false : Bool) = true from hn) (by decide), by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide⟩
  · exact ⟨fun _ hn => absurd (show (false : Bool) = true from hn) (by decide), by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide⟩
  · exact fun h => absurd h.2.2 (by decide)
  · exact ⟨fun _ hn => absurd (show (false : Bool) = true from hn) (by decide), by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide⟩
  · exact ⟨fun _ hn => absurd (show (false : Bool) = true from hn) (by decide), by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide⟩
  · exact fun h => absurd h.2.2 (by decide)

/-- Two clash blocks on the linked document: each flag day's endpoints merge
over budget too. -/
theorem linked_clashBlocks :
    ClashBlocks LinkedWF flagDayStep docStart linkedBlocks := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · exact ⟨fun _ hn => absurd (show (false : Bool) = true from hn) (by decide),
           by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide, rfl⟩
  · exact ⟨fun _ hn => absurd (show (false : Bool) = true from hn) (by decide),
           by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide, rfl⟩
  · exact fun h => absurd h.2.1.2 (by decide)
  · exact ⟨fun _ hn => absurd (show (false : Bool) = true from hn) (by decide),
           by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide, rfl⟩
  · exact ⟨fun _ hn => absurd (show (false : Bool) = true from hn) (by decide),
           by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide, rfl⟩
  · exact fun h => absurd h.2.1.2 (by decide)

/-- ⚠ **The unlinked document's floor is two, not four.** Under every valid
seam, the unlinked workload costs at least two coordination events — the two
re-allocations. Its canonical pair seam pays four
(`linked_halves_the_crossings`), so those four are the price of *that seam*,
not of the specification. -/
theorem unlinked_floor_is_two :
    ∀ {Seg : Type v} [DecidableEq Seg] (σ : TwoFieldDoc → Seg),
      SegmentedIConfluent σ twoFieldInv →
      2 ≤ crossings σ docStep docStart unlinkedW := by
  intro Seg _ σ hseg
  have h := coordination_forced (I := twoFieldInv) unlinked_clashBlocks σ hseg
  rw [unlinkedBlocks_flatten] at h
  exact h

/-- **The linked document's floor is two, and it pays two.** Under every valid
seam the linked workload costs at least two, and the version seam of
`linkedWF_segmented` costs exactly two. The linked document is optimal for this
behaviour. -/
theorem linked_floor_is_two :
    (∀ {Seg : Type v} [DecidableEq Seg] (σ : TwoFieldDoc → Seg),
        SegmentedIConfluent σ LinkedWF →
        2 ≤ crossings σ flagDayStep docStart linkedW)
      ∧ crossings (fun p : TwoFieldDoc => p.1.1) flagDayStep docStart linkedW = 2 := by
  constructor
  · intro Seg _ σ hseg
    have h := coordination_forced (I := LinkedWF) linked_clashBlocks σ hseg
    rw [linkedBlocks_flatten] at h
    exact h
  · decide

/-! ⚠ **What §7 actually shows.** Both documents have a floor of two. The link
does not make the behaviour cheaper; it makes the *obvious* seam optimal. The
unlinked document's four crossings are a fact about reading `(version,
allocation)` as the seam — the reading `SeamAlgebra.no_schema_only_seam` and
`no_quota_only_seam` push you toward — and not a fact about the document.

⟨UNDONE⟩ Whether four is optimal for the unlinked document. A seam reading
"does the store hold a record the next version will forbid" separates the
schema clash without separating our workload's versions, and would plausibly
reach two; it is not `DecidableEq`-shaped as written, and we did not prove it a
valid seam. Until someone does, "unlinked costs four" means "costs four under
this seam", and the honest comparison is floor-to-floor: two and two. -/

/-! ## §8. Amortization, as far as it honestly goes

The distinction the module docstring flags — crossings are not meetings — has
exactly one half this file can prove: **re-blocking**. If the workload's
intermediate states are never occupied, they are never paid for, and both the
floor and the achieved count collapse to one. That is what a batch *is*. -/

/-- The batched workload: the whole of `budgetW` as a single op. A replica that
applies this never occupies the intermediate allocations. -/
def batchStep (s : QuotaState) (_ : Unit) : QuotaState :=
  run (reallocStep 10) s budgetW

/-- The batched workload is one op. -/
def batchW : List Unit := [()]

/-- The batched workload, as one block. -/
def batchBlocks : List (List Unit) := [[()]]

/-- The block really is the batched workload. -/
theorem batchBlocks_flatten : batchBlocks.flatten = batchW := rfl

/-- The batched workload's single block is still a clash: the first and last
allocations merge over budget, so the batch is not free either. -/
theorem batch_clashBlocks :
    ClashBlocks (BudgetInv 10) batchStep budgetStart batchBlocks := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide
  · refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide
  · exact fun h => absurd h.2 (by decide)

/-- **Batching amortizes three coordination events into one — floor included.**
The same net re-division that costs exactly three when its three steps are
separately occupied (`budget_cost_is_three`) costs exactly one when they are
one op: floor one, achieved one.

The saving is not a trick of the measure. It is the content of batching: the
intermediate allocations were the clash pairs, and a batch is the statement
that no replica is ever in them. What this does **not** model, and the module
docstring records as ⟨UNDONE⟩, is a *meeting* that agrees several future seam
values in one round while replicas do occupy the intermediate states. -/
theorem batched_cost_is_one :
    (∀ {Seg : Type v} [DecidableEq Seg] (σ : QuotaState → Seg),
        SegmentedIConfluent σ (BudgetInv 10) →
        1 ≤ crossings σ batchStep budgetStart batchW)
      ∧ crossings (fun s : QuotaState => s.1 true) batchStep budgetStart batchW = 1 := by
  constructor
  · intro Seg _ σ hseg
    have h := coordination_forced (I := BudgetInv 10) batch_clashBlocks σ hseg
    rw [batchBlocks_flatten] at h
    exact h
  · decide

/-! ## §9. ⚠ The refutation — where the measure undercounts

`crossings σ step s w` reads **one stream against one seam**. A workload is
run by several replicas, and they must share a seam. This section exhibits the
gap concretely, on the uniqueness ceiling: two streams, each free under a seam
of its own, and no single valid seam that frees both. -/

/-- The one-slot pin over two candidate nodes, as a grow-only set. -/
abbrev PinSet := GSet Bool

/-- The uniqueness ceiling on the pin: at most one node is pinned —
`Catalog.gset_atMostOne_not_iconfluent`'s invariant, over `Bool`. -/
def pinInv : Invariant PinSet := fun s => ∀ m n : Bool, s m = true → s n = true → m = n

/-- Pinning a node: add it to the set. Inflationary, so §5 says the floor on
any single stream of these is zero — which is exactly why the undercount below
is not visible to the floor. -/
def pinStep (s : PinSet) (b : Bool) : PinSet := fun m => s m || (m == b)

/-- Nothing pinned yet. -/
def emptyPin : PinSet := fun _ => false

/-- **Pinning really is an inflation**, so `clashBlocks_nil_of_inflationary`
gives each stream below a floor of zero. That is *why* the undercount is
invisible to §3's bound: the coordination these two streams need is between
them, not along either one, and no per-stream clash exists to see. -/
theorem pinStep_inflationary : Inflationary pinStep := by
  intro s b
  show (fun m => s m || (s m || (m == b))) = fun m => s m || (m == b)
  funext m
  rw [← Bool.or_assoc, Bool.or_self]

/-- **"Is `false` pinned?" is a valid seam.** Its two fibers are `{nothing,
just true}` — whose merges are legal — and `{just false}`. So a replica may pin
`true` without ever leaving its fiber. -/
theorem seamFalse_segmented :
    SegmentedIConfluent (S := PinSet) (fun s => s false) pinInv := by
  intro x y hσ hx hy
  have hf : x false = y false := hσ
  refine ⟨?_, ?_⟩
  · intro m n hm hn
    have hm' : (x m || y m) = true := hm
    have hn' : (x n || y n) = true := hn
    cases m with
    | false =>
        cases n with
        | false => rfl
        | true =>
            have hxf : x false = true := by
              rcases (Bool.or_eq_true _ _).mp hm' with h | h
              · exact h
              · rw [hf]; exact h
            rcases (Bool.or_eq_true _ _).mp hn' with h | h
            · exact hx false true hxf h
            · exact hy false true (by rw [← hf]; exact hxf) h
    | true =>
        cases n with
        | false =>
            have hxf : x false = true := by
              rcases (Bool.or_eq_true _ _).mp hn' with h | h
              · exact h
              · rw [hf]; exact h
            rcases (Bool.or_eq_true _ _).mp hm' with h | h
            · exact hx true false h hxf
            · exact hy true false h (by rw [← hf]; exact hxf)
        | true => rfl
  · show (x false || y false) = x false
    rw [← hf, Bool.or_self]

/-- **"Is `true` pinned?" is a valid seam** — the mirror image, freeing the
other stream. -/
theorem seamTrue_segmented :
    SegmentedIConfluent (S := PinSet) (fun s => s true) pinInv := by
  intro x y hσ hx hy
  have ht : x true = y true := hσ
  refine ⟨?_, ?_⟩
  · intro m n hm hn
    have hm' : (x m || y m) = true := hm
    have hn' : (x n || y n) = true := hn
    cases m with
    | true =>
        cases n with
        | true => rfl
        | false =>
            have hxt : x true = true := by
              rcases (Bool.or_eq_true _ _).mp hm' with h | h
              · exact h
              · rw [ht]; exact h
            rcases (Bool.or_eq_true _ _).mp hn' with h | h
            · exact hx true false hxt h
            · exact hy true false (by rw [← ht]; exact hxt) h
    | false =>
        cases n with
        | true =>
            have hxt : x true = true := by
              rcases (Bool.or_eq_true _ _).mp hn' with h | h
              · exact h
              · rw [ht]; exact h
            rcases (Bool.or_eq_true _ _).mp hm' with h | h
            · exact hx false true h hxt
            · exact hy false true h (by rw [← ht]; exact hxt)
        | false => rfl
  · show (x true || y true) = x true
    rw [← ht, Bool.or_self]

/-- Pinning `true` from nothing is free under the `false`-seam. -/
theorem pinTrue_free_under_seamFalse :
    crossings (fun s : PinSet => s false) pinStep emptyPin [true] = 0 := by decide

/-- Pinning `false` from nothing is free under the `true`-seam. -/
theorem pinFalse_free_under_seamTrue :
    crossings (fun s : PinSet => s true) pinStep emptyPin [false] = 0 := by decide

/-- ⚠ **The undercount, proved: no single valid seam frees both streams.**
Each of the two one-op streams costs zero under a seam of its own
(`pinTrue_free_under_seamFalse`, `pinFalse_free_under_seamTrue`), so the
per-stream minimum of `crossings` is 0 for each. But if one seam gave both
streams cost zero, the two pinned states would share a fiber — and their merge
pins two nodes, which segmented I-confluence forbids. Two replicas running
these streams concurrently must coordinate; no per-stream crossing count says
so.

**This is the measure's domain of validity, stated as scope rather than
patched:** `crossings` is a per-stream, per-seam quantity, sound as the cost of
*one* replica's trajectory once a seam is fixed, and an under-estimate of a
concurrent workload's cost, because the seam is a global choice and the streams
do not get one each. -/
theorem no_seam_frees_both {Seg : Type v} [DecidableEq Seg] (σ : PinSet → Seg)
    (hseg : SegmentedIConfluent σ pinInv) :
    ¬ (crossings σ pinStep emptyPin [true] = 0
        ∧ crossings σ pinStep emptyPin [false] = 0) := by
  intro ⟨h1, h2⟩
  have e1 : σ (pinStep emptyPin true) = σ emptyPin :=
    sigma_const_of_crossings_eq_zero h1
  have e2 : σ (pinStep emptyPin false) = σ emptyPin :=
    sigma_const_of_crossings_eq_zero h2
  have hlegT : pinInv (pinStep emptyPin true) := by
    intro m n hm hn
    cases m with
    | false => cases n with
      | false => rfl
      | true => exact absurd hm (by decide)
    | true => cases n with
      | false => exact absurd hn (by decide)
      | true => rfl
  have hlegF : pinInv (pinStep emptyPin false) := by
    intro m n hm hn
    cases m with
    | false => cases n with
      | false => rfl
      | true => exact absurd hn (by decide)
    | true => cases n with
      | false => exact absurd hm (by decide)
      | true => rfl
  have hbad := (hseg _ _ (e1.trans e2.symm) hlegT hlegF).1
  exact absurd (hbad true false (by decide) (by decide)) (by decide)

/-! ## §10. The readings, side by side

Three answers to "how often must I coordinate?", on three schemas, each a term
rather than a slogan. -/

/-- Three re-divisions of a shared budget: three coordination events, floor and
achievement. -/
example : crossings (fun s : QuotaState => s.1 true) (reallocStep 10)
    budgetStart budgetW = 3 := budget_cost_is_three.{0}.2

/-- The same net re-division, batched: one. -/
example : crossings (fun s : QuotaState => s.1 true) batchStep
    budgetStart batchW = 1 := batched_cost_is_one.{0}.2

/-- Two flag days on the linked document: two, and two is the floor. -/
example : crossings (fun p : TwoFieldDoc => p.1.1) flagDayStep docStart linkedW = 2 :=
  linked_floor_is_two.{0}.2

end Uwueave.Cost
